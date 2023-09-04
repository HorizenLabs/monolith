//! Implementation of the Poseidon hash function, as described in
//! <https://eprint.iacr.org/2019/458.pdf>

use alloc::vec;
use alloc::vec::Vec;

use unroll::unroll_for_loops;

use crate::field::extension::{Extendable, FieldExtension};
use crate::field::types::{Field, PrimeField64};
use crate::gates::monolith::MonolithGate;
use crate::gates::split_monolith::monolith_init::MonolithInitGate;
use crate::gates::split_monolith::monolith_rounds::MonolithRoundsGate;
use crate::hash::hash_types::{HashOut, RichField};
use crate::hash::hashing::{compress, hash_n_to_hash_no_pad, PlonkyPermutation};
use crate::iop::ext_target::ExtensionTarget;
use crate::iop::target::{BoolTarget, Target};
use crate::plonk::circuit_builder::CircuitBuilder;
use crate::plonk::config::{AlgebraicHasher, Hasher, MonolithHashConfig};
use crate::hash::monolith_mds_12::mds_multiply_u128;

pub const SPONGE_RATE: usize = 8;
pub const SPONGE_CAPACITY: usize = 4;
pub const SPONGE_WIDTH: usize = SPONGE_RATE + SPONGE_CAPACITY;
pub const NUM_BARS: usize = 4;

// The number of full rounds and partial rounds is given by the
// calc_round_numbers.py script. They happen to be the same for both
// width 8 and width 12 with s-box x^7.
//
// NB: Changing any of these values will require regenerating all of
// the precomputed constant arrays in this file.
pub const N_ROUNDS: usize = 6;
pub const LOOKUP_BITS: usize = 8;
pub const LOOKUP_SIZE: usize = 1 << LOOKUP_BITS;
pub const LOOKUP_NUM_LIMBS: usize = 64 / LOOKUP_BITS;

const _MAX_WIDTH: usize = 12; // we only have width 8 and 12, and 12 is bigger. :)

#[inline(always)]
fn _add_u160_u128((x_lo, x_hi): (u128, u32), y: u128) -> (u128, u32) {
    let (res_lo, over) = x_lo.overflowing_add(y);
    let res_hi = x_hi + (over as u32);
    (res_lo, res_hi)
}

#[inline(always)]
fn _reduce_u160<F: PrimeField64>((n_lo, n_hi): (u128, u32)) -> F {
    let n_lo_hi = (n_lo >> 64) as u64;
    let n_lo_lo = n_lo as u64;
    let reduced_hi: u64 = F::from_noncanonical_u96((n_lo_hi, n_hi)).to_noncanonical_u64();
    let reduced128: u128 = ((reduced_hi as u128) << 64) + (n_lo_lo as u128);
    F::from_noncanonical_u128(reduced128)
}

// Temp helpers
const EPSILON: u64 = u32::MAX as u64;
#[inline]
pub fn split(x: u128) -> (u64, u64) {
    (x as u64, (x >> 64) as u64)
}

#[cfg(target_arch = "x86_64")]
unsafe fn add_no_canonicalize_trashing_input(x: u64, y: u64) -> u64 {
    let res_wrapped: u64;
    let adjustment: u64;
    core::arch::asm!(
        "add {0}, {1}",
        // Trick. The carry flag is set iff the addition overflowed.
        // sbb x, y does x := x - y - CF. In our case, x and y are both {1:e}, so it simply does
        // {1:e} := 0xffffffff on overflow and {1:e} := 0 otherwise. {1:e} is the low 32 bits of
        // {1}; the high 32-bits are zeroed on write. In the end, we end up with 0xffffffff in {1}
        // on overflow; this happens be EPSILON.
        // Note that the CPU does not realize that the result of sbb x, x does not actually depend
        // on x. We must write the result to a register that we know to be ready. We have a
        // dependency on {1} anyway, so let's use it.
        "sbb {1:e}, {1:e}",
        inlateout(reg) x => res_wrapped,
        inlateout(reg) y => adjustment,
        options(pure, nomem, nostack),
    );
    // assume(x != 0 || (res_wrapped == y && adjustment == 0));
    // assume(y != 0 || (res_wrapped == x && adjustment == 0));
    // Add EPSILON == subtract ORDER.
    // Cannot overflow unless the assumption if x + y < 2**64 + ORDER is incorrect.
    res_wrapped + adjustment
}

#[inline(always)]
fn branch_hint() {
    // NOTE: These are the currently supported assembly architectures. See the
    // [nightly reference](https://doc.rust-lang.org/nightly/reference/inline-assembly.html) for
    // the most up-to-date list.
    #[cfg(any(
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "riscv32",
        target_arch = "riscv64",
        target_arch = "x86",
        target_arch = "x86_64",
    ))]
    unsafe {
        core::arch::asm!("", options(nomem, nostack, preserves_flags));
    }
}

fn reduce96(x: &mut u128) {
    let (x_lo, x_hi_lo) = split(*x); // This is a no-op
    let t1 = x_hi_lo * EPSILON;
    *x = unsafe { add_no_canonicalize_trashing_input(x_lo, t1) } as u128;
}

fn reduce128(x: &mut u128) {
    let (x_lo, x_hi) = split(*x); // This is a no-op
    let x_hi_hi = x_hi >> 32;
    let x_hi_lo = x_hi & EPSILON;

    let (mut t0, borrow) = x_lo.overflowing_sub(x_hi_hi);
    if borrow {
        branch_hint(); // A borrow is exceedingly rare. It is faster to branch.
        t0 -= EPSILON; // Cannot underflow.
    }
    let t1 = x_hi_lo * EPSILON;
    *x = unsafe { add_no_canonicalize_trashing_input(t0, t1) } as u128;
}

// const LOOKUP_TABLE: [u16; LOOKUP_SIZE] = [
//     0, 2, 4, 22, 8, 10, 44, 46, 16, 18, 20, 6, 88, 90, 92, 94,
//     32, 34, 36, 54, 40, 42, 12, 14, 176, 178, 180, 166, 184, 186, 188, 190,
//     64, 66, 68, 86, 72, 74, 108, 110, 80, 82, 84, 70, 24, 26, 28, 30,
//     97, 99, 101, 119, 105, 107, 77, 79, 113, 115, 117, 103, 121, 123, 125, 127,
//     128, 130, 132, 150, 136, 138, 172, 174, 144, 146, 148, 134, 216, 218, 220, 222,
//     160, 162, 164, 182, 168, 170, 140, 142, 48, 50, 52, 38, 56, 58, 60, 62,
//     194, 192, 198, 212, 202, 200, 238, 236, 210, 208, 214, 196, 154, 152, 158, 156,
//     226, 224, 230, 244, 234, 232, 206, 204, 242, 240, 246, 228, 250, 248, 254, 252,
//     1, 11, 5, 23, 9, 3, 45, 47, 17, 27, 21, 7, 89, 83, 93, 95,
//     33, 43, 37, 55, 41, 35, 13, 15, 177, 187, 181, 167, 185, 179, 189, 191,
//     65, 75, 69, 87, 73, 67, 109, 111, 81, 91, 85, 71, 25, 19, 29, 31,
//     96, 106, 100, 118, 104, 98, 76, 78, 112, 122, 116, 102, 120, 114, 124, 126,
//     133, 139, 129, 151, 141, 131, 169, 175, 149, 155, 145, 135, 221, 211, 217, 223,
//     165, 171, 161, 183, 173, 163, 137, 143, 53, 59, 49, 39, 61, 51, 57, 63,
//     197, 203, 193, 215, 205, 195, 233, 239, 213, 219, 209, 199, 157, 147, 153, 159,
//     229, 235, 225, 247, 237, 227, 201, 207, 245, 251, 241, 231, 253, 243, 249, 255,
// ];

pub trait Monolith: PrimeField64 {
    // Static data
    const N_ROUND_CONSTANTS: usize = SPONGE_WIDTH * (N_ROUNDS + 1);
    const ROUND_CONSTANTS: [[u64; SPONGE_WIDTH]; N_ROUNDS + 1];
    const MAT_12: [[u64; SPONGE_WIDTH]; SPONGE_WIDTH];

    /// Compute the "Bar" component
    /// element is split in (16-bit lookups, analogous for 8-bit lookups):
    /// [x_3 || x_2 || x_1 || x_0], where x_i is 16 bits large
    /// element = 2^48 * x_3 + 2^32 * x_2 + 2^16 * x_1 + x_0
    /// Use lookups on x_3, x_2, x_1, x_0 and obtain y_3, y_2, y_1, y_0
    /// [y_3 || y_2 || y_1 || y_0], where y_i is 16 bits large
    /// Output y is set such that y = 2^48 * x_3 + 2^32 * x_2 + 2^16 * x_1 + x_0
    #[inline(always)]
    #[unroll_for_loops]
    fn bar(limb: &mut Self) {
        match LOOKUP_BITS {
            8 => {
                let limb_u64 = limb.to_canonical_u64();
                let limbl1 = ((!limb_u64 & 0x8080808080808080) >> 7) | ((!limb_u64 & 0x7F7F7F7F7F7F7F7F) << 1); // Left rotation by 1
                let limbl2 = ((limb_u64 & 0xC0C0C0C0C0C0C0C0) >> 6) | ((limb_u64 & 0x3F3F3F3F3F3F3F3F) << 2); // Left rotation by 2
                let limbl3 = ((limb_u64 & 0xE0E0E0E0E0E0E0E0) >> 5) | ((limb_u64 & 0x1F1F1F1F1F1F1F1F) << 3); // Left rotation by 3

                let tmp = limb_u64 ^ limbl1 & limbl2 & limbl3;
                *limb = Self::from_canonical_u64(((tmp & 0x8080808080808080) >> 7) | ((tmp & 0x7F7F7F7F7F7F7F7F) << 1)); // Final rotation
            },
            16 => {
                let limb_u64 = limb.to_canonical_u64();
                let limbl1 = ((!limb_u64 & 0x8000800080008000) >> 15) | ((!limb_u64 & 0x7FFF7FFF7FFF7FFF) << 1); // Left rotation by 1
                let limbl2 = ((limb_u64 & 0xC000C000C000C000) >> 14) | ((limb_u64 & 0x3FFF3FFF3FFF3FFF) << 2); // Left rotation by 2
                let limbl3 = ((limb_u64 & 0xE000E000E000E000) >> 13) | ((limb_u64 & 0x1FFF1FFF1FFF1FFF) << 3); // Left rotation by 3

                let tmp = limb_u64 ^ limbl1 & limbl2 & limbl3;
                *limb = Self::from_canonical_u64(((tmp & 0x8000800080008000) >> 15) | ((tmp & 0x7FFF7FFF7FFF7FFF) << 1)); // Final rotation
            }
            _ => {
                panic!("Unsupported lookup size");
            }
        }
    }

    /// Same as `bar` optimized for u128 (helper)
    #[inline(always)]
    fn bar_64(limb: u64) -> u64 {
        match LOOKUP_BITS {
            8 => {
                let limbl1 = ((!limb & 0x8080808080808080) >> 7) | ((!limb & 0x7F7F7F7F7F7F7F7F) << 1); // Left rotation by 1
                let limbl2 = ((limb & 0xC0C0C0C0C0C0C0C0) >> 6) | ((limb & 0x3F3F3F3F3F3F3F3F) << 2); // Left rotation by 2
                let limbl3 = ((limb & 0xE0E0E0E0E0E0E0E0) >> 5) | ((limb & 0x1F1F1F1F1F1F1F1F) << 3); // Left rotation by 3

                // y_i = x_i + (1 + x_{i+1}) * x_{i+2} * x_{i+3}
                let tmp = limb ^ limbl1 & limbl2 & limbl3;
                ((tmp & 0x8080808080808080) >> 7) | ((tmp & 0x7F7F7F7F7F7F7F7F) << 1)
            },
            16 => {
                let limbl1 = ((!limb & 0x8000800080008000) >> 15) | ((!limb & 0x7FFF7FFF7FFF7FFF) << 1); // Left rotation by 1
                let limbl2 = ((limb & 0xC000C000C000C000) >> 14) | ((limb & 0x3FFF3FFF3FFF3FFF) << 2); // Left rotation by 2
                let limbl3 = ((limb & 0xE000E000E000E000) >> 13) | ((limb & 0x1FFF1FFF1FFF1FFF) << 3); // Left rotation by 3

                // y_i = x_i + (1 + x_{i+1}) * x_{i+2} * x_{i+3}
                let tmp = limb ^ limbl1 & limbl2 & limbl3;
                ((tmp & 0x8000800080008000) >> 15) | ((tmp & 0x7FFF7FFF7FFF7FFF) << 1) // Final rotation
            }
            _ => {
                panic!("Unsupported lookup size");
            }
        }
    }

    /// Same as `bar` optimized for u128
    #[inline(always)]
    fn bar_u128(el: &mut u128) {
        *el = Self::bar_64(*el as u64) as u128;
    }

    /// Compute the "Bars" component
    #[inline(always)]
    #[unroll_for_loops]
    fn bars(state: &mut [Self; SPONGE_WIDTH]) {
        Self::bar(&mut state[0]);
        Self::bar(&mut state[1]);
        Self::bar(&mut state[2]);
        Self::bar(&mut state[3]);
    }

    /// Same as `bars` optimized for u128
    fn bars_u128(state_u128: &mut [u128; SPONGE_WIDTH]) {
        Self::bar_u128(&mut state_u128[0]);
        Self::bar_u128(&mut state_u128[1]);
        Self::bar_u128(&mut state_u128[2]);
        Self::bar_u128(&mut state_u128[3]);
    }

    /// Compute the "Bricks" component
    #[inline(always)]
    #[unroll_for_loops]
    fn bricks(state: &mut [Self; SPONGE_WIDTH]) {
        // Feistel Type-3
        let tmp = state.to_owned();
        for (x_, x) in tmp.iter().zip(state.iter_mut().skip(1)) {
            let tmp_square = *x_ * *x_;
            *x += tmp_square;
        }
    }

    /// Same as `bricks` optimized for u128
    /// Result is not reduced!
    /// Use "& 0xFFFFFFFFFFFFFFFF" to tell the compiler it is dealing with 64-bit values (safe some instructions for upper half)
    fn bricks_u128(state_u128: &mut [u128; SPONGE_WIDTH]) {
        // Feistel Type-3
        let tmp = state_u128.to_owned();
        for (x_, x) in tmp.iter().zip(state_u128.iter_mut().skip(1)) {
            let mut tmp_square = (x_ & 0xFFFFFFFFFFFFFFFF_u128) * (x_ & 0xFFFFFFFFFFFFFFFF_u128);
            reduce128(&mut tmp_square);
            *x = (*x & 0xFFFFFFFFFFFFFFFF_u128) + (tmp_square & 0xFFFFFFFFFFFFFFFF_u128);
        }
    }

    /// Same as `bricks` for field extensions of `Self`.
    #[inline(always)]
    #[unroll_for_loops]
    fn bricks_field<F: FieldExtension<D, BaseField = Self>, const D: usize>(
        state: &mut [F; SPONGE_WIDTH]
    ) {
        // Feistel Type-3
        let tmp = state.to_owned();
        for (x_, x) in tmp.iter().zip(state.iter_mut().skip(1)) {
            let tmp_square = *x_ * *x_;
            *x += tmp_square;
        }
    }

    /// Recursive version of `bricks`.
    #[inline(always)]
    #[unroll_for_loops]
    fn bricks_circuit<const D: usize>(
        builder: &mut CircuitBuilder<Self, D>,
        state: &mut [ExtensionTarget<D>; SPONGE_WIDTH]
    ) where
        Self: RichField + Extendable<D>,
    {
        // Feistel Type-3
        let tmp = state.to_owned();
        for (x_, x) in tmp.iter().zip(state.iter_mut().skip(1)) {
            let tmp_square = builder.square_extension(*x_);
            *x = builder.add_extension(*x, tmp_square);
        }
    }

    /// Compute the "Concrete" component
    #[inline(always)]
    #[unroll_for_loops]
    fn concrete(state: &mut [Self; SPONGE_WIDTH], round_constants: &[u64; SPONGE_WIDTH]) {
        let mut state_tmp = vec![Self::ZERO; SPONGE_WIDTH];
        for row in 0..SPONGE_WIDTH {
            for (column, input) in state.iter().enumerate() {
                state_tmp[row] += *input * Self::from_canonical_u64(Self::MAT_12[row][column]);
            }
        }
        state.copy_from_slice(&state_tmp);

        // Round constants
        for (el, rc) in state
            .iter_mut()
            .zip(round_constants.iter())
        {
            *el += Self::from_canonical_u64(*rc);
        }
    }

    /// Same as `concrete` optimized for u128
    fn concrete_u128(state_u128: &mut [u128; SPONGE_WIDTH], round_constants: &[u64; SPONGE_WIDTH]) {
        mds_multiply_u128(state_u128, round_constants);
        // let mut state_tmp = vec![0 as u128; SPONGE_WIDTH];
        // for row in 0..SPONGE_WIDTH {
        //     for (column, input) in state_u128.iter().enumerate() {
        //         state_tmp[row] += *input * (Self::MAT_12[row][column] as u128);
        //     }
        // }
        // state_u128.copy_from_slice(&state_tmp);

        // // Round constants
        // for (el, rc) in state_u128
        //     .iter_mut()
        //     .zip(round_constants.iter())
        // {
        //     *el += *rc as u128;
        //     reduce96(el);
        // }
    }

    /// Same as `concrete` for field extensions of `Self`.
    #[inline(always)]
    #[unroll_for_loops]
    fn concrete_field<F: FieldExtension<D, BaseField = Self>, const D: usize>(
        state: &mut [F; SPONGE_WIDTH], round_constants: &[u64; SPONGE_WIDTH]
    ) {
        let mut state_tmp = vec![F::ZERO; SPONGE_WIDTH];
        for row in 0..SPONGE_WIDTH {
            for (column, input) in state.iter().enumerate() {
                state_tmp[row] += *input * F::from_canonical_u64(Self::MAT_12[row][column]);
            }
        }
        state.copy_from_slice(&state_tmp);

        // Round constants
        for (el, rc) in state
            .iter_mut()
            .zip(round_constants.iter())
        {
            *el += F::from_canonical_u64(*rc);
        }
    }

    /// Recursive version of `concrete`.
    #[inline(always)]
    #[unroll_for_loops]
    fn concrete_circuit<const D: usize>(
        builder: &mut CircuitBuilder<Self, D>,
        state: &mut [ExtensionTarget<D>; SPONGE_WIDTH], round_constants: &[u64; SPONGE_WIDTH],
    ) where
        Self: RichField + Extendable<D>,
    {
        let mut state_tmp = vec![builder.zero_extension(); SPONGE_WIDTH];
        for row in 0..SPONGE_WIDTH {
            for (column, input) in state.iter().enumerate() {
                state_tmp[row] = builder.mul_const_add_extension(Self::from_canonical_u64(Self::MAT_12[row][column]), *input, state_tmp[row]);
            }
        }
        state.copy_from_slice(&state_tmp);

        // Round constants
        for (el, rc) in state
            .iter_mut()
            .zip(round_constants.iter())
        {
            let rc_et = builder.constant_extension(Self::Extension::from_canonical_u64(*rc));
            *el = builder.add_extension(*el, rc_et);
        }
    }

    #[inline]
    fn monolith_u128(input: [Self; SPONGE_WIDTH]) -> [Self; SPONGE_WIDTH] {
        let mut state_u128 = [0; SPONGE_WIDTH];
        for (out, inp) in state_u128.iter_mut().zip(input.iter()) {
            *out = inp.to_noncanonical_u64() as u128;
        }

        Self::concrete_u128(&mut state_u128, &Self::ROUND_CONSTANTS[0].try_into().unwrap());
        for rc in Self::ROUND_CONSTANTS.iter().skip(1) {
            Self::bars_u128(&mut state_u128);
            Self::bricks_u128(&mut state_u128);
            Self::concrete_u128(&mut state_u128, rc.try_into().unwrap());
        }

        // Convert back
        let mut state_f = [Self::ZERO; SPONGE_WIDTH];
        for (out, inp) in state_f.iter_mut().zip(state_u128.iter()) {
            *out = Self::from_canonical_u64(*inp as u64);
        }
        state_f
    }

    #[inline]
    fn monolith(input: [Self; SPONGE_WIDTH]) -> [Self; SPONGE_WIDTH] {
        let mut state = input;

        Self::concrete(&mut state, &Self::ROUND_CONSTANTS[0].try_into().unwrap());
        for rc in Self::ROUND_CONSTANTS.iter().skip(1) {
            Self::bars(&mut state);
            Self::bricks(&mut state);
            Self::concrete(&mut state, rc.try_into().unwrap());
        }

        state
    }
}

/// Monolith permutation
pub struct MonolithPermutation;
impl<F: RichField + Monolith> PlonkyPermutation<F, MonolithHashConfig> for MonolithPermutation {
    fn permute(input: [F; SPONGE_WIDTH]) -> [F; SPONGE_WIDTH] {
        F::monolith_u128(input)
    }
}

/// Monolith hash function.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct MonolithHash;
impl<F: RichField> Hasher<F, MonolithHashConfig> for MonolithHash {
    const HASH_SIZE: usize = 4 * 8;
    type Hash = HashOut<F>;
    type Permutation = MonolithPermutation;

    fn hash_no_pad(input: &[F]) -> Self::Hash {
        hash_n_to_hash_no_pad::<F, MonolithHashConfig, Self::Permutation>(input)
    }

    fn two_to_one(left: Self::Hash, right: Self::Hash) -> Self::Hash {
        compress::<F, MonolithHashConfig, Self::Permutation>(left, right)
    }
}

pub fn add_lookup_table<F: RichField + Extendable<D>, const D:usize>(
    builder: &mut CircuitBuilder<F,D>
) -> usize {
    // Add lookup table
    // TODO: Find a more elegant way to generate the table. Moreover, this should be done only once...
    let inp_table: [u16; LOOKUP_SIZE] = core::array::from_fn(|i| i as u16);
    // let lut_index = builder.add_lookup_table_from_table(&inp_table, &LOOKUP_TABLE);
    builder.add_lookup_table_from_fn(|i| {
        let limb = i as u16;
        match LOOKUP_BITS {
            8 => {
                let limbl1 = ((!limb & 0x80) >> 7) | ((!limb & 0x7F) << 1); // Left rotation by 1
                let limbl2 = ((limb & 0xC0) >> 6) | ((limb & 0x3F) << 2); // Left rotation by 2
                let limbl3 = ((limb & 0xE0) >> 5) | ((limb & 0x1F) << 3); // Left rotation by 3

                // y_i = x_i + (1 + x_{i+1}) * x_{i+2} * x_{i+3}
                let tmp = limb ^ limbl1 & limbl2 & limbl3;
                ((tmp & 0x80) >> 7) | ((tmp & 0x7F) << 1)
            },
            16 => {
                let limbl1 = ((!limb & 0x8000) >> 15) | ((!limb & 0x7FFF) << 1); // Left rotation by 1
                let limbl2 = ((limb & 0xC000) >> 14) | ((limb & 0x3FFF) << 2); // Left rotation by 2
                let limbl3 = ((limb & 0xE000) >> 13) | ((limb & 0x1FFF) << 3); // Left rotation by 3

                // y_i = x_i + (1 + x_{i+1}) * x_{i+2} * x_{i+3}
                let tmp = limb ^ limbl1 & limbl2 & limbl3;
                ((tmp & 0x8000) >> 15) | ((tmp & 0x7FFF) << 1) // Final rotation
            }
            _ => {
                panic!("Unsupported lookup size");
            }
        }
    }, &inp_table)
}

impl<F: RichField> AlgebraicHasher<F, MonolithHashConfig> for MonolithHash {
    fn permute_swapped<const D: usize>(
        inputs: [Target; SPONGE_WIDTH],
        swap: BoolTarget,
        builder: &mut CircuitBuilder<F, D>,
    ) -> [Target; SPONGE_WIDTH]
    where
        F: RichField + Extendable<D>,
    {
        let lut_index = add_lookup_table(builder);
        let gate_type = MonolithGate::<F, D>::new();
        let gate = builder.add_gate(gate_type, vec![]);

        let swap_wire = MonolithGate::<F, D>::WIRE_SWAP;
        let swap_wire = Target::wire(gate, swap_wire);
        builder.connect(swap.target, swap_wire);

        // Route input wires.
        for i in 0..SPONGE_WIDTH {
            let in_wire = MonolithGate::<F, D>::wire_input(i);
            let in_wire = Target::wire(gate, in_wire);
            builder.connect(inputs[i], in_wire);
        }

        // Route lookup wires
        for round_ctr in 0..N_ROUNDS {
            for i in 0..NUM_BARS {
                let target_input: Target = Target::wire(gate, MonolithGate::<F, D>::wire_concrete_out(round_ctr, i));
                let target_output = Target::wire(gate, MonolithGate::<F, D>::wire_bars_out(round_ctr, i));
                let target_should = builder.split_le_lookup::<LOOKUP_SIZE>(target_input, LOOKUP_NUM_LIMBS, lut_index); // Assumes a single lookup table
                builder.connect(target_output, target_should);
            }
        }

        // Collect output wires.
        (0..SPONGE_WIDTH)
            .map(|i| Target::wire(gate, MonolithGate::<F, D>::wire_output(i)))
            .collect::<Vec<_>>()
            .try_into()
            .unwrap()
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct MonolithCompactHash;
impl<F: RichField> Hasher<F, MonolithHashConfig> for MonolithCompactHash {
    const HASH_SIZE: usize = 4 * 8;
    type Hash = HashOut<F>;
    type Permutation = MonolithPermutation;

    fn hash_no_pad(input: &[F]) -> Self::Hash {
        hash_n_to_hash_no_pad::<F, MonolithHashConfig, Self::Permutation>(input)
    }

    fn two_to_one(left: Self::Hash, right: Self::Hash) -> Self::Hash {
        compress::<F, MonolithHashConfig, Self::Permutation>(left, right)
    }
}

impl<F: RichField> AlgebraicHasher<F, MonolithHashConfig> for MonolithCompactHash {
    fn permute_swapped<const D: usize>(
        inputs: [Target; SPONGE_WIDTH],
        swap: BoolTarget,
        builder: &mut CircuitBuilder<F, D>,
    ) -> [Target; SPONGE_WIDTH]
        where
            F: RichField + Extendable<D>, {
        let lut_index = add_lookup_table(builder);
        let init_gate = MonolithInitGate::<F,D>::new(&builder.config);
        let gate = builder.add_gate(init_gate.clone(), vec![]);

        let swap_wire = MonolithInitGate::<F, D>::WIRE_SWAP;
        let swap_wire = Target::wire(gate, swap_wire);
        builder.connect(swap.target, swap_wire);

        // Route input wires
        for i in 0..SPONGE_WIDTH {
            let in_wire = MonolithInitGate::<F, D>::wire_input(i);
            let in_wire = Target::wire(gate, in_wire);
            builder.connect(inputs[i], in_wire);
        }

        // Route lookup wires
        for round_ctr in 0..init_gate.num_rounds() {
            for i in 0..NUM_BARS {
                let target_input: Target = Target::wire(gate, MonolithInitGate::<F, D>::wire_concrete_out(round_ctr, i));
                let target_output = Target::wire(gate, MonolithInitGate::<F, D>::wire_bars_out(round_ctr, i));
                let target_should = builder.split_le_lookup::<LOOKUP_SIZE>(target_input, LOOKUP_NUM_LIMBS, lut_index); // Assumes a single lookup table
                builder.connect(target_output, target_should);
            }
        }

        // Collect output wires
        let mut targets: [Target; SPONGE_WIDTH] = (0..SPONGE_WIDTH)
            .map(|i| Target::wire(gate, MonolithInitGate::<F, D>::wire_output(i)))
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let mut rounds_done = init_gate.num_rounds();
        while rounds_done < N_ROUNDS {
            let gate_type = MonolithRoundsGate::<F,D>::new(rounds_done, &builder.config);
            let gate = builder.add_gate(gate_type.clone(), vec![]);
            
            // Route input wires
            for i in 0..SPONGE_WIDTH {
                let in_wire = MonolithRoundsGate::<F, D>::wire_input(i);
                let in_wire = Target::wire(gate, in_wire);
                builder.connect(targets[i], in_wire);
            }
            
            // Route lookup wires
            for round_ctr in 0..gate_type.num_rounds() {
                for i in 0..NUM_BARS {
                    let target_input: Target = Target::wire(gate, MonolithRoundsGate::<F, D>::wire_concrete_out(round_ctr, i));
                    let target_output = Target::wire(gate, MonolithRoundsGate::<F, D>::wire_bars_out(round_ctr, i));
                    let target_should = builder.split_le_lookup::<LOOKUP_SIZE>(target_input, LOOKUP_NUM_LIMBS, lut_index); // Assumes a single lookup table
                    builder.connect(target_output, target_should);
                }
            }

            // Collect output wires
            targets = (0..SPONGE_WIDTH)
                .map(|i| Target::wire(gate, MonolithRoundsGate::<F, D>::wire_output(i)))
                .collect::<Vec<_>>()
                .try_into()
                .unwrap();
            rounds_done += gate_type.num_rounds();
        }

        targets

    }
}

#[cfg(test)]
pub(crate) mod test_helpers {
    use std::collections::HashMap;
    use crate::field::types::Field;
    use crate::gates::gate::Gate;
    use crate::gates::monolith::MonolithGate;
    use crate::hash::monolith::{Monolith, MonolithCompactHash, MonolithHash, SPONGE_WIDTH};
    use crate::iop::witness::{PartialWitness, WitnessWrite};
    use crate::plonk::circuit_builder::CircuitBuilder;
    use crate::plonk::circuit_data::CircuitConfig;
    use crate::plonk::config::{AlgebraicHasher, GenericConfig, MonolithGoldilocksConfig};
    use std::cmp;

    pub(crate) fn check_test_vectors<F: Field>(
        test_vectors: Vec<([u64; SPONGE_WIDTH], [u64; SPONGE_WIDTH])>,
    ) where
        F: Monolith,
    {
        for (input_, expected_output_) in test_vectors.into_iter() {
            let mut input = [F::ZERO; SPONGE_WIDTH];
            for i in 0..SPONGE_WIDTH {
                input[i] = F::from_canonical_u64(input_[i]);
            }
            let output = F::monolith_u128(input);
            for i in 0..SPONGE_WIDTH {
                let ex_output = F::from_canonical_u64(expected_output_[i]);
                assert_eq!(output[i], ex_output);
            }
        }
    }

    fn test_monolith_hash_circuit(compact: bool) {
        const D: usize = 2;
        type C = MonolithGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        // let config = if compact {
        //     CircuitConfig::standard_recursion_config()
        // } else {
        //     // let needed_wires = MonolithGate::<F,D>::new().num_wires();
        //     let needed_wires = cmp::max(MonolithGate::<F,D>::new().num_wires(), 135);
        //     CircuitConfig {
        //         num_wires: needed_wires,
        //         num_routed_wires: needed_wires,
        //         ..CircuitConfig::standard_recursion_config()
        //     }
        // };
        let needed_wires = cmp::max(MonolithGate::<F,D>::new().num_wires(), 135);
        let config = CircuitConfig {
            num_wires: needed_wires,
            num_routed_wires: needed_wires,
            ..CircuitConfig::standard_recursion_config()
        };

        let mut builder = CircuitBuilder::new(config);
        let inp_targets = builder.add_virtual_target_arr::<SPONGE_WIDTH>();
        let out_targets = if compact {
            MonolithCompactHash::permute_swapped(inp_targets, builder._false(), &mut builder)
        } else {
            MonolithHash::permute_swapped(inp_targets, builder._false(), &mut builder)
        };
        builder.register_public_inputs(out_targets.as_slice());
        // Print occurrences of the gate in the circuit
        println!("{} {:?}", builder.num_gates(), {
            let mut counters = HashMap::new();
            builder.gate_instances.iter().for_each(|g|
                match counters.get_mut(&g.gate_ref.0.id()) {
                    Some(v) => *v += 1,
                    None => _ = counters.insert(g.gate_ref.0.id(), 1),
                }
            );
            counters
        }
        );

        println!("Num wires: {}", builder.config.num_wires);
        println!("Num routed wires: {}", builder.config.num_routed_wires);

        let now = std::time::Instant::now();
        let circuit = builder.build::<C>();
        println!("[Build time] {:.4} s", now.elapsed().as_secs_f64());
        println!("Circuit degree bits: {}", circuit.common.degree_bits());

        let permutation_inputs = (0..SPONGE_WIDTH)
            .map(F::from_canonical_usize)
            .collect::<Vec<_>>();

        let mut inputs = PartialWitness::new();
        inp_targets.iter().zip(permutation_inputs.iter()).for_each(|(t, val)| inputs.set_target(
            *t, *val
        ));

        let now = std::time::Instant::now();
        let proof = circuit.prove(inputs).unwrap();
        println!("[Prove time] {:.4} s", now.elapsed().as_secs_f64());
        println!("Proof size (bytes): {}", proof.to_bytes().len());

        let expected_outputs: [F; SPONGE_WIDTH] = F::monolith_u128(permutation_inputs.try_into().unwrap());

        proof.public_inputs.iter().zip(expected_outputs.iter()).for_each(|(v, out)| {
            assert_eq!(*v, *out)
        });

        let now = std::time::Instant::now();
        circuit.verify(proof).unwrap();
        println!("[Verify time] {:.4} s", now.elapsed().as_secs_f64());
    }

    #[test]
    fn test_monolith_hash() {
        test_monolith_hash_circuit(false)
    }


    #[test]
    fn test_monolith_compact_hash() {
        test_monolith_hash_circuit(true)
    }

}
