use alloc::vec;
use alloc::vec::Vec;
use core::fmt::Debug;

use serde::de::DeserializeOwned;
use serde::Serialize;

use crate::field::extension::quadratic::QuadraticExtension;
use crate::field::extension::{Extendable, FieldExtension};
use crate::field::goldilocks_field::GoldilocksField;
use crate::hash::hash_types::{HashOut, RichField};
use crate::hash::hashing::{HashConfig, PlonkyPermutation};
use crate::hash::keccak::KeccakHash;
use crate::hash::poseidon::PoseidonHash;
use crate::hash::monolith::MonolithHash;
use crate::iop::target::{BoolTarget, Target};
use crate::plonk::circuit_builder::CircuitBuilder;

pub trait GenericHashOut<F: RichField>:
    Copy + Clone + Debug + Eq + PartialEq + Send + Sync + Serialize + DeserializeOwned
{
    fn to_bytes(&self) -> Vec<u8>;
    fn from_bytes(bytes: &[u8]) -> Self;

    fn to_vec(&self) -> Vec<F>;
}

/// Trait for hash functions.
pub trait Hasher<F: RichField, HC: HashConfig>: Sized + Clone + Debug + Eq + PartialEq {
    /// Size of `Hash` in bytes.
    const HASH_SIZE: usize;

    /// Hash Output
    type Hash: GenericHashOut<F>;

    /// Permutation used in the sponge construction.
    type Permutation: PlonkyPermutation<F, HC>;

    /// Hash a message without any padding step. Note that this can enable length-extension attacks.
    /// However, it is still collision-resistant in cases where the input has a fixed length.
    fn hash_no_pad(input: &[F]) -> Self::Hash
    where
        [(); HC::WIDTH]:;

    /// Pad the message using the `pad10*1` rule, then hash it.
    fn hash_pad(input: &[F]) -> Self::Hash
    where
        [(); HC::WIDTH]:,
    {
        let mut padded_input = input.to_vec();
        padded_input.push(F::ONE);
        while (padded_input.len() + 1) % HC::WIDTH != 0 {
            padded_input.push(F::ZERO);
        }
        padded_input.push(F::ONE);
        Self::hash_no_pad(&padded_input)
    }

    /// Hash the slice if necessary to reduce its length to ~256 bits. If it already fits, this is a
    /// no-op.
    fn hash_or_noop(inputs: &[F]) -> Self::Hash
    where
        [(); HC::WIDTH]:,
    {
        if inputs.len() * 8 <= Self::HASH_SIZE {
            let mut inputs_bytes = vec![0u8; Self::HASH_SIZE];
            for i in 0..inputs.len() {
                inputs_bytes[i * 8..(i + 1) * 8]
                    .copy_from_slice(&inputs[i].to_canonical_u64().to_le_bytes());
            }
            Self::Hash::from_bytes(&inputs_bytes)
        } else {
            Self::hash_no_pad(inputs)
        }
    }

    fn two_to_one(left: Self::Hash, right: Self::Hash) -> Self::Hash
    where
        [(); HC::WIDTH]:;
}

/// Trait for algebraic hash functions, built from a permutation using the sponge construction.
pub trait AlgebraicHasher<F: RichField, HC: HashConfig>: Hasher<F, HC, Hash = HashOut<F>> {
    /// Circuit to conditionally swap two chunks of the inputs (useful in verifying Merkle proofs),
    /// then apply the permutation.
    fn permute_swapped<const D: usize>(
        inputs: [Target; HC::WIDTH],
        swap: BoolTarget,
        builder: &mut CircuitBuilder<F, D>,
    ) -> [Target; HC::WIDTH]
    where
        [(); HC::WIDTH]:,
        F: RichField + Extendable<D>;
}

/// Generic configuration trait.
pub trait GenericConfig<const D: usize>:
    Debug + Clone + Sync + Sized + Send + Eq + PartialEq
{
    /// Main field.
    type F: RichField + Extendable<D, Extension = Self::FE>;
    /// Field extension of degree D of the main field.
    type FE: FieldExtension<D, BaseField = Self::F>;
    /// Hash configuration for this GenericConfig's `Hasher`.
    type HCO: HashConfig;
    /// Hash configuration for this GenericConfig's `InnerHasher`.
    type HCI: HashConfig;
    /// Hash function used for building Merkle trees.
    type Hasher: Hasher<Self::F, Self::HCO>;
    /// Algebraic hash function used for the challenger and hashing public inputs.
    type InnerHasher: AlgebraicHasher<Self::F, Self::HCI>;
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PoseidonHashConfig;
impl HashConfig for PoseidonHashConfig {
    const RATE: usize = 8;
    const WIDTH: usize = 12;
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MonolithHashConfig;
impl HashConfig for MonolithHashConfig {
    const RATE: usize = 8;
    const WIDTH: usize = 12;
}

/// Configuration using Poseidon over the Goldilocks field.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct PoseidonGoldilocksConfig;
impl GenericConfig<2> for PoseidonGoldilocksConfig {
    type F = GoldilocksField;
    type FE = QuadraticExtension<Self::F>;
    type HCO = PoseidonHashConfig;
    type HCI = PoseidonHashConfig;
    type Hasher = PoseidonHash;
    type InnerHasher = PoseidonHash;
}

/// Configuration using Monolith over the Goldilocks field.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct MonolithGoldilocksConfig;
impl GenericConfig<2> for MonolithGoldilocksConfig {
    type F = GoldilocksField;
    type FE = QuadraticExtension<Self::F>;
    type HCO = MonolithHashConfig;
    type HCI = PoseidonHashConfig;
    type Hasher = MonolithHash;
    type InnerHasher = PoseidonHash;
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct KeccakHashConfig;
impl HashConfig for KeccakHashConfig {
    const RATE: usize = 8;
    const WIDTH: usize = 12;
}
/// Configuration using truncated Keccak over the Goldilocks field.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct KeccakGoldilocksConfig;
impl GenericConfig<2> for KeccakGoldilocksConfig {
    type F = GoldilocksField;
    type FE = QuadraticExtension<Self::F>;
    type HCO = KeccakHashConfig;
    type HCI = PoseidonHashConfig;
    type Hasher = KeccakHash<25>;
    type InnerHasher = PoseidonHash;
}
