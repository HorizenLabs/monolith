use plonky2::field::extension::Extendable;
use plonky2::hash::hash_types::RichField;
use plonky2::hash::hashing::PlonkyPermutation;
use plonky2::iop::generator::{GeneratedValues, SimpleGenerator};
use plonky2::iop::target::{BoolTarget, Target};
use plonky2::iop::witness::{PartitionWitness, Witness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::CommonCircuitData;
use plonky2::plonk::config::AlgebraicHasher;
use plonky2::util::serialization::{Buffer, IoResult};
use crate::gates::base_sum_custom::{BaseSplitGenerator, BaseSumCustomGate};
use crate::gates::monolith::MonolithGate;
use crate::monolith_hash::{LOOKUP_BITS, LOOKUP_NUM_LIMBS, LOOKUP_SIZE, Monolith, MonolithHash, MonolithPermutation, N_ROUNDS, NUM_BARS, SPONGE_WIDTH};

pub trait SplitAndLookup {
    /// 1) Split the given element into a list of targets, where each one represents a
    /// base-B limb of the element, with little-endian ordering
    /// 2) Applies the lookup argument to these targets
    /// 3) Composes the final target using the outputs of the lookup argument
    fn split_le_lookup<const B: usize>(&mut self, x: Target, num_limbs: usize, lut_index: usize) -> Target;
}

impl<F: RichField + Extendable<D>, const D: usize> SplitAndLookup for CircuitBuilder<F, D> {
    fn split_le_lookup<const B: usize>(&mut self, x: Target, num_limbs: usize, lut_index: usize) -> Target {

        // Split into individual targets (decompose)
        let gate_type = BaseSumCustomGate::<B>::new(num_limbs, &self.config);
        let (gate, i) = self.find_slot(gate_type, &[F::from_canonical_usize(num_limbs)], &[]);
        let sum = Target::wire(gate, gate_type.ith_wire_sum(i));
        self.connect(x, sum);

        let split_targets_in = Target::wires_from_range(gate, gate_type.ith_limbs(i));

        // Apply lookups
        let mut split_targets_out = vec![];
        for i in 0..num_limbs {
            split_targets_out.push(self.add_lookup_from_index(split_targets_in[i], lut_index));
        }

        // Get final output target (compose)
        let limbs = split_targets_out;

        let (row, i) = self.find_slot(gate_type, &[F::from_canonical_usize(num_limbs)],&vec![]);
        for (limb, wire) in limbs
            .iter()
            .zip(gate_type.ith_limbs(i))
        {
            self.connect(*limb, Target::wire(row, wire));
        }

        self.add_simple_generator(BaseSumCustomRestrictGenerator::<B>( BaseSplitGenerator::new(row, num_limbs, i)));

        Target::wire(row, gate_type.ith_wire_sum(i))
    }
}

#[derive(Debug, Default)]
struct BaseSumCustomRestrictGenerator<const B: usize>(BaseSplitGenerator<B>);

impl<F: RichField + Extendable<D>, const B: usize, const D: usize> SimpleGenerator<F, D> for BaseSumCustomRestrictGenerator<B> {

    fn id(&self) -> String {
        "BaseSumCustomRestrictGenerator".to_string()
    }

    fn dependencies(&self) -> Vec<Target> {
        self.0.limbs_wires()
    }

    fn run_once(&self, witness: &PartitionWitness<F>, out_buffer: &mut GeneratedValues<F>) {
        let sum = self
            .0
            .limbs_wires()
            .iter()
            .map(|&t| witness.get_target(t))
            .rev()
            .fold(F::ZERO, |acc, limb| {
                acc * F::from_canonical_usize(B) + limb
            });

        out_buffer.set_target(self.0.wire_sum(), sum);
    }

    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &CommonCircuitData<F, D>) -> IoResult<()> {
        self.0.serialize(dst, _common_data)
    }

    fn deserialize(src: &mut Buffer, _common_data: &CommonCircuitData<F, D>) -> IoResult<Self> {
        let gen = BaseSplitGenerator::deserialize(src, _common_data)?;
        Ok(BaseSumCustomRestrictGenerator::<B>( gen))
    }

}

impl<F: RichField + Monolith> AlgebraicHasher<F> for MonolithHash {
    type AlgebraicPermutation = MonolithPermutation<Target>;

    fn permute_swapped<const D: usize>(
        inputs: Self::AlgebraicPermutation,
        swap: BoolTarget,
        builder: &mut CircuitBuilder<F, D>,
    ) -> Self::AlgebraicPermutation
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
        let inputs = inputs.as_ref();
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
        Self::AlgebraicPermutation::new(
            (0..SPONGE_WIDTH).map(|i| Target::wire(gate, MonolithGate::<F, D>::wire_output(i))),
        )
    }
}

pub fn add_lookup_table<F: RichField + Extendable<D>, const D:usize>(
    builder: &mut CircuitBuilder<F,D>
) -> usize {
    // Add lookup table
    // TODO: Find a more elegant way to generate the table. Moreover, this should be done only once...
    let inp_table: [u16; LOOKUP_SIZE] = core::array::from_fn(|i| i as u16);
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

#[cfg(test)]
mod tests {
    use std::cmp;
    use plonky2::field::types::Field;
    use plonky2::gates::gate::Gate;
    use plonky2::hash::hashing::PlonkyPermutation;
    use plonky2::iop::target::Target;
    use plonky2::iop::witness::{PartialWitness, WitnessWrite};
    use plonky2::plonk::circuit_builder::CircuitBuilder;
    use plonky2::plonk::circuit_data::CircuitConfig;
    use plonky2::plonk::config::{AlgebraicHasher, GenericConfig};
    use crate::gates::monolith::MonolithGate;
    use crate::monolith_hash::{Monolith, MonolithHash, MonolithPermutation, SPONGE_WIDTH};
    use crate::monolith_hash::monolith_goldilocks::MonolithGoldilocksConfig;

    fn test_monolith_hash_circuit() {
        const D: usize = 2;
        type C = MonolithGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let needed_wires = cmp::max(MonolithGate::<F,D>::new().num_wires(), CircuitConfig::standard_recursion_config().num_wires);
        let config = CircuitConfig {
            num_wires: needed_wires,
            num_routed_wires: needed_wires,
            ..CircuitConfig::standard_recursion_config()
        };

        let mut builder = CircuitBuilder::new(config);

        let inp_targets_array = builder.add_virtual_target_arr::<SPONGE_WIDTH>();
        let inp_targets = MonolithPermutation::<Target>::new(inp_targets_array);

        let out_targets = MonolithHash::permute_swapped(inp_targets, builder._false(), &mut builder);
        builder.register_public_inputs(out_targets.as_ref());
        builder.print_gate_counts(0);

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
        inp_targets.as_ref().iter().zip(permutation_inputs.iter()).for_each(|(t, val)| inputs.set_target(
            *t, *val
        ));

        let now = std::time::Instant::now();
        let proof = circuit.prove(inputs).unwrap();
        println!("[Prove time] {:.4} s", now.elapsed().as_secs_f64());
        println!("Proof size (bytes): {}", proof.to_bytes().len());

        let expected_outputs: [F; SPONGE_WIDTH] = F::monolith(permutation_inputs.try_into().unwrap());

        proof.public_inputs.iter().zip(expected_outputs.iter()).for_each(|(v, out)| {
            assert_eq!(*v, *out)
        });

        let now = std::time::Instant::now();
        circuit.verify(proof).unwrap();
        println!("[Verify time] {:.4} s", now.elapsed().as_secs_f64());
    }

    #[test]
    fn test_monolith_hash() {
        test_monolith_hash_circuit()
    }
}