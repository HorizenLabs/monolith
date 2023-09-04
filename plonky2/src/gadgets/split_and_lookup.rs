use alloc::vec;
use alloc::vec::Vec;

use crate::field::extension::Extendable;
use crate::field::types::Field;
use crate::gates::base_sum_custom_restrict::{BaseSplitRestrictGenerator, BaseSumCustomRestrictGate};
use crate::hash::hash_types::RichField;
use crate::iop::generator::{GeneratedValues, SimpleGenerator};
use crate::iop::target::Target;
use crate::iop::witness::{PartitionWitness, Witness, WitnessWrite};
use crate::plonk::circuit_builder::CircuitBuilder;

impl<F: RichField + Extendable<D>, const D: usize> CircuitBuilder<F, D> {
    /// 1) Split the given element into a list of targets, where each one represents a
    /// base-B limb of the element, with little-endian ordering
    /// 2) Applies the lookup argument to these targets
    /// 3) Composes the final target using the outputs of the lookup argument
    pub fn split_le_lookup<const B: usize>(&mut self, x: Target, num_limbs: usize, lut_index: usize) -> Target {

        // Split into individual targets (decompose)
        let gate_type = BaseSumCustomRestrictGate::<B>::new(num_limbs, &self.config);
        let (gate, i) = self.find_slot(gate_type, &[F::from_canonical_usize(num_limbs)], &[]);
        let sum = Target::wire(gate, gate_type.ith_wire_sum(i));
        self.connect(x, sum);

        let split_targets_in = Target::wires_from_range(gate, gate_type.ith_limbs(i));

        // Apply lookups
        let mut split_targets_out = vec![];
        // let mut test = vec![];
        // test.push(split_targets_in[0]);
        for i in 0..num_limbs {
            // split_targets_out[i] = self.add_lookup_from_index(split_targets_in[i], 0);
            split_targets_out.push(self.add_lookup_from_index(split_targets_in[i], lut_index));
        }

        // Get final output target (compose)
        let limbs = split_targets_out;

        debug_assert!(
            BaseSumCustomRestrictGate::<B>::START_LIMBS + num_limbs + 2 <= self.config.num_routed_wires,
            "Not enough routed wires."
        );
        //let gate_type = BaseSumCustomRestrictGate::<B>::new_from_config::<F>(&self.config);

        let (row, i) = self.find_slot(gate_type, &[F::from_canonical_usize(num_limbs)],&vec![]);
        for (limb, wire) in limbs
            .iter()
            .zip(gate_type.ith_limbs(i))
        {
            self.connect(*limb, Target::wire(row, wire));
        }

        self.add_simple_generator(BaseSumCustomRestrictGenerator::<B>( BaseSplitRestrictGenerator::new(row, num_limbs, i)));

        Target::wire(row, gate_type.ith_wire_sum(i))
    }
}

#[derive(Debug)]
struct BaseSumCustomRestrictGenerator<const B: usize>(BaseSplitRestrictGenerator<B>);

impl<F: Field, const B: usize> SimpleGenerator<F> for BaseSumCustomRestrictGenerator<B> {
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
}

#[cfg(test)]
mod tests {
    
    use crate::field::types::Field;
    use crate::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};

    use crate::plonk::circuit_builder::CircuitBuilder;
    use crate::plonk::circuit_data::CircuitConfig;

    use crate::iop::witness::PartialWitness;
    use crate::plonk::verifier::verify;

    pub const LOOKUP_TABLE: [u16; 256] = [
        0, 2, 4, 22, 8, 10, 44, 46, 16, 18, 20, 6, 88, 90, 92, 94,
        32, 34, 36, 54, 40, 42, 12, 14, 176, 178, 180, 166, 184, 186, 188, 190,
        64, 66, 68, 86, 72, 74, 108, 110, 80, 82, 84, 70, 24, 26, 28, 30,
        97, 99, 101, 119, 105, 107, 77, 79, 113, 115, 117, 103, 121, 123, 125, 127,
        128, 130, 132, 150, 136, 138, 172, 174, 144, 146, 148, 134, 216, 218, 220, 222,
        160, 162, 164, 182, 168, 170, 140, 142, 48, 50, 52, 38, 56, 58, 60, 62,
        194, 192, 198, 212, 202, 200, 238, 236, 210, 208, 214, 196, 154, 152, 158, 156,
        226, 224, 230, 244, 234, 232, 206, 204, 242, 240, 246, 228, 250, 248, 254, 252,
        1, 11, 5, 23, 9, 3, 45, 47, 17, 27, 21, 7, 89, 83, 93, 95,
        33, 43, 37, 55, 41, 35, 13, 15, 177, 187, 181, 167, 185, 179, 189, 191,
        65, 75, 69, 87, 73, 67, 109, 111, 81, 91, 85, 71, 25, 19, 29, 31,
        96, 106, 100, 118, 104, 98, 76, 78, 112, 122, 116, 102, 120, 114, 124, 126,
        133, 139, 129, 151, 141, 131, 169, 175, 149, 155, 145, 135, 221, 211, 217, 223,
        165, 171, 161, 183, 173, 163, 137, 143, 53, 59, 49, 39, 61, 51, 57, 63,
        197, 203, 193, 215, 205, 195, 233, 239, 213, 219, 209, 199, 157, 147, 153, 159,
        229, 235, 225, 247, 237, 227, 201, 207, 245, 251, 241, 231, 253, 243, 249, 255,
    ];

    #[test]
    fn test_custom_split_lookup() {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        
        // Add table
        let inp_table: [u16; 256] = core::array::from_fn(|i| i as u16);
        builder.add_lookup_table_from_table(&inp_table, &LOOKUP_TABLE);


        let pw = PartialWitness::new();
        let input_target = builder.constant(F::from_canonical_usize(0x113a4c0e613a9d2a));
        let output_target_is = builder.split_le_lookup::<256>(input_target, 8, 0);

        let output_target_should = builder.constant(F::from_canonical_usize(0x2275d85cc075b354));
        builder.connect(output_target_is, output_target_should);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        let _result = verify(proof, &data.verifier_only, &data.common);

    }
}
