use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;
use alloc::{format, vec};
use core::ops::Range;

use crate::field::extension::Extendable;
use crate::field::packed::PackedField;
use crate::field::types::{Field, Field64};
use crate::gates::gate::Gate;
use crate::gates::packed_util::PackedEvaluableBase;
use crate::gates::util::StridedConstraintConsumer;
use crate::hash::hash_types::RichField;
use crate::iop::ext_target::ExtensionTarget;
use crate::iop::generator::{GeneratedValues, SimpleGenerator, WitnessGenerator};
use crate::iop::target::Target;
use crate::iop::witness::{PartitionWitness, Witness, WitnessWrite};
use crate::plonk::circuit_builder::CircuitBuilder;
use crate::plonk::circuit_data::CircuitConfig;
use crate::plonk::plonk_common::{reduce_with_powers, reduce_with_powers_ext_circuit};
use crate::plonk::vars::{
    EvaluationTargets, EvaluationVars, EvaluationVarsBase, EvaluationVarsBaseBatch,
    EvaluationVarsBasePacked,
};
use crate::util::log_floor;

/// A gate which can decompose a number into base B little-endian limbs.
#[derive(Copy, Clone, Debug)]
pub struct BaseSumCustomRestrictGate<const B: usize> {
    pub num_limbs: usize,
    pub num_ops: usize,
}

impl<const B: usize> BaseSumCustomRestrictGate<B> {
    pub fn new(num_limbs: usize, config: &CircuitConfig) -> Self {
        let wires_per_op = num_limbs + 1 + 2;
        let num_ops = config.num_routed_wires / wires_per_op;
        Self { num_limbs, num_ops }
    }

    pub fn new_from_config<F: Field64>(config: &CircuitConfig) -> Self {
        let num_limbs = log_floor(F::ORDER - 1, B as u64).min(config.num_routed_wires - Self::START_LIMBS - 2);
        Self::new(num_limbs, config)
    }

    pub const WIRE_SUM: usize = 0;
    pub const START_LIMBS: usize = 1;

    pub fn ith_wire_sum(&self, i: usize) -> usize {
        let wires_per_op = self.num_limbs + 1 + 2;
        i * wires_per_op + Self::WIRE_SUM
    }

    /// Returns the index of the limb wires for i-th op.
    pub fn ith_limbs(&self, i: usize) -> Range<usize> {
        let wires_per_op = self.num_limbs + 1 + 2;
        (i * wires_per_op + Self::START_LIMBS)..(i * wires_per_op + Self::START_LIMBS + self.num_limbs)
    }
}

impl<F: RichField + Extendable<D>, const D: usize, const B: usize> Gate<F, D> for BaseSumCustomRestrictGate<B> {
    fn id(&self) -> String {
        format!("{self:?} + Base: {B}")
    }

    fn num_ops(&self) -> usize {
        self.num_ops
    }

    fn eval_unfiltered(&self, vars: EvaluationVars<F, D>) -> Vec<F::Extension> {
        let mut constraints = Vec::with_capacity(self.num_ops * 3);
        for i in 0..self.num_ops {
            // Splitting constraint
            let sum = vars.local_wires[self.ith_wire_sum(i)];
            let limbs = vars.local_wires[self.ith_limbs(i)].to_vec();
            let computed_sum = reduce_with_powers(&limbs, F::Extension::from_canonical_usize(B));
            constraints.push(computed_sum - sum);

            // Boundary constraints
            let z = vars.local_wires[self.ith_wire_sum(i) + self.num_limbs + 1];
            let z_prime = vars.local_wires[self.ith_wire_sum(i) + self.num_limbs + 2];

            let one = F::Extension::from_canonical_usize(1_u64 as usize);
            let two_8 = F::Extension::from_canonical_usize((1_u64 << 8) as usize);
            let two_16 = F::Extension::from_canonical_usize((1_u64 << 16) as usize);
            let two_24 = F::Extension::from_canonical_usize((1_u64 << 24) as usize);
            let two_32_m1 = F::Extension::from_canonical_usize(((1_u64 << 32) - 1) as usize);

            let a = limbs[3] * two_24 + limbs[2] * two_16 + limbs[1] * two_8 + limbs[0];
            let b = limbs[7] * two_24 + limbs[6] * two_16 + limbs[5] * two_8 + limbs[4] - z;

            constraints.push(a * b);
            constraints.push((z - two_32_m1) * z_prime - one);
        }
        constraints
    }

    fn eval_unfiltered_base_one(
        &self,
        _vars: EvaluationVarsBase<F>,
        _yield_constr: StridedConstraintConsumer<F>,
    ) {
        panic!("use eval_unfiltered_base_packed instead");
    }

    fn eval_unfiltered_base_batch(&self, vars_base: EvaluationVarsBaseBatch<F>) -> Vec<F> {
        self.eval_unfiltered_base_batch_packed(vars_base)
    }

    fn eval_unfiltered_circuit(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        vars: EvaluationTargets<D>,
    ) -> Vec<ExtensionTarget<D>> {
        let mut constraints = Vec::with_capacity(self.num_ops * 3);
        for i in 0..self.num_ops {
            // Splitting constraint
            let base = builder.constant(F::from_canonical_usize(B));
            let sum = vars.local_wires[self.ith_wire_sum(i)];
            let limbs = vars.local_wires[self.ith_limbs(i)].to_vec();
            let computed_sum = reduce_with_powers_ext_circuit(builder, &limbs, base);
            constraints.push(builder.sub_extension(computed_sum, sum));

            // Boundary constraints
            let z = vars.local_wires[self.ith_wire_sum(i) + self.num_limbs + 1];
            let z_prime = vars.local_wires[self.ith_wire_sum(i) + self.num_limbs + 2];

            let one = builder.one_extension();
            let two_8 = builder.constant_extension(F::Extension::from_canonical_usize((1_u64 << 8) as usize));
            let two_16 = builder.constant_extension(F::Extension::from_canonical_usize((1_u64 << 16) as usize));
            let two_24 = builder.constant_extension(F::Extension::from_canonical_usize((1_u64 << 24) as usize));
            let two_32_m1 = builder.constant_extension(F::Extension::from_canonical_usize(((1_u64 << 32) - 1) as usize));

            let mut temp = builder.mul_extension(limbs[3], two_24);
            temp = builder.mul_add_extension(limbs[2], two_16, temp);
            temp = builder.mul_add_extension(limbs[1], two_8, temp);
            let a = builder.add_extension(temp, limbs[0]);

            temp = builder.mul_extension(limbs[7], two_24);
            temp = builder.mul_add_extension(limbs[6], two_16, temp);
            temp = builder.mul_add_extension(limbs[5], two_8, temp);
            temp = builder.add_extension(temp, limbs[4]);
            let b = builder.sub_extension(temp, z);
            
            temp = builder.mul_extension(a, b);
            constraints.push(temp);

            temp = builder.sub_extension(z, two_32_m1);
            temp = builder.mul_extension(temp, z_prime);
            temp = builder.sub_extension(temp, one);
            constraints.push(temp);
        }
        constraints
    }

    fn generators(&self, row: usize, _local_constants: &[F]) -> Vec<Box<dyn WitnessGenerator<F>>> {
        (0..self.num_ops).map(|i| {
            let g: Box<dyn WitnessGenerator<F>> =
            Box::new(BaseSplitRestrictGenerator::<B> {
                row,
                num_limbs: self.num_limbs,
                op: i,
            }.adapter());
            g
        }).collect()
    }

    // 1 for the sum then `num_limbs` for the limbs.
    // + 2 for the boundary constraints
    fn num_wires(&self) -> usize {
        (1 + self.num_limbs + 2) * self.num_ops
    }

    fn num_constants(&self) -> usize {
        0
    }

    // 2 from boundary constraint of degree 2
    fn degree(&self) -> usize {
        2
    }

    // num_ops for the splitting, + 2 * num_ops for the boundary constraints
    fn num_constraints(&self) -> usize {
        3 * self.num_ops
    }
}

impl<F: RichField + Extendable<D>, const D: usize, const B: usize> PackedEvaluableBase<F, D>
    for BaseSumCustomRestrictGate<B>
{
    fn eval_unfiltered_base_packed<P: PackedField<Scalar = F>>(
        &self,
        vars: EvaluationVarsBasePacked<P>,
        mut yield_constr: StridedConstraintConsumer<P>,
    ) {
        for i in 0..self.num_ops {
            // Splitting constraint
            let sum = vars.local_wires[self.ith_wire_sum(i)];
            let limbs = vars.local_wires.view(self.ith_limbs(i));
            let computed_sum = reduce_with_powers(limbs, F::from_canonical_usize(B));

            yield_constr.one(computed_sum - sum);

            // Boundary constraints
            let z = vars.local_wires[self.ith_wire_sum(i) + self.num_limbs + 1];
            let z_prime = vars.local_wires[self.ith_wire_sum(i) + self.num_limbs + 2];

            let two_8 = F::from_canonical_usize((1_u64 << 8) as usize);
            let two_16 = F::from_canonical_usize((1_u64 << 16) as usize);
            let two_24 = F::from_canonical_usize((1_u64 << 24) as usize);
            let two_32_m1 = F::from_canonical_usize(((1_u64 << 32) - 1) as usize);

            let a = limbs[3] * two_24 + limbs[2] * two_16 + limbs[1] * two_8 + limbs[0];
            let b = limbs[7] * two_24 + limbs[6] * two_16 + limbs[5] * two_8 + limbs[4] - z;

            yield_constr.one(a * b);
            yield_constr.one((z - two_32_m1) * z_prime - F::ONE);
        }

    }
}

#[derive(Debug)]
pub struct BaseSplitRestrictGenerator<const B: usize> {
    row: usize,
    num_limbs: usize,
    op: usize,
}

impl<const B: usize> BaseSplitRestrictGenerator<B> {
    pub(crate) fn new(row: usize, num_limbs: usize, op: usize) -> Self {
        Self {
            row,
            num_limbs,
            op,
        }
    }

    fn wires_per_op(&self) -> usize {
        self.num_limbs + 1 + 2
    }

    pub(crate) fn wire_sum(&self) -> Target {
        Target::wire(self.row, self.wires_per_op() * self.op + BaseSumCustomRestrictGate::<B>::WIRE_SUM)
    }

    pub(crate) fn limbs_wires(&self) -> Vec<Target> {
        ((self.wires_per_op() * self.op + BaseSumCustomRestrictGate::<B>::START_LIMBS)..(self.wires_per_op() * self.op + BaseSumCustomRestrictGate::<B>::START_LIMBS + self.num_limbs)).map(|i| Target::wire(self.row, i)).collect()
    }

    pub(crate) fn boundary_constraints_wires(&self) -> Vec<Target> {
        ((self.wires_per_op() * self.op + BaseSumCustomRestrictGate::<B>::START_LIMBS + self.num_limbs)..(self.wires_per_op() * self.op + BaseSumCustomRestrictGate::<B>::START_LIMBS + self.num_limbs + 2)).map(|i| Target::wire(self.row, i)).collect()
    }
}

impl<F: RichField, const B: usize> SimpleGenerator<F> for BaseSplitRestrictGenerator<B> {
    fn dependencies(&self) -> Vec<Target> {
        vec![self.wire_sum()]
    }

    fn run_once(&self, witness: &PartitionWitness<F>, out_buffer: &mut GeneratedValues<F>) {
        let sum_value = witness
            .get_target(self.wire_sum())
            .to_canonical_u64() as usize;
        debug_assert_eq!(
            (0..self.num_limbs).fold(sum_value, |acc, _| acc / B),
            0,
            "Integer too large to fit in given number of limbs"
        );

        // Splitting targets
        let limbs = self.limbs_wires();
        let mut limbs_value = (0..self.num_limbs)
            .scan(sum_value, |acc, _| {
                let tmp = *acc % B;
                *acc /= B;
                Some(F::from_canonical_usize(tmp))
            })
            .collect::<Vec<_>>();

        for (&b, b_value) in limbs.iter().zip(limbs_value) {
            out_buffer.set_target(b, b_value);
        }

        limbs_value = (0..self.num_limbs)
            .scan(sum_value, |acc, _| {
                let tmp = *acc % B;
                *acc /= B;
                Some(F::from_canonical_usize(tmp))
            })
            .collect::<Vec<_>>();

        // Boundary constraints targets
        let a = limbs_value[3] * F::from_canonical_u64(1_u64 << 24) + limbs_value[2] * F::from_canonical_u64(1_u64 << 16) + limbs_value[1] * F::from_canonical_u64(1_u64 << 8) + limbs_value[0];
        let b = limbs_value[7] * F::from_canonical_u64(1_u64 << 24) + limbs_value[6] * F::from_canonical_u64(1_u64 << 16) + limbs_value[5] * F::from_canonical_u64(1_u64 << 8) + limbs_value[4];

        let boundary_constraints = self.boundary_constraints_wires();
        let z_field: F;
        if a == F::ZERO {
            z_field = F::ONE;
        }
        else {
            z_field = b;
        }
        let z_prime_field = F::inverse(&(z_field - F::from_canonical_u64(1_u64 << 32) + F::ONE));
        out_buffer.set_target(boundary_constraints[0], z_field);
        out_buffer.set_target(boundary_constraints[1], z_prime_field);

    }
}

#[cfg(test)]
mod tests {
    use anyhow::Result;

    use crate::field::goldilocks_field::GoldilocksField;
    use crate::gates::base_sum_custom_restrict::BaseSumCustomRestrictGate;
    use crate::gates::gate_testing::{test_eval_fns, test_low_degree};
    use crate::plonk::circuit_data::CircuitConfig;
    use crate::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};

    #[test]
    fn low_degree() {
        // test_low_degree::<GoldilocksField, _, 4>(BaseSumCustomRestrictGate::<65536>::new(4))
        test_low_degree::<GoldilocksField, _, 4>(BaseSumCustomRestrictGate::<256>::new(8, &CircuitConfig::standard_recursion_config()))
    }

    #[test]
    fn eval_fns() -> Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        // test_eval_fns::<F, C, _, D>(BaseSumCustomRestrictGate::<65536>::new(4))
        test_eval_fns::<F, C, _, D>(BaseSumCustomRestrictGate::<256>::new(8, &CircuitConfig::standard_recursion_config()))
    }
}
