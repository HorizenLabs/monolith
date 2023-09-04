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
pub struct BaseSumCustomGate<const B: usize> {
    pub num_limbs: usize,
    pub num_ops: usize,
}

impl<const B: usize> BaseSumCustomGate<B> {
    pub fn new(num_limbs: usize, config: &CircuitConfig) -> Self {
        let wires_per_op = num_limbs+1;
        let num_ops = config.num_routed_wires/wires_per_op;
        Self { num_limbs, num_ops }
    }

    pub fn new_from_config<F: Field64>(config: &CircuitConfig) -> Self {
        let num_limbs =
            log_floor(F::ORDER - 1, B as u64).min(config.num_routed_wires - Self::START_LIMBS);
        Self::new(num_limbs, config)
    }

    pub const WIRE_SUM: usize = 0;
    pub const START_LIMBS: usize = 1;

    pub fn ith_wire_sum(&self, i: usize) -> usize {
        let wire_per_op = self.num_limbs+1;
        i*wire_per_op + Self::WIRE_SUM
    }

    /// Returns the index of the limb wires for i-th op.
    pub fn ith_limbs(&self, i: usize) -> Range<usize> {
        let wire_per_op = self.num_limbs+1;
        (i*wire_per_op+Self::START_LIMBS)..(i*wire_per_op + Self::START_LIMBS + self.num_limbs)
    }
}

impl<F: RichField + Extendable<D>, const D: usize, const B: usize> Gate<F, D> for BaseSumCustomGate<B> {
    fn id(&self) -> String {
        format!("{self:?} + Base: {B}")
    }

    fn num_ops(&self) -> usize {
        self.num_ops
    }

    fn eval_unfiltered(&self, vars: EvaluationVars<F, D>) -> Vec<F::Extension> {
        (0..self.num_ops).map(|i| {
            let sum = vars.local_wires[self.ith_wire_sum(i)];
            let limbs = vars.local_wires[self.ith_limbs(i)].to_vec();
            let computed_sum = reduce_with_powers(&limbs, F::Extension::from_canonical_usize(B));
            computed_sum - sum
        }).collect()
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
        (0..self.num_ops).map(|i| {
            let base = builder.constant(F::from_canonical_usize(B));
            let sum = vars.local_wires[self.ith_wire_sum(i)];
            let limbs = vars.local_wires[self.ith_limbs(i)].to_vec();
            let computed_sum = reduce_with_powers_ext_circuit(builder, &limbs, base);
            builder.sub_extension(computed_sum, sum)
        }).collect()
    }

    fn generators(&self, row: usize, _local_constants: &[F]) -> Vec<Box<dyn WitnessGenerator<F>>> {
        (0..self.num_ops).map(|i| {
            let g: Box<dyn WitnessGenerator<F>> =
            Box::new(BaseSplitGenerator::<B> {
                row,
                num_limbs: self.num_limbs,
                op: i,
            }.adapter());
            g
        }).collect()
    }

    // 1 for the sum then `num_limbs` for the limbs.
    fn num_wires(&self) -> usize {
        (1 + self.num_limbs)*self.num_ops
    }

    fn num_constants(&self) -> usize {
        0
    }

    // Bounded by the range-check (x-0)*(x-1)*...*(x-B+1).
    fn degree(&self) -> usize {
        1
    }

    // 1 for checking the sum then `num_limbs` for range-checking the limbs.
    fn num_constraints(&self) -> usize {
        self.num_ops
    }
}

impl<F: RichField + Extendable<D>, const D: usize, const B: usize> PackedEvaluableBase<F, D>
    for BaseSumCustomGate<B>
{
    fn eval_unfiltered_base_packed<P: PackedField<Scalar = F>>(
        &self,
        vars: EvaluationVarsBasePacked<P>,
        mut yield_constr: StridedConstraintConsumer<P>,
    ) {
        (0..self.num_ops).for_each(|i| {
            let sum = vars.local_wires[self.ith_wire_sum(i)];
            let limbs = vars.local_wires.view(self.ith_limbs(i));
            let computed_sum = reduce_with_powers(limbs, F::from_canonical_usize(B));

            yield_constr.one(computed_sum - sum);
        })

    }
}

#[derive(Debug)]
pub struct BaseSplitGenerator<const B: usize> {
    row: usize,
    num_limbs: usize,
    op: usize,
}

impl<const B: usize> BaseSplitGenerator<B> {
    pub(crate) fn new(row: usize, num_limbs: usize, op: usize) -> Self {
        Self {
            row,
            num_limbs,
            op,
        }
    }

    fn wires_per_op(&self) -> usize {
        self.num_limbs+1
    }

    pub(crate) fn wire_sum(&self) -> Target {
        Target::wire(self.row, self.wires_per_op()*self.op + BaseSumCustomGate::<B>::WIRE_SUM)
    }

    pub(crate) fn limbs_wires(&self) -> Vec<Target> {
        ((self.wires_per_op()*self.op  + BaseSumCustomGate::<B>::START_LIMBS)..(self.wires_per_op()*self.op + BaseSumCustomGate::<B>::START_LIMBS + self.num_limbs)).map(|i| Target::wire(self.row, i)).collect()
    }
}

impl<F: RichField, const B: usize> SimpleGenerator<F> for BaseSplitGenerator<B> {
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

        let limbs = self.limbs_wires();
        let limbs_value = (0..self.num_limbs)
            .scan(sum_value, |acc, _| {
                let tmp = *acc % B;
                *acc /= B;
                Some(F::from_canonical_usize(tmp))
            })
            .collect::<Vec<_>>();

        for (&b, b_value) in limbs.iter().zip(limbs_value) {
            out_buffer.set_target(b, b_value);
        }
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Result;

    use crate::field::goldilocks_field::GoldilocksField;
    use crate::gates::base_sum_custom::BaseSumCustomGate;
    use crate::gates::gate_testing::{test_eval_fns, test_low_degree};
    use crate::plonk::circuit_data::CircuitConfig;
    use crate::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};

    #[test]
    fn low_degree() {
        // test_low_degree::<GoldilocksField, _, 4>(BaseSumCustomGate::<65536>::new(4))
        test_low_degree::<GoldilocksField, _, 4>(BaseSumCustomGate::<256>::new(4, &CircuitConfig::standard_recursion_config()))
    }

    #[test]
    fn eval_fns() -> Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        // test_eval_fns::<F, C, _, D>(BaseSumCustomGate::<65536>::new(4))
        test_eval_fns::<F, C, _, D>(BaseSumCustomGate::<256>::new(4, &CircuitConfig::standard_recursion_config()))
    }
}
