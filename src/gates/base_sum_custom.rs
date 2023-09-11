use std::ops::Range;
use plonky2::field::extension::Extendable;
use plonky2::field::packed::PackedField;
use plonky2::field::types::{Field, Field64};
use plonky2::gates::gate::Gate;
use plonky2::gates::packed_util::PackedEvaluableBase;
use plonky2::gates::util::StridedConstraintConsumer;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::ext_target::ExtensionTarget;
use plonky2::iop::generator::{GeneratedValues, SimpleGenerator, WitnessGeneratorRef};
use plonky2::iop::target::Target;
use plonky2::iop::witness::{PartitionWitness, Witness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig, CommonCircuitData};
use plonky2::plonk::plonk_common::{reduce_with_powers, reduce_with_powers_ext_circuit};
use plonky2::plonk::vars::{EvaluationTargets, EvaluationVars, EvaluationVarsBaseBatch, EvaluationVarsBasePacked};
use plonky2::util::log_floor;
use plonky2::util::serialization::{Buffer, IoResult, Read, Write};

/// A gate which can decompose an element of a field F into base B little-endian limbs.
/// This gate is customized to be used for lookups of the Monolith hash function, and thus it has
/// the following differences w.r.t. the `BaseSum` gate:
/// - It allows to pack many instances of a decomposition gate on a single row
/// - It does not range-check each limb, since the lookup table to be applied on each limb will
/// already implicitly perform a range-check
/// - It supports the decomposition of any field element, while the `BaseSum` gate unpacks only
/// elements of at most `floor(log_B(F::order))`
#[derive(Copy, Clone, Debug)]
pub struct BaseSumCustomGate<const B: usize> {
    num_limbs: usize,
    num_ops: usize,
}

fn log_ceil(n: u64, base: u64) -> usize {
    let res = log_floor(n, base);
    if base.pow(res as u32) < n {
        res + 1
    } else {
        res
    }
}

impl<const B: usize> BaseSumCustomGate<B> {
    pub fn new(num_limbs: usize, config: &CircuitConfig) -> Self {
        let wires_per_op = Self::wires_per_op_from_limbs(num_limbs);
        let num_ops = config.num_routed_wires / wires_per_op;
        Self { num_limbs, num_ops }
    }

    pub fn new_from_config<F: Field64>(config: &CircuitConfig) -> Self {
        let num_limbs = log_ceil(F::ORDER, B as u64).min(config.num_routed_wires - Self::START_LIMBS - 2);
        Self::new(num_limbs, config)
    }

    pub const WIRE_SUM: usize = 0;
    pub const START_LIMBS: usize = 1;

    fn wires_per_op_from_limbs(num_limbs: usize) -> usize {
        // num limbs + 1 wire for the element to be decomposed + 2 wires to range-check the
        // field element obtained by re-composing the limbs
        num_limbs + 1 + 2
    }

    fn wires_per_op(&self) -> usize {
        Self::wires_per_op_from_limbs(self.num_limbs)
    }

    pub fn ith_wire_sum(&self, i: usize) -> usize {
        let wires_per_op = self.wires_per_op();
        i * wires_per_op + Self::WIRE_SUM
    }

    /// Returns the index of the limb wires for i-th op.
    pub fn ith_limbs(&self, i: usize) -> Range<usize> {
        let wires_per_op = self.wires_per_op();
        (i * wires_per_op + Self::START_LIMBS)..(i * wires_per_op + Self::START_LIMBS + self.num_limbs)
    }
}


impl<F: RichField + Extendable<D>, const D: usize, const B: usize> Gate<F, D> for BaseSumCustomGate<B> {
    fn id(&self) -> String {
        format!("{self:?} + Base: {B}")
    }

    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &CommonCircuitData<F, D>) -> IoResult<()> {
        dst.write_usize(self.num_limbs)?;
        dst.write_usize(self.num_ops)
    }

    fn deserialize(src: &mut Buffer, _common_data: &CommonCircuitData<F, D>) -> IoResult<Self> {
        let num_limbs = src.read_usize()?;
        let num_ops = src.read_usize()?;
        Ok(Self { num_limbs, num_ops })
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
            let two_8 = F::from_canonical_usize((1_u64 << 8) as usize);
            let two_16 = F::from_canonical_usize((1_u64 << 16) as usize);
            let two_24 = F::from_canonical_usize((1_u64 << 24) as usize);
            let two_32_m1 = builder.constant_extension(F::Extension::from_canonical_usize(((1_u64 << 32) - 1) as usize));

            let mut temp = builder.mul_const_add_extension(two_8, limbs[1], limbs[0]);
            temp = builder.mul_const_add_extension(two_16, limbs[2], temp);
            let a = builder.mul_const_add_extension(two_24, limbs[3], temp);

            let mut temp = builder.mul_const_add_extension(two_8, limbs[5], limbs[4]);
            temp = builder.mul_const_add_extension(two_16, limbs[6], temp);
            temp = builder.mul_const_add_extension(two_24, limbs[7], temp);
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

    fn generators(&self, row: usize, _local_constants: &[F]) -> Vec<WitnessGeneratorRef<F, D>> {
        (0..self.num_ops).map(|i| {
            let gen = BaseSplitGenerator::<B> {
                row,
                num_limbs: self.num_limbs,
                op: i,
            };
            WitnessGeneratorRef::new(gen.adapter())
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
for BaseSumCustomGate<B>
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

#[derive(Debug, Default)]
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
        BaseSumCustomGate::<B>::wires_per_op_from_limbs(self.num_limbs)
    }

    pub(crate) fn wire_sum(&self) -> Target {
        Target::wire(self.row, self.wires_per_op() * self.op + BaseSumCustomGate::<B>::WIRE_SUM)
    }

    pub(crate) fn limbs_wires(&self) -> Vec<Target> {
        ((self.wires_per_op() * self.op + BaseSumCustomGate::<B>::START_LIMBS)..(self.wires_per_op() * self.op + BaseSumCustomGate::<B>::START_LIMBS + self.num_limbs)).map(|i| Target::wire(self.row, i)).collect()
    }

    pub(crate) fn boundary_constraints_wires(&self) -> Vec<Target> {
        ((self.wires_per_op() * self.op + BaseSumCustomGate::<B>::START_LIMBS + self.num_limbs)..(self.wires_per_op() * self.op + BaseSumCustomGate::<B>::START_LIMBS + self.num_limbs + 2)).map(|i| Target::wire(self.row, i)).collect()
    }
}

impl<F: RichField + Extendable<D>, const B: usize, const D: usize> SimpleGenerator<F, D>
for BaseSplitGenerator<B>
{
    fn id(&self) -> String {
        "BaseSplitRestrictGenerator".to_string()
    }

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
            .zip(limbs.iter())
            .scan(sum_value, |acc, (_, t)| {
                let tmp = F::from_canonical_usize(*acc % B);
                *acc /= B;
                out_buffer.set_target(*t, tmp);
                Some(tmp)
            })
            .collect::<Vec<_>>();

        let a = limbs_value[3] * F::from_canonical_u64(1_u64 << 24) + limbs_value[2] * F::from_canonical_u64(1_u64 << 16) + limbs_value[1] * F::from_canonical_u64(1_u64 << 8) + limbs_value[0];
        let b = limbs_value[7] * F::from_canonical_u64(1_u64 << 24) + limbs_value[6] * F::from_canonical_u64(1_u64 << 16) + limbs_value[5] * F::from_canonical_u64(1_u64 << 8) + limbs_value[4];

        let z_field: F;
        if a == F::ZERO {
            z_field = F::ONE;
        }
        else {
            z_field = b;
        }
        let z_prime_field = F::inverse(&(z_field - F::from_canonical_u64(1_u64 << 32) + F::ONE));
        out_buffer.set_target(self.boundary_constraints_wires()[0], z_field);
        out_buffer.set_target(self.boundary_constraints_wires()[1], z_prime_field);
    }

    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &CommonCircuitData<F, D>) -> IoResult<()> {
        dst.write_usize(self.row)?;
        dst.write_usize(self.num_limbs)?;
        dst.write_usize(self.op)
    }

    fn deserialize(src: &mut Buffer, _common_data: &CommonCircuitData<F, D>) -> IoResult<Self> {
        let row = src.read_usize()?;
        let num_limbs = src.read_usize()?;
        let op = src.read_usize()?;
        Ok(Self { row, num_limbs, op })
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Result;
    use plonky2::field::goldilocks_field::GoldilocksField;
    use plonky2::gates::gate_testing::{test_eval_fns, test_low_degree};
    use plonky2::plonk::circuit_data::CircuitConfig;
    use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
    use crate::gates::base_sum_custom::BaseSumCustomGate;

    #[test]
    fn low_degree() {
        test_low_degree::<GoldilocksField, _, 4>(BaseSumCustomGate::<256>::new(8, &CircuitConfig::standard_recursion_config()))
    }

    #[test]
    fn eval_fns() -> Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        test_eval_fns::<F, C, _, D>(BaseSumCustomGate::<256>::new(8, &CircuitConfig::standard_recursion_config()))
    }
}
