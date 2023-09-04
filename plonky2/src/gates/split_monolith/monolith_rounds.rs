use std::cmp::min;
use std::marker::PhantomData;
use itertools::Itertools;
use plonky2_field::extension::Extendable;
use crate::gates::gate::Gate;
use crate::gates::split_monolith::{eval_circuit_round, eval_unfiltered_base_one_round, eval_unfiltered_round, generate_round, MonolithRoundWires};
use crate::gates::util::StridedConstraintConsumer;
use crate::hash::hash_types::RichField;
use crate::hash::monolith::{N_ROUNDS, Monolith, SPONGE_WIDTH, NUM_BARS};
use crate::iop::ext_target::ExtensionTarget;
use crate::iop::generator::{GeneratedValues, WitnessGenerator};
use crate::iop::target::Target;
use crate::iop::wire::Wire;
use crate::iop::witness::{PartitionWitness, Witness, WitnessWrite};
use crate::plonk::circuit_builder::CircuitBuilder;
use crate::plonk::circuit_data::CircuitConfig;
use crate::plonk::vars::{EvaluationTargets, EvaluationVars, EvaluationVarsBase};

/// Evaluate several number of rounds of Monolith permutation starting from round `from_round`;
/// it assumes that at least the first round has been performed with ab `MonolithInitGate`
#[derive(Debug, Default, Clone)]
pub struct MonolithRoundsGate<F: RichField + Extendable<D>, const D: usize> {
    from_round: usize,
    num_rounds: usize,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> MonolithRoundsGate<F, D> {
    pub fn new(from_round: usize, config: &CircuitConfig) -> Self {
        let available_wires = config.num_routed_wires-Self::START_PERM;
        let max_num_rounds = available_wires/Self::WIRES_PER_ROUND;
        assert!(from_round >= 2); // any previous round can be performed in the init gate
        let num_rounds = min(max_num_rounds, N_ROUNDS - from_round);
        Self {
            from_round,
            num_rounds,
            _phantom: PhantomData,
        }
    }

    pub fn num_rounds(&self) -> usize {
        self.num_rounds
    }

    /// The wire index for the `i`th input to the permutation.
    pub fn wire_input(i: usize) -> usize {
        i
    }

    /// The wire index for the `i`th output to the permutation.
    pub fn wire_output(i: usize) -> usize {
        SPONGE_WIDTH + i
    }

    const WIRES_PER_ROUND: usize = NUM_BARS + SPONGE_WIDTH;

    const START_PERM: usize = 2*SPONGE_WIDTH;
    
    /// A wire which stores the output of the `i`-th Concrete of the `round`-th round
    pub fn wire_concrete_out(round: usize, i: usize) -> usize {
        debug_assert!(i < SPONGE_WIDTH);
        Self::START_PERM + (Self::WIRES_PER_ROUND * round) + i
    }

    /// A wire which stores the output of the `i`-th Bar of the `round`-th round
    pub fn wire_bars_out(round: usize, i: usize) -> usize {
        debug_assert!(i < NUM_BARS);
        Self::START_PERM + (Self::WIRES_PER_ROUND * round) + SPONGE_WIDTH + i
    }
}

struct Rc64Round<F: RichField + Extendable<D>, const D: usize> {
    round: usize,
    _f: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> MonolithRoundWires for Rc64Round<F,D> {
    fn wire_concrete_out(&self, i: usize) -> usize {
        MonolithRoundsGate::<F,D>::wire_concrete_out(self.round, i)
    }

    fn wire_bars_out(&self, i: usize) -> usize {
        MonolithRoundsGate::<F,D>::wire_bars_out(self.round, i)
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Gate<F, D> for MonolithRoundsGate<F, D> {
    fn id(&self) -> String {
        format!("{self:?}<WIDTH={SPONGE_WIDTH}>")
    }

    fn eval_unfiltered(&self, vars: EvaluationVars<F, D>) -> Vec<F::Extension> {
        let mut constraints = Vec::with_capacity(self.num_constraints());

        let mut state: [F::Extension; SPONGE_WIDTH] = (0..SPONGE_WIDTH).map(|i| {
            vars.local_wires[Self::wire_input(i)]
        }).collect::<Vec<_>>().try_into().unwrap();

        for (round_ctr, rc) in <F as Monolith>::ROUND_CONSTANTS.iter().skip(self.from_round + 1).take(self.num_rounds).enumerate() {
            eval_unfiltered_round(
                Rc64Round {
                    round: round_ctr,
                    _f: PhantomData::<F>,
                },
                rc,
                &vars,
                &mut state,
                &mut constraints,
            )
        }

        for i in 0..SPONGE_WIDTH {
            constraints.push(state[i] - vars.local_wires[Self::wire_output(i)]);
        }

        constraints
    }

    fn eval_unfiltered_base_one(
        &self, vars_base: EvaluationVarsBase<F>,
        mut yield_constr: StridedConstraintConsumer<F>
    ) {
        let mut state: [F; SPONGE_WIDTH] = (0..SPONGE_WIDTH).map(|i| {
            vars_base.local_wires[Self::wire_input(i)]
        }).collect::<Vec<_>>().try_into().unwrap();

        for (round_ctr, rc) in <F as Monolith>::ROUND_CONSTANTS.iter().skip(self.from_round + 1).take(self.num_rounds).enumerate() {
            eval_unfiltered_base_one_round(
                Rc64Round {
                    round: round_ctr,
                    _f: PhantomData::<F>,
                },
                rc,
                &vars_base,
                &mut state,
                &mut yield_constr,
            )
        }

        for i in 0..SPONGE_WIDTH {
            yield_constr.one(state[i] - vars_base.local_wires[Self::wire_output(i)]);
        }
    }

    fn eval_unfiltered_circuit(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        vars: EvaluationTargets<D>
    ) -> Vec<ExtensionTarget<D>> {
        let mut constraints = Vec::with_capacity(self.num_constraints());

        let mut state: [ExtensionTarget<D>; SPONGE_WIDTH] = (0..SPONGE_WIDTH).map(|i| {
            vars.local_wires[Self::wire_input(i)]
        }).collect::<Vec<_>>().try_into().unwrap();

        for (round_ctr, rc) in <F as Monolith>::ROUND_CONSTANTS.iter().skip(self.from_round + 1).take(self.num_rounds).enumerate() {
            eval_circuit_round(
                Rc64Round {
                    round: round_ctr,
                    _f: PhantomData::<F>,
                },
                rc,
                &vars,
                builder,
                &mut constraints,
                &mut state,
            )
        }

        for i in 0..SPONGE_WIDTH {
            constraints.push(builder.sub_extension(state[i], vars.local_wires[Self::wire_output(i)]));
        }

        constraints
    }

    fn generators(&self, row: usize, _local_constants: &[F]) -> Vec<Box<dyn WitnessGenerator<F>>> {
        let gen = MonolithRoundsGenerator::<F, D> {
            row,
            from_round: self.from_round,
            num_rounds: self.num_rounds,
            _phantom: PhantomData,
        };
        vec![Box::new(gen)]
    }

    fn num_wires(&self) -> usize {
        Self::START_PERM + self.num_rounds*Self::WIRES_PER_ROUND
    }

    fn num_constants(&self) -> usize {
        0
    }

    fn degree(&self) -> usize {
        2
    }

    fn num_constraints(&self) -> usize {
        SPONGE_WIDTH*self.num_rounds + SPONGE_WIDTH
    }
}

#[derive(Debug)]
struct MonolithRoundsGenerator<F: RichField + Extendable<D> + Monolith, const D: usize> {
    row: usize,
    from_round: usize,
    num_rounds: usize,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D> + Monolith, const D:usize> WitnessGenerator<F>
for MonolithRoundsGenerator<F,D> {
    fn watch_list(&self) -> Vec<Target> {
        (0..SPONGE_WIDTH)
            .map(|i| MonolithRoundsGate::<F, D>::wire_input(i))
            .chain(
                (0..self.num_rounds).cartesian_product(0..NUM_BARS).map(
                    |(round, i)| MonolithRoundsGate::<F, D>::wire_bars_out(round, i)
                )
            )
            .map(|column| Target::wire(self.row, column))
            .collect()
    }

    fn run(&self, witness: &PartitionWitness<F>, out_buffer: &mut GeneratedValues<F>) -> bool {
        let local_wire = |column| Wire {
            row: self.row,
            column,
        };

        let mut state: [F; SPONGE_WIDTH] = match (0..SPONGE_WIDTH)
            .map(|i| witness.try_get_wire(local_wire(MonolithRoundsGate::<F, D>::wire_input(i)))
                .ok_or("wire not yet set"))
            .collect::<Result<Vec<_>,_>>() {
            Ok(st) => st.try_into().unwrap(),
            Err(_) => return false,
        };

        // Permutation
        for (round_ctr, rc) in <F as Monolith>::ROUND_CONSTANTS.iter().skip(self.from_round + 1).take(self.num_rounds).enumerate() {
            if !generate_round(
                Rc64Round {
                    round: round_ctr,
                    _f: PhantomData::<F>,
                },
                rc,
                local_wire,
                witness,
                out_buffer,
                &mut state,
            ) {
                return false
            }
        }

        for i in 0..SPONGE_WIDTH {
            out_buffer.set_wire(local_wire(MonolithRoundsGate::<F, D>::wire_output(i)), state[i]);
        }

        return true
    }
}

#[cfg(test)]
mod tests {
    use plonky2_field::goldilocks_field::GoldilocksField;
    use crate::gates::gate_testing::{test_eval_fns, test_low_degree};
    use super::MonolithRoundsGate;
    use crate::plonk::circuit_data::CircuitConfig;
    use crate::plonk::config::{GenericConfig, MonolithGoldilocksConfig};

    #[test]
    fn low_degree() {
        type F = GoldilocksField;
        let gate = MonolithRoundsGate::<F, 4>::new(2, &CircuitConfig::standard_recursion_config());
        assert_eq!(gate.num_rounds, 3);
        test_low_degree(gate)
    }

    #[test]
    fn eval_fns() {
        const D: usize = 2;
        type C = MonolithGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let gate = MonolithRoundsGate::<F, 2>::new(2, &CircuitConfig::standard_recursion_config());
        test_eval_fns::<F, C, _, D>(gate).unwrap();
    }
}