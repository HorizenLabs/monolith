use std::cmp::min;
use std::marker::PhantomData;
use itertools::Itertools;
use plonky2_field::extension::Extendable;
use plonky2_field::types::Field;
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

/// Evaluates an Monolith permutation performing as many rounds as possible given the current
/// circuit configuration
#[derive(Debug, Default, Clone)]
pub struct MonolithInitGate<F: RichField + Extendable<D>, const D: usize> {
    num_rounds: usize,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> MonolithInitGate<F, D> {
    pub fn new(config: &CircuitConfig) -> Self {
        let available_wires = config.num_routed_wires - Self::START_DELTA;
        let max_num_rounds = (available_wires - 2 * NUM_BARS) / Self::WIRES_PER_ROUND_AFTER_FIRST + 1;
        let num_rounds = min(max_num_rounds, N_ROUNDS);
        Self {
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

    pub fn wire_output(i: usize) -> usize {SPONGE_WIDTH + i}

    /// If this is set to 1, the first four inputs will be swapped with the next four inputs. This
    /// is useful for ordering hashes in Merkle proofs. Otherwise, this should be set to 0.
    pub const WIRE_SWAP: usize = 2*SPONGE_WIDTH;

    const START_DELTA: usize = Self::WIRE_SWAP + 1;

    /// A wire which stores `swap * (input[i + 4] - input[i])`; used to compute the swapped inputs.
    fn wire_delta(i: usize) -> usize {
        assert!(i < 4);
        Self::START_DELTA + i
    }

    const START_PERM: usize = Self::START_DELTA + 4;

    const WIRES_PER_ROUND_AFTER_FIRST: usize = SPONGE_WIDTH + NUM_BARS;

    /// Configuration:
    /// 1 Brick_out for each state element
    /// 1 Bar_out for each state element which goes through Bars
    /// = STATE_SIZE + NUM_BARS cells for each round

    /// A wire which stores the output of the `i`-th Concrete of the `round`-th round
    pub fn wire_concrete_out(round: usize, i: usize) -> usize {
        match round {
            0 => {
                    debug_assert!(round == 0);
                    debug_assert!(i < NUM_BARS);
                    Self::START_PERM + i
                },
            _ => {
                    debug_assert!(round > 0);
                    debug_assert!(i < SPONGE_WIDTH);
                    Self::START_PERM + (2 * NUM_BARS) + Self::WIRES_PER_ROUND_AFTER_FIRST * (round - 1) + i
            },
        }
    }

    /// A wire which stores the output of the `i`-th Bar of the `round`-th round
    pub fn wire_bars_out(round: usize, i: usize) -> usize {
        debug_assert!(i < NUM_BARS);
        match round {
            0 => Self::START_PERM + NUM_BARS + i,
            _ => Self::START_PERM + (2 * NUM_BARS) + Self::WIRES_PER_ROUND_AFTER_FIRST * (round - 1) + SPONGE_WIDTH + i,
        }
    }
}

struct Rc64Round<F: RichField + Extendable<D>, const D: usize> {
    round: usize,
    _f: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> MonolithRoundWires for Rc64Round<F,D> {
    fn wire_concrete_out(&self, i: usize) -> usize {
        MonolithInitGate::<F,D>::wire_concrete_out(self.round, i)
    }

    fn wire_bars_out(&self, i: usize) -> usize {
        MonolithInitGate::<F,D>::wire_bars_out(self.round, i)
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Gate<F, D> for MonolithInitGate<F, D> {
    fn id(&self) -> String {
        format!("{self:?}<WIDTH={SPONGE_WIDTH}>")
    }

    fn eval_unfiltered(&self, vars: EvaluationVars<F, D>) -> Vec<F::Extension> {
        let mut constraints = Vec::with_capacity(self.num_constraints());

        // Assert that `swap` is binary.
        let swap = vars.local_wires[Self::WIRE_SWAP];
        constraints.push(swap * (swap - F::Extension::ONE));

        // Assert that each delta wire is set properly: `delta_i = swap * (rhs - lhs)`.
        for i in 0..4 {
            let input_lhs = vars.local_wires[Self::wire_input(i)];
            let input_rhs = vars.local_wires[Self::wire_input(i + 4)];
            let delta_i = vars.local_wires[Self::wire_delta(i)];
            constraints.push(swap * (input_rhs - input_lhs) - delta_i);
        }

        // Compute the possibly-swapped input layer.
        let mut state = [F::Extension::ZERO; SPONGE_WIDTH];
        for i in 0..4 {
            let delta_i = vars.local_wires[Self::wire_delta(i)];
            let input_lhs = Self::wire_input(i);
            let input_rhs = Self::wire_input(i + 4);
            state[i] = vars.local_wires[input_lhs] + delta_i;
            state[i + 4] = vars.local_wires[input_rhs] - delta_i;
        }
        for i in 8..SPONGE_WIDTH {
            state[i] = vars.local_wires[Self::wire_input(i)];
        }

        // Permutation
        <F as Monolith>::concrete_field(&mut state, &<F as Monolith>::ROUND_CONSTANTS[0].try_into().unwrap());
        for (round_ctr, rc) in <F as Monolith>::ROUND_CONSTANTS.iter().skip(1).take(self.num_rounds).enumerate() {
            eval_unfiltered_round(
                Rc64Round {
                    round: round_ctr,
                    _f: PhantomData::<F>,
                },
                rc,
                &vars,
                &mut state,
                &mut constraints
            )
        }

        for i in 0..SPONGE_WIDTH {
            constraints.push(state[i] - vars.local_wires[Self::wire_output(i)]);
        }

        constraints

    }

    fn eval_unfiltered_base_one(
        &self,
        vars: EvaluationVarsBase<F>,
        mut yield_constr: StridedConstraintConsumer<F>,
    ) {
        // Assert that `swap` is binary.
        let swap = vars.local_wires[Self::WIRE_SWAP];
        yield_constr.one(swap * swap.sub_one());

        // Assert that each delta wire is set properly: `delta_i = swap * (rhs - lhs)`.
        for i in 0..4 {
            let input_lhs = vars.local_wires[Self::wire_input(i)];
            let input_rhs = vars.local_wires[Self::wire_input(i + 4)];
            let delta_i = vars.local_wires[Self::wire_delta(i)];
            yield_constr.one(swap * (input_rhs - input_lhs) - delta_i);
        }

        // Compute the possibly-swapped input layer.
        let mut state = [F::ZERO; SPONGE_WIDTH];
        for i in 0..4 {
            let delta_i = vars.local_wires[Self::wire_delta(i)];
            let input_lhs = Self::wire_input(i);
            let input_rhs = Self::wire_input(i + 4);
            state[i] = vars.local_wires[input_lhs] + delta_i;
            state[i + 4] = vars.local_wires[input_rhs] - delta_i;
        }
        for i in 8..SPONGE_WIDTH {
            state[i] = vars.local_wires[Self::wire_input(i)];
        }

        // Permutation
        <F as Monolith>::concrete(&mut state, &<F as Monolith>::ROUND_CONSTANTS[0].try_into().unwrap());
        for (round_ctr, rc) in <F as Monolith>::ROUND_CONSTANTS.iter().skip(1).take(self.num_rounds).enumerate() {
            eval_unfiltered_base_one_round(
                Rc64Round {
                    round: round_ctr,
                    _f: PhantomData::<F>,
                },
                rc,
                &vars,
                &mut state,
                &mut yield_constr,
            )
        }

        for i in 0..SPONGE_WIDTH {
            yield_constr.one(state[i] - vars.local_wires[Self::wire_output(i)]);
        }
    }

    fn eval_unfiltered_circuit(&self, builder: &mut CircuitBuilder<F, D>, vars: EvaluationTargets<D>) -> Vec<ExtensionTarget<D>> {
        let mut constraints = Vec::with_capacity(self.num_constraints());

        // Assert that `swap` is binary.
        let swap = vars.local_wires[Self::WIRE_SWAP];
        constraints.push(builder.mul_sub_extension(swap, swap, swap));

        // Assert that each delta wire is set properly: `delta_i = swap * (rhs - lhs)`.
        for i in 0..4 {
            let input_lhs = vars.local_wires[Self::wire_input(i)];
            let input_rhs = vars.local_wires[Self::wire_input(i + 4)];
            let delta_i = vars.local_wires[Self::wire_delta(i)];
            let diff = builder.sub_extension(input_rhs, input_lhs);
            constraints.push(builder.mul_sub_extension(swap, diff, delta_i));
        }

        // Compute the possibly-swapped input layer.
        let mut state = [builder.zero_extension(); SPONGE_WIDTH];
        for i in 0..4 {
            let delta_i = vars.local_wires[Self::wire_delta(i)];
            let input_lhs = vars.local_wires[Self::wire_input(i)];
            let input_rhs = vars.local_wires[Self::wire_input(i + 4)];
            state[i] = builder.add_extension(input_lhs, delta_i);
            state[i + 4] = builder.sub_extension(input_rhs, delta_i);
        }
        for i in 8..SPONGE_WIDTH {
            state[i] = vars.local_wires[Self::wire_input(i)];
        }

        // Permutation
        <F as Monolith>::concrete_circuit(builder, &mut state, &<F as Monolith>::ROUND_CONSTANTS[0].try_into().unwrap());
        for (round_ctr, rc) in <F as Monolith>::ROUND_CONSTANTS.iter().skip(1).take(self.num_rounds).enumerate() {
            eval_circuit_round(
                Rc64Round{
                    round: round_ctr,
                    _f: PhantomData::<F>
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
        let gen = MonolithInitGenerator::<F, D> {
            row,
            num_rounds: self.num_rounds,
            _phantom: PhantomData,
        };
        vec![Box::new(gen)]
    }

    fn num_wires(&self) -> usize {
        Self::START_PERM + 2 * NUM_BARS + (self.num_rounds - 1) * Self::WIRES_PER_ROUND_AFTER_FIRST
    }

    fn num_constants(&self) -> usize {
        0
    }

    fn degree(&self) -> usize {
        2
    }

    fn num_constraints(&self) -> usize {
        NUM_BARS + SPONGE_WIDTH * (self.num_rounds - 1)
            + SPONGE_WIDTH
            + 1
            + 4
    }
}

#[derive(Debug)]
struct MonolithInitGenerator<F: RichField + Extendable<D> + Monolith, const D: usize> {
    row: usize,
    num_rounds: usize,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D> + Monolith, const D:usize> WitnessGenerator<F>
for MonolithInitGenerator<F,D> {
    fn watch_list(&self) -> Vec<Target> {
        (0..SPONGE_WIDTH)
            .map(|i| MonolithInitGate::<F, D>::wire_input(i))
            .chain(Some(MonolithInitGate::<F, D>::WIRE_SWAP))
            .chain(
                (0..self.num_rounds).cartesian_product(0..NUM_BARS).map(
                    |(round, i)| MonolithInitGate::<F, D>::wire_bars_out(round, i)
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

        let mut state = (0..SPONGE_WIDTH)
            .map(|i| witness.get_wire(local_wire(MonolithInitGate::<F, D>::wire_input(i))))
            .collect::<Vec<_>>();

        let swap_value = witness.get_wire(local_wire(MonolithInitGate::<F, D>::WIRE_SWAP));
        debug_assert!(swap_value == F::ZERO || swap_value == F::ONE);

        match witness.try_get_wire(local_wire(MonolithInitGate::<F, D>::wire_delta(0))) {
            None => for i in 0..4 {
                let delta_i = swap_value * (state[i + 4] - state[i]);
                out_buffer.set_wire(local_wire(MonolithInitGate::<F, D>::wire_delta(i)), delta_i);
            },
            Some(_) => (),
        }

        if swap_value == F::ONE {
            for i in 0..4 {
                state.swap(i, 4 + i);
            }
        }

        let mut state: [F; SPONGE_WIDTH] = state.try_into().unwrap();

        // Permutation
        <F as Monolith>::concrete_field(&mut state, &<F as Monolith>::ROUND_CONSTANTS[0].try_into().unwrap());
        for (round_ctr, rc) in <F as Monolith>::ROUND_CONSTANTS.iter().skip(1).take(self.num_rounds).enumerate() {
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
            out_buffer.set_wire(local_wire(MonolithInitGate::<F, D>::wire_output(i)), state[i]);
        }

        return true
    }
}

#[cfg(test)]
mod tests {
    use plonky2_field::goldilocks_field::GoldilocksField;
    use crate::gates::gate_testing::{test_eval_fns, test_low_degree};
    use super::MonolithInitGate;
    use crate::plonk::circuit_data::CircuitConfig;
    use crate::plonk::config::{GenericConfig, MonolithGoldilocksConfig};

    #[test]
    fn low_degree() {
        type F = GoldilocksField;
        let gate = MonolithInitGate::<F, 4>::new(&CircuitConfig::standard_recursion_config());
        assert_eq!(gate.num_rounds, 3);
        test_low_degree(gate)
    }

    #[test]
    fn eval_fns() {
        const D: usize = 2;
        type C = MonolithGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let gate = MonolithInitGate::<F, 2>::new(&CircuitConfig::standard_recursion_config());
        test_eval_fns::<F, C, _, D>(gate).unwrap();
    }
}