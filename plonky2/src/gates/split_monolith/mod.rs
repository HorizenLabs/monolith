use plonky2_field::extension::Extendable;
use crate::gates::util::StridedConstraintConsumer;
use crate::hash::hash_types::RichField;
use crate::hash::monolith::{Monolith, SPONGE_WIDTH, NUM_BARS};
use crate::iop::ext_target::ExtensionTarget;
use crate::iop::generator::GeneratedValues;
use crate::iop::wire::Wire;
use crate::iop::witness::{PartitionWitness, Witness, WitnessWrite};
use crate::plonk::circuit_builder::CircuitBuilder;
use crate::plonk::vars::{EvaluationTargets, EvaluationVars, EvaluationVarsBase};

pub mod monolith_init;
pub mod monolith_rounds;



trait MonolithRoundWires {
    /// A wire which stores the output of the `i`-th Concrete of the round
    fn wire_concrete_out(&self, i: usize) -> usize;

    /// A wire which stores the output of the `i`-th Bar of the round
    fn wire_bars_out(&self, i: usize) -> usize;
}

/* Functions for round constraints for shared logic between MonolithInitGate and MonolithRoundsGate */
fn eval_unfiltered_round<F: RichField + Extendable<D>, const D: usize, W: MonolithRoundWires>(
    round_wires: W,
    rc: &[u64; SPONGE_WIDTH],
    vars: &EvaluationVars<F,D>,
    state: &mut [F::Extension; SPONGE_WIDTH],
    constraints: &mut Vec<F::Extension>,
) {
    // Set values after Concrete
    // (+ a very hacky way to distinguish between first and other rounds using first round constant in first "real" round)
    let loop_end = match rc[0] { 13596126580325903823 => NUM_BARS, _ => SPONGE_WIDTH };
    for i in 0..loop_end {
        let concrete_out = vars.local_wires[round_wires.wire_concrete_out(i)];
        constraints.push(state[i] - concrete_out);
        state[i] = concrete_out;
    }

    // Get values after Bars (this assumes lookups have already been applied, i.e., these are the outputs of Bars)
    for i in 0..NUM_BARS {
        state[i] = vars.local_wires[round_wires.wire_bars_out(i)];
    }

    // Bricks + Concrete
    <F as Monolith>::bricks_field(state);
    <F as Monolith>::concrete_field(state, rc.try_into().unwrap());
}

fn eval_unfiltered_base_one_round<F: RichField + Extendable<D>, const D: usize, W: MonolithRoundWires>(
    round_wires: W,
    rc: &[u64; SPONGE_WIDTH],
    vars: &EvaluationVarsBase<F>,
    state: &mut [F; SPONGE_WIDTH],
    yield_constr: &mut StridedConstraintConsumer<F>,
) {
    // Set values after Concrete
    // (+ a very hacky way to distinguish between first and other rounds using first round constant in first "real" round)
    let loop_end = match rc[0] { 13596126580325903823 => NUM_BARS, _ => SPONGE_WIDTH };
    for i in 0..loop_end {
        let concrete_out = vars.local_wires[round_wires.wire_concrete_out(i)];
        yield_constr.one(state[i] - concrete_out);
        state[i] = concrete_out;
    }

    // Get values after Bars (this assumes lookups have already been applied, i.e., these are the outputs of Bars)
    for i in 0..NUM_BARS {
        state[i] = vars.local_wires[round_wires.wire_bars_out(i)];
    }

    // Bricks + Concrete
    <F as Monolith>::bricks(state);
    <F as Monolith>::concrete(state, rc.try_into().unwrap());
}

fn eval_circuit_round<F: RichField + Extendable<D>, const D: usize, W: MonolithRoundWires>(
    round_wires: W,
    rc: &[u64; SPONGE_WIDTH],
    vars: &EvaluationTargets<D>,
    builder: &mut CircuitBuilder<F,D>,
    constraints: &mut Vec<ExtensionTarget<D>>,
    state: &mut [ExtensionTarget<D>; SPONGE_WIDTH],
) {
    // Set values after Concrete
    // (+ a very hacky way to distinguish between first and other rounds using first round constant in first "real" round)
    let loop_end = match rc[0] { 13596126580325903823 => NUM_BARS, _ => SPONGE_WIDTH };
    for i in 0..loop_end {
        let concrete_out = vars.local_wires[round_wires.wire_concrete_out(i)];
        constraints.push(builder.sub_extension(state[i], concrete_out));
        state[i] = concrete_out;
    }

    // Get values after Bars (this assumes lookups have already been applied, i.e., these are the outputs of Bars)
    for i in 0..NUM_BARS {
        state[i] = vars.local_wires[round_wires.wire_bars_out(i)];
    }

    // Bricks + Concrete
    <F as Monolith>::bricks_circuit(builder, state);
    <F as Monolith>::concrete_circuit(builder, state, rc.try_into().unwrap());
}

fn generate_round<F: RichField + Extendable<D>, const D: usize, W: MonolithRoundWires, FN: Fn(usize) -> Wire>(
    round_wires: W,
    rc: &[u64; SPONGE_WIDTH],
    local_wire: FN,
    witness: &PartitionWitness<F>,
    out_buffer: &mut GeneratedValues<F>,
    state: &mut [F; SPONGE_WIDTH],
) -> bool {
    // Set values after Concrete
    // (+ a very hacky way to distinguish between first and other rounds using first round constant in first "real" round)
    let loop_end = match rc[0] { 13596126580325903823 => NUM_BARS, _ => SPONGE_WIDTH };
    for i in 0..loop_end {
        match witness.try_get_wire(local_wire(round_wires.wire_concrete_out(0))) {
            None => for i in 0..loop_end {
                out_buffer.set_wire(
                    local_wire(round_wires.wire_concrete_out(i)),
                    state[i],
                );
            },
            Some(_) => ()
        }
    }

    // Get values after Bars (this assumes lookups have already been applied, i.e., these are the outputs of Bars)
    for i in 0..NUM_BARS {
        state[i] = match witness.try_get_wire(local_wire(round_wires.wire_bars_out(i))) {
            Some(value) => value,
            None => {
                return false
            },
        };
    }

    // Bricks + Concrete
    <F as Monolith>::bricks_field(state);
    <F as Monolith>::concrete_field(state, rc.try_into().unwrap());

    return true
}