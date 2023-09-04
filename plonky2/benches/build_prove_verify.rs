mod allocator;

use criterion::{criterion_group, criterion_main, BatchSize, Criterion, black_box};
use plonky2::gates::monolith::MonolithGate;
use plonky2::gates::poseidon::PoseidonGate;
use plonky2::field::types::Field;
use plonky2::hash::hash_types::RichField;
use plonky2::hash::poseidon::{Poseidon, PoseidonHash, SPONGE_WIDTH};
use plonky2::hash::monolith::{Monolith, MonolithHash, N_ROUNDS, NUM_BARS, LOOKUP_SIZE, LOOKUP_NUM_LIMBS, add_lookup_table, MonolithCompactHash};
use plonky2::iop::target::{Target, BoolTarget};
use plonky2_field::extension::Extendable;
use std::collections::HashMap;
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::CircuitConfig;
use plonky2::plonk::config::{AlgebraicHasher, GenericConfig, PoseidonGoldilocksConfig, MonolithGoldilocksConfig};
use std::cmp;
use plonky2::gates::gate::Gate;

#[inline]
fn permute_swapped_poseidon<F: RichField, const D: usize>(
    inputs: [Target; SPONGE_WIDTH],
    builder: &mut CircuitBuilder<F, D>,
) -> [Target; SPONGE_WIDTH]
where
    F: RichField + Extendable<D>,
{
    let swap_target = builder._false().target;
    let gate_type = PoseidonGate::<F, D>::new();
    let gate = builder.add_gate(gate_type, vec![]);

    let swap_wire = PoseidonGate::<F, D>::WIRE_SWAP;
    let swap_wire = Target::wire(gate, swap_wire);
    builder.connect(swap_target, swap_wire);

    // Route input wires.
    for i in 0..SPONGE_WIDTH {
        let in_wire = PoseidonGate::<F, D>::wire_input(i);
        let in_wire = Target::wire(gate, in_wire);
        builder.connect(inputs[i], in_wire);
    }

    // Collect output wires.
    (0..SPONGE_WIDTH)
        .map(|i| Target::wire(gate, PoseidonGate::<F, D>::wire_output(i)))
        .collect::<Vec<_>>()
        .try_into()
        .unwrap()
}

#[inline]
fn permute_swapped_monolith<F: RichField, const D: usize>(
    inputs: [Target; SPONGE_WIDTH],
    builder: &mut CircuitBuilder<F, D>,
) -> [Target; SPONGE_WIDTH]
where
    F: RichField + Extendable<D>,
{
    let lut_index = add_lookup_table(builder);
    let swap_target = builder._false().target;
    let gate_type = MonolithGate::<F, D>::new();
    let gate = builder.add_gate(gate_type, vec![]);

    let swap_wire = MonolithGate::<F, D>::WIRE_SWAP;
    let swap_wire = Target::wire(gate, swap_wire);
    builder.connect(swap_target, swap_wire);

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

// pub(crate) fn bench_poseidon_build(c: &mut Criterion) {
//     const D: usize = 2;
//     type C = PoseidonGoldilocksConfig;
//     type F = <C as GenericConfig<D>>::F;


//     let config = CircuitConfig::standard_recursion_config();
//     let mut builder = CircuitBuilder::new(config);
//     let inp_targets = builder.add_virtual_target_arr::<SPONGE_WIDTH>();
//     let out_targets = permute_swapped_poseidon(inp_targets, &mut builder);

//     builder.register_public_inputs(out_targets.as_slice());
//     let circuit = builder.build::<C>();

//     c.bench_function("[Poseidon] Build", |b| b.iter(|| {let circuit = builder.build::<C>();}));
// }

pub(crate) fn bench_poseidon_prove(c: &mut Criterion) {
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;


    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::new(config);
    let inp_targets = builder.add_virtual_target_arr::<SPONGE_WIDTH>();
    let out_targets = permute_swapped_poseidon(inp_targets, &mut builder);

    builder.register_public_inputs(out_targets.as_slice());

    let circuit = builder.build::<C>();

    let permutation_inputs = (0..SPONGE_WIDTH)
        .map(F::from_canonical_usize)
        .collect::<Vec<_>>();

    let mut inputs = PartialWitness::new();
    inp_targets.iter().zip(permutation_inputs.iter()).for_each(|(t, val)| inputs.set_target(
        *t, *val
    ));

    c.bench_function("[Poseidon] Prove", |b| b.iter(|| {let res = circuit.prove(black_box(inputs.to_owned())).unwrap(); black_box(res)}));
}

pub(crate) fn bench_poseidon_verify(c: &mut Criterion) {
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;


    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::new(config);
    let inp_targets = builder.add_virtual_target_arr::<SPONGE_WIDTH>();
    let out_targets = permute_swapped_poseidon(inp_targets, &mut builder);

    builder.register_public_inputs(out_targets.as_slice());

    let circuit = builder.build::<C>();

    let permutation_inputs = (0..SPONGE_WIDTH)
        .map(F::from_canonical_usize)
        .collect::<Vec<_>>();

    let mut inputs = PartialWitness::new();
    inp_targets.iter().zip(permutation_inputs.iter()).for_each(|(t, val)| inputs.set_target(
        *t, *val
    ));

    let proof = circuit.prove(inputs).unwrap();

    let expected_outputs: [F; SPONGE_WIDTH] = F::poseidon(permutation_inputs.try_into().unwrap());

    proof.public_inputs.iter().zip(expected_outputs.iter()).for_each(|(v, out)| {
        assert_eq!(*v, *out)
    });

    c.bench_function("[Poseidon] Verify", |b| b.iter(|| {let res = circuit.verify(black_box(proof.to_owned())); black_box(res)}));
}

pub(crate) fn bench_monolith_prove(c: &mut Criterion) {
    const D: usize = 2;
    type C = MonolithGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;

    let needed_wires = cmp::max(MonolithGate::<F,D>::new().num_wires(), 135);
    let config = CircuitConfig {
        num_wires: needed_wires,
        num_routed_wires: needed_wires,
        ..CircuitConfig::standard_recursion_config()
    };

    let mut builder = CircuitBuilder::new(config);
    let inp_targets = builder.add_virtual_target_arr::<SPONGE_WIDTH>();
    let out_targets = permute_swapped_monolith(inp_targets, &mut builder);
    builder.register_public_inputs(out_targets.as_slice());

    

    let circuit = builder.build::<C>();

    let permutation_inputs = (0..SPONGE_WIDTH)
        .map(F::from_canonical_usize)
        .collect::<Vec<_>>();

    let mut inputs = PartialWitness::new();
    inp_targets.iter().zip(permutation_inputs.iter()).for_each(|(t, val)| inputs.set_target(
        *t, *val
    ));

    c.bench_function("[Monolith] Prove", |b| b.iter(|| {let res = circuit.prove(black_box(inputs.to_owned())).unwrap(); black_box(res)}));
}

pub(crate) fn bench_monolith_verify(c: &mut Criterion) {
    const D: usize = 2;
    type C = MonolithGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;

    let needed_wires = cmp::max(MonolithGate::<F,D>::new().num_wires(), 135);
    let config = CircuitConfig {
        num_wires: needed_wires,
        num_routed_wires: needed_wires,
        ..CircuitConfig::standard_recursion_config()
    };

    let mut builder = CircuitBuilder::new(config);
    let inp_targets = builder.add_virtual_target_arr::<SPONGE_WIDTH>();
    let out_targets = permute_swapped_monolith(inp_targets, &mut builder);
    builder.register_public_inputs(out_targets.as_slice());

    let circuit = builder.build::<C>();

    let permutation_inputs = (0..SPONGE_WIDTH)
        .map(F::from_canonical_usize)
        .collect::<Vec<_>>();

    let mut inputs = PartialWitness::new();
    inp_targets.iter().zip(permutation_inputs.iter()).for_each(|(t, val)| inputs.set_target(
        *t, *val
    ));

    let proof = circuit.prove(inputs).unwrap();

    let expected_outputs: [F; SPONGE_WIDTH] = F::monolith_u128(permutation_inputs.try_into().unwrap());

    proof.public_inputs.iter().zip(expected_outputs.iter()).for_each(|(v, out)| {
        assert_eq!(*v, *out)
    });

    c.bench_function("[Monolith] Verify", |b| b.iter(|| {let res = circuit.verify(black_box(proof.to_owned())); black_box(res)}));
}

fn criterion_benchmark(c: &mut Criterion) {
    // bench_poseidon_build(c);
    bench_poseidon_prove(c);
    bench_poseidon_verify(c);

    bench_monolith_prove(c);
    bench_monolith_verify(c);
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
