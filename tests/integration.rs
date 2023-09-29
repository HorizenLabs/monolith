use plonky2_monolith::monolith_hash::MonolithHash;
use plonky2_monolith::{gates::generate_config_for_monolith_gate, monolith_hash::monolith_goldilocks::MonolithGoldilocksConfig};
use plonky2::field::{goldilocks_field::GoldilocksField, types::Sample};
use plonky2::hash::hash_types::NUM_HASH_OUT_ELTS;
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::config::Hasher;
use plonky2::iop::witness::{PartialWitness,WitnessWrite};
use core::ops::Mul;





#[test]
fn test_circuit_with_monolith() {
    type F = GoldilocksField;
    const D: usize = 2;
    type H = MonolithHash;
    type C = MonolithGoldilocksConfig;
    const NUM_OPS: usize = 1024;
    let config = generate_config_for_monolith_gate::<F,D>();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let init_t = builder.add_virtual_public_input();
    let mut res_t = builder.add_virtual_target();
    builder.connect(init_t, res_t);
    let hash_targets = (0..NUM_HASH_OUT_ELTS - 1)
        .map(|_| builder.add_virtual_target())
        .collect::<Vec<_>>();
    for _ in 0..NUM_OPS {
        res_t = builder.mul(res_t, res_t);
        let mut to_be_hashed_elements = vec![res_t];
        to_be_hashed_elements.extend_from_slice(hash_targets.as_slice());
        res_t = builder
            .hash_or_noop::<H>(to_be_hashed_elements)
            .elements[0]
    }
    let out_t = builder.add_virtual_public_input();
    let is_eq_t = builder.is_equal(out_t, res_t);
    builder.assert_one(is_eq_t.target);

    let data = builder.build::<C>();


    let mut pw = PartialWitness::<F>::new();
    let input = F::rand();
    pw.set_target(init_t, input);

    let input_hash_elements = hash_targets
        .iter()
        .map(|&hash_t| {
            let elem = F::rand();
            pw.set_target(hash_t, elem);
            elem
        })
        .collect::<Vec<_>>();

    let mut res = input;
    for _ in 0..NUM_OPS {
        res = res.mul(res);
        let mut to_be_hashed_elements = vec![res];
        to_be_hashed_elements.extend_from_slice(input_hash_elements.as_slice());
        res = H::hash_or_noop(to_be_hashed_elements.as_slice()).elements[0]
    }

    pw.set_target(out_t, res);

    let proof = data.prove(pw).unwrap();


    assert_eq!(proof.public_inputs[0], input);
    assert_eq!(proof.public_inputs[1], res);

    data.verify(proof).unwrap();

}
