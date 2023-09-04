mod allocator;

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use plonky2::field::goldilocks_field::GoldilocksField;

use anyhow::ensure;
use plonky2_maybe_rayon::*;
use serde::{Deserialize, Serialize};

use plonky2::field::extension::Extendable;
use plonky2::fri::oracle::PolynomialBatch;
use plonky2::fri::proof::{
    CompressedFriProof, FriChallenges, FriChallengesTarget, FriProof, FriProofTarget,
};
use plonky2::fri::structure::{
    FriOpeningBatch, FriOpeningBatchTarget, FriOpenings, FriOpeningsTarget,
};
use plonky2::fri::FriParams;
use plonky2::hash::hash_types::{MerkleCapTarget, RichField};
use plonky2::hash::hashing::HashConfig;
use plonky2::hash::merkle_tree::MerkleCap;
use plonky2::iop::ext_target::ExtensionTarget;
use plonky2::iop::target::Target;
use plonky2::plonk::circuit_data::{CommonCircuitData, VerifierOnlyCircuitData};
use plonky2::plonk::config::{GenericConfig, Hasher};
use plonky2::util::serialization::Write;

extern crate alloc;
use alloc::sync::Arc;

use anyhow::Result;
use itertools::Itertools;

use plonky2::field::types::Sample;
use plonky2::fri::reduction_strategies::FriReductionStrategy;
use plonky2::gates::noop::NoopGate;
use plonky2::iop::witness::PartialWitness;
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::CircuitConfig;
use plonky2::plonk::config::{PoseidonGoldilocksConfig};
// use plonky2::plonk::verifier::verify;

fn lookup_plonky2(c: &mut Criterion, number_lookups: u64) {
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    use plonky2_field::types::Field;
    type F = <C as GenericConfig<D>>::F;

    // let mut config = CircuitConfig::standard_recursion_config();
    // config.fri_config.reduction_strategy = FriReductionStrategy::Fixed(vec![1, 1]);
    // config.fri_config.num_query_rounds = 50;

    let pw: PartialWitness<plonky2_field::goldilocks_field::GoldilocksField> = PartialWitness::new();
    let lookup_size = 0x4000;
    let monolith_table: Vec<u16> = (0..=0x3FFF).collect(); // Dummy, just for correct size
    let table: Arc<Vec<(u16, u16)>> = Arc::new((0..=0x3FFF).zip_eq(monolith_table).collect());
    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let lut_index = builder.add_lookup_table_from_pairs(table);

    // Build dummy circuit with a lookup to get a valid proof.
    // let x = F::TWO;
    // let out = builder.constant(F::from_canonical_usize(2));

    // let xt = builder.constant(x);
    // let look_out = builder.add_lookup_from_index(xt, lut_index);
    // builder.connect(look_out, out);

    // Build benchmark
    let data = builder.build::<C>();

    // Prove benchmark
    // for num in 0..number_lookups {
    //     let out = builder.constant(F::from_canonical_u64(num % lookup_size));
    //     let xt = builder.constant(F::from_canonical_u64(num % lookup_size));
    //     let look_out = builder.add_lookup_from_index(xt, lut_index);
    //     builder.connect(look_out, out);

    //     // let a = builder.constant(F::from_canonical_usize(3));
    //     // let b = builder.constant(F::from_canonical_usize(5));
    //     // let c = builder.mul(a, b);
    //     // let d = builder.constant(F::from_canonical_usize(15));
    //     // builder.connect(c, d);
    // }
    
    // let data = builder.build::<C>();

    // c.bench_function(&format!("[Prove] Lookups for Plonky2, #lookups: {number_lookups}"),|bench| {
    //     bench.iter(|| {
    //         let pw_inp = pw.to_owned();
    //         let proof = data.prove(pw_inp);
    //     });
    // });
    // let proof = data.prove(pw);

    // verify(proof, &data.verifier_only, &data.common);

    // Verify that `decompress ∘ compress = identity`.
    // let compressed_proof = data.compress(proof.clone())?;
    // let decompressed_compressed_proof = data.decompress(compressed_proof.clone())?;
    // assert_eq!(proof, decompressed_compressed_proof);
    // println!("Proof size (bytes): {:?}", proof.unwrap().to_bytes().len());

    // verify(proof, &data.verifier_only, &data.common)?;
    // data.verify_compressed(compressed_proof)
}

fn lookup_plonky2_build(c: &mut Criterion, number_lookups: u64) {
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    use plonky2_field::types::Field;
    type F = <C as GenericConfig<D>>::F;

    c.bench_function(&format!("[Build] Lookups for Plonky2, #lookups: {number_lookups}"), |bench| {
        bench.iter(|| {
            let lookup_size = 0x100;
            let monolith_table: Vec<u16> = (0..=0xFF).collect(); // Dummy, just for correct size
            let table: Arc<Vec<(u16, u16)>> = Arc::new((0..=0xFF).zip_eq(monolith_table).collect());
            let config = CircuitConfig::standard_recursion_config();
            let mut builder = CircuitBuilder::<F, D>::new(config);
            let lut_index = builder.add_lookup_table_from_pairs(table);

            for num in 0..number_lookups {
                let out = builder.constant(F::from_canonical_u64(num % lookup_size));
                let xt = builder.constant(F::from_canonical_u64(num % lookup_size));
                let look_out = builder.add_lookup_from_index(xt, lut_index);
                builder.connect(look_out, out);
            }

            let _data = builder.build::<C>();
        });
    });
}

fn lookup_plonky2_prove(c: &mut Criterion, number_lookups: u64) {
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    use plonky2_field::types::Field;
    type F = <C as GenericConfig<D>>::F;

    let pw: PartialWitness<plonky2_field::goldilocks_field::GoldilocksField> = PartialWitness::new();
    let lookup_size = 0x100;
    let dummy_table: Vec<u16> = (0..=0xFF).collect(); // Dummy, just for correct size
    let table: Arc<Vec<(u16, u16)>> = Arc::new((0..=0xFF).zip_eq(dummy_table).collect());
    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let lut_index = builder.add_lookup_table_from_pairs(table);

    for num in 0..number_lookups {
        let out = builder.constant(F::from_canonical_u64(num % lookup_size));
        let xt = builder.constant(F::from_canonical_u64(num % lookup_size));
        let look_out = builder.add_lookup_from_index(xt, lut_index);
        builder.connect(look_out, out);
    }
    
    let data = builder.build::<C>();

    c.bench_function(&format!("[Prove] Lookups for Plonky2, #lookups: {number_lookups}"),|bench| {
        bench.iter(|| {
            let pw_inp = pw.to_owned();
            let _proof = data.prove(pw_inp);
        });
    });
}

fn lookup_plonky2_single(c: &mut Criterion) {
    use plonky2_field::types::Field;

    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;

    c.bench_function(&format!("[Build+Prove] Single lookup for Plonky2"),|bench| {
        bench.iter(|| {
            let config = CircuitConfig::standard_recursion_config();
            let mut builder = CircuitBuilder::<F, D>::new(config);
            
            // Add table
            let outp_table: [u16; 1024] = core::array::from_fn(|i| i as u16);
            let inp_table: [u16; 1024] = core::array::from_fn(|i| i as u16);
            // builder.add_lookup_table_from_table(&inp_table, &LOOKUP_TABLE);
            builder.add_lookup_table_from_table(&inp_table, &outp_table);


            let pw = PartialWitness::new();
            // let input_target = builder.constant(F::from_canonical_usize(0x113a4c0e613a9d2a));
            let input_target = builder.constant(F::from_canonical_usize(0x0));
            // let output_target_is = builder.split_le_lookup::<256>(input_target, 8, 0);
            let output_target_is = builder.split_le_lookup::<256>(input_target, 8, 0);

            // let output_target_should = builder.constant(F::from_canonical_usize(0x2275d85cc075b354));
            let output_target_should = builder.constant(F::from_canonical_usize(0x0));
            builder.connect(output_target_is, output_target_should);

            let data = builder.build::<C>();
            let _proof = data.prove(pw).unwrap();
        });
    });
}

fn criterion_benchmark(c: &mut Criterion) {
    // for number_lookups in [128, 256, 512] {
    //     // lookup_plonky2_build(c, number_lookups);
    //     lookup_plonky2_prove(c, number_lookups);
    // }
    lookup_plonky2_single(c);
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
