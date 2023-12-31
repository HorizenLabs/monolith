use anyhow::Result;
use plonky2::field::extension::Extendable;
use plonky2::hash::hash_types::RichField;
use plonky2::hash::hashing::hash_n_to_m_no_pad;
use plonky2::iop::target::Target;
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig, CircuitData};
use plonky2::plonk::config::{AlgebraicHasher, GenericConfig, Hasher};
use plonky2::plonk::proof::ProofWithPublicInputs;
use std::marker::PhantomData;

/// Data structure with all input/output targets and the `CircuitData` for the circuit proven
/// in base proofs. The circuit is designed to be representative of a common base circuit
/// operating on a common public state employing also some private data.
/// The computation performed on the state was chosen to employ commonly used gates, such as
/// arithmetic and hash ones
pub struct BaseCircuit<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    const D: usize,
    H: Hasher<F> + AlgebraicHasher<F>,
> {
    private_input: Target,
    public_input: Target,
    public_output: Target,
    circuit_data: CircuitData<F, C, D>,
    num_powers: usize,
    _hasher: PhantomData<H>,
}

impl<
        F: RichField + Extendable<D>,
        C: GenericConfig<D, F = F>,
        const D: usize,
        H: Hasher<F> + AlgebraicHasher<F>,
    > BaseCircuit<F, C, D, H>
{
    pub fn build_base_circuit(config: CircuitConfig, log_num_hashes: usize) -> Self {
        let num_hashes: usize = 1usize << log_num_hashes;

        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut res_t = builder.add_virtual_public_input();
        let init_t = res_t;
        let zero = builder.zero();
        let to_be_hashed_t = builder.add_virtual_target();
        for _ in 0..num_hashes {
            res_t = builder.mul(res_t, init_t);
            res_t = builder.hash_n_to_m_no_pad::<H>(vec![res_t, to_be_hashed_t, zero, zero], 1)[0];
        }

        let out_t = builder.add_virtual_public_input();
        let is_eq_t = builder.is_equal(out_t, res_t);
        builder.assert_one(is_eq_t.target);

        let data = builder.build::<C>();

        Self {
            private_input: to_be_hashed_t,
            public_input: init_t,
            public_output: out_t,
            circuit_data: data,
            num_powers: num_hashes,
            _hasher: PhantomData::<H>,
        }
    }

    pub fn generate_base_proof(&self, init: F) -> Result<ProofWithPublicInputs<F, C, D>> {
        let mut pw = PartialWitness::<F>::new();

        pw.set_target(self.public_input, init);
        let to_be_hashed = F::rand();
        pw.set_target(self.private_input, to_be_hashed);
        let mut res = init;
        for _ in 0..self.num_powers {
            res = res.mul(init);
            res =
                hash_n_to_m_no_pad::<_, H::Permutation>(&[res, to_be_hashed, F::ZERO, F::ZERO], 1)
                    [0];
        }

        pw.set_target(self.public_output, res);

        let proof = self.circuit_data.prove(pw)?;

        self.circuit_data.verify(proof.clone())?;

        assert_eq!(proof.public_inputs[1], res);

        Ok(proof)
    }

    pub fn get_circuit_data(&self) -> &CircuitData<F, C, D> {
        &self.circuit_data
    }
}
