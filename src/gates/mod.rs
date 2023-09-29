/// Monolith gate for Plonky2 circuits
pub mod monolith;
/// A gate employed to split a Goldilocks field element in limbs of
/// [`crate::monolith_hash::LOOKUP_BITS`], which is necessary to apply the lookup table encoding the
/// function to be applied in the `Bars` layer; the same gate is also employed to reconstruct a
/// Goldilocks field element from the limbs, after the evaluation of the lookup table to each limb.
/// The gate works similarly to the Plonky2 `BaseSum` gate, but it is customized to be employed
/// specifically for the Monolith permutation
pub mod base_sum_custom;
/// This module provides the methods necessary to compute hashes employing Monolith gate in a
/// Plonky2 circuit
pub mod gadget;

use std::cmp;
use plonky2::plonk::circuit_data::CircuitConfig;
use plonky2::hash::hash_types::RichField;
use plonky2::field::extension::Extendable;
use plonky2::gates::gate::Gate;
use crate::{monolith_hash::Monolith,gates::monolith::MonolithGate};

/// This function provides the recommended circuit configuration to be employed when Monolith
/// permutations are computed inside a circuit with the Monolith gate
pub fn generate_config_for_monolith_gate<
F: RichField + Extendable<D> + Monolith,
const D: usize,
>() -> CircuitConfig {
let needed_wires = cmp::max(MonolithGate::<F,D>::new().num_wires(), CircuitConfig::standard_recursion_config().num_wires);
CircuitConfig {
    num_wires: needed_wires,
    num_routed_wires: needed_wires,
    ..CircuitConfig::standard_recursion_config()
}
}