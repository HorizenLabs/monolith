pub mod monolith;
pub mod base_sum_custom;
pub mod gadget;

use std::cmp;
use plonky2::plonk::circuit_data::CircuitConfig;
use plonky2::hash::hash_types::RichField;
use plonky2::field::extension::Extendable;
use plonky2::gates::gate::Gate;
use crate::{monolith_hash::Monolith,gates::monolith::MonolithGate};

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