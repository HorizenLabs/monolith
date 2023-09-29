#![warn(missing_docs)]
#![allow(clippy::needless_range_loop)]

#![doc = include_str!("../README.md")]
 
/// Implementation of Monolith hash function and data structures to employ it in Plonky2
pub mod monolith_hash;

/// Implementation of a Plonky2 gate for Monolith and data structures to employ it in Plonky2 circuits
pub mod gates;