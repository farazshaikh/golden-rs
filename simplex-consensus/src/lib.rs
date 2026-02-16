//! Simplex BFT Consensus -- demo crate.
//!
//! The consensus core (replica, types, vrf) lives in `golden_dkg::consensus`.
//! This crate provides the simulation harness and demo binary.
//!
//! Re-exports from `golden_dkg::consensus` for backward compatibility.

// Re-export the consensus core from golden-dkg
pub use golden_dkg::consensus::types;
pub use golden_dkg::consensus::replica;
pub use golden_dkg::consensus::vrf;

// Simulation (local to this demo crate)
pub mod sim;
