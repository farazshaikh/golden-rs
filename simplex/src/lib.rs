//! # Simplex BFT Consensus -- Demo
//!
//! A local simulation of the Simplex BFT consensus protocol (Chan & Pass, 2023)
//! using BLS12-381 threshold signatures from `threshold-crypto`.
//!
//! The core consensus state machine lives in `simplex-consensus`.
//! This crate provides the simulation engine, Byzantine scenarios, and display.

// Re-export the consensus core.
pub use simplex_consensus::types;
pub use simplex_consensus::replica;
pub use simplex_consensus::vrf;

// Simulation-specific modules (NOT in scope for formal verification).
pub mod engine;
pub mod naughty;
