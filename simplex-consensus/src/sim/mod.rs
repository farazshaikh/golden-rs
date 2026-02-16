//! Simulation harness for the Simplex consensus protocol.
//!
//! This module is NOT in scope for formal verification. It provides:
//! - [`engine`]: Pure message-routing engine that drives N replicas
//! - [`naughty`]: Byzantine behavior presets and message manipulation

pub mod engine;
pub mod naughty;
