//! Simplex BFT consensus -- pure state machine core.
//!
//! Implements the Simplex consensus protocol (Chan & Pass 2023, ePrint 2023/463).
//! The core is a deterministic state machine with no I/O, no timers, no networking.
//!
//! - [`replica`] -- `Replica::apply_message()` state machine
//! - [`types`] -- `Block`, `Message`, `StateTransition`, `Outgoing`, `NetworkConfig`
//! - [`vrf`] -- Leader election oracle

pub mod types;
pub mod replica;
pub mod vrf;
