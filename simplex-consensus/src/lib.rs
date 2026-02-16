//! # Simplex Consensus
//!
//! Pure state machine implementation of the Simplex BFT consensus protocol
//! (Chan & Pass, 2023) using BLS12-381 threshold signatures.
//!
//! ## Crate structure
//!
//! **Formal verification target** (the consensus core):
//! - [`types`] -- Protocol data structures (Block, Certificate, Message, etc.)
//! - [`replica`] -- The state machine: [`Replica::apply_message`]
//! - [`vrf`] -- Leader election oracle
//!
//! **Simulation** (NOT in scope for verification):
//! - [`sim::engine`] -- Message-routing engine that drives N replicas
//! - [`sim::naughty`] -- Byzantine behavior presets
//!
//! ## Protocol summary (Paper Section 2.1)
//!
//! Simplex runs in sequential iterations h = 1, 2, 3, ... Each iteration:
//! 1. Leader L_h proposes a block extending a notarized parent chain.
//! 2. Timer T_h starts. If it fires, the node votes for the dummy block.
//! 3. On seeing the first valid proposal from L_h, the node votes for it.
//! 4. On seeing a notarized chain of height h, enter iteration h+1.
//!    If the timer has NOT fired, also send a finalize vote.
//! 5. A block is finalized when notarized AND has >= 2n/3 finalize votes.
//!
//! Safety (Theorem 3.1) holds for f < n/3 via quorum intersection.

// ── Consensus core (formal verification target) ────────────────────────
pub mod types;
pub mod replica;
pub mod vrf;

// ── Simulation (NOT in scope for formal verification) ──────────────────
pub mod sim;
