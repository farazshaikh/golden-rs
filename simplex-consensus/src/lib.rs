//! # Simplex Consensus Core
//!
//! Pure state machine implementation of the Simplex BFT consensus protocol
//! (Chan & Pass, 2023) using BLS12-381 threshold signatures.
//!
//! This crate is the formal verification target. It contains NO networking,
//! timers, display, or simulation logic. The single entry point is
//! [`replica::Replica::apply_message`].
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

pub mod types;
pub mod replica;
pub mod vrf;
