//! VRF-based leader election for Simplex.
//!
//! Paper (Section 2.1, page 9): "each iteration h has a pre-determined
//! block proposer or leader L_h that is randomly chosen ahead of time;
//! this is referred to as a random leader election oracle and can be
//! implemented using a random oracle: namely, L_h := H*(h) mod n."
//!
//! We instantiate H* using the threshold BLS signature from the previous
//! notarization as a VRF seed, then SHA-256 for the final election.
//!
//! # Liveness Role (Paper Section 3.3)
//!
//! **Lemma 3.4** (Synchronized Iterations): "If some honest process has
//! entered iteration h by time t, then every honest process has entered
//! iteration h by time max(GST, t + delta)."
//!
//! **Lemma 3.5** (Honest Leaders): "Let h be any iteration with an honest
//! leader L_h. [...] every honest process will see a finalized block at
//! height h, proposed by L_h, by time t + 3*delta."
//!
//! **Theorem 3.4** (Expected Liveness): "3.5*delta + 1.5*Delta view-based
//! liveness." The random leader oracle ensures that after at most ~1.5
//! faulty leaders in expectation, an honest leader is elected.

use crate::types::NodeId;
use sha2::{Digest, Sha256};

use crate::consensus::types::View;

/// Construct the VRF message bytes for a given view.
///
/// The message is deterministic per view:
/// `"simplex-vrf-v1" || view.to_be_bytes()`
pub fn vrf_message(view: View) -> Vec<u8> {
    let mut msg = b"simplex-vrf-v1".to_vec();
    msg.extend_from_slice(&view.to_be_bytes());
    msg
}

/// Elect a leader from a VRF seed.
///
/// Paper: "L_h := H*(h) mod n" (1-indexed NodeId).
///
/// The VRF seed is the randomness derived from the previous view's
/// combined threshold signature (either notarization or nullification).
pub fn elect_leader(vrf_seed: &[u8], n: u32) -> NodeId {
    let hash = Sha256::digest(vrf_seed);
    let val = u32::from_be_bytes([hash[0], hash[1], hash[2], hash[3]]);
    (val % n) + 1
}
