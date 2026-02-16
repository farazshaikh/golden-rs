//! VRF-based leader election for Simplex.
//!
//! Paper Section 2.1: "each iteration h has a pre-determined block proposer
//! or leader L_h that is randomly chosen ahead of time; this is referred to
//! as a random leader election oracle."
//!
//! Uses the threshold BLS signature as a verifiable random function.
//! The VRF message for each view is deterministic, and the combined
//! threshold signature serves as the unpredictable seed for leader election.

use golden_dkg::types::NodeId;
use sha2::{Digest, Sha256};

use crate::types::View;

/// Construct the VRF message bytes for a given view.
///
/// `message = "simplex-vrf-v1" || view.to_be_bytes()`
pub fn vrf_message(view: View) -> Vec<u8> {
    let mut msg = b"simplex-vrf-v1".to_vec();
    msg.extend_from_slice(&view.to_be_bytes());
    msg
}

/// Elect a leader from a VRF seed.
///
/// Paper: `L_h := H*(h) mod n` (1-indexed NodeId).
pub fn elect_leader(vrf_seed: &[u8], n: u32) -> NodeId {
    let hash = Sha256::digest(vrf_seed);
    let val = u32::from_be_bytes([hash[0], hash[1], hash[2], hash[3]]);
    (val % n) + 1
}
