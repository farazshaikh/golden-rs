//! Bridge from [`golden_dkg`] to threshold-crypto types.
//!
//! Converts the raw DKG output (secret shares + public keys) into the
//! [`KeyShare`] and [`GroupInfo`] types used by this crate's signing API.

use ark_bls12_381::{Fr, G1Affine};
use ark_ff::UniformRand;
use crate::types::*;
use crate::dkg;
use rayon::prelude::*;
use std::collections::HashMap;

use crate::threshold::types::{GroupInfo, KeyShare};

/// Convert raw DKG outputs into threshold-crypto key shares and group info.
///
/// Takes the `(NodeId, DkgOutput)` pairs produced by `golden_dkg` and
/// extracts the secret shares and shared public key into this crate's types.
///
/// # Panics
///
/// Panics if `dkg_outputs` is empty.
pub fn bootstrap(dkg_outputs: &[(NodeId, DkgOutput)], t: u32) -> (Vec<KeyShare>, GroupInfo) {
    assert!(!dkg_outputs.is_empty(), "need at least one DKG output");

    let n = dkg_outputs.len() as u32;
    let pk = dkg_outputs[0].1.public_key;

    let group_info = GroupInfo {
        public_key: pk,
        threshold: t,
        num_nodes: n,
    };

    let shares = dkg_outputs
        .iter()
        .map(|(id, out)| KeyShare {
            id: *id,
            secret: out.secret_share,
            group_info: group_info.clone(),
        })
        .collect();

    (shares, group_info)
}

/// Run a full DKG ceremony and return threshold-crypto types.
///
/// Convenience function that executes the complete golden-dkg protocol
/// (create dealings + complete) with `n` participants and threshold `t`,
/// then converts the output.
///
/// Uses rayon for parallel dealing creation and completion.
pub fn run_dkg(n: u32, t: u32) -> (Vec<KeyShare>, GroupInfo) {
    let mut rng = rand::rngs::OsRng;
    let beta = Fr::rand(&mut rng);
    let session_id = SessionId::random(&mut rng);
    let participants: Vec<Participant> = (1..=n).map(|id| Participant::new(id, &mut rng)).collect();
    let peers: HashMap<NodeId, G1Affine> = participants.iter().map(|p| (p.id, p.pk)).collect();
    let config = DkgConfig { n, t, beta, session_id };

    let dealings: Vec<_> = participants
        .par_iter()
        .map(|p| {
            let mut thread_rng = rand::rngs::OsRng;
            dkg::create_dealing(p, &config, &peers, &mut thread_rng).unwrap()
        })
        .collect();

    let outputs: Vec<(NodeId, DkgOutput)> = participants
        .par_iter()
        .enumerate()
        .map(|(idx, p)| {
            let mut received = HashMap::new();
            for (jdx, d) in dealings.iter().enumerate() {
                if idx != jdx {
                    received.insert(participants[jdx].id, d.message.clone());
                }
            }
            let output = dkg::complete(p, &dealings[idx], &received, &peers, &config).unwrap();
            (p.id, output)
        })
        .collect();

    bootstrap(&outputs, t)
}
