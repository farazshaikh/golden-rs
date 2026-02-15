//! # Threshold VRF (Verifiable Random Beacon) Demo
//!
//! Demonstrates a threshold VRF chain using Golden DKG:
//!
//! 1. 4 participants run DKG (n=4, t=3) to establish a shared key
//! 2. Round 0: sign a seed message `[0u8; 128] || round_number(0)`
//!    -> collect t=3 partial sigs -> combine -> that's the VRF output for round 0
//! 3. Round N: sign `previous_vrf_output || round_number(N)`
//!    -> collect t=3 partial sigs -> combine -> VRF output for round N
//!
//! The VRF output is deterministic given the same signing subset reaches threshold.
//! Any 3-of-4 participants produce the SAME VRF output (threshold property).
//! The output is unpredictable before t signatures are collected.
//!
//! This is the same construction used by DFINITY/Internet Computer for their
//! random beacon, and by drand for distributed randomness.
//!
//! Run: `cargo run --example threshold_vrf`

use ark_bls12_381::{Bls12_381, Fr, G1Affine, G2Affine, G2Projective};
use ark_ec::pairing::Pairing;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{Field, UniformRand};
use ark_serialize::CanonicalSerialize;
use ark_std::rand::SeedableRng;
use golden_dkg::dkg;
use golden_dkg::types::*;
use std::collections::HashMap;

/// Hash a message to a G2 curve point (deterministic).
fn hash_to_g2(msg: &[u8]) -> G2Affine {
    use sha2::{Digest, Sha256};
    let hash = Sha256::digest(msg);
    let mut seed = [0u8; 32];
    seed.copy_from_slice(&hash);
    let mut rng = ark_std::rand::rngs::StdRng::from_seed(seed);
    G2Projective::rand(&mut rng).into_affine()
}

/// Compute Lagrange coefficient L_i(0) for node `node_id` given `all_ids`.
fn lagrange_coeff(node_id: NodeId, all_ids: &[NodeId]) -> Fr {
    let xi = Fr::from(node_id as u64);
    let mut li = Fr::from(1u64);
    for &id in all_ids {
        if id == node_id {
            continue;
        }
        let xj = Fr::from(id as u64);
        li *= xj * (xj - xi).inverse().expect("duplicate node IDs");
    }
    li
}

/// Serialize a G2 point to bytes (compressed).
fn g2_to_bytes(point: &G2Affine) -> Vec<u8> {
    let mut buf = Vec::new();
    point.serialize_compressed(&mut buf).expect("serialize");
    buf
}

/// Build the message for a VRF round: `previous_output || round_number`.
fn build_round_message(prev_vrf_bytes: &[u8], round: u64) -> Vec<u8> {
    let mut msg = prev_vrf_bytes.to_vec();
    msg.extend_from_slice(&round.to_le_bytes());
    msg
}

/// Produce a threshold BLS signature from a subset of signers.
/// Returns the combined signature (G2 point).
fn threshold_sign(
    msg_hash: &G2Affine,
    signer_ids: &[NodeId],
    outputs: &[(NodeId, DkgOutput)],
) -> G2Affine {
    let mut combined = G2Projective::default(); // identity
    for &id in signer_ids {
        let (_, output) = outputs.iter().find(|(nid, _)| *nid == id).unwrap();
        let partial_sig = (*msg_hash * output.secret_share).into_affine();
        let li = lagrange_coeff(id, signer_ids);
        combined += partial_sig * li;
    }
    combined.into_affine()
}

/// Verify a BLS signature: e(PK, H(msg)) == e(g1, sig)
fn verify_bls(pk: &G1Affine, msg_hash: &G2Affine, sig: &G2Affine) -> bool {
    let g1 = G1Affine::generator();
    Bls12_381::pairing(*pk, *msg_hash) == Bls12_381::pairing(g1, *sig)
}

/// Run the DKG and return outputs for n participants with threshold t.
fn run_dkg(n: u32, t: u32) -> Vec<(NodeId, DkgOutput)> {
    let mut rng = rand::rngs::OsRng;
    let beta = Fr::rand(&mut rng);
    let session_id = SessionId::random(&mut rng);

    let participants: Vec<Participant> = (1..=n).map(|id| Participant::new(id, &mut rng)).collect();

    let mut peers: HashMap<NodeId, G1Affine> = HashMap::new();
    for p in &participants {
        peers.insert(p.id, p.pk);
    }

    let config = DkgConfig {
        n,
        t,
        beta,
        session_id,
    };

    let dealings: Vec<_> = participants
        .iter()
        .map(|p| dkg::create_dealing(p, &config, &peers, &mut rng).unwrap())
        .collect();

    let mut outputs = Vec::new();
    for (idx, p) in participants.iter().enumerate() {
        let mut received = HashMap::new();
        for (jdx, d) in dealings.iter().enumerate() {
            if idx != jdx {
                received.insert(participants[jdx].id, d.message.clone());
            }
        }
        let output = dkg::complete(p, &dealings[idx], &received, &peers, &config).unwrap();
        outputs.push((p.id, output));
    }

    outputs
}

fn main() {
    let n = 4u32;
    let t = 3u32;
    let num_rounds = 10;

    println!("=== Threshold VRF (Random Beacon) Demo ===");
    println!("Protocol: Golden DKG + BLS Threshold Signatures");
    println!("Curve: BLS12-381");
    println!("Participants: n={}, Threshold: t={}", n, t);
    println!("Rounds: {}", num_rounds);
    println!();

    // Step 1: DKG
    println!("--- Phase 1: Distributed Key Generation ---");
    let outputs = run_dkg(n, t);
    let pk = outputs[0].1.public_key;
    println!("DKG complete. Group public key established.");
    println!();

    // Step 2: VRF chain
    println!("--- Phase 2: VRF Chain (Random Beacon) ---");
    println!();

    // Seed: 128 zero bytes (the "genesis" input)
    let seed = vec![0u8; 128];
    let mut prev_vrf_bytes = seed;

    // Two different signing subsets to demonstrate determinism
    let subset_a: Vec<NodeId> = vec![1, 2, 3];
    let subset_b: Vec<NodeId> = vec![2, 3, 4];

    for round in 0..num_rounds {
        // Build the round message: prev_output || round_number
        let round_msg = build_round_message(&prev_vrf_bytes, round);

        // Hash to G2
        let h = hash_to_g2(&round_msg);

        // Subset A signs
        let sig_a = threshold_sign(&h, &subset_a, &outputs);

        // Subset B signs (different 3-of-4)
        let sig_b = threshold_sign(&h, &subset_b, &outputs);

        // Both subsets MUST produce the same signature (threshold property)
        let sig_a_bytes = g2_to_bytes(&sig_a);
        let sig_b_bytes = g2_to_bytes(&sig_b);
        let sigs_match = sig_a_bytes == sig_b_bytes;

        // Verify the signature
        let valid = verify_bls(&pk, &h, &sig_a);

        // The VRF output is the signature bytes (deterministic, verifiable)
        let vrf_output = &sig_a_bytes;

        // Display
        let vrf_hex: String = vrf_output.iter().take(16).map(|b| format!("{:02x}", b)).collect();
        println!(
            "Round {:>2}: VRF = {}...  (valid: {}, subsets match: {})",
            round,
            vrf_hex,
            if valid { "yes" } else { "NO!" },
            if sigs_match { "yes" } else { "NO!" },
        );

        if !valid {
            println!("  ERROR: VRF signature invalid!");
            std::process::exit(1);
        }
        if !sigs_match {
            println!("  ERROR: Different subsets produced different outputs!");
            std::process::exit(1);
        }

        // Chain: next round uses this VRF output as input
        prev_vrf_bytes = sig_a_bytes;
    }

    println!();
    println!("--- Summary ---");
    println!("All {} rounds produced valid, deterministic VRF outputs.", num_rounds);
    println!("Any 3-of-4 participants produce the SAME output (threshold property).");
    println!("Each round's input chains from the previous round's output.");
    println!();
    println!("This is the random beacon construction used by:");
    println!("  - DFINITY/Internet Computer (chain-key cryptography)");
    println!("  - drand (distributed randomness beacon)");
    println!("  - Ethereum 2.0 RANDAO (conceptually similar)");
}
