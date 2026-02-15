//! # Threshold BLS Signature Demo
//!
//! Demonstrates threshold signing using Golden DKG:
//! - 4 participants run DKG (n=4, t=3)
//! - Any 3 can produce a valid BLS threshold signature
//! - The signature verifies against the group public key using BLS12-381 pairing
//!
//! Run: `cargo run --example threshold_bls`

use ark_bls12_381::{Bls12_381, Fr, G1Affine, G2Affine, G2Projective};
use ark_ec::pairing::Pairing;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{Field, UniformRand};
use ark_std::rand::SeedableRng;
use golden_dkg::types::*;
use golden_dkg::dkg;
use std::collections::HashMap;

/// Hash a message to a G2 curve point (simple deterministic method for demo).
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
        // L_i(0) *= x_j / (x_j - x_i)
        li *= xj * (xj - xi).inverse().expect("duplicate node IDs");
    }
    li
}

/// Run the full DKG and return (outputs, peers) for n participants with threshold t.
fn run_dkg(
    n: u32,
    t: u32,
) -> Vec<(NodeId, DkgOutput)> {
    let mut rng = rand::rngs::OsRng;
    let beta = Fr::rand(&mut rng);
    let session_id = SessionId::random(&mut rng);

    // Create participants (each with independent randomness)
    let participants: Vec<Participant> = (1..=n).map(|id| Participant::new(id, &mut rng)).collect();

    // Build peer map
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

    // Round 0: create dealings
    let dealings: Vec<_> = participants
        .iter()
        .map(|p| dkg::create_dealing(p, &config, &peers, &mut rng).unwrap())
        .collect();

    // Verify all dealings (skip batch eVRF proof check for this demo --
    // the full DKG demo in golden-demo verifies these over the network)
    // For the threshold BLS demo we only need correct shares, not proofs.
    // In production, always call verify_dealing before accepting a dealing.

    // Complete: each participant collects others' dealings
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
    println!("=== Threshold BLS Signature Demo ===");
    println!("Protocol: Golden DKG (Bünz, Choi, Komlo 2025)");
    println!("Curve: BLS12-381");
    println!("Participants: n=4, Threshold: t=3");
    println!();

    // Step 1: Run DKG
    println!("1. Running DKG...");
    let outputs = run_dkg(4, 3);

    let pk = outputs[0].1.public_key;
    println!("   Group public key: PK = {:?}...", &format!("{:?}", pk)[..40]);
    println!("   All 4 participants have their secret shares.");
    println!();

    // Step 2: Sign a message
    let msg = b"Hello, threshold BLS!";
    println!("2. Message: \"{}\"", std::str::from_utf8(msg).unwrap());

    let h = hash_to_g2(msg);
    println!("   H(msg) = point on G2");
    println!();

    // Step 3: Pick 3 of 4 signers (participants 1, 2, 3)
    let signer_ids: Vec<NodeId> = vec![1, 2, 3];
    println!(
        "3. Signing with participants: {:?} (3 of 4)",
        signer_ids
    );

    // Each signer produces a partial signature: sig_i = sk_i * H(msg)
    let mut partial_sigs: Vec<(NodeId, G2Affine)> = Vec::new();
    for &id in &signer_ids {
        let (_, output) = outputs.iter().find(|(nid, _)| *nid == id).unwrap();
        let sk_i = output.secret_share;
        let sig_i = (h * sk_i).into_affine();
        partial_sigs.push((id, sig_i));
        println!("   Signer {} produced partial signature", id);
    }
    println!();

    // Step 4: Combine partial signatures using Lagrange interpolation in G2
    println!("4. Combining partial signatures (Lagrange in the exponent)...");
    let mut combined_sig = G2Projective::default(); // identity
    for &(id, sig_i) in &partial_sigs {
        let li = lagrange_coeff(id, &signer_ids);
        combined_sig += sig_i * li;
    }
    let combined_sig = combined_sig.into_affine();
    println!("   Combined signature computed.");
    println!();

    // Step 5: Verify using BLS12-381 pairing
    // Check: e(g1, sig) == e(PK, H(msg))
    println!("5. Verifying with BLS12-381 pairing...");
    let g1 = G1Affine::generator();
    let lhs = Bls12_381::pairing(pk, h);
    let rhs = Bls12_381::pairing(g1, combined_sig);

    if lhs == rhs {
        println!("   PASS: e(PK, H(msg)) == e(g1, sig)");
    } else {
        println!("   FAIL: pairing check failed!");
        std::process::exit(1);
    }
    println!();

    // Step 6: Try a different subset (participants 2, 3, 4)
    println!("6. Trying different signer subset: [2, 3, 4]...");
    let signer_ids_2: Vec<NodeId> = vec![2, 3, 4];
    let mut combined_sig_2 = G2Projective::default();
    for &id in &signer_ids_2 {
        let (_, output) = outputs.iter().find(|(nid, _)| *nid == id).unwrap();
        let sk_i = output.secret_share;
        let sig_i = (h * sk_i).into_affine();
        let li = lagrange_coeff(id, &signer_ids_2);
        combined_sig_2 += sig_i * li;
    }
    let combined_sig_2 = combined_sig_2.into_affine();
    let lhs2 = Bls12_381::pairing(pk, h);
    let rhs2 = Bls12_381::pairing(g1, combined_sig_2);

    if lhs2 == rhs2 {
        println!("   PASS: different 3-of-4 subset also produces valid signature");
    } else {
        println!("   FAIL");
        std::process::exit(1);
    }
    println!();

    // Step 7: Show that 2-of-4 fails (below threshold)
    println!("7. Trying only 2 signers (below threshold t=3)...");
    let signer_ids_3: Vec<NodeId> = vec![1, 4];
    let mut combined_sig_3 = G2Projective::default();
    for &id in &signer_ids_3 {
        let (_, output) = outputs.iter().find(|(nid, _)| *nid == id).unwrap();
        let sk_i = output.secret_share;
        let sig_i = (h * sk_i).into_affine();
        let li = lagrange_coeff(id, &signer_ids_3);
        combined_sig_3 += sig_i * li;
    }
    let combined_sig_3 = combined_sig_3.into_affine();
    let lhs3 = Bls12_381::pairing(pk, h);
    let rhs3 = Bls12_381::pairing(g1, combined_sig_3);

    if lhs3 != rhs3 {
        println!("   EXPECTED FAIL: 2-of-4 does NOT produce a valid signature (below threshold)");
    } else {
        println!("   UNEXPECTED: 2-of-4 somehow passed (this shouldn't happen)");
    }
    println!();

    println!("=== Demo Complete ===");
    println!("Golden DKG + Threshold BLS: any 3-of-4 can sign, 2-of-4 cannot.");
}
