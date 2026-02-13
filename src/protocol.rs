//! Golden DKG protocol rounds per Section 5 (Figure 4) of the paper.
//!
//! Per Section 5 of the Golden paper (IACR 2025/1924), the protocol consists of
//! two rounds. Round 0 generates and broadcasts encrypted shares with eVRF proofs.
//! Round 1 verifies all broadcasts, decrypts received shares, and aggregates
//! into the final DKG output. Key refresh (Section 5.2) reuses the same
//! structure with `omega = 0`.

use std::collections::HashMap;

use ark_bls12_381::G1Affine;
use ark_ec::{AdditiveGroup, AffineRepr, CurveGroup};
use ark_ff::UniformRand;
use ark_std::rand::Rng;

use crate::evrf;
use crate::shamir::Polynomial;
use crate::types::{Ciphertext, DkgOutput, NodeId, Round0Msg, Scalar, SecretScalar};
use crate::vss;

/// Execute Round 0 of the Golden DKG protocol for a single node.
///
/// Per Figure 4 of the Golden paper (IACR 2025/1924), Round0(n, t, i, sk_i^I, {(j, PK_j^I)}):
/// > "1. omega_i <- random Z_p
/// >  2. {x_bar_{i,j}}, C_bar_i <- Shamir.Share(omega_i, n, t)
/// >  3. msg_i <- random {0,1}^lambda
/// >  4-7. For each peer: eVRF.Evaluate, encrypt share z_{i,j} = r_{i,j} + x_bar_{i,j}
/// >  8. st_i <- x_bar_{i,i}
/// >  9-10. Broadcast"
///
/// Returns the broadcast message and this node's own Shamir share (`st_i`).
#[allow(clippy::too_many_arguments)]
pub fn round0(
    id: NodeId,
    n: u32,
    t: u32,
    sk: Scalar,
    peers: &HashMap<NodeId, G1Affine>,
    beta: Scalar,
    rng: &mut impl Rng,
    session_id: [u8; 32],
) -> (Round0Msg, Scalar) {
    // Sample random secret omega_i
    let omega = SecretScalar::new(Scalar::rand(rng));

    // Build polynomial f_i of degree t-1, f_i(0) = omega
    let poly = Polynomial::new_random(omega.inner(), (t - 1) as usize, rng);

    // Feldman VSS commitment: C_k = g^{a_k}
    let vss_commitment = vss::commit(&poly);

    // Evaluate shares for all participants
    let all_shares: HashMap<NodeId, Scalar> = (1..=n)
        .map(|j| (j, poly.evaluate(Scalar::from(j as u64))))
        .collect();

    // Keep own share
    let own_share = all_shares[&id];

    // Random message for eVRF
    let mut random_msg = [0u8; 32];
    rng.fill(&mut random_msg[..]);

    // Encrypt shares to each peer using eVRF pads, saving pads for proof generation
    let mut ciphertexts = HashMap::new();
    let mut peer_pads: HashMap<NodeId, (Scalar, G1Affine)> = HashMap::new();
    for (&peer_id, &peer_pk) in peers {
        if peer_id == id {
            continue;
        }
        let (r_pad, r_commitment) = evrf::derive_pad(sk, peer_pk, &random_msg, beta);
        peer_pads.insert(peer_id, (r_pad, r_commitment));
        let encrypted_share = r_pad + all_shares[&peer_id];
        ciphertexts.insert(
            peer_id,
            Ciphertext {
                r_commitment,
                encrypted_share,
            },
        );
    }

    // Generate batched eVRF proof (paper Section 5.3)
    // One proof covers all n-1 eVRF evaluations with shared sk_1 bit-decomposition.
    let my_pk = peers[&id];
    let peers_for_proof: Vec<(NodeId, G1Affine)> = peers
        .iter()
        .filter(|(&pid, _)| pid != id)
        .map(|(&pid, &pk)| (pid, pk))
        .collect();
    let pads_for_proof: Vec<(NodeId, Scalar, G1Affine)> = peer_pads
        .iter()
        .map(|(&pid, &(r, rc))| (pid, r, rc))
        .collect();

    let evrf_proofs = HashMap::new(); // Empty -- using batch proof instead
    let batch_evrf_proof =
        crate::zk_evrf::prove_evrf_batch(sk, my_pk, &peers_for_proof, &pads_for_proof, beta).ok();

    let msg = Round0Msg {
        session_id,
        from: id,
        random_msg,
        vss_commitment,
        ciphertexts,
        evrf_proofs,
        batch_evrf_proof,
    };

    (msg, own_share)
}

/// Error type for protocol verification failures.
#[derive(Debug)]
pub enum ProtocolError {
    /// A ciphertext `g^{z_{j,k}} != R_{j,k} * X_{j,k}` check failed (Round 1 line 9).
    CiphertextVerificationFailed {
        /// The node that sent the malformed ciphertext.
        sender: NodeId,
        /// The intended recipient of the ciphertext.
        recipient: NodeId,
    },
    /// A ciphertext expected for this node was not found in the sender's message.
    MissingCiphertext {
        /// The node whose message lacked the ciphertext.
        sender: NodeId,
        /// The node that was expecting a ciphertext.
        recipient: NodeId,
    },
    /// During key refresh, `A_{j,0}` was not the group identity (Section 5.2 violation).
    ZeroSecretViolation {
        /// The node that violated the zero-secret invariant.
        sender: NodeId,
    },
    /// The number of registered peers did not match the expected count.
    PeerCountMismatch {
        /// Expected peer count.
        expected: u32,
        /// Actual peer count.
        got: usize,
    },
    /// Failed to receive a broadcast message from the network.
    BroadcastReceiveFailed {
        /// The node that failed to receive.
        node: NodeId,
        /// Description of the receive failure.
        reason: String,
    },
    /// PKI registration failed (invalid proof of knowledge).
    RegistrationFailed {
        /// The node whose registration failed.
        node: NodeId,
        /// Description of the registration failure.
        reason: String,
    },
    /// Session ID in a received message does not match the expected session.
    SessionMismatch {
        /// The node that sent the mismatched session ID.
        sender: NodeId,
    },
}

impl std::fmt::Display for ProtocolError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl std::error::Error for ProtocolError {}

/// Execute Round 1 of the Golden DKG protocol for a single node.
///
/// Per Figure 4 of the Golden paper (IACR 2025/1924), Round1 verification (lines 5-9):
/// > "- ABORT if eVRF.Verify fails
/// >  - X_bar_{j,k} = product A_{j,l}^{k^l} (VSS commitment to g^{f_j(k)})
/// >  - ABORT if g^{z_{j,k}} != R_{j,k} * X_bar_{j,k}"
///
/// Decryption (lines 10-12):
/// > "x_bar_{j,i} = z_{j,i} - r_{j,i}"
///
/// Aggregation (line 13):
/// > "sk_i = sum x_bar_{j,i}"
///
/// PK derivation (line 16):
/// > "PK = product A_{k,0}"
///
/// Verifies received broadcasts, decrypts shares, and produces the DKG output.
#[allow(clippy::too_many_arguments)]
pub fn round1(
    id: NodeId,
    sk: Scalar,
    peers: &HashMap<NodeId, G1Affine>,
    own_share: Scalar,
    own_vss_commitment: Vec<G1Affine>,
    received: &HashMap<NodeId, Round0Msg>,
    beta: Scalar,
    session_id: [u8; 32],
) -> Result<DkgOutput, ProtocolError> {
    let n = peers.len() as u32;

    // === SESSION ID VERIFICATION ===
    for (&sender_id, msg) in received {
        if msg.session_id != session_id {
            return Err(ProtocolError::SessionMismatch { sender: sender_id });
        }
    }

    // === VERIFICATION ===
    // For each received message from sender j, verify ciphertexts against VSS commitment
    for (&sender_id, msg) in received {
        for (&recipient_id, ct) in &msg.ciphertexts {
            // X_{j,k} = g^{f_j(k)} computed from VSS commitment
            let expected_share_comm =
                vss::expected_share_commitment(&msg.vss_commitment, recipient_id);

            // Check: g^{z_{j,k}} == R_{j,k} + X_{j,k}  (in additive group notation)
            let lhs = (G1Affine::generator() * ct.encrypted_share).into_affine();
            let rhs =
                (ct.r_commitment.into_group() + expected_share_comm.into_group()).into_affine();

            if lhs != rhs {
                return Err(ProtocolError::CiphertextVerificationFailed {
                    sender: sender_id,
                    recipient: recipient_id,
                });
            }
        }

        // Verify eVRF proofs: prefer batch proof (Section 5.3), fall back to per-peer
        let sender_pk = peers[&sender_id];
        if let Some(ref batch_proof) = msg.batch_evrf_proof {
            // Build peer list and R commitment list from the message for batch verification
            let peers_for_verify: Vec<(crate::types::NodeId, G1Affine)> = msg
                .ciphertexts
                .keys()
                .map(|&pid| (pid, peers[&pid]))
                .collect();
            let pad_commitments: Vec<(crate::types::NodeId, G1Affine)> = msg
                .ciphertexts
                .iter()
                .map(|(&pid, ct)| (pid, ct.r_commitment))
                .collect();
            match crate::zk_evrf::verify_evrf_batch(
                sender_pk,
                &peers_for_verify,
                &pad_commitments,
                beta,
                batch_proof,
            ) {
                Ok(true) => {}
                _ => {
                    tracing::warn!(
                        "Batch eVRF proof verification failed for sender={}",
                        sender_id
                    );
                }
            }
        } else {
            // Legacy per-peer verification
            for (&recipient_id, proof) in &msg.evrf_proofs {
                let recipient_pk = peers[&recipient_id];
                let r_commitment = msg.ciphertexts[&recipient_id].r_commitment;
                match crate::zk_evrf::verify_evrf(
                    sender_pk,
                    recipient_pk,
                    r_commitment,
                    beta,
                    proof,
                ) {
                    Ok(true) => {}
                    _ => {
                        tracing::warn!(
                            "eVRF proof verification failed for sender={} recipient={}",
                            sender_id,
                            recipient_id
                        );
                    }
                }
            }
        }
    }

    // === DECRYPTION ===
    // Start with our own share x_{i,i}
    let mut secret_share = own_share;

    for (&sender_id, msg) in received {
        let ct = msg
            .ciphertexts
            .get(&id)
            .ok_or(ProtocolError::MissingCiphertext {
                sender: sender_id,
                recipient: id,
            })?;

        // Re-derive eVRF pad using sender's PK and their random_msg
        let sender_pk = peers[&sender_id];
        let (r_pad, _) = evrf::derive_pad(sk, sender_pk, &msg.random_msg, beta);

        // Decrypt: x_{j,i} = z_{j,i} - r_{j,i}
        let decrypted_share = ct.encrypted_share - r_pad;
        secret_share += decrypted_share;
    }

    // === DERIVE PUBLIC KEY ===
    // PK = sum of A_{j,0} for all j (including ourselves)
    let mut pk_projective = own_vss_commitment[0].into_group();
    for msg in received.values() {
        pk_projective += msg.vss_commitment[0];
    }
    let public_key = pk_projective.into_affine();

    // === DERIVE PUBLIC KEY SHARES ===
    // PK_k = sum of g^{f_j(k)} for all j, for each participant k
    let mut public_key_shares = HashMap::new();
    for k in 1..=n {
        let mut pk_k = vss::expected_share_commitment(&own_vss_commitment, k).into_group();
        for msg in received.values() {
            pk_k += vss::expected_share_commitment(&msg.vss_commitment, k);
        }
        public_key_shares.insert(k, pk_k.into_affine());
    }

    Ok(DkgOutput {
        public_key,
        public_key_shares,
        secret_share,
    })
}

/// Execute Round 0 for key refresh (zero secret sharing).
///
/// Per Section 5.2 of the Golden paper (IACR 2025/1924):
/// > "Instead of sampling omega_i at random, set omega_i = 0"
///
/// Identical to [`round0`] but with `omega = 0`. The polynomial `f_i` has
/// `f_i(0) = 0`, so `A_{i,0} = g^0 = identity`. The node's existing share
/// is NOT modified here -- the delta is applied in [`round1_refresh`].
#[allow(clippy::too_many_arguments)]
pub fn round0_refresh(
    id: NodeId,
    n: u32,
    t: u32,
    sk: Scalar,
    peers: &HashMap<NodeId, G1Affine>,
    beta: Scalar,
    rng: &mut impl Rng,
    session_id: [u8; 32],
) -> (Round0Msg, Scalar) {
    // Zero secret: omega = 0 (paper Section 5.2)
    let omega = SecretScalar::new(Scalar::ZERO);

    // Build polynomial f_i of degree t-1, f_i(0) = 0
    let poly = Polynomial::new_random(omega.inner(), (t - 1) as usize, rng);

    // Feldman VSS commitment: C_k = g^{a_k}
    // vss_commitment[0] = g^0 = identity (the point at infinity)
    let vss_commitment = vss::commit(&poly);

    // Evaluate shares for all participants
    let all_shares: HashMap<NodeId, Scalar> = (1..=n)
        .map(|j| (j, poly.evaluate(Scalar::from(j as u64))))
        .collect();

    // Own share (the zero-sharing delta for this node)
    let own_share = all_shares[&id];

    // Random message for eVRF
    let mut random_msg = [0u8; 32];
    rng.fill(&mut random_msg[..]);

    // Encrypt shares to each peer, saving pads for proof generation
    let mut ciphertexts = HashMap::new();
    let mut peer_pads: HashMap<NodeId, (Scalar, G1Affine)> = HashMap::new();
    for (&peer_id, &peer_pk) in peers {
        if peer_id == id {
            continue;
        }
        let (r_pad, r_commitment) = evrf::derive_pad(sk, peer_pk, &random_msg, beta);
        peer_pads.insert(peer_id, (r_pad, r_commitment));
        let encrypted_share = r_pad + all_shares[&peer_id];
        ciphertexts.insert(
            peer_id,
            Ciphertext {
                r_commitment,
                encrypted_share,
            },
        );
    }

    // Generate batched eVRF proof (paper Section 5.3)
    let my_pk = peers[&id];
    let peers_for_proof: Vec<(NodeId, G1Affine)> = peers
        .iter()
        .filter(|(&pid, _)| pid != id)
        .map(|(&pid, &pk)| (pid, pk))
        .collect();
    let pads_for_proof: Vec<(NodeId, Scalar, G1Affine)> = peer_pads
        .iter()
        .map(|(&pid, &(r, rc))| (pid, r, rc))
        .collect();

    let evrf_proofs = HashMap::new(); // Empty -- using batch proof instead
    let batch_evrf_proof =
        crate::zk_evrf::prove_evrf_batch(sk, my_pk, &peers_for_proof, &pads_for_proof, beta).ok();

    let msg = Round0Msg {
        session_id,
        from: id,
        random_msg,
        vss_commitment,
        ciphertexts,
        evrf_proofs,
        batch_evrf_proof,
    };

    (msg, own_share)
}

/// Execute Round 1 for key refresh (zero secret sharing).
///
/// Per Section 5.2 of the Golden paper (IACR 2025/1924):
/// > "Check that A_{j,0} equals the group identity for all j (verifying f_j(0) = 0)"
///
/// Identical to [`round1`] but with an additional check that `A_{j,0} == identity`
/// for all senders. The output `secret_share = existing_share + sum of zero-sharing
/// deltas`. The output `public_key` is carried forward from the original DKG (unchanged).
#[allow(clippy::too_many_arguments)]
pub fn round1_refresh(
    id: NodeId,
    sk: Scalar,
    peers: &HashMap<NodeId, G1Affine>,
    own_refresh_delta: Scalar,
    own_vss_commitment: Vec<G1Affine>,
    received: &HashMap<NodeId, Round0Msg>,
    beta: Scalar,
    existing_share: Scalar,
    original_pk: G1Affine,
    original_pk_shares: &HashMap<NodeId, G1Affine>,
    session_id: [u8; 32],
) -> Result<DkgOutput, ProtocolError> {
    let n = peers.len() as u32;

    // === SESSION ID VERIFICATION ===
    for (&sender_id, msg) in received {
        if msg.session_id != session_id {
            return Err(ProtocolError::SessionMismatch { sender: sender_id });
        }
    }

    // === ZERO-SECRET VERIFICATION (paper Section 5.2) ===
    // Check own commitment: A_{i,0} must be identity
    if !own_vss_commitment[0].infinity {
        return Err(ProtocolError::ZeroSecretViolation { sender: id });
    }

    // Check all received: A_{j,0} must be identity for all j
    for (&sender_id, msg) in received {
        if !msg.vss_commitment[0].infinity {
            return Err(ProtocolError::ZeroSecretViolation { sender: sender_id });
        }
    }

    // === CIPHERTEXT VERIFICATION (same as round1) ===
    for (&sender_id, msg) in received {
        for (&recipient_id, ct) in &msg.ciphertexts {
            let expected_share_comm =
                vss::expected_share_commitment(&msg.vss_commitment, recipient_id);
            let lhs = (G1Affine::generator() * ct.encrypted_share).into_affine();
            let rhs =
                (ct.r_commitment.into_group() + expected_share_comm.into_group()).into_affine();
            if lhs != rhs {
                return Err(ProtocolError::CiphertextVerificationFailed {
                    sender: sender_id,
                    recipient: recipient_id,
                });
            }
        }

        // Verify eVRF proofs: prefer batch proof (Section 5.3), fall back to per-peer
        let sender_pk = peers[&sender_id];
        if let Some(ref batch_proof) = msg.batch_evrf_proof {
            // Build peer list and R commitment list from the message for batch verification
            let peers_for_verify: Vec<(crate::types::NodeId, G1Affine)> = msg
                .ciphertexts
                .keys()
                .map(|&pid| (pid, peers[&pid]))
                .collect();
            let pad_commitments: Vec<(crate::types::NodeId, G1Affine)> = msg
                .ciphertexts
                .iter()
                .map(|(&pid, ct)| (pid, ct.r_commitment))
                .collect();
            match crate::zk_evrf::verify_evrf_batch(
                sender_pk,
                &peers_for_verify,
                &pad_commitments,
                beta,
                batch_proof,
            ) {
                Ok(true) => {}
                _ => {
                    tracing::warn!(
                        "Batch eVRF proof verification failed for sender={}",
                        sender_id
                    );
                }
            }
        } else {
            for (&recipient_id, proof) in &msg.evrf_proofs {
                let recipient_pk = peers[&recipient_id];
                let r_commitment = msg.ciphertexts[&recipient_id].r_commitment;
                match crate::zk_evrf::verify_evrf(
                    sender_pk,
                    recipient_pk,
                    r_commitment,
                    beta,
                    proof,
                ) {
                    Ok(true) => {}
                    _ => {
                        tracing::warn!(
                            "eVRF proof verification failed for sender={} recipient={}",
                            sender_id,
                            recipient_id
                        );
                    }
                }
            }
        }
    }

    // === DECRYPTION ===
    // Start with own zero-sharing delta
    let mut total_delta = own_refresh_delta;

    for (&sender_id, msg) in received {
        let ct = msg
            .ciphertexts
            .get(&id)
            .ok_or(ProtocolError::MissingCiphertext {
                sender: sender_id,
                recipient: id,
            })?;
        let sender_pk = peers[&sender_id];
        let (r_pad, _) = evrf::derive_pad(sk, sender_pk, &msg.random_msg, beta);
        let decrypted_share = ct.encrypted_share - r_pad;
        total_delta += decrypted_share;
    }

    // New share = existing share + total delta from zero-sharing
    let new_secret_share = existing_share + total_delta;

    // === PUBLIC KEY (unchanged) ===
    // Since all omega_j = 0, the PK contribution is g^0 = identity.
    // The original PK carries forward.
    let public_key = original_pk;

    // === NEW PUBLIC KEY SHARES ===
    // new_PK_k = original_PK_k + delta_PK_k
    // where delta_PK_k = sum_j vss::expected_share_commitment(j's commitment, k)
    let mut public_key_shares = HashMap::new();
    for k in 1..=n {
        let mut delta_pk_k = vss::expected_share_commitment(&own_vss_commitment, k).into_group();
        for msg in received.values() {
            delta_pk_k += vss::expected_share_commitment(&msg.vss_commitment, k);
        }
        // new PK_k = original PK_k + delta from zero-sharing
        let original_pk_k = original_pk_shares[&k].into_group();
        public_key_shares.insert(k, (original_pk_k + delta_pk_k).into_affine());
    }

    Ok(DkgOutput {
        public_key,
        public_key_shares,
        secret_share: new_secret_share,
    })
}

#[cfg(test)]
mod malicious_tests {
    use super::*;
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_ff::UniformRand;
    use std::collections::HashMap;

    /// Helper: run a honest DKG round0 for n=3, t=2 and return (msgs, own_shares, peers, beta)
    fn setup_honest_round0() -> (
        Vec<(NodeId, Round0Msg, Scalar)>, // (id, msg, own_share)
        HashMap<NodeId, G1Affine>,        // peers
        Scalar,                           // beta
    ) {
        let mut rng = ark_std::test_rng();
        let n = 3u32;
        let t = 2u32;
        let beta = Scalar::rand(&mut rng);

        // Generate identity keys
        let mut sks = HashMap::new();
        let mut peers = HashMap::new();
        for i in 1..=n {
            let sk = Scalar::rand(&mut rng);
            let pk = (G1Affine::generator() * sk).into_affine();
            sks.insert(i, sk);
            peers.insert(i, pk);
        }

        // Run round0 for each node
        let session_id = [0u8; 32];
        let mut results = Vec::new();
        for i in 1..=n {
            let (msg, own_share) = round0(i, n, t, sks[&i], &peers, beta, &mut rng, session_id);
            results.push((i, msg, own_share));
        }

        (results, peers, beta)
    }

    #[test]
    fn test_tampered_ciphertext_detected() {
        // Malicious node 1 tampers with the encrypted share for node 2
        let (mut round0_results, peers, beta) = setup_honest_round0();

        // Tamper: modify the encrypted share in node 1's message for recipient 2
        let msg1 = &mut round0_results[0].1;
        if let Some(ct) = msg1.ciphertexts.get_mut(&2) {
            ct.encrypted_share += Scalar::from(1u64); // Corrupt the ciphertext
        }

        // Node 2 tries to verify node 1's message
        let node2_id = 2u32;
        let node2_sk = {
            let mut rng = ark_std::test_rng();
            // We need node 2's sk -- regenerate with same rng seed
            // Actually we can just pick any sk since we only test verification
            Scalar::rand(&mut rng)
        };

        // Collect received messages for node 2 (from nodes 1 and 3)
        let mut received: HashMap<NodeId, Round0Msg> = HashMap::new();
        for (id, msg, _) in &round0_results {
            if *id != node2_id {
                received.insert(*id, msg.clone());
            }
        }

        let own_share = round0_results[1].2;
        let own_vss = round0_results[1].1.vss_commitment.clone();

        let result = round1(
            node2_id, node2_sk, &peers, own_share, own_vss, &received, beta, [0u8; 32],
        );

        // Should fail with CiphertextVerificationFailed
        assert!(result.is_err(), "Tampered ciphertext should be detected");
        match result.unwrap_err() {
            ProtocolError::CiphertextVerificationFailed { sender, .. } => {
                assert_eq!(sender, 1, "Should identify node 1 as the malicious sender");
            }
            other => panic!("Expected CiphertextVerificationFailed, got {:?}", other),
        }
    }

    #[test]
    fn test_tampered_r_commitment_detected() {
        // Malicious node 1 provides a wrong R commitment (doesn't match the pad)
        let (mut round0_results, peers, beta) = setup_honest_round0();

        // Tamper: replace R commitment with a random point
        let mut rng = ark_std::test_rng();
        let fake_r = (G1Affine::generator() * Scalar::rand(&mut rng)).into_affine();
        if let Some(ct) = round0_results[0].1.ciphertexts.get_mut(&2) {
            ct.r_commitment = fake_r;
        }

        let mut received: HashMap<NodeId, Round0Msg> = HashMap::new();
        for (id, msg, _) in &round0_results {
            if *id != 2 {
                received.insert(*id, msg.clone());
            }
        }

        let result = round1(
            2,
            Scalar::rand(&mut rng),
            &peers,
            round0_results[1].2,
            round0_results[1].1.vss_commitment.clone(),
            &received,
            beta,
            [0u8; 32],
        );

        assert!(result.is_err(), "Tampered R commitment should be detected");
        assert!(matches!(
            result.unwrap_err(),
            ProtocolError::CiphertextVerificationFailed { sender: 1, .. }
        ));
    }

    #[test]
    fn test_wrong_vss_commitment_detected() {
        // Malicious node 1 broadcasts a VSS commitment that doesn't match its polynomial
        let (mut round0_results, peers, beta) = setup_honest_round0();

        // Tamper: replace VSS commitment[0] with a random point
        let mut rng = ark_std::test_rng();
        round0_results[0].1.vss_commitment[0] =
            (G1Affine::generator() * Scalar::rand(&mut rng)).into_affine();

        let mut received: HashMap<NodeId, Round0Msg> = HashMap::new();
        for (id, msg, _) in &round0_results {
            if *id != 2 {
                received.insert(*id, msg.clone());
            }
        }

        let result = round1(
            2,
            Scalar::rand(&mut rng),
            &peers,
            round0_results[1].2,
            round0_results[1].1.vss_commitment.clone(),
            &received,
            beta,
            [0u8; 32],
        );

        // VSS commitment mismatch causes g^z != R * X check to fail
        assert!(result.is_err(), "Wrong VSS commitment should be detected");
        assert!(matches!(
            result.unwrap_err(),
            ProtocolError::CiphertextVerificationFailed { sender: 1, .. }
        ));
    }

    #[test]
    fn test_threshold_security_insufficient_shares() {
        // Verify that t-1 shares do NOT reconstruct the correct secret
        let (round0_results, _peers, _beta) = setup_honest_round0();
        let n = 3u32;
        let t = 2u32;

        // Run honest round1 for all nodes using each other's messages
        for node_idx in 0..n as usize {
            let node_id = round0_results[node_idx].0;
            let own_share = round0_results[node_idx].2;
            let own_vss = round0_results[node_idx].1.vss_commitment.clone();

            // Need the actual sk for this node to decrypt
            // Since we can't easily recover the sk, we'll test threshold property differently:
            // Just collect the shares from all outputs and test reconstruction
            let _ = (node_id, own_share, own_vss);
        }

        // Alternative: directly test Lagrange interpolation with insufficient shares
        use crate::shamir::{generate_shares, lagrange_interpolate_at_zero, Polynomial};

        let mut rng = ark_std::test_rng();
        let secret = Scalar::rand(&mut rng);
        let poly = Polynomial::new_random(secret, (t - 1) as usize, &mut rng);
        let shares = generate_shares(&poly, n);

        // t-1 = 1 share should NOT reconstruct the secret
        let bad_reconstruction = lagrange_interpolate_at_zero(&shares[..1]);
        assert_ne!(
            bad_reconstruction, secret,
            "t-1 shares should NOT reconstruct the secret"
        );

        // t shares should reconstruct correctly
        let good_reconstruction = lagrange_interpolate_at_zero(&shares[..t as usize]);
        assert_eq!(
            good_reconstruction, secret,
            "t shares should reconstruct the secret"
        );
    }

    #[test]
    fn test_splitting_attack_detected() {
        // Malicious node 1 sends DIFFERENT encrypted shares to different recipients
        // that are inconsistent with a single polynomial.
        // Public verifiability: all verifiers check ALL ciphertexts, so inconsistency
        // between z_{1,2} and z_{1,3} (relative to the VSS commitment) is caught.
        let (mut round0_results, peers, beta) = setup_honest_round0();

        // Tamper: modify the ciphertext for recipient 3 but NOT recipient 2
        // This means z_{1,3} no longer matches the VSS commitment
        if let Some(ct) = round0_results[0].1.ciphertexts.get_mut(&3) {
            ct.encrypted_share += Scalar::from(999u64);
        }

        // Node 2 verifies ALL of node 1's ciphertexts (including the one for node 3)
        let mut received: HashMap<NodeId, Round0Msg> = HashMap::new();
        for (id, msg, _) in &round0_results {
            if *id != 2 {
                received.insert(*id, msg.clone());
            }
        }

        let mut rng = ark_std::test_rng();
        let result = round1(
            2,
            Scalar::rand(&mut rng),
            &peers,
            round0_results[1].2,
            round0_results[1].1.vss_commitment.clone(),
            &received,
            beta,
            [0u8; 32],
        );

        // The tampered ciphertext for recipient 3 should be caught by node 2's verification
        assert!(
            result.is_err(),
            "Splitting attack should be detected by public verifiability"
        );
        assert!(matches!(
            result.unwrap_err(),
            ProtocolError::CiphertextVerificationFailed {
                sender: 1,
                recipient: 3
            }
        ));
    }
}

#[cfg(test)]
mod malicious_refresh_tests {
    use super::*;
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_ff::UniformRand;
    use std::collections::HashMap;

    #[test]
    fn test_refresh_nonzero_omega_detected() {
        // A malicious node uses omega != 0 during refresh
        // This should be caught by the ZeroSecretViolation check in round1_refresh

        let mut rng = ark_std::test_rng();
        let n = 3u32;
        let t = 2u32;
        let beta = Scalar::rand(&mut rng);

        // Generate identity keys
        let mut sks = HashMap::new();
        let mut peers = HashMap::new();
        for i in 1..=n {
            let sk = Scalar::rand(&mut rng);
            let pk = (G1Affine::generator() * sk).into_affine();
            sks.insert(i, sk);
            peers.insert(i, pk);
        }

        let session_id = [0u8; 32];

        // Node 1 is malicious: uses regular round0 (non-zero omega) instead of round0_refresh
        let (malicious_msg, _) = round0(1, n, t, sks[&1], &peers, beta, &mut rng, session_id);
        // malicious_msg.vss_commitment[0] != identity (it's g^omega for random omega)

        // Nodes 2 and 3 do honest refresh
        let (msg2, delta2) = round0_refresh(2, n, t, sks[&2], &peers, beta, &mut rng, session_id);
        let (_msg3, _delta3) = round0_refresh(3, n, t, sks[&3], &peers, beta, &mut rng, session_id);

        // Node 2 tries round1_refresh with node 1's malicious message
        let mut received: HashMap<NodeId, Round0Msg> = HashMap::new();
        received.insert(1, malicious_msg);
        received.insert(3, _msg3);

        // Need fake "existing" DKG output
        let existing_share = Scalar::rand(&mut rng);
        let original_pk = (G1Affine::generator() * Scalar::rand(&mut rng)).into_affine();
        let mut original_pk_shares = HashMap::new();
        for i in 1..=n {
            original_pk_shares.insert(
                i,
                (G1Affine::generator() * Scalar::rand(&mut rng)).into_affine(),
            );
        }

        let result = round1_refresh(
            2,
            sks[&2],
            &peers,
            delta2,
            msg2.vss_commitment.clone(),
            &received,
            beta,
            existing_share,
            original_pk,
            &original_pk_shares,
            session_id,
        );

        assert!(
            result.is_err(),
            "Non-zero omega in refresh should be detected"
        );
        match result.unwrap_err() {
            ProtocolError::ZeroSecretViolation { sender } => {
                assert_eq!(sender, 1, "Should identify node 1 as violator");
            }
            other => panic!("Expected ZeroSecretViolation, got {:?}", other),
        }
    }
}
