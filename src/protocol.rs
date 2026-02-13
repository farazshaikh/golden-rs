use std::collections::HashMap;

use ark_bls12_381::G1Affine;
use ark_ec::{AdditiveGroup, AffineRepr, CurveGroup};
use ark_ff::UniformRand;
use ark_std::rand::Rng;

use crate::evrf;
use crate::shamir::Polynomial;
use crate::types::{Ciphertext, DkgOutput, NodeId, Round0Msg, Scalar};
use crate::vss;

/// Execute Round 0 of the Golden DKG protocol for a single node.
///
/// Returns the broadcast message and this node's own Shamir share.
pub fn round0(
    id: NodeId,
    n: u32,
    t: u32,
    sk: Scalar,
    peers: &HashMap<NodeId, G1Affine>,
    beta: Scalar,
    rng: &mut impl Rng,
) -> (Round0Msg, Scalar) {
    // Sample random secret omega_i
    let omega = Scalar::rand(rng);

    // Build polynomial f_i of degree t-1, f_i(0) = omega
    let poly = Polynomial::new_random(omega, (t - 1) as usize, rng);

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

    // Encrypt shares to each peer using eVRF pads
    let mut ciphertexts = HashMap::new();
    for (&peer_id, &peer_pk) in peers {
        if peer_id == id {
            continue;
        }
        let (r_pad, r_commitment) = evrf::derive_pad(sk, peer_pk, &random_msg, beta);
        let encrypted_share = r_pad + all_shares[&peer_id];
        ciphertexts.insert(
            peer_id,
            Ciphertext {
                r_commitment,
                encrypted_share,
            },
        );
    }

    let msg = Round0Msg {
        from: id,
        random_msg,
        vss_commitment,
        ciphertexts,
    };

    (msg, own_share)
}

/// Error type for protocol verification failures.
#[derive(Debug)]
pub enum ProtocolError {
    CiphertextVerificationFailed { sender: NodeId, recipient: NodeId },
    MissingCiphertext { sender: NodeId, recipient: NodeId },
    ZeroSecretViolation { sender: NodeId },
}

impl std::fmt::Display for ProtocolError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl std::error::Error for ProtocolError {}

/// Execute Round 1 of the Golden DKG protocol for a single node.
///
/// Verifies received broadcasts, decrypts shares, and produces the DKG output.
pub fn round1(
    id: NodeId,
    sk: Scalar,
    peers: &HashMap<NodeId, G1Affine>,
    own_share: Scalar,
    own_vss_commitment: Vec<G1Affine>,
    received: &HashMap<NodeId, Round0Msg>,
    beta: Scalar,
) -> Result<DkgOutput, ProtocolError> {
    let n = peers.len() as u32;

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
        // NOTE: eVRF proof verification skipped (TODO: Bulletproofs)
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
/// Per paper Section 5.2: identical to round0 but with omega = 0.
/// The polynomial f_i has f_i(0) = 0, so A_{i,0} = g^0 = identity.
/// The node's existing share is NOT modified here -- the delta is applied in round1_refresh.
pub fn round0_refresh(
    id: NodeId,
    n: u32,
    t: u32,
    sk: Scalar,
    peers: &HashMap<NodeId, G1Affine>,
    beta: Scalar,
    rng: &mut impl Rng,
) -> (Round0Msg, Scalar) {
    // Zero secret: omega = 0 (paper Section 5.2)
    let omega = Scalar::ZERO;

    // Build polynomial f_i of degree t-1, f_i(0) = 0
    let poly = Polynomial::new_random(omega, (t - 1) as usize, rng);

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

    // Encrypt shares to each peer
    let mut ciphertexts = HashMap::new();
    for (&peer_id, &peer_pk) in peers {
        if peer_id == id {
            continue;
        }
        let (r_pad, r_commitment) = evrf::derive_pad(sk, peer_pk, &random_msg, beta);
        let encrypted_share = r_pad + all_shares[&peer_id];
        ciphertexts.insert(
            peer_id,
            Ciphertext {
                r_commitment,
                encrypted_share,
            },
        );
    }

    let msg = Round0Msg {
        from: id,
        random_msg,
        vss_commitment,
        ciphertexts,
    };

    (msg, own_share)
}

/// Execute Round 1 for key refresh (zero secret sharing).
///
/// Per paper Section 5.2: identical to round1 but with an additional check
/// that A_{j,0} == identity for all senders (verifying f_j(0) = 0).
///
/// The output secret_share = existing_share + sum of zero-sharing deltas.
/// The output public_key is carried forward from the original DKG (unchanged).
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
) -> Result<DkgOutput, ProtocolError> {
    let n = peers.len() as u32;

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
