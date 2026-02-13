use std::collections::HashMap;

use ark_bls12_381::{G1Affine, G1Projective};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::Field;
use ark_std::rand::Rng;

use crate::evrf;
use crate::shamir::Polynomial;
use crate::types::{Ciphertext, DkgOutput, NodeId, ReshareMsg, Scalar};
use crate::vss;

#[derive(Debug)]
pub enum ReshareError {
    CiphertextVerificationFailed { sender: NodeId, recipient: NodeId },
    MissingCiphertext { sender: NodeId, recipient: NodeId },
    InsufficientDealers { needed: u32, got: u32 },
}

impl std::fmt::Display for ReshareError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl std::error::Error for ReshareError {}

/// Old node deals its existing share to the new group.
///
/// Creates a polynomial g_i of degree (t_new - 1) with g_i(0) = old_share,
/// encrypts g_i(j) for each new member j using eVRF pads.
pub fn reshare_deal(
    old_id: NodeId,
    old_share: Scalar,
    old_sk_identity: Scalar,
    new_members: &HashMap<NodeId, G1Affine>, // new NodeId -> new identity PK
    t_new: u32,
    beta: Scalar,
    rng: &mut impl Rng,
) -> ReshareMsg {
    // Polynomial g_i of degree t_new-1 with g_i(0) = old_share
    let poly = Polynomial::new_random(old_share, (t_new - 1) as usize, rng);

    // VSS commitment
    let vss_commitment = vss::commit(&poly);

    // Random message for eVRF
    let mut random_msg = [0u8; 32];
    rng.fill(&mut random_msg[..]);

    // Encrypt shares for each new member
    let mut ciphertexts = HashMap::new();
    for (&new_id, &new_pk) in new_members {
        let share_for_new = poly.evaluate(Scalar::from(new_id as u64));
        let (r_pad, r_commitment) = evrf::derive_pad(old_sk_identity, new_pk, &random_msg, beta);
        let encrypted_share = r_pad + share_for_new;
        ciphertexts.insert(
            new_id,
            Ciphertext {
                r_commitment,
                encrypted_share,
            },
        );
    }

    ReshareMsg {
        from: old_id,
        random_msg,
        vss_commitment,
        ciphertexts,
    }
}

/// New node receives resharing messages from old group and computes new share.
///
/// Each old member i dealt their share sk_i under polynomial g_i.
/// New member j decrypts g_i(j) from each old member, then computes:
///   new_sk_j = sum_{i in S} g_i(j) * L_i(0)
/// where S is the set of old members used and L_i(0) are Lagrange coefficients
/// for the old members' indices.
pub fn reshare_receive(
    new_id: NodeId,
    new_sk_identity: Scalar,
    old_members: &HashMap<NodeId, G1Affine>, // old NodeId -> old identity PK
    received: &HashMap<NodeId, ReshareMsg>,  // old NodeId -> their ReshareMsg
    beta: Scalar,
    original_pk: G1Affine,
    old_pk_shares: &HashMap<NodeId, G1Affine>, // old NodeId -> g^{sk_i} (for verification)
    t_old: u32,
) -> Result<DkgOutput, ReshareError> {
    // Need at least t_old valid messages
    if (received.len() as u32) < t_old {
        return Err(ReshareError::InsufficientDealers {
            needed: t_old,
            got: received.len() as u32,
        });
    }

    // === VERIFICATION ===
    for (&sender_id, msg) in received {
        // Verify vss_commitment[0] == g^{sk_i} (old PK share)
        // This ensures the dealer is sharing their actual share, not garbage
        if let Some(&expected_pk_share) = old_pk_shares.get(&sender_id) {
            if msg.vss_commitment[0] != expected_pk_share {
                return Err(ReshareError::CiphertextVerificationFailed {
                    sender: sender_id,
                    recipient: new_id,
                });
            }
        }

        // Verify ciphertexts against VSS commitment
        for (&recipient_id, ct) in &msg.ciphertexts {
            let expected_share_comm =
                vss::expected_share_commitment(&msg.vss_commitment, recipient_id);
            let lhs = (G1Affine::generator() * ct.encrypted_share).into_affine();
            let rhs =
                (ct.r_commitment.into_group() + expected_share_comm.into_group()).into_affine();
            if lhs != rhs {
                return Err(ReshareError::CiphertextVerificationFailed {
                    sender: sender_id,
                    recipient: recipient_id,
                });
            }
        }
    }

    // === DECRYPTION ===
    // Decrypt sub-shares from each old member
    let mut sub_shares: Vec<(NodeId, Scalar)> = Vec::new(); // (old_id, g_i(new_id))

    for (&sender_id, msg) in received {
        let ct = msg
            .ciphertexts
            .get(&new_id)
            .ok_or(ReshareError::MissingCiphertext {
                sender: sender_id,
                recipient: new_id,
            })?;

        let sender_pk = old_members[&sender_id];
        let (r_pad, _) = evrf::derive_pad(new_sk_identity, sender_pk, &msg.random_msg, beta);
        let decrypted = ct.encrypted_share - r_pad;
        sub_shares.push((sender_id, decrypted));
    }

    // === LAGRANGE AGGREGATION ===
    // new_sk_j = sum_{i in S} g_i(j) * L_i(0)
    // where L_i(0) = product_{k != i} k / (k - i) using OLD member indices
    let mut new_secret_share = Scalar::from(0u64);
    for (idx, &(xi_id, sub_share)) in sub_shares.iter().enumerate() {
        let xi = Scalar::from(xi_id as u64);

        // Compute Lagrange coefficient L_i(0)
        let mut li = Scalar::from(1u64);
        for (jdx, &(xj_id, _)) in sub_shares.iter().enumerate() {
            if idx == jdx {
                continue;
            }
            let xj = Scalar::from(xj_id as u64);
            li *= xj * (xj - xi).inverse().expect("duplicate old node indices");
        }

        new_secret_share += sub_share * li;
    }

    // === DERIVE NEW PUBLIC KEY SHARES ===
    // For each new member k, compute PK_k = sum_{i in S} vss::expected_share_commitment(C_i, k) * L_i(0)
    // Collect all new member IDs from the ciphertexts of the first message
    let new_member_ids: Vec<NodeId> = received
        .values()
        .next()
        .unwrap()
        .ciphertexts
        .keys()
        .copied()
        .collect();

    let mut public_key_shares = HashMap::new();
    for &k in &new_member_ids {
        let mut pk_k = G1Projective::default(); // identity
        for (idx, &(sender_id, _)) in sub_shares.iter().enumerate() {
            let xi = Scalar::from(sender_id as u64);
            let mut li = Scalar::from(1u64);
            for (jdx, &(xj_id, _)) in sub_shares.iter().enumerate() {
                if idx == jdx {
                    continue;
                }
                let xj = Scalar::from(xj_id as u64);
                li *= xj * (xj - xi).inverse().expect("duplicate old node indices");
            }
            let msg = &received[&sender_id];
            let share_comm = vss::expected_share_commitment(&msg.vss_commitment, k);
            pk_k += share_comm.into_group() * li;
        }
        public_key_shares.insert(k, pk_k.into_affine());
    }

    Ok(DkgOutput {
        public_key: original_pk,
        public_key_shares,
        secret_share: new_secret_share,
    })
}
