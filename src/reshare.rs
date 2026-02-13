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

#[cfg(test)]
mod malicious_tests {
    use super::*;
    use ark_bls12_381::G1Affine;
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_ff::UniformRand;

    use crate::shamir::{generate_shares, Polynomial};
    use crate::types::{NodeId, Scalar};

    /// Setup an old group of `n_old` members with threshold `t_old` sharing a known secret.
    fn setup_old_group(
        n_old: u32,
        t_old: u32,
        rng: &mut impl ark_std::rand::Rng,
    ) -> (
        Scalar,                    // secret
        Vec<(NodeId, Scalar)>,     // old shares
        HashMap<NodeId, Scalar>,   // old sk_identity
        HashMap<NodeId, G1Affine>, // old pk_identity (old_members)
        HashMap<NodeId, G1Affine>, // old pk_shares (g^{sk_i})
        G1Affine,                  // original_pk
    ) {
        let secret = Scalar::rand(rng);
        let poly = Polynomial::new_random(secret, (t_old - 1) as usize, rng);
        let shares = generate_shares(&poly, n_old);
        let original_pk = (G1Affine::generator() * secret).into_affine();

        let mut old_sk_identities = HashMap::new();
        let mut old_pk_identities = HashMap::new();
        let mut old_pk_shares = HashMap::new();

        for &(id, share) in &shares {
            let sk_id = Scalar::rand(rng);
            old_sk_identities.insert(id, sk_id);
            old_pk_identities.insert(id, (G1Affine::generator() * sk_id).into_affine());
            old_pk_shares.insert(id, (G1Affine::generator() * share).into_affine());
        }

        (
            secret,
            shares,
            old_sk_identities,
            old_pk_identities,
            old_pk_shares,
            original_pk,
        )
    }

    /// Setup a new group of `n_new` members with IDs starting at `start_id`.
    fn setup_new_group(
        n_new: u32,
        start_id: NodeId,
        rng: &mut impl ark_std::rand::Rng,
    ) -> (HashMap<NodeId, Scalar>, HashMap<NodeId, G1Affine>) {
        let mut sk_map = HashMap::new();
        let mut pk_map = HashMap::new();
        for i in 0..n_new {
            let id = start_id + i;
            let sk = Scalar::rand(rng);
            sk_map.insert(id, sk);
            pk_map.insert(id, (G1Affine::generator() * sk).into_affine());
        }
        (sk_map, pk_map)
    }

    #[test]
    fn test_reshare_wrong_share_detected() {
        let mut rng = ark_std::test_rng();
        let (_, shares, old_sk_ids, old_pk_ids, old_pk_shares, original_pk) =
            setup_old_group(3, 2, &mut rng);
        let (new_sk_ids, new_pk_ids) = setup_new_group(2, 10, &mut rng);
        let beta = Scalar::rand(&mut rng);

        // Node 1 deals honestly
        let msg1 = reshare_deal(
            1,
            shares[0].1,
            old_sk_ids[&1],
            &new_pk_ids,
            2,
            beta,
            &mut rng,
        );

        // Node 2 deals with a FAKE share (not its real sk_2)
        let fake_share = Scalar::rand(&mut rng);
        let msg2 = reshare_deal(
            2,
            fake_share,
            old_sk_ids[&2],
            &new_pk_ids,
            2,
            beta,
            &mut rng,
        );

        let mut received = HashMap::new();
        received.insert(1, msg1);
        received.insert(2, msg2);

        let result = reshare_receive(
            10,
            new_sk_ids[&10],
            &old_pk_ids,
            &received,
            beta,
            original_pk,
            &old_pk_shares,
            2,
        );

        match result {
            Err(ReshareError::CiphertextVerificationFailed { sender, .. }) => {
                assert_eq!(sender, 2, "should detect malicious node 2");
                println!("correctly detected wrong share from node {sender}");
            }
            other => panic!("Expected CiphertextVerificationFailed, got {other:?}"),
        }
    }

    #[test]
    fn test_reshare_tampered_ciphertext_detected() {
        let mut rng = ark_std::test_rng();
        let (_, shares, old_sk_ids, old_pk_ids, old_pk_shares, original_pk) =
            setup_old_group(3, 2, &mut rng);
        let (new_sk_ids, new_pk_ids) = setup_new_group(2, 10, &mut rng);
        let beta = Scalar::rand(&mut rng);

        // Node 1 deals honestly
        let msg1 = reshare_deal(
            1,
            shares[0].1,
            old_sk_ids[&1],
            &new_pk_ids,
            2,
            beta,
            &mut rng,
        );

        // Node 2 deals honestly, then we tamper the encrypted_share
        let mut msg2 = reshare_deal(
            2,
            shares[1].1,
            old_sk_ids[&2],
            &new_pk_ids,
            2,
            beta,
            &mut rng,
        );
        msg2.ciphertexts
            .get_mut(&10)
            .unwrap()
            .encrypted_share += Scalar::from(1u64);

        let mut received = HashMap::new();
        received.insert(1, msg1);
        received.insert(2, msg2);

        let result = reshare_receive(
            10,
            new_sk_ids[&10],
            &old_pk_ids,
            &received,
            beta,
            original_pk,
            &old_pk_shares,
            2,
        );

        match result {
            Err(ReshareError::CiphertextVerificationFailed { sender, .. }) => {
                assert_eq!(sender, 2, "should detect tampered ciphertext from node 2");
                println!("correctly detected tampered ciphertext from node {sender}");
            }
            other => panic!("Expected CiphertextVerificationFailed, got {other:?}"),
        }
    }

    #[test]
    fn test_reshare_insufficient_dealers() {
        let mut rng = ark_std::test_rng();
        let (_, shares, old_sk_ids, old_pk_ids, old_pk_shares, original_pk) =
            setup_old_group(3, 2, &mut rng);
        let (new_sk_ids, new_pk_ids) = setup_new_group(2, 10, &mut rng);
        let beta = Scalar::rand(&mut rng);

        // Only 1 dealer when t_old=2
        let msg1 = reshare_deal(
            1,
            shares[0].1,
            old_sk_ids[&1],
            &new_pk_ids,
            2,
            beta,
            &mut rng,
        );

        let mut received = HashMap::new();
        received.insert(1, msg1);

        let result = reshare_receive(
            10,
            new_sk_ids[&10],
            &old_pk_ids,
            &received,
            beta,
            original_pk,
            &old_pk_shares,
            2,
        );

        match result {
            Err(ReshareError::InsufficientDealers { needed, got }) => {
                assert_eq!(needed, 2);
                assert_eq!(got, 1);
                println!("correctly detected {got} of {needed} needed dealers");
            }
            other => panic!("Expected InsufficientDealers, got {other:?}"),
        }
    }

    #[test]
    fn test_reshare_honest_succeeds() {
        let mut rng = ark_std::test_rng();
        let t_old = 2u32;
        let t_new = 2u32;

        let (secret, shares, old_sk_ids, old_pk_ids, old_pk_shares, original_pk) =
            setup_old_group(3, t_old, &mut rng);
        let (new_sk_ids, new_pk_ids) = setup_new_group(2, 10, &mut rng);
        let beta = Scalar::rand(&mut rng);

        // t_old old nodes deal honestly
        let mut received = HashMap::new();
        for &(id, share) in &shares[..t_old as usize] {
            let msg = reshare_deal(
                id,
                share,
                old_sk_ids[&id],
                &new_pk_ids,
                t_new,
                beta,
                &mut rng,
            );
            received.insert(id, msg);
        }

        // Each new node receives and computes their new share
        let mut new_outputs = HashMap::new();
        for (&new_id, &new_sk) in &new_sk_ids {
            let output = reshare_receive(
                new_id,
                new_sk,
                &old_pk_ids,
                &received,
                beta,
                original_pk,
                &old_pk_shares,
                t_old,
            )
            .expect("honest reshare must succeed");
            new_outputs.insert(new_id, output);
        }

        // Public key preserved
        for output in new_outputs.values() {
            assert_eq!(output.public_key, original_pk, "PK must be preserved");
        }

        // New shares reconstruct the original secret
        let new_shares: Vec<(NodeId, Scalar)> = new_outputs
            .iter()
            .map(|(&id, out)| (id, out.secret_share))
            .collect();
        let reconstructed = crate::shamir::lagrange_interpolate_at_zero(&new_shares);
        assert_eq!(reconstructed, secret, "reconstructed secret must match");

        // PK shares consistent with secret shares
        for (&new_id, output) in &new_outputs {
            let expected = (G1Affine::generator() * output.secret_share).into_affine();
            assert_eq!(
                output.public_key_shares[&new_id], expected,
                "PK share must match g^share for node {new_id}"
            );
        }

        println!("honest reshare preserved secret and PK across groups");
    }
}
