//! Core data types for the Golden DKG protocol.
//!
//! Contains the message structures exchanged during protocol rounds, the
//! DKG output type, and type aliases for the underlying BLS12-381 curve
//! primitives. All public types implement Borsh serialization for
//! network transport.

use ark_bls12_381::{Fr, G1Affine, G1Projective};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use borsh::{BorshDeserialize, BorshSerialize};
use std::collections::HashMap;
use std::io::{self, Read, Write};

/// Participant identifier (1-indexed).
pub type NodeId = u32;
/// BLS12-381 scalar field element (Fr).
pub type Scalar = Fr;
/// BLS12-381 G1 projective point.
pub type G1 = G1Projective;

/// A scalar value that is zeroed from memory on drop.
///
/// SECURITY: Wraps `Fr` (BLS12-381 scalar field) for secret keys,
/// polynomial coefficients, and other sensitive values. The internal
/// representation is overwritten with zeros when the value goes out of scope.
pub struct SecretScalar(pub Scalar);

impl SecretScalar {
    /// Create a new secret scalar.
    pub fn new(val: Scalar) -> Self {
        Self(val)
    }

    /// Get the inner scalar value.
    pub fn inner(&self) -> Scalar {
        self.0
    }
}

impl std::ops::Deref for SecretScalar {
    type Target = Scalar;
    fn deref(&self) -> &Scalar {
        &self.0
    }
}

impl Drop for SecretScalar {
    fn drop(&mut self) {
        // Zero the scalar's internal representation (BigInt<4> = [u64; 4])
        // arkworks Fr is repr'd as Montgomery form in [u64; 4]
        unsafe {
            let ptr = &mut self.0 as *mut Scalar as *mut u8;
            let len = std::mem::size_of::<Scalar>();
            std::ptr::write_bytes(ptr, 0, len);
        }
    }
}

/// Helper: serialize an arkworks type to bytes via CanonicalSerialize (compressed).
fn ark_to_bytes<T: CanonicalSerialize>(val: &T) -> Vec<u8> {
    let mut buf = Vec::new();
    val.serialize_compressed(&mut buf)
        .expect("ark serialization failed");
    buf
}

/// Helper: deserialize an arkworks type from bytes via CanonicalDeserialize (compressed).
fn ark_from_bytes<T: CanonicalDeserialize>(bytes: &[u8]) -> T {
    T::deserialize_compressed(bytes).expect("ark deserialization failed")
}

/// A single encrypted share from node i to node j.
///
/// Per Round 0 line 7 of Figure 4 in the Golden paper (IACR 2025/1924):
/// > "sigma_{i,j} = (R_{i,j}, z_{i,j})"
///
/// where `R_{i,j} = g^{r_{i,j}}` is the eVRF pad commitment and
/// `z_{i,j} = r_{i,j} + x_bar_{i,j}` is the encrypted Shamir share.
#[derive(Clone, Debug)]
pub struct Ciphertext {
    /// `R_{i,j} = g^{r_{i,j}}` -- commitment to the eVRF pad.
    pub r_commitment: G1Affine,
    /// `z_{i,j} = r_{i,j} + share_{i,j}` -- encrypted Shamir share.
    pub encrypted_share: Scalar,
}

impl BorshSerialize for Ciphertext {
    fn serialize<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        let r_bytes = ark_to_bytes(&self.r_commitment);
        let s_bytes = ark_to_bytes(&self.encrypted_share);
        BorshSerialize::serialize(&r_bytes, writer)?;
        BorshSerialize::serialize(&s_bytes, writer)?;
        Ok(())
    }
}

impl BorshDeserialize for Ciphertext {
    fn deserialize_reader<R: Read>(reader: &mut R) -> io::Result<Self> {
        let r_bytes: Vec<u8> = BorshDeserialize::deserialize_reader(reader)?;
        let s_bytes: Vec<u8> = BorshDeserialize::deserialize_reader(reader)?;
        Ok(Ciphertext {
            r_commitment: ark_from_bytes(&r_bytes),
            encrypted_share: ark_from_bytes(&s_bytes),
        })
    }
}

/// Round 0 broadcast message from a single node.
///
/// Per Round 0 lines 9-10 of Figure 4 in the Golden paper (IACR 2025/1924):
/// > "bmsg_i = {(msg_i, C_bar_i, sigma_{i,j}, pi_{i,j})} for j != i"
///
/// Contains the VSS commitment, encrypted shares for all peers, and eVRF proofs
/// demonstrating correct pad derivation.
#[derive(Clone, Debug)]
pub struct Round0Msg {
    /// Session ID for replay protection (must match across all messages in a session).
    pub session_id: [u8; 32],
    /// Sender node ID.
    pub from: NodeId,
    /// Random message used for eVRF evaluation (`msg_i` in the paper).
    pub random_msg: [u8; 32],
    /// Feldman VSS commitment: `(A_{i,0}, ..., A_{i,t-1})` where `A_{i,k} = g^{a_k}`.
    pub vss_commitment: Vec<G1Affine>,
    /// Encrypted shares: one [`Ciphertext`] per peer (keyed by recipient [`NodeId`]).
    pub ciphertexts: HashMap<NodeId, Ciphertext>,
    /// eVRF proofs: one per peer, proving the pad was correctly derived (legacy per-peer).
    pub evrf_proofs: HashMap<NodeId, crate::zk_evrf::EVRFProof>,
    /// Batched eVRF proof covering all peers (Section 5.3 optimization).
    pub batch_evrf_proof: Option<crate::zk_evrf::EVRFProof>,
}

impl BorshSerialize for Round0Msg {
    fn serialize<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        BorshSerialize::serialize(&self.session_id, writer)?;
        BorshSerialize::serialize(&self.from, writer)?;
        BorshSerialize::serialize(&self.random_msg, writer)?;
        // vss_commitment: Vec<G1Affine> -- serialize each element as bytes
        let commitment_bytes: Vec<Vec<u8>> = self.vss_commitment.iter().map(ark_to_bytes).collect();
        BorshSerialize::serialize(&commitment_bytes, writer)?;
        // ciphertexts: HashMap<NodeId, Ciphertext> -- serialize as length + entries
        let ct_entries: Vec<(NodeId, &Ciphertext)> =
            self.ciphertexts.iter().map(|(&k, v)| (k, v)).collect();
        let len = ct_entries.len() as u32;
        BorshSerialize::serialize(&len, writer)?;
        for (node_id, ct) in ct_entries {
            BorshSerialize::serialize(&node_id, writer)?;
            BorshSerialize::serialize(ct, writer)?;
        }
        // evrf_proofs: HashMap<NodeId, EVRFProof> -- serialize as length + entries
        let proof_entries: Vec<(NodeId, &crate::zk_evrf::EVRFProof)> =
            self.evrf_proofs.iter().map(|(&k, v)| (k, v)).collect();
        let proof_len = proof_entries.len() as u32;
        BorshSerialize::serialize(&proof_len, writer)?;
        for (node_id, proof) in proof_entries {
            BorshSerialize::serialize(&node_id, writer)?;
            BorshSerialize::serialize(proof, writer)?;
        }
        // batch_evrf_proof: Option<EVRFProof> -- bool flag + optional proof
        let has_batch = self.batch_evrf_proof.is_some();
        BorshSerialize::serialize(&has_batch, writer)?;
        if let Some(ref proof) = self.batch_evrf_proof {
            BorshSerialize::serialize(proof, writer)?;
        }
        Ok(())
    }
}

impl BorshDeserialize for Round0Msg {
    fn deserialize_reader<R: Read>(reader: &mut R) -> io::Result<Self> {
        let session_id: [u8; 32] = BorshDeserialize::deserialize_reader(reader)?;
        let from: NodeId = BorshDeserialize::deserialize_reader(reader)?;
        let random_msg: [u8; 32] = BorshDeserialize::deserialize_reader(reader)?;
        let commitment_bytes: Vec<Vec<u8>> = BorshDeserialize::deserialize_reader(reader)?;
        let vss_commitment: Vec<G1Affine> =
            commitment_bytes.iter().map(|b| ark_from_bytes(b)).collect();
        let len: u32 = BorshDeserialize::deserialize_reader(reader)?;
        let mut ciphertexts = HashMap::new();
        for _ in 0..len {
            let node_id: NodeId = BorshDeserialize::deserialize_reader(reader)?;
            let ct: Ciphertext = BorshDeserialize::deserialize_reader(reader)?;
            ciphertexts.insert(node_id, ct);
        }
        let proof_len: u32 = BorshDeserialize::deserialize_reader(reader)?;
        let mut evrf_proofs = HashMap::new();
        for _ in 0..proof_len {
            let node_id: NodeId = BorshDeserialize::deserialize_reader(reader)?;
            let proof: crate::zk_evrf::EVRFProof = BorshDeserialize::deserialize_reader(reader)?;
            evrf_proofs.insert(node_id, proof);
        }
        // batch_evrf_proof: Option<EVRFProof>
        let has_batch: bool = BorshDeserialize::deserialize_reader(reader)?;
        let batch_evrf_proof = if has_batch {
            Some(BorshDeserialize::deserialize_reader(reader)?)
        } else {
            None
        };
        Ok(Round0Msg {
            session_id,
            from,
            random_msg,
            vss_commitment,
            ciphertexts,
            evrf_proofs,
            batch_evrf_proof,
        })
    }
}

/// Reshare broadcast message from an old-group member to the new group.
///
/// Structurally similar to [`Round0Msg`] but without eVRF proofs (the reshare
/// protocol relies on VSS commitment verification against known public key shares
/// instead).
#[derive(Clone, Debug)]
pub struct ReshareMsg {
    /// Session ID for replay protection.
    pub session_id: [u8; 32],
    /// Sender node ID (old-group member).
    pub from: NodeId,
    /// Random message used for eVRF pad derivation.
    pub random_msg: [u8; 32],
    /// Feldman VSS commitment to the dealing polynomial `g_i`.
    pub vss_commitment: Vec<G1Affine>,
    /// Encrypted sub-shares for each new-group member.
    pub ciphertexts: HashMap<NodeId, Ciphertext>,
}

/// Output of the DKG protocol for a single node.
///
/// Per Round 1 line 17 of Figure 4 in the Golden paper (IACR 2025/1924):
/// > "return (PK, {PK_j}, sk_i)"
///
/// Contains the shared public key, per-participant public key shares, and
/// this node's secret key share.
#[derive(Clone, Debug)]
pub struct DkgOutput {
    /// The shared public key `PK = g^{sk}`.
    pub public_key: G1Affine,
    /// Public key share for each participant: `PK_j = g^{sk_j}`.
    pub public_key_shares: HashMap<NodeId, G1Affine>,
    /// This node's secret key share `sk_i`.
    pub secret_share: Scalar,
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_ff::UniformRand;

    #[test]
    fn test_ciphertext_borsh_roundtrip() {
        let mut rng = ark_std::test_rng();
        let sk = Scalar::rand(&mut rng);
        let ct = Ciphertext {
            r_commitment: (G1Affine::generator() * sk).into_affine(),
            encrypted_share: Scalar::rand(&mut rng),
        };
        let bytes = borsh::to_vec(&ct).unwrap();
        let ct2: Ciphertext = borsh::from_slice(&bytes).unwrap();
        assert_eq!(ct.r_commitment, ct2.r_commitment);
        assert_eq!(ct.encrypted_share, ct2.encrypted_share);
    }

    #[test]
    fn test_round0msg_borsh_roundtrip() {
        let mut rng = ark_std::test_rng();

        let sk1 = Scalar::rand(&mut rng);
        let sk2 = Scalar::rand(&mut rng);

        let mut ciphertexts = HashMap::new();
        ciphertexts.insert(
            2u32,
            Ciphertext {
                r_commitment: (G1Affine::generator() * Scalar::rand(&mut rng)).into_affine(),
                encrypted_share: Scalar::rand(&mut rng),
            },
        );
        ciphertexts.insert(
            3u32,
            Ciphertext {
                r_commitment: (G1Affine::generator() * Scalar::rand(&mut rng)).into_affine(),
                encrypted_share: Scalar::rand(&mut rng),
            },
        );

        let msg = Round0Msg {
            session_id: [0u8; 32],
            from: 1,
            random_msg: [42u8; 32],
            vss_commitment: vec![
                (G1Affine::generator() * sk1).into_affine(),
                (G1Affine::generator() * sk2).into_affine(),
            ],
            ciphertexts,
            evrf_proofs: HashMap::new(),
            batch_evrf_proof: None,
        };

        let bytes = borsh::to_vec(&msg).unwrap();
        let msg2: Round0Msg = borsh::from_slice(&bytes).unwrap();

        assert_eq!(msg.from, msg2.from);
        assert_eq!(msg.random_msg, msg2.random_msg);
        assert_eq!(msg.vss_commitment.len(), msg2.vss_commitment.len());
        for (a, b) in msg.vss_commitment.iter().zip(msg2.vss_commitment.iter()) {
            assert_eq!(a, b);
        }
        assert_eq!(msg.ciphertexts.len(), msg2.ciphertexts.len());
        for (k, v) in &msg.ciphertexts {
            let v2 = &msg2.ciphertexts[k];
            assert_eq!(v.r_commitment, v2.r_commitment);
            assert_eq!(v.encrypted_share, v2.encrypted_share);
        }
    }
}
