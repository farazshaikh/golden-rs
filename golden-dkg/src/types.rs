//! Core data types for the Golden DKG protocol.
//!
//! This module defines the message structures exchanged during protocol rounds,
//! the DKG output type, participant identity, session configuration, and type
//! aliases for the underlying BLS12-381 curve primitives.
//!
//! All public message types ([`Round0Msg`], [`ReshareMsg`], [`Ciphertext`],
//! [`SessionId`], [`SchnorrPoK`](crate::schnorr_pok::SchnorrPoK)) implement
//! [Borsh](https://borsh.io/) serialization for network transport when the
//! `borsh` feature is enabled.

use ark_bls12_381::{Fr, G1Affine, G1Projective};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::UniformRand;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::rand::Rng;
#[cfg(feature = "borsh")]
use borsh::{BorshDeserialize, BorshSerialize};
use std::collections::HashMap;
use std::io::{self, Read, Write};

/// Participant identifier (1-indexed).
///
/// Node IDs start at 1 and go up to `n` (the total number of participants).
/// They serve as the Shamir evaluation points: participant `i` receives the
/// share `f(i)`. The value 0 is reserved for the secret itself (`f(0) = sk`).
pub type NodeId = u32;

/// BLS12-381 scalar field element (`Fr`).
///
/// This is the prime-order field of the BLS12-381 curve, used for secret keys,
/// Shamir shares, polynomial coefficients, and eVRF pad values. The field order
/// is approximately 2^255.
pub type Scalar = Fr;

/// BLS12-381 G1 projective point.
///
/// Used for intermediate elliptic curve computations. Affine form ([`G1Affine`])
/// is preferred for storage and serialization; projective form is used during
/// multi-scalar multiplications and point additions for efficiency.
pub type G1 = G1Projective;

/// Session identifier for replay protection.
///
/// A random 32-byte nonce generated per DKG/refresh/reshare session.
/// All participants in a session must use the same `SessionId`.
/// Messages with mismatched session IDs are rejected.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SessionId(pub [u8; 32]);

impl SessionId {
    /// Generate a random session ID.
    pub fn random(rng: &mut impl ark_std::rand::Rng) -> Self {
        let mut bytes = [0u8; 32];
        rng.fill(&mut bytes[..]);
        Self(bytes)
    }
}

#[cfg(feature = "borsh")]
impl BorshSerialize for SessionId {
    fn serialize<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        BorshSerialize::serialize(&self.0, writer)
    }
}

#[cfg(feature = "borsh")]
impl BorshDeserialize for SessionId {
    fn deserialize_reader<R: Read>(reader: &mut R) -> io::Result<Self> {
        let bytes: [u8; 32] = BorshDeserialize::deserialize_reader(reader)?;
        Ok(Self(bytes))
    }
}

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

#[cfg(feature = "borsh")]
impl BorshSerialize for Ciphertext {
    fn serialize<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        let r_bytes = ark_to_bytes(&self.r_commitment);
        let s_bytes = ark_to_bytes(&self.encrypted_share);
        BorshSerialize::serialize(&r_bytes, writer)?;
        BorshSerialize::serialize(&s_bytes, writer)?;
        Ok(())
    }
}

#[cfg(feature = "borsh")]
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
    pub session_id: SessionId,
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

#[cfg(feature = "borsh")]
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

#[cfg(feature = "borsh")]
impl BorshDeserialize for Round0Msg {
    fn deserialize_reader<R: Read>(reader: &mut R) -> io::Result<Self> {
        let session_id: SessionId = BorshDeserialize::deserialize_reader(reader)?;
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
/// Sent by each old-group member during the [`crate::reshare`] protocol.
/// Structurally similar to [`Round0Msg`] but without eVRF proofs -- the reshare
/// protocol relies on VSS commitment verification against known public key shares
/// instead (see [`crate::reshare::verify_dealing`]).
///
/// The old member re-shares their secret key share `sk_i` using a fresh
/// degree-(t'-1) polynomial `g_i(x)` where `g_i(0) = sk_i`. The VSS commitment
/// allows verifiers to check `commitment[0] == PK_i` (the known public key share).
#[derive(Clone, Debug)]
pub struct ReshareMsg {
    /// Session ID for replay protection (must match across all reshare messages).
    pub session_id: SessionId,
    /// Sender node ID (old-group member who is re-sharing their share).
    pub from: NodeId,
    /// Random message `msg_i` used for eVRF pad derivation.
    pub random_msg: [u8; 32],
    /// Feldman VSS commitment to the dealing polynomial `g_i`:
    /// `[g^{g_i(0)}, g^{a_1}, ..., g^{a_{t'-1}}]` where `g_i(0) = sk_i`.
    pub vss_commitment: Vec<G1Affine>,
    /// Encrypted sub-shares for each new-group member, keyed by new-member [`NodeId`].
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

/// A participant's identity for the DKG protocol.
///
/// Each participant generates a `Participant` once (via [`Participant::new`]) and
/// retains it across DKG, refresh, and reshare sessions. The identity keypair
/// `(sk, pk)` is used for eVRF pad derivation (DH key exchange), and the Schnorr
/// proof of knowledge `pok` is required for PKI registration (Appendix F of the
/// Golden paper) to prevent rogue-key attacks.
///
/// # Example
///
/// ```rust,no_run
/// # use golden_dkg::types::Participant;
/// let mut rng = rand::rngs::OsRng;
/// let alice = Participant::new(1, &mut rng);
/// // alice.pk is the public key to share with other participants
/// // alice.pok should be verified by other participants on registration
/// ```
pub struct Participant {
    /// Unique participant identifier (1-indexed, serves as the Shamir evaluation point).
    pub id: NodeId,
    /// Identity secret key `sk_i^I` (zeroed from memory on drop via [`SecretScalar`]).
    pub sk: SecretScalar,
    /// Identity public key `PK_i^I = g^{sk_i^I}` (shared with all peers).
    pub pk: G1Affine,
    /// Schnorr proof of knowledge of `sk_i^I` (verified during PKI registration).
    pub pok: crate::schnorr_pok::SchnorrPoK,
}

impl Participant {
    /// Generate a new participant with a fresh identity keypair and Schnorr PoK.
    ///
    /// Samples a random secret key `sk <- Z_p`, computes `pk = g^sk`, and
    /// generates a Schnorr proof of knowledge. The caller should distribute
    /// `pk` and `pok` to all other participants for PKI registration.
    pub fn new(id: NodeId, rng: &mut impl Rng) -> Self {
        let sk_val = Scalar::rand(rng);
        let pk = (G1Affine::generator() * sk_val).into_affine();
        let pok = crate::schnorr_pok::prove(sk_val, pk, rng);
        Self {
            id,
            sk: SecretScalar::new(sk_val),
            pk,
            pok,
        }
    }
}

/// Configuration for a DKG or refresh session.
///
/// All participants in a session must agree on the same configuration values.
/// Mismatched configurations will cause verification failures.
///
/// # Choosing `n` and `t`
///
/// - `n` -- total number of participants in the group
/// - `t` -- minimum number of shares required to reconstruct the secret (threshold).
///   The Shamir polynomial has degree `t - 1`, so any `t` shares suffice for
///   reconstruction and `t - 1` shares reveal nothing.
///
/// Common choices: `(n=3, t=2)` for 2-of-3, `(n=5, t=3)` for 3-of-5.
pub struct DkgConfig {
    /// Total number of participants (`n` in the paper).
    pub n: u32,
    /// Threshold: minimum shares needed to reconstruct (`t` in the paper).
    ///
    /// Must satisfy `1 <= t <= n`. The degree of the Shamir polynomial is `t - 1`.
    pub t: u32,
    /// Public parameter `beta` for the leftover hash lemma (Appendix C of the paper).
    ///
    /// Used in the eVRF evaluation: `r = beta * r_1 + r_2`. Should be sampled
    /// uniformly at random and agreed upon by all participants before the session.
    pub beta: Scalar,
    /// Session identifier for replay protection.
    ///
    /// Must be unique per DKG/refresh/reshare session. Generate with
    /// [`SessionId::random`].
    pub session_id: SessionId,
}

/// Output of Round 0: the broadcast message and private local state.
///
/// Returned by [`crate::dkg::create_dealing`] and [`crate::refresh::create_dealing`].
/// The `message` field should be broadcast to all peers. The `private_share` field
/// **must be kept secret** -- it is this participant's own Shamir share `x_bar_{i,i} = f_i(i)`
/// (or the delta share in the refresh case).
///
/// Both `private_share` and `own_vss_commitment` are needed by
/// [`crate::dkg::complete`] / [`crate::refresh::complete`] and should be retained
/// until the protocol completes.
pub struct DkgDealing {
    /// The [`Round0Msg`] to **broadcast** to all participants.
    pub message: Round0Msg,
    /// The participant's own Shamir share `x_bar_{i,i}` (private, **never** sent).
    ///
    /// SECURITY: this is a secret value. In the DKG protocol it is `f_i(i)` where
    /// `f_i` is the participant's Shamir polynomial. In the refresh protocol it is
    /// the delta share. Must be passed to [`crate::dkg::complete`] or
    /// [`crate::refresh::complete`].
    pub private_share: Scalar,
    /// This participant's own Feldman VSS commitment (retained for Round 1 aggregation).
    pub own_vss_commitment: Vec<G1Affine>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_ff::UniformRand;

    #[cfg(feature = "borsh")]
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

    #[cfg(feature = "borsh")]
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
            session_id: SessionId([0u8; 32]),
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
