//! drand-compatible random beacon construction.
//!
//! Implements the message digest, hash-to-curve, and randomness derivation
//! functions matching the [drand](https://drand.love/) beacon wire format.
//!
//! Two modes are supported:
//! - **Chained**: `digest = SHA-256(prev_signature || round_be_8bytes)`
//! - **Unchained**: `digest = SHA-256(round_be_8bytes)`

use ark_bls12_381::{G1Affine, G2Affine, G2Projective};
use ark_ec::CurveGroup;
use ark_ff::UniformRand;
use ark_serialize::CanonicalSerialize;
use ark_std::rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use sha2::{Digest, Sha256};

use crate::threshold::types::{Beacon, BeaconMode, ThresholdSignature};

/// Compute the message digest for a given round.
///
/// - **Chained**: `SHA-256(prev_sig || round.to_be_bytes())`
/// - **Unchained** (prev_sig is `None`): `SHA-256(round.to_be_bytes())`
///
/// The big-endian encoding of the round number matches the drand specification.
pub fn digest_message(round: u64, prev_sig: Option<&[u8]>) -> Vec<u8> {
    let mut hasher = Sha256::new();
    if let Some(sig) = prev_sig {
        hasher.update(sig);
    }
    hasher.update(round.to_be_bytes());
    hasher.finalize().to_vec()
}

/// Hash an arbitrary byte digest to a BLS12-381 G2 curve point.
///
/// Uses SHA-256 → ChaCha8Rng → `G2Projective::rand` for deterministic
/// hash-to-curve.  This matches the approach used in the golden-dkg examples.
pub fn hash_to_g2(digest: &[u8]) -> G2Affine {
    let hash = Sha256::digest(digest);
    let mut seed = [0u8; 32];
    seed.copy_from_slice(&hash);
    let mut rng = ChaCha8Rng::from_seed(seed);
    G2Projective::rand(&mut rng).into_affine()
}

/// Derive 32 bytes of randomness from a threshold signature.
///
/// `randomness = SHA-256(signature_bytes)`
pub fn derive_randomness(signature: &[u8]) -> [u8; 32] {
    let hash = Sha256::digest(signature);
    let mut out = [0u8; 32];
    out.copy_from_slice(&hash);
    out
}

/// Serialize a G2 point to compressed bytes.
pub fn g2_to_bytes(point: &G2Affine) -> Vec<u8> {
    let mut buf = Vec::new();
    point.serialize_compressed(&mut buf).expect("G2 serialize");
    buf
}

impl Beacon {
    /// Construct a new beacon from a round number and threshold signature.
    ///
    /// For chained mode, `prev_sig` should be the previous round's signature
    /// bytes.  For unchained mode, pass `None`.
    pub fn new(round: u64, prev_sig: Option<Vec<u8>>, threshold_sig: &ThresholdSignature) -> Self {
        let sig_bytes = g2_to_bytes(&threshold_sig.signature);
        let randomness = derive_randomness(&sig_bytes);
        Self {
            round,
            previous_signature: prev_sig,
            signature: sig_bytes,
            randomness,
        }
    }

    /// Verify this beacon's signature against the group public key.
    ///
    /// Recomputes the message digest according to `mode`, hashes it to G2,
    /// and checks the BLS pairing equation.
    pub fn verify(&self, group_pk: &G1Affine, mode: BeaconMode) -> bool {
        let prev = match mode {
            BeaconMode::Chained => self.previous_signature.as_deref(),
            BeaconMode::Unchained => None,
        };
        let digest = digest_message(self.round, prev);
        let msg_hash = hash_to_g2(&digest);

        let sig: G2Affine = {
            use ark_serialize::CanonicalDeserialize;
            G2Affine::deserialize_compressed(&*self.signature).expect("deserialize G2 sig")
        };

        let threshold_sig = ThresholdSignature { signature: sig };
        crate::threshold::signing::verify(&msg_hash, &threshold_sig, group_pk)
    }
}
