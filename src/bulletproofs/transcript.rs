use ark_bls12_381::{Fr, G1Affine};
use ark_ff::PrimeField;
use ark_serialize::CanonicalSerialize;
use sha2::{Digest, Sha256};

/// Fiat-Shamir transcript for Bulletproofs.
/// Absorbs messages and squeezes challenges deterministically via SHA-256.
pub struct Transcript {
    hasher: Sha256,
}

impl Transcript {
    /// Create a new transcript with a domain separator label.
    pub fn new(label: &[u8]) -> Self {
        let mut hasher = Sha256::new();
        hasher.update(b"golden-bulletproofs-transcript");
        hasher.update(label);
        Self { hasher }
    }

    /// Append a scalar to the transcript.
    pub fn append_scalar(&mut self, label: &[u8], scalar: &Fr) {
        self.hasher.update(label);
        let mut buf = Vec::new();
        scalar
            .serialize_compressed(&mut buf)
            .expect("serialize failed");
        self.hasher.update(&buf);
    }

    /// Append a group element to the transcript.
    pub fn append_point(&mut self, label: &[u8], point: &G1Affine) {
        self.hasher.update(label);
        let mut buf = Vec::new();
        point
            .serialize_compressed(&mut buf)
            .expect("serialize failed");
        self.hasher.update(&buf);
    }

    /// Squeeze a challenge scalar from the transcript.
    /// Finalizes current state, produces a scalar, and reseeds.
    pub fn challenge_scalar(&mut self, label: &[u8]) -> Fr {
        self.hasher.update(label);
        let hash = self.hasher.finalize_reset();
        // Reseed the hasher with the hash output for domain separation
        self.hasher.update(b"golden-bulletproofs-transcript");
        self.hasher.update(hash);
        Fr::from_le_bytes_mod_order(&hash)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_transcript_deterministic() {
        let mut t1 = Transcript::new(b"test");
        let mut t2 = Transcript::new(b"test");

        let s = Fr::from(42u64);
        t1.append_scalar(b"val", &s);
        t2.append_scalar(b"val", &s);

        let c1 = t1.challenge_scalar(b"challenge");
        let c2 = t2.challenge_scalar(b"challenge");
        assert_eq!(c1, c2, "Same inputs must produce same challenge");
    }

    #[test]
    fn test_transcript_different_inputs() {
        let mut t1 = Transcript::new(b"test");
        let mut t2 = Transcript::new(b"test");

        t1.append_scalar(b"val", &Fr::from(1u64));
        t2.append_scalar(b"val", &Fr::from(2u64));

        let c1 = t1.challenge_scalar(b"challenge");
        let c2 = t2.challenge_scalar(b"challenge");
        assert_ne!(c1, c2, "Different inputs must produce different challenges");
    }
}
