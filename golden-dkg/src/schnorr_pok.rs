//! Schnorr Proof of Knowledge for PKI registration.
//!
//! Implements the Schnorr Sigma protocol (made non-interactive via the Fiat-Shamir
//! heuristic) for proving knowledge of a discrete logarithm. This is used during
//! PKI registration as specified in Appendix F of the Golden paper
//! (Bünz, Choi, Komlo, [IACR 2025/1924](https://eprint.iacr.org/2025/1924)):
//!
//! > "F_pki: KeyGen, Register (with proof of knowledge), Query.
//! > Must prove knowledge of sk_i^I when registering."
//!
//! Each DKG participant must register their identity public key with the PKI
//! and prove they know the corresponding secret key. This prevents **rogue-key
//! attacks** where an adversary registers a crafted public key (e.g., `PK_adv = g^x / PK_honest`)
//! to cancel out honest contributions.
//!
//! # Protocol
//!
//! The Sigma protocol for relation `{(PK; sk) : PK = g^sk}`:
//! 1. Prover samples nonce `k <- Z_p`, sends commitment `R = g^k`
//! 2. Challenge `c = H("golden-schnorr-pok" || g || PK || R)` (Fiat-Shamir)
//! 3. Prover sends response `s = k + c * sk`
//! 4. Verifier checks `g^s == R + c * PK`

// SECURITY: Constant-time analysis
// - prove: nonce sampling (OsRng), scalar mul (constant-time), field add/mul (constant-time).
// - verify: scalar mul and field ops are constant-time. The final equality check
//   on affine points compares field elements, which is constant-time in arkworks.
// - compute_challenge: SHA-256 is constant-time for fixed-length inputs.
// Verdict: All operations are constant-time.

use ark_bls12_381::{Fr, G1Affine};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::rand::Rng;
use ark_std::UniformRand;
#[cfg(feature = "borsh")]
use borsh::{BorshDeserialize, BorshSerialize};
use sha2::{Digest, Sha256};

use crate::types::{Scalar, SecretScalar};

/// A Schnorr proof of knowledge of discrete log: proves knowledge of `sk` such
/// that `PK = g^sk`.
///
/// Per Appendix F of the Golden paper (IACR 2025/1924), this proof is required
/// when registering an identity public key with the PKI functionality `F_pki`.
/// The proof consists of a commitment `R = g^nonce` and a response
/// `s = nonce + challenge * sk` using the Fiat-Shamir heuristic.
///
/// Generate with [`prove`], verify with [`verify`]. The proof is bound to a
/// specific public key via the Fiat-Shamir challenge -- it cannot be reused for
/// a different key.
#[derive(Clone, Debug)]
pub struct SchnorrPoK {
    /// Commitment `R = g^k` where `k` is the prover's random nonce.
    pub commitment: G1Affine,
    /// Response `s = k + c * sk` where `c = H(g || PK || R)` is the Fiat-Shamir challenge.
    pub response: Scalar,
}

/// Generate a Schnorr proof of knowledge.
///
/// Proves: "I know `sk` such that `pk = g^sk`" using the Sigma protocol
/// made non-interactive via the Fiat-Shamir transform:
///   1. Sample nonce `k <- Z_p`
///   2. `R = g^k`
///   3. `c = H(g || pk || R)` (Fiat-Shamir challenge)
///   4. `s = k + c * sk`
///   5. Output `(R, s)`
pub fn prove(sk: Scalar, pk: G1Affine, rng: &mut impl Rng) -> SchnorrPoK {
    // 1. Sample random nonce
    let nonce = SecretScalar::new(Scalar::rand(rng));

    // 2. R = g^nonce
    let commitment = (G1Affine::generator() * nonce.inner()).into_affine();

    // 3. Fiat-Shamir challenge: c = H(g || pk || R)
    let challenge = compute_challenge(pk, commitment);

    // 4. s = nonce + c * sk
    let response = nonce.inner() + challenge * sk;

    SchnorrPoK {
        commitment,
        response,
    }
}

/// Verify a Schnorr proof of knowledge.
///
/// Checks the verification equation: `g^s == R + c * PK`
/// where `c = H(g || pk || R)`.
///
/// This ensures the prover knows `sk` such that `PK = g^sk` without
/// revealing `sk`.
pub fn verify(pk: G1Affine, proof: &SchnorrPoK) -> bool {
    // Recompute challenge
    let challenge = compute_challenge(pk, proof.commitment);

    // Check: g^s == R + c * PK
    let lhs = (G1Affine::generator() * proof.response).into_affine();
    let rhs = (proof.commitment.into_group() + pk * challenge).into_affine();

    lhs == rhs
}

/// Compute the Fiat-Shamir challenge: `c = H(g || pk || R) mod r`.
///
/// Uses SHA-256 with domain separator `"golden-schnorr-pok"` to hash the
/// generator, public key, and commitment into a challenge scalar. This
/// converts the interactive Sigma protocol into a non-interactive proof.
fn compute_challenge(pk: G1Affine, commitment: G1Affine) -> Scalar {
    let mut hasher = Sha256::new();
    hasher.update(b"golden-schnorr-pok");

    // Serialize generator
    let mut buf = Vec::new();
    G1Affine::generator()
        .serialize_compressed(&mut buf)
        .expect("serialize failed");
    hasher.update(&buf);

    // Serialize pk
    buf.clear();
    pk.serialize_compressed(&mut buf).expect("serialize failed");
    hasher.update(&buf);

    // Serialize commitment R
    buf.clear();
    commitment
        .serialize_compressed(&mut buf)
        .expect("serialize failed");
    hasher.update(&buf);

    let hash = hasher.finalize();
    Fr::from_le_bytes_mod_order(&hash)
}

#[cfg(feature = "borsh")]
impl BorshSerialize for SchnorrPoK {
    fn serialize<W: std::io::Write>(&self, writer: &mut W) -> std::io::Result<()> {
        let mut buf = Vec::new();
        self.commitment
            .serialize_compressed(&mut buf)
            .map_err(|e| std::io::Error::other(e.to_string()))?;
        BorshSerialize::serialize(&buf, writer)?;
        buf.clear();
        self.response
            .serialize_compressed(&mut buf)
            .map_err(|e| std::io::Error::other(e.to_string()))?;
        BorshSerialize::serialize(&buf, writer)?;
        Ok(())
    }
}

#[cfg(feature = "borsh")]
impl BorshDeserialize for SchnorrPoK {
    fn deserialize_reader<R: std::io::Read>(reader: &mut R) -> std::io::Result<Self> {
        let buf: Vec<u8> = BorshDeserialize::deserialize_reader(reader)?;
        let commitment = G1Affine::deserialize_compressed(&buf[..])
            .map_err(|e| std::io::Error::other(e.to_string()))?;
        let buf: Vec<u8> = BorshDeserialize::deserialize_reader(reader)?;
        let response = Fr::deserialize_compressed(&buf[..])
            .map_err(|e| std::io::Error::other(e.to_string()))?;
        Ok(SchnorrPoK {
            commitment,
            response,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::UniformRand;

    #[test]
    fn test_schnorr_pok_valid() {
        let mut rng = ark_std::test_rng();
        let sk = Scalar::rand(&mut rng);
        let pk = (G1Affine::generator() * sk).into_affine();

        let proof = prove(sk, pk, &mut rng);
        assert!(verify(pk, &proof), "Valid proof should verify");
    }

    #[test]
    fn test_schnorr_pok_wrong_sk() {
        let mut rng = ark_std::test_rng();
        let sk = Scalar::rand(&mut rng);
        let pk = (G1Affine::generator() * sk).into_affine();

        // Prove with wrong sk
        let wrong_sk = Scalar::rand(&mut rng);
        let bad_proof = prove(wrong_sk, pk, &mut rng);
        assert!(
            !verify(pk, &bad_proof),
            "Proof with wrong sk should NOT verify"
        );
    }

    #[test]
    fn test_schnorr_pok_wrong_pk() {
        let mut rng = ark_std::test_rng();
        let sk = Scalar::rand(&mut rng);
        let pk = (G1Affine::generator() * sk).into_affine();

        let proof = prove(sk, pk, &mut rng);

        // Verify against wrong pk
        let wrong_pk = (G1Affine::generator() * Scalar::rand(&mut rng)).into_affine();
        assert!(
            !verify(wrong_pk, &proof),
            "Proof should NOT verify against wrong PK"
        );
    }

    #[test]
    fn test_schnorr_pok_tampered_commitment() {
        let mut rng = ark_std::test_rng();
        let sk = Scalar::rand(&mut rng);
        let pk = (G1Affine::generator() * sk).into_affine();

        let mut proof = prove(sk, pk, &mut rng);
        // Tamper with commitment
        proof.commitment = (G1Affine::generator() * Scalar::rand(&mut rng)).into_affine();
        assert!(!verify(pk, &proof), "Tampered proof should NOT verify");
    }

    #[test]
    fn test_schnorr_pok_tampered_response() {
        let mut rng = ark_std::test_rng();
        let sk = Scalar::rand(&mut rng);
        let pk = (G1Affine::generator() * sk).into_affine();

        let mut proof = prove(sk, pk, &mut rng);
        // Tamper with response
        proof.response += Scalar::from(1u64);
        assert!(!verify(pk, &proof), "Tampered response should NOT verify");
    }

    #[cfg(feature = "borsh")]
    #[test]
    fn test_schnorr_pok_borsh_roundtrip() {
        let mut rng = ark_std::test_rng();
        let sk = Scalar::rand(&mut rng);
        let pk = (G1Affine::generator() * sk).into_affine();

        let proof = prove(sk, pk, &mut rng);
        let bytes = borsh::to_vec(&proof).unwrap();
        let proof2: SchnorrPoK = borsh::from_slice(&bytes).unwrap();

        assert_eq!(proof.commitment, proof2.commitment);
        assert_eq!(proof.response, proof2.response);
        assert!(verify(pk, &proof2), "Deserialized proof should verify");
    }
}
