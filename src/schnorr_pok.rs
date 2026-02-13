use ark_bls12_381::{Fr, G1Affine};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::rand::Rng;
use ark_std::UniformRand;
use borsh::{BorshDeserialize, BorshSerialize};
use sha2::{Digest, Sha256};

use crate::types::Scalar;

/// A Schnorr proof of knowledge of discrete log: proves knowledge of sk such that PK = g^sk.
/// Per Golden paper Appendix F (F_pki functionality).
#[derive(Clone, Debug)]
pub struct SchnorrPoK {
    /// Commitment: R = g^nonce
    pub commitment: G1Affine,
    /// Response: s = nonce + challenge * sk
    pub response: Scalar,
}

/// Generate a Schnorr proof of knowledge.
///
/// Proves: "I know sk such that pk = g^sk"
/// Protocol (Fiat-Shamir):
///   1. Sample nonce k <- Zp
///   2. R = g^k
///   3. c = H(g || pk || R)    (Fiat-Shamir challenge)
///   4. s = k + c * sk
///   5. Output (R, s)
pub fn prove(sk: Scalar, pk: G1Affine, rng: &mut impl Rng) -> SchnorrPoK {
    // 1. Sample random nonce
    let nonce = Scalar::rand(rng);

    // 2. R = g^nonce
    let commitment = (G1Affine::generator() * nonce).into_affine();

    // 3. Fiat-Shamir challenge: c = H(g || pk || R)
    let challenge = compute_challenge(pk, commitment);

    // 4. s = nonce + c * sk
    let response = nonce + challenge * sk;

    SchnorrPoK {
        commitment,
        response,
    }
}

/// Verify a Schnorr proof of knowledge.
///
/// Checks: g^s == R + c * PK
/// Where c = H(g || pk || R)
pub fn verify(pk: G1Affine, proof: &SchnorrPoK) -> bool {
    // Recompute challenge
    let challenge = compute_challenge(pk, proof.commitment);

    // Check: g^s == R + c * PK
    let lhs = (G1Affine::generator() * proof.response).into_affine();
    let rhs = (proof.commitment.into_group() + pk * challenge).into_affine();

    lhs == rhs
}

/// Compute Fiat-Shamir challenge: c = H(g || pk || R) mod r
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
