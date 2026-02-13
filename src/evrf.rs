use ark_bls12_381::{Fr, G1Affine};
use ark_ec::{AdditiveGroup, AffineRepr, CurveGroup};
use ark_ff::{BigInteger, PrimeField};
use sha2::{Digest, Sha256};

use crate::types::Scalar;

/// Extract the x-coordinate of an affine point as a scalar in Fr.
///
/// Converts the Fq x-coordinate (381 bits) to bytes, then reduces mod r
/// into the scalar field. Returns Fr::zero() for the identity point.
fn extract_x_as_scalar(point: G1Affine) -> Scalar {
    if point.infinity {
        return Scalar::ZERO;
    }
    let bytes = point.x.into_bigint().to_bytes_le();
    Fr::from_le_bytes_mod_order(&bytes)
}

/// Prototype hash-to-curve using hash-and-multiply.
///
/// 1. SHA-256(domain || msg) -> 32 bytes
/// 2. Interpret as scalar via from_le_bytes_mod_order
/// 3. Multiply the G1 generator by that scalar
///
/// NOT standards-compliant (no constant-time, no try-and-increment),
/// but sufficient for a prototype.
fn hash_to_curve(domain: &[u8], msg: &[u8]) -> G1Affine {
    let mut hasher = Sha256::new();
    hasher.update(domain);
    hasher.update(msg);
    let hash_bytes = hasher.finalize();

    let scalar = Fr::from_le_bytes_mod_order(&hash_bytes);
    (G1Affine::generator() * scalar).into_affine()
}

/// Derive the eVRF pad that both parties can independently compute.
///
/// Party i calls: `derive_pad(sk_i, PK_j, msg, beta)`
/// Party j calls: `derive_pad(sk_j, PK_i, msg, beta)`
/// Both get the same `(r, R)` output thanks to DH symmetry:
///   `PK_j * sk_i == g^{sk_j * sk_i} == PK_i * sk_j`
///
/// Steps:
///   1. DH shared secret S = peer_pk * sk
///   2. k = int(S.x) mod r
///   3. H1 = hash_to_curve("golden-evrf-h1", msg), H2 = hash_to_curve("golden-evrf-h2", msg)
///   4. T1 = H1^k, T2 = H2^k
///   5. r1 = int(T1.x) mod r, r2 = int(T2.x) mod r
///   6. r = beta * r1 + r2  (leftover hash lemma extraction)
///   7. R = g^r
pub fn derive_pad(sk: Scalar, peer_pk: G1Affine, msg: &[u8], beta: Scalar) -> (Scalar, G1Affine) {
    // 1. DH shared secret
    let s = (peer_pk * sk).into_affine();

    // 2. Extract x-coordinate as scalar
    let k = extract_x_as_scalar(s);

    // 3. Hash to curve with two different domain separators
    let h1 = hash_to_curve(b"golden-evrf-h1", msg);
    let h2 = hash_to_curve(b"golden-evrf-h2", msg);

    // 4. T1 = H1(msg)^k, T2 = H2(msg)^k
    let t1 = (h1 * k).into_affine();
    let t2 = (h2 * k).into_affine();

    // 5. r1 = int(T1.x) mod r, r2 = int(T2.x) mod r
    let r1 = extract_x_as_scalar(t1);
    let r2 = extract_x_as_scalar(t2);

    // 6. r = beta * r1 + r2 (leftover hash lemma extraction)
    let r = beta * r1 + r2;

    // 7. R = g^r
    let r_commitment = (G1Affine::generator() * r).into_affine();

    (r, r_commitment)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ec::AffineRepr;
    use ark_ff::UniformRand;

    #[test]
    fn test_symmetric_pad_derivation() {
        let mut rng = ark_std::test_rng();

        // Party A keypair
        let sk_a = Scalar::rand(&mut rng);
        let pk_a = (G1Affine::generator() * sk_a).into_affine();

        // Party B keypair
        let sk_b = Scalar::rand(&mut rng);
        let pk_b = (G1Affine::generator() * sk_b).into_affine();

        let msg = b"test-message-round-1";
        let beta = Scalar::rand(&mut rng);

        // A derives pad using B's public key
        let (r_a, big_r_a) = derive_pad(sk_a, pk_b, msg, beta);

        // B derives pad using A's public key
        let (r_b, big_r_b) = derive_pad(sk_b, pk_a, msg, beta);

        // Must be identical (DH symmetry)
        assert_eq!(r_a, r_b, "Pads must match due to DH symmetry");
        assert_eq!(big_r_a, big_r_b, "Commitments must match");
    }

    #[test]
    fn test_different_messages_different_pads() {
        let mut rng = ark_std::test_rng();
        let sk_a = Scalar::rand(&mut rng);
        let _pk_a = (G1Affine::generator() * sk_a).into_affine();
        let sk_b = Scalar::rand(&mut rng);
        let pk_b = (G1Affine::generator() * sk_b).into_affine();
        let beta = Scalar::rand(&mut rng);

        let (r1, _) = derive_pad(sk_a, pk_b, b"msg-1", beta);
        let (r2, _) = derive_pad(sk_a, pk_b, b"msg-2", beta);

        assert_ne!(r1, r2, "Different messages should produce different pads");
    }

    #[test]
    fn test_different_peers_different_pads() {
        let mut rng = ark_std::test_rng();
        let sk_a = Scalar::rand(&mut rng);
        let sk_b = Scalar::rand(&mut rng);
        let sk_c = Scalar::rand(&mut rng);
        let pk_b = (G1Affine::generator() * sk_b).into_affine();
        let pk_c = (G1Affine::generator() * sk_c).into_affine();
        let beta = Scalar::rand(&mut rng);

        let (r1, _) = derive_pad(sk_a, pk_b, b"msg", beta);
        let (r2, _) = derive_pad(sk_a, pk_c, b"msg", beta);

        assert_ne!(r1, r2, "Different peers should produce different pads");
    }
}
