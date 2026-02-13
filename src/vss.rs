use ark_bls12_381::{G1Affine, G1Projective};
use ark_ec::{AffineRepr, CurveGroup};

use crate::shamir::Polynomial;
use crate::types::{NodeId, Scalar};

/// Generate Feldman VSS commitment for a polynomial.
/// Returns a vector of g^{a_k} for each coefficient a_k.
pub fn commit(poly: &Polynomial) -> Vec<G1Affine> {
    poly.coefficients
        .iter()
        .map(|coeff| (G1Affine::generator() * coeff).into_affine())
        .collect()
}

/// Verify that a share is consistent with a VSS commitment.
/// Checks: g^{share} == product_{k=0}^{t-1} C_k^{j^k}
pub fn verify_share(commitment: &[G1Affine], index: NodeId, share: Scalar) -> bool {
    let x = Scalar::from(index as u64);
    let mut expected = G1Projective::default();
    let mut x_pow = Scalar::from(1u64);
    for c_k in commitment {
        expected += *c_k * x_pow;
        x_pow *= x;
    }
    let actual = G1Affine::generator() * share;
    expected == actual
}

/// Compute the expected public key share for a given index from the VSS commitment.
/// Returns g^{f(index)} = product_{k=0}^{t-1} C_k^{index^k}
pub fn expected_share_commitment(commitment: &[G1Affine], index: NodeId) -> G1Affine {
    let x = Scalar::from(index as u64);
    let mut result = G1Projective::default();
    let mut x_pow = Scalar::from(1u64);
    for c_k in commitment {
        result += *c_k * x_pow;
        x_pow *= x;
    }
    result.into_affine()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::shamir::{generate_shares, Polynomial};
    use ark_ff::UniformRand;

    #[test]
    fn test_commit_and_verify() {
        let mut rng = ark_std::test_rng();
        let secret = Scalar::rand(&mut rng);
        let t = 3usize;
        let n = 5u32;
        let poly = Polynomial::new_random(secret, t - 1, &mut rng);
        let commitment = commit(&poly);
        assert_eq!(commitment.len(), t);
        let expected_pk = (G1Affine::generator() * secret).into_affine();
        assert_eq!(commitment[0], expected_pk);
        let shares = generate_shares(&poly, n);
        for (id, share) in &shares {
            assert!(
                verify_share(&commitment, *id, *share),
                "Share for node {} should verify",
                id
            );
        }
    }

    #[test]
    fn test_reject_tampered_share() {
        let mut rng = ark_std::test_rng();
        let secret = Scalar::rand(&mut rng);
        let poly = Polynomial::new_random(secret, 2, &mut rng);
        let commitment = commit(&poly);
        let shares = generate_shares(&poly, 5);
        let (id, share) = shares[0];
        let tampered = share + Scalar::from(1u64);
        assert!(
            !verify_share(&commitment, id, tampered),
            "Tampered share should NOT verify"
        );
    }

    #[test]
    fn test_expected_share_commitment() {
        let mut rng = ark_std::test_rng();
        let secret = Scalar::rand(&mut rng);
        let poly = Polynomial::new_random(secret, 2, &mut rng);
        let commitment = commit(&poly);
        let shares = generate_shares(&poly, 5);
        for (id, share) in &shares {
            let expected = expected_share_commitment(&commitment, *id);
            let actual = (G1Affine::generator() * share).into_affine();
            assert_eq!(
                expected, actual,
                "Expected commitment should match g^share for node {}",
                id
            );
        }
    }
}
