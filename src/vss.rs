//! Feldman Verifiable Secret Sharing per Section 3.3 of the Golden paper.
//!
//! Per Section 3.2 of the Golden paper (IACR 2025/1924):
//! > "Commits to polynomial f by publishing C_k = g^{a_k} for each coefficient.
//! > Verification: g^{f(j)} == product_{k=0}^{t-1} C_k^{j^k}"
//!
//! Feldman VSS extends Shamir secret sharing with public commitments that allow
//! any party to verify the consistency of a received share without learning
//! the secret. The commitment vector `[C_0, ..., C_{t-1}]` is published
//! alongside the (encrypted) shares.

// SECURITY: Constant-time analysis
// - commit: Scalar mul of public coefficients -- constant-time but coefficients are secret.
//   arkworks scalar mul is constant-time regardless of scalar value.
// - verify_share: All operations on the share value use constant-time field/group arithmetic.
// Verdict: Constant-time.

use ark_bls12_381::{G1Affine, G1Projective};
use ark_ec::{AffineRepr, CurveGroup};

use crate::shamir::Polynomial;
use crate::types::{NodeId, Scalar};

/// Generate a Feldman VSS commitment for a polynomial.
///
/// Per Section 3.2 of the Golden paper (IACR 2025/1924):
/// > "C_k = g^{a_k} for each coefficient a_k"
///
/// Returns a vector of `g^{a_k}` for each coefficient `a_k` in the polynomial.
/// The first element `C_0 = g^{a_0}` is a commitment to the secret itself.
///
/// NOTE: Uses index-based push loop instead of `iter().map().collect()` for hax
/// extraction compatibility. See: formal_verification/Implementation.md
/// "Extraction-Friendly Rust"
pub fn commit(poly: &Polynomial) -> Vec<G1Affine> {
    let n = poly.coefficients.len();
    let mut commitments = Vec::with_capacity(n);
    for idx in 0..n {
        let coeff = poly.coefficients[idx];
        commitments.push((G1Affine::generator() * coeff).into_affine());
    }
    commitments
}

/// Verify that a share is consistent with a VSS commitment.
///
/// Per Section 3.2 of the Golden paper (IACR 2025/1924), checks the
/// verification equation:
/// > "g^{f(j)} == product_{k=0}^{t-1} C_k^{j^k}"
///
/// Returns `true` if `g^{share}` equals the product of `C_k^{index^k}` over
/// all commitment elements, confirming the share lies on the committed polynomial.
///
/// NOTE: Uses index-based loop instead of `for c_k in commitment` for hax
/// extraction compatibility. See: formal_verification/Implementation.md
/// "Extraction-Friendly Rust"
pub fn verify_share(commitment: &[G1Affine], index: NodeId, share: Scalar) -> bool {
    let x = Scalar::from(index as u64);
    let mut expected = G1Projective::default();
    let mut x_pow = Scalar::from(1u64);
    let n = commitment.len();
    for idx in 0..n {
        expected += commitment[idx] * x_pow;
        x_pow *= x;
    }
    let actual = G1Affine::generator() * share;
    expected == actual
}

/// Compute the expected public key share for a given index from the VSS commitment.
///
/// Per Round 1 line 8 of Figure 4 in the Golden paper (IACR 2025/1924):
/// > "X_{j,k} = product_{l=0}^{t-1} A_{j,l}^{k^l}"
///
/// Returns `g^{f(index)} = product_{k=0}^{t-1} C_k^{index^k}`, which is the
/// commitment to the share value at `index` without revealing the share itself.
///
/// NOTE: Uses index-based loop for hax extraction compatibility.
pub fn expected_share_commitment(commitment: &[G1Affine], index: NodeId) -> G1Affine {
    let x = Scalar::from(index as u64);
    let mut result = G1Projective::default();
    let mut x_pow = Scalar::from(1u64);
    let n = commitment.len();
    for idx in 0..n {
        result += commitment[idx] * x_pow;
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
