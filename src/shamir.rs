//! Shamir Secret Sharing per Section 3.3 of the Golden paper.
//!
//! Per Section 3.3 of the Golden paper (IACR 2025/1924):
//! > "A polynomial f(x) = a_0 + a_1*x + ... + a_{t-1}*x^{t-1} of degree t-1
//! > can be interpolated by t points."
//!
//! This module implements polynomial-based secret sharing where a secret `a_0`
//! is embedded as the constant term of a random polynomial, and shares are
//! evaluations of that polynomial at distinct nonzero points.

// SECURITY: Constant-time analysis
// - Polynomial::evaluate: Horner's method uses ark-ff mul/add which are constant-time.
// - lagrange_interpolate_at_zero: Uses ark-ff mul/add/inverse which are constant-time.
//   The loop structure is data-independent (iterates over all shares).
// - generate_shares: Evaluates polynomial at public indices -- no secret-dependent branching.
// Verdict: All operations on secret values use constant-time field arithmetic.

use ark_ff::{Field, UniformRand};
use ark_std::rand::Rng;

use crate::types::{NodeId, Scalar};

/// A polynomial over the scalar field, used for Shamir secret sharing.
///
/// Per Section 3.3 of the Golden paper (IACR 2025/1924), Share(x, n, t):
/// > "Define polynomial f(Z) = x + a_1*Z + ... + a_{t-1}*Z^{t-1} with random
/// > a_1,...,a_{t-1}"
///
/// `coefficients[0]` is the secret (constant term `a_0`), and subsequent
/// coefficients are the random blinding terms.
pub struct Polynomial {
    /// Polynomial coefficients in ascending degree order: `[a_0, a_1, ..., a_{t-1}]`.
    pub coefficients: Vec<Scalar>,
}

impl Polynomial {
    /// Create a random polynomial of the given degree whose constant term is `secret`.
    ///
    /// Per Section 3.3 of the Golden paper (IACR 2025/1924):
    /// > "Define polynomial f(Z) = x + a_1*Z + ... + a_{t-1}*Z^{t-1} with random
    /// > a_1,...,a_{t-1}"
    ///
    /// For threshold `t`, use `degree = t - 1`. The constant term is fixed to
    /// `secret`, and the remaining `degree` coefficients are sampled uniformly
    /// at random from Z_p.
    pub fn new_random(secret: Scalar, degree: usize, rng: &mut impl Rng) -> Self {
        let mut coefficients = Vec::with_capacity(degree + 1);
        coefficients.push(secret);
        for _ in 0..degree {
            coefficients.push(Scalar::rand(rng));
        }
        Self { coefficients }
    }

    /// Evaluate the polynomial at `x` using Horner's method.
    ///
    /// Computes `f(x) = a_0 + x*(a_1 + x*(a_2 + ... + x*a_n))` by walking
    /// coefficients from highest degree down to the constant term. This is
    /// numerically stable and requires only `degree` multiplications.
    ///
    /// NOTE: Uses index-based access instead of `iter().rev()` for hax
    /// extraction compatibility. Iterator adapters (Rev, Map) generate
    /// dependent closure types in F* that fail typeclass resolution.
    /// Index-based loops extract as simple `fold_range` with no closures.
    /// See: formal_verification/Implementation.md "Extraction-Friendly Rust"
    pub fn evaluate(&self, x: Scalar) -> Scalar {
        // Horner's: a_0 + x*(a_1 + x*(a_2 + ... + x*a_n))
        // Walk coefficients from highest degree down via index.
        let mut result = Scalar::from(0u64);
        let n = self.coefficients.len();
        for idx in 0..n {
            result = result * x + self.coefficients[n - 1 - idx];
        }
        result
    }

    /// Return the degree of the polynomial.
    pub fn degree(&self) -> usize {
        self.coefficients.len() - 1
    }
}

/// Generate `n` shares by evaluating the polynomial at x = 1, 2, ..., n.
///
/// Per Section 3.3 of the Golden paper (IACR 2025/1924):
/// > "Each share x_bar_i = f(i) for i in [n]"
///
/// Returns `(node_id, share_value)` pairs with `node_id` in `1..=n`.
/// The evaluation points are the natural numbers 1 through n, which ensures
/// they are distinct and nonzero (as required for Lagrange interpolation).
///
/// NOTE: Uses explicit push loop instead of `map().collect()` for hax
/// extraction compatibility. See: formal_verification/Implementation.md
/// "Extraction-Friendly Rust"
pub fn generate_shares(poly: &Polynomial, n: u32) -> Vec<(NodeId, Scalar)> {
    let mut shares = Vec::with_capacity(n as usize);
    // Use exclusive range 0..n (extracts as fold_range) instead of
    // inclusive range 1..=n (extracts as f_fold over RangeInclusive with FnOnce).
    for idx in 0..n {
        let i = idx + 1;
        let x = Scalar::from(i as u64);
        shares.push((i, poly.evaluate(x)));
    }
    shares
}

/// Reconstruct `f(0)` (the secret) from a set of shares using Lagrange interpolation.
///
/// Per Section 3.3 of the Golden paper (IACR 2025/1924), Recover(t, {(i, x_bar_i)}):
/// > "x = sum_{i in C} x_bar_i * L_i(0)
/// > where L_i(0) = product_{j in C, j != i} j / (j - i)"
///
/// Each share is `(node_id, y_i)` where `x_i = Scalar::from(node_id)`.
/// Requires at least `t` shares for a degree-`(t-1)` polynomial.
///
pub fn lagrange_interpolate_at_zero(shares: &[(NodeId, Scalar)]) -> Scalar {
    let mut result = Scalar::from(0u64);

    // NOTE: Uses iter().enumerate() pattern which hax extracts as
    // fold_enumerated_slice (no FnOnce needed). Direct index shares[i]
    // generates .[ ] notation requiring Index typeclass instances.
    // See: formal_verification/Implementation.md "Extraction-Friendly Rust"
    for (i, &(xi_id, yi)) in shares.iter().enumerate() {
        let xi = Scalar::from(xi_id as u64);

        // Lagrange basis polynomial evaluated at 0:
        //   L_i(0) = product_{j != i} (0 - x_j) / (x_i - x_j)
        //          = product_{j != i} x_j / (x_j - x_i)
        let mut li = Scalar::from(1u64);
        for (j, &(xj_id, _)) in shares.iter().enumerate() {
            if i == j {
                continue;
            }
            let xj = Scalar::from(xj_id as u64);
            // L_i(0) *= x_j / (x_j - x_i)
            li *= xj * (xj - xi).inverse().expect("duplicate x values in shares");
        }

        result += yi * li;
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::UniformRand;

    #[test]
    fn test_share_and_reconstruct() {
        let mut rng = ark_std::test_rng();
        let secret = Scalar::rand(&mut rng);
        let t = 3usize; // threshold
        let n = 5u32; // total nodes

        let poly = Polynomial::new_random(secret, t - 1, &mut rng);
        assert_eq!(poly.evaluate(Scalar::from(0u64)), secret);

        let shares = generate_shares(&poly, n);
        assert_eq!(shares.len(), 5);

        // Reconstruct from exactly t shares
        let reconstructed = lagrange_interpolate_at_zero(&shares[..t]);
        assert_eq!(reconstructed, secret);

        // Reconstruct from different t shares
        let other_shares = vec![shares[0], shares[2], shares[4]];
        let reconstructed2 = lagrange_interpolate_at_zero(&other_shares);
        assert_eq!(reconstructed2, secret);

        // Reconstruct from all n shares
        let reconstructed3 = lagrange_interpolate_at_zero(&shares);
        assert_eq!(reconstructed3, secret);
    }

    #[test]
    fn test_insufficient_shares_wrong_result() {
        let mut rng = ark_std::test_rng();
        let secret = Scalar::rand(&mut rng);
        let poly = Polynomial::new_random(secret, 2, &mut rng); // degree 2 => need 3 shares
        let shares = generate_shares(&poly, 5);

        // Only 2 shares -- should NOT reconstruct correctly (with high probability)
        let bad = lagrange_interpolate_at_zero(&shares[..2]);
        assert_ne!(bad, secret);
    }
}
