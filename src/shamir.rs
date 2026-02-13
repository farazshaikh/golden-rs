use ark_ff::{Field, UniformRand};
use ark_std::rand::Rng;

use crate::types::{NodeId, Scalar};

/// A polynomial over the scalar field, used for Shamir secret sharing.
/// coefficients[0] is the secret (constant term).
pub struct Polynomial {
    pub coefficients: Vec<Scalar>,
}

impl Polynomial {
    /// Create a random polynomial of the given degree whose constant term is `secret`.
    /// For threshold t, use degree = t - 1.
    pub fn new_random(secret: Scalar, degree: usize, rng: &mut impl Rng) -> Self {
        let mut coefficients = Vec::with_capacity(degree + 1);
        coefficients.push(secret);
        for _ in 0..degree {
            coefficients.push(Scalar::rand(rng));
        }
        Self { coefficients }
    }

    /// Evaluate the polynomial at `x` using Horner's method.
    pub fn evaluate(&self, x: Scalar) -> Scalar {
        // Horner's: a_0 + x*(a_1 + x*(a_2 + ... + x*a_n))
        // Walk coefficients from highest degree down.
        let mut result = Scalar::from(0u64);
        for coeff in self.coefficients.iter().rev() {
            result = result * x + coeff;
        }
        result
    }

    /// Return the degree of the polynomial.
    pub fn degree(&self) -> usize {
        self.coefficients.len() - 1
    }
}

/// Generate n shares by evaluating the polynomial at x = 1, 2, ..., n.
/// Returns (node_id, share_value) pairs with node_id in 1..=n.
pub fn generate_shares(poly: &Polynomial, n: u32) -> Vec<(NodeId, Scalar)> {
    (1..=n)
        .map(|i| {
            let x = Scalar::from(i as u64);
            (i, poly.evaluate(x))
        })
        .collect()
}

/// Reconstruct f(0) (the secret) from a set of shares using Lagrange interpolation.
///
/// Each share is (node_id, y_i) where x_i = Scalar::from(node_id).
/// Requires at least t shares for a degree-(t-1) polynomial.
pub fn lagrange_interpolate_at_zero(shares: &[(NodeId, Scalar)]) -> Scalar {
    let mut result = Scalar::from(0u64);

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
