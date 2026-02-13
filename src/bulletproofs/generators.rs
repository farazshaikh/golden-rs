use ark_bls12_381::{Fr, G1Affine};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::PrimeField;
use sha2::{Digest, Sha256};

/// A set of generators for Bulletproofs.
/// Contains two vectors g and h of independent generators, plus a blinding generator.
pub struct BulletproofGens {
    /// Generator vector g: g_1, ..., g_n
    pub g: Vec<G1Affine>,
    /// Generator vector h: h_1, ..., h_n
    pub h: Vec<G1Affine>,
    /// Blinding generator (independent of g and h)
    pub b_blinding: G1Affine,
    /// Inner product generator u
    pub u: G1Affine,
}

impl BulletproofGens {
    /// Create a new set of generators for vectors of length `n`.
    /// Generators are derived deterministically via hash-to-curve.
    pub fn new(n: usize) -> Self {
        let g = (0..n)
            .map(|i| hash_to_generator(b"golden-bp-g", i as u64))
            .collect();
        let h = (0..n)
            .map(|i| hash_to_generator(b"golden-bp-h", i as u64))
            .collect();
        let b_blinding = hash_to_generator(b"golden-bp-blinding", 0);
        let u = hash_to_generator(b"golden-bp-u", 0);
        Self {
            g,
            h,
            b_blinding,
            u,
        }
    }
}

/// Derive a generator deterministically from a domain and index.
/// Uses hash-and-multiply: SHA-256(domain || index) -> scalar -> generator * scalar.
fn hash_to_generator(domain: &[u8], index: u64) -> G1Affine {
    let mut hasher = Sha256::new();
    hasher.update(domain);
    hasher.update(index.to_le_bytes());
    let hash = hasher.finalize();
    let scalar = Fr::from_le_bytes_mod_order(&hash);
    (G1Affine::generator() * scalar).into_affine()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_generators_distinct() {
        let gens = BulletproofGens::new(8);
        // All g generators should be distinct
        for i in 0..8 {
            for j in (i + 1)..8 {
                assert_ne!(gens.g[i], gens.g[j], "g[{}] == g[{}]", i, j);
            }
        }
        // g and h should be distinct
        for i in 0..8 {
            assert_ne!(gens.g[i], gens.h[i], "g[{}] == h[{}]", i, i);
        }
        // Blinding generator should be distinct
        assert_ne!(gens.b_blinding, gens.g[0]);
        assert_ne!(gens.u, gens.g[0]);
        assert_ne!(gens.b_blinding, gens.u);
    }

    #[test]
    fn test_generators_deterministic() {
        let g1 = BulletproofGens::new(4);
        let g2 = BulletproofGens::new(4);
        for i in 0..4 {
            assert_eq!(g1.g[i], g2.g[i]);
            assert_eq!(g1.h[i], g2.h[i]);
        }
    }

    #[test]
    fn test_generators_on_curve() {
        let gens = BulletproofGens::new(16);
        for g in &gens.g {
            assert!(g.is_on_curve(), "Generator not on curve");
            assert!(!g.is_zero(), "Generator is identity");
        }
    }
}
