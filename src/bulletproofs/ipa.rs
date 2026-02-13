//! Inner Product Argument (IPA) prover and verifier.
//!
//! Implements Protocol 2 from Bünz et al. 2018 (Bulletproofs paper): given
//! generators `(g, h, u)` and a Pedersen vector commitment
//! `P = <a,g> + <b,h> + <a,b>*u`, proves knowledge of vectors `a` and `b`
//! in `O(log n)` proof size via recursive halving of generators and vectors.

use ark_bls12_381::{Fr, G1Affine, G1Projective};
use ark_ec::{CurveGroup, VariableBaseMSM};
use ark_ff::{Field, Zero};
use ark_std::vec::Vec;

use super::generators::BulletproofGens;
use super::transcript::Transcript;
use super::types::IPAProof;

/// Multi-scalar multiplication helper: `sum(scalars[i] * points[i])`.
///
/// Wraps arkworks' variable-base MSM for convenience. Panics if the
/// lengths of `points` and `scalars` do not match.
pub fn msm_helper(points: &[G1Affine], scalars: &[Fr]) -> G1Projective {
    G1Projective::msm(points, scalars).expect("MSM failed: length mismatch")
}

/// Inner product of two scalar vectors: `sum(a[i] * b[i])`.
///
/// Panics if the vectors have different lengths.
pub fn inner_product_helper(a: &[Fr], b: &[Fr]) -> Fr {
    assert_eq!(a.len(), b.len());
    a.iter()
        .zip(b.iter())
        .map(|(ai, bi)| *ai * *bi)
        .fold(Fr::zero(), |acc, x| acc + x)
}

/// Prove an inner product relation.
///
/// Implements Protocol 2 from Bünz et al. 2018: recursive halving of
/// generators and vectors. Given generators `(g, h, u)` and vectors `a, b`
/// such that `P = <a,g> + <b,h> + <a,b>*u`, produces a proof of size
/// `2*log2(n)` group elements plus 2 scalars.
///
/// Each round:
/// 1. Split vectors and generators into low/high halves
/// 2. Compute cross-term commitments `L` and `R`
/// 3. Squeeze a Fiat-Shamir challenge `x`
/// 4. Fold vectors: `a' = a_lo*x + a_hi*x^{-1}`, `b' = b_lo*x^{-1} + b_hi*x`
/// 5. Fold generators similarly
/// 6. Recurse until vectors have length 1
pub fn prove(transcript: &mut Transcript, gens: &BulletproofGens, a: &[Fr], b: &[Fr]) -> IPAProof {
    let n = a.len();
    assert_eq!(n, b.len());
    assert!(n.is_power_of_two(), "Vector length must be power of two");
    assert!(n <= gens.g.len(), "Not enough generators");

    let u = gens.u;

    // Working copies that get folded each round
    let mut a = a.to_vec();
    let mut b = b.to_vec();
    let mut g = gens.g[..n].to_vec();
    let mut h = gens.h[..n].to_vec();

    let mut l_vec = Vec::new();
    let mut r_vec = Vec::new();

    let mut cur_n = n;
    while cur_n > 1 {
        let half = cur_n / 2;

        let (a_lo, a_hi) = a.split_at(half);
        let (b_lo, b_hi) = b.split_at(half);
        let (g_lo, g_hi) = g.split_at(half);
        let (h_lo, h_hi) = h.split_at(half);

        // L = <a_lo, G_hi> + <b_hi, H_lo> + <a_lo, b_hi> * u
        let l =
            msm_helper(g_hi, a_lo) + msm_helper(h_lo, b_hi) + u * inner_product_helper(a_lo, b_hi);
        let l_affine = l.into_affine();

        // R = <a_hi, G_lo> + <b_lo, H_hi> + <a_hi, b_lo> * u
        let r =
            msm_helper(g_lo, a_hi) + msm_helper(h_hi, b_lo) + u * inner_product_helper(a_hi, b_lo);
        let r_affine = r.into_affine();

        // Append L, R to transcript and squeeze challenge
        transcript.append_point(b"L", &l_affine);
        transcript.append_point(b"R", &r_affine);
        let x = transcript.challenge_scalar(b"x");
        let x_inv = x.inverse().expect("challenge must be nonzero");

        l_vec.push(l_affine);
        r_vec.push(r_affine);

        // Fold scalar vectors
        let a_new: Vec<Fr> = a_lo
            .iter()
            .zip(a_hi.iter())
            .map(|(lo, hi)| *lo * x + *hi * x_inv)
            .collect();
        let b_new: Vec<Fr> = b_lo
            .iter()
            .zip(b_hi.iter())
            .map(|(lo, hi)| *lo * x_inv + *hi * x)
            .collect();

        // Fold generator vectors
        let g_new: Vec<G1Affine> = g_lo
            .iter()
            .zip(g_hi.iter())
            .map(|(lo, hi)| ((*lo * x_inv) + (*hi * x)).into_affine())
            .collect();
        let h_new: Vec<G1Affine> = h_lo
            .iter()
            .zip(h_hi.iter())
            .map(|(lo, hi)| ((*lo * x) + (*hi * x_inv)).into_affine())
            .collect();

        a = a_new;
        b = b_new;
        g = g_new;
        h = h_new;
        cur_n = half;
    }

    IPAProof {
        l_vec,
        r_vec,
        a: a[0],
        b: b[0],
    }
}

/// Verify an inner product proof.
///
/// Uses the efficient verifier from Section 3.1 of Bünz et al. 2018:
/// recomputes folded generators via challenge scalars rather than performing
/// the full recursion. This avoids `O(n log n)` group operations by computing
/// per-generator scalar factors from all challenges in a single pass.
///
/// Given commitment `P` (the Pedersen vector commitment), verifies the proof
/// that `P = <a,g> + <b,h> + <a,b>*u` for some `a`, `b` known to the prover.
pub fn verify(
    transcript: &mut Transcript,
    gens: &BulletproofGens,
    n: usize,
    p_commitment: &G1Projective,
    proof: &IPAProof,
) -> bool {
    assert!(n.is_power_of_two());
    let k = proof.l_vec.len();
    assert_eq!(k, n.trailing_zeros() as usize);

    // Replay transcript to recover challenges x_1, ..., x_k
    let mut challenges = Vec::with_capacity(k);
    for i in 0..k {
        transcript.append_point(b"L", &proof.l_vec[i]);
        transcript.append_point(b"R", &proof.r_vec[i]);
        let x = transcript.challenge_scalar(b"x");
        challenges.push(x);
    }

    // Compute per-generator scalar factors from all challenges.
    //
    // For each generator index i in [0, n):
    //   s_i     = product over rounds j of { x_j^{-1} if bit is 0, x_j if bit is 1 }
    //   s_inv_i = product over rounds j of { x_j     if bit is 0, x_j^{-1} if bit is 1 }
    //
    // The "bit" for round j is determined by which half index i falls into
    // at that level of the recursion.
    let mut s_scalars = vec![Fr::ONE; n];
    let mut s_inv_scalars = vec![Fr::ONE; n];

    for (j, x) in challenges.iter().enumerate() {
        let x_inv = x.inverse().expect("challenge must be nonzero");
        let step = 1 << (k - 1 - j);
        for i in 0..n {
            if (i / step).is_multiple_of(2) {
                // Index is in the "lo" half at this recursion level
                s_scalars[i] *= x_inv;
                s_inv_scalars[i] *= *x;
            } else {
                // Index is in the "hi" half at this recursion level
                s_scalars[i] *= *x;
                s_inv_scalars[i] *= x_inv;
            }
        }
    }

    // Compute folded generators
    let g_final = msm_helper(&gens.g[..n], &s_scalars);
    let h_final = msm_helper(&gens.h[..n], &s_inv_scalars);

    // Expected RHS: a * g_final + b * h_final + (a*b) * u
    let expected = g_final * proof.a + h_final * proof.b + gens.u * (proof.a * proof.b);

    // Accumulate LHS: P' = P + sum(x_i^2 * L_i + x_i^{-2} * R_i)
    let mut p_prime = *p_commitment;
    for (i, x) in challenges.iter().enumerate() {
        let x_sq = *x * *x;
        let x_inv_sq = x_sq.inverse().expect("challenge must be nonzero");
        p_prime += proof.l_vec[i] * x_sq + proof.r_vec[i] * x_inv_sq;
    }

    // Verification: P' == expected
    p_prime == expected
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::UniformRand;

    #[test]
    fn test_ipa_prove_verify() {
        let n = 4;
        let gens = BulletproofGens::new(n);
        let mut rng = ark_std::test_rng();

        let a: Vec<Fr> = (0..n).map(|_| Fr::rand(&mut rng)).collect();
        let b: Vec<Fr> = (0..n).map(|_| Fr::rand(&mut rng)).collect();

        // Commitment: P = <a,g> + <b,h> + <a,b>*u
        let p = msm_helper(&gens.g[..n], &a)
            + msm_helper(&gens.h[..n], &b)
            + gens.u * inner_product_helper(&a, &b);

        let mut prove_transcript = Transcript::new(b"test-ipa");
        let proof = prove(&mut prove_transcript, &gens, &a, &b);

        let mut verify_transcript = Transcript::new(b"test-ipa");
        assert!(verify(&mut verify_transcript, &gens, n, &p, &proof));
    }

    #[test]
    fn test_ipa_reject_bad_proof() {
        let n = 4;
        let gens = BulletproofGens::new(n);
        let mut rng = ark_std::test_rng();

        let a: Vec<Fr> = (0..n).map(|_| Fr::rand(&mut rng)).collect();
        let b: Vec<Fr> = (0..n).map(|_| Fr::rand(&mut rng)).collect();

        let p = msm_helper(&gens.g[..n], &a)
            + msm_helper(&gens.h[..n], &b)
            + gens.u * inner_product_helper(&a, &b);

        let mut prove_transcript = Transcript::new(b"test-ipa");
        let mut proof = prove(&mut prove_transcript, &gens, &a, &b);

        // Tamper with the proof
        proof.a += Fr::ONE;

        let mut verify_transcript = Transcript::new(b"test-ipa");
        assert!(!verify(&mut verify_transcript, &gens, n, &p, &proof));
    }

    #[test]
    fn test_ipa_different_sizes() {
        for n in [2, 4, 8, 16] {
            let gens = BulletproofGens::new(n);
            let mut rng = ark_std::test_rng();

            let a: Vec<Fr> = (0..n).map(|_| Fr::rand(&mut rng)).collect();
            let b: Vec<Fr> = (0..n).map(|_| Fr::rand(&mut rng)).collect();

            let p = msm_helper(&gens.g[..n], &a)
                + msm_helper(&gens.h[..n], &b)
                + gens.u * inner_product_helper(&a, &b);

            let mut pt = Transcript::new(b"test");
            let proof = prove(&mut pt, &gens, &a, &b);

            let mut vt = Transcript::new(b"test");
            assert!(verify(&mut vt, &gens, n, &p, &proof), "Failed for n={}", n);

            // Proof size should be logarithmic
            assert_eq!(proof.l_vec.len(), n.trailing_zeros() as usize);
        }
    }
}
