//! Proof data structures for the Bulletproofs system.
//!
//! Contains the serializable proof types produced by the IPA prover and
//! the (stub) R1CS prover.

use ark_bls12_381::{Fr, G1Affine};

/// A Bulletproofs Inner Product Argument proof.
///
/// Per Protocol 2 from Bünz et al. 2018 (Bulletproofs paper), the proof
/// consists of `k = log2(n)` pairs of left/right commitments from the
/// recursive halving steps, plus the final scalar pair `(a, b)` after
/// all folding rounds.
#[derive(Clone, Debug)]
pub struct IPAProof {
    /// Left commitments from recursive halving: `L_1, ..., L_k` where `k = log2(n)`.
    pub l_vec: Vec<G1Affine>,
    /// Right commitments from recursive halving: `R_1, ..., R_k`.
    pub r_vec: Vec<G1Affine>,
    /// Final scalar `a` after recursive halving.
    pub a: Fr,
    /// Final scalar `b` after recursive halving.
    pub b: Fr,
}

/// An R1CS Bulletproofs proof.
///
/// Combines the arithmetic circuit satisfiability reduction with the inner
/// product argument. The outer commitments encode the R1CS witness and
/// constraint structure, while the inner [`IPAProof`] proves the resulting
/// inner product relation.
#[derive(Clone, Debug)]
pub struct R1CSProof {
    /// Commitment to the witness auxiliary variables.
    pub ai_commitment: G1Affine,
    /// Commitment to the Hadamard product terms.
    pub ao_commitment: G1Affine,
    /// Commitment to blinding factors.
    pub s_commitment: G1Affine,
    /// Challenge-phase commitment `T_1`.
    pub t1_commitment: G1Affine,
    /// Challenge-phase commitment `T_2`.
    pub t2_commitment: G1Affine,
    /// Evaluation proof scalar `tau_x`.
    pub tau_x: Fr,
    /// Blinding evaluation scalar `mu`.
    pub mu: Fr,
    /// Inner product evaluation `t_hat`.
    pub t_hat: Fr,
    /// The inner product proof for the final relation.
    pub ipa_proof: IPAProof,
}
