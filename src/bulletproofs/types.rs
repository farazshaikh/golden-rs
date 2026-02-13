use ark_bls12_381::{Fr, G1Affine};

/// A Bulletproofs Inner Product Argument proof.
#[derive(Clone, Debug)]
pub struct IPAProof {
    /// Left commitments from recursive halving: L_1, ..., L_k where k = log2(n)
    pub l_vec: Vec<G1Affine>,
    /// Right commitments from recursive halving: R_1, ..., R_k
    pub r_vec: Vec<G1Affine>,
    /// Final scalar a after recursive halving
    pub a: Fr,
    /// Final scalar b after recursive halving
    pub b: Fr,
}

/// An R1CS Bulletproofs proof.
#[derive(Clone, Debug)]
pub struct R1CSProof {
    /// Commitment to the witness auxiliary variables
    pub ai_commitment: G1Affine,
    /// Commitment to the Hadamard product terms
    pub ao_commitment: G1Affine,
    /// Commitment to blinding
    pub s_commitment: G1Affine,
    /// Challenge-phase commitments
    pub t1_commitment: G1Affine,
    pub t2_commitment: G1Affine,
    /// Evaluation proofs
    pub tau_x: Fr,
    pub mu: Fr,
    pub t_hat: Fr,
    /// The inner product proof
    pub ipa_proof: IPAProof,
}
