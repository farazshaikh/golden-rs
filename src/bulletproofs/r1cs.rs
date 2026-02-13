//! R1CS-to-IPA reduction (stub).
//!
//! Provides the constraint system representation and (stub) prover/verifier for
//! reducing Rank-1 Constraint System satisfiability to an inner product argument.
//! The full R1CS-to-IPA reduction is planned for a future phase.

// TODO: implement in next phase

use ark_bls12_381::Fr;

use super::generators::BulletproofGens;
use super::transcript::Transcript;

/// Sparse R1CS constraint system.
///
/// Represents `(A*z) . (B*z) = (C*z)` where `z = (1, x, w)` is the extended
/// witness (constant, public inputs, private witnesses) and `.` denotes the
/// Hadamard (entrywise) product. The matrices `A`, `B`, `C` are stored in
/// sparse COO (coordinate) format.
pub struct R1CS {
    /// Number of constraints.
    pub num_constraints: usize,
    /// Number of public inputs (`x`).
    pub num_inputs: usize,
    /// Number of auxiliary witness variables (`w`).
    pub num_aux: usize,
    /// `A` matrix: `Vec` of `(row, col, val)` triples.
    pub a: Vec<(usize, usize, Fr)>,
    /// `B` matrix: `Vec` of `(row, col, val)` triples.
    pub b: Vec<(usize, usize, Fr)>,
    /// `C` matrix: `Vec` of `(row, col, val)` triples.
    pub c: Vec<(usize, usize, Fr)>,
}

/// Prove satisfiability of an R1CS instance using the Bulletproofs IPA.
///
/// Takes the constraint system, public inputs, private witness, and produces
/// an R1CS proof that reduces to the inner product argument.
///
/// **Stub:** not yet implemented.
pub fn prove(
    _transcript: &mut Transcript,
    _gens: &BulletproofGens,
    _r1cs: &R1CS,
    _inputs: &[Fr],
    _witness: &[Fr],
) -> super::types::R1CSProof {
    todo!("R1CS prove: implement in next phase")
}

/// Verify an R1CS proof.
///
/// Checks that the proof demonstrates satisfiability of the given R1CS instance
/// with respect to the provided public inputs.
///
/// **Stub:** not yet implemented.
pub fn verify(
    _transcript: &mut Transcript,
    _gens: &BulletproofGens,
    _r1cs: &R1CS,
    _inputs: &[Fr],
    _proof: &super::types::R1CSProof,
) -> bool {
    todo!("R1CS verify: implement in next phase")
}
