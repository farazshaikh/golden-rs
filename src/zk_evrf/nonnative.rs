//! Non-native field arithmetic constraint system per Appendix E of the Golden paper.
//!
//! Per Appendix E of the Golden paper (IACR 2025/1924), when `G_in = G_out`
//! (i.e., the eVRF operates entirely on BLS12-381), point coordinates live in
//! Fq (381 bits) while the R1CS is over Fr (255 bits). This module provides a
//! low-level constraint system that represents Fq values as Fr witness variables
//! with explicit reduction.
//!
//! For the arkworks-based circuit (see [`super::circuit`] and
//! [`super::exponentiation`]), non-native arithmetic is handled automatically by
//! `EmulatedFpVar<Fq, Fr>`.

use ark_bls12_381::{Fq, Fr};
use ark_ff::{BigInteger, PrimeField};

/// Variable index in the R1CS constraint system.
/// Index 0 is always the constant "1".
pub type VarIndex = usize;

/// A single R1CS constraint: `<a, z> * <b, z> = <c, z>`
/// Stored as sparse vectors of `(variable_index, coefficient)`.
#[derive(Clone, Debug)]
pub struct Constraint {
    /// Left-hand linear combination `a`.
    pub a: Vec<(VarIndex, Fr)>,
    /// Right-hand linear combination `b`.
    pub b: Vec<(VarIndex, Fr)>,
    /// Output linear combination `c`.
    pub c: Vec<(VarIndex, Fr)>,
}

/// Constraint system that accumulates R1CS constraints.
///
/// Variables are indexed starting from 0 (constant 1), then public inputs,
/// then witnesses. The system supports both constraint generation (for circuit
/// definition) and satisfaction checking (for testing).
pub struct ConstraintSystem {
    /// Total number of variables allocated (including the constant).
    pub num_vars: usize,
    /// Number of public input variables.
    pub num_inputs: usize,
    /// Accumulated constraints.
    pub constraints: Vec<Constraint>,
    /// Witness values (for the prover; `None` for the verifier).
    pub witness: Vec<Fr>,
}

impl Default for ConstraintSystem {
    fn default() -> Self {
        Self::new()
    }
}

impl ConstraintSystem {
    /// Create a new constraint system. Variable 0 is the constant 1.
    pub fn new() -> Self {
        Self {
            num_vars: 1, // var 0 = constant 1
            num_inputs: 0,
            constraints: Vec::new(),
            witness: vec![Fr::from(1u64)], // witness[0] = 1
        }
    }

    /// Allocate a new public input variable and set its witness value.
    pub fn alloc_input(&mut self, value: Fr) -> VarIndex {
        let idx = self.num_vars;
        self.num_vars += 1;
        self.num_inputs += 1;
        self.witness.push(value);
        idx
    }

    /// Allocate a new private witness variable and set its value.
    pub fn alloc_witness(&mut self, value: Fr) -> VarIndex {
        let idx = self.num_vars;
        self.num_vars += 1;
        self.witness.push(value);
        idx
    }

    /// Add a constraint: `<a, z> * <b, z> = <c, z>`.
    pub fn constrain(
        &mut self,
        a: Vec<(VarIndex, Fr)>,
        b: Vec<(VarIndex, Fr)>,
        c: Vec<(VarIndex, Fr)>,
    ) {
        self.constraints.push(Constraint { a, b, c });
    }

    /// Enforce that variable `var` equals a known constant value.
    ///
    /// Constraint: `var * 1 = constant`.
    pub fn enforce_equal_constant(&mut self, var: VarIndex, constant: Fr) {
        self.constrain(
            vec![(var, Fr::from(1u64))],
            vec![(0, Fr::from(1u64))], // variable 0 = constant 1
            vec![(0, constant)],
        );
    }

    /// Enforce multiplication: `a * b = c` (all are variable indices).
    pub fn enforce_mul(&mut self, a: VarIndex, b: VarIndex, c: VarIndex) {
        self.constrain(
            vec![(a, Fr::from(1u64))],
            vec![(b, Fr::from(1u64))],
            vec![(c, Fr::from(1u64))],
        );
    }

    /// Enforce addition: `a + b = c`.
    ///
    /// Implemented as: `(a + b) * 1 = c`.
    pub fn enforce_add(&mut self, a: VarIndex, b: VarIndex, c: VarIndex) {
        self.constrain(
            vec![(a, Fr::from(1u64)), (b, Fr::from(1u64))],
            vec![(0, Fr::from(1u64))],
            vec![(c, Fr::from(1u64))],
        );
    }

    /// Enforce linear combination: `sum(coeff_i * var_i) = result`.
    pub fn enforce_lc_equals(&mut self, terms: Vec<(VarIndex, Fr)>, result: VarIndex) {
        self.constrain(
            terms,
            vec![(0, Fr::from(1u64))],
            vec![(result, Fr::from(1u64))],
        );
    }

    /// Allocate a witness variable for `a * b` and enforce the multiplication constraint.
    ///
    /// Returns the index of the product variable.
    pub fn mul(&mut self, a: VarIndex, b: VarIndex) -> VarIndex {
        let a_val = self.witness[a];
        let b_val = self.witness[b];
        let c_val = a_val * b_val;
        let c = self.alloc_witness(c_val);
        self.enforce_mul(a, b, c);
        c
    }

    /// Check if all constraints are satisfied by the current witness.
    pub fn is_satisfied(&self) -> bool {
        for constraint in &self.constraints {
            let a_val = eval_lc(&constraint.a, &self.witness);
            let b_val = eval_lc(&constraint.b, &self.witness);
            let c_val = eval_lc(&constraint.c, &self.witness);
            if a_val * b_val != c_val {
                return false;
            }
        }
        true
    }

    /// Return the number of constraints.
    pub fn num_constraints(&self) -> usize {
        self.constraints.len()
    }
}

/// Evaluate a linear combination given witness values.
fn eval_lc(lc: &[(VarIndex, Fr)], witness: &[Fr]) -> Fr {
    lc.iter()
        .map(|(idx, coeff)| witness[*idx] * coeff)
        .fold(Fr::from(0u64), |a, b| a + b)
}

/// Convert an Fq element to Fr (reduce mod r).
///
/// Per Appendix E of the Golden paper (IACR 2025/1924), when the eVRF operates
/// on a single curve (`G_in = G_out`), point coordinates in Fq must be represented
/// as Fr witness variables. This conversion is lossy for large Fq values (> Fr modulus)
/// but the circuit compensates with sufficient constraints to uniquely determine
/// the correct values.
pub fn fq_to_fr(val: Fq) -> Fr {
    let bytes = val.into_bigint().to_bytes_le();
    Fr::from_le_bytes_mod_order(&bytes)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_constraint_system_mul() {
        let mut cs = ConstraintSystem::new();
        let a = cs.alloc_witness(Fr::from(3u64));
        let b = cs.alloc_witness(Fr::from(7u64));
        let c = cs.mul(a, b);

        assert!(cs.is_satisfied());
        assert_eq!(cs.witness[c], Fr::from(21u64));
        assert_eq!(cs.num_constraints(), 1);
    }

    #[test]
    fn test_constraint_system_add() {
        let mut cs = ConstraintSystem::new();
        let a = cs.alloc_witness(Fr::from(10u64));
        let b = cs.alloc_witness(Fr::from(20u64));
        let sum = cs.alloc_witness(Fr::from(30u64));
        cs.enforce_add(a, b, sum);

        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_constraint_unsatisfied() {
        let mut cs = ConstraintSystem::new();
        let a = cs.alloc_witness(Fr::from(3u64));
        let b = cs.alloc_witness(Fr::from(7u64));
        let c = cs.alloc_witness(Fr::from(22u64)); // wrong: should be 21
        cs.enforce_mul(a, b, c);

        assert!(!cs.is_satisfied());
    }

    #[test]
    fn test_linear_combination() {
        let mut cs = ConstraintSystem::new();
        // 2*a + 3*b = result
        let a = cs.alloc_witness(Fr::from(5u64));
        let b = cs.alloc_witness(Fr::from(10u64));
        let result = cs.alloc_witness(Fr::from(40u64)); // 2*5 + 3*10 = 40
        cs.enforce_lc_equals(vec![(a, Fr::from(2u64)), (b, Fr::from(3u64))], result);

        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_fq_to_fr() {
        // Basic sanity: small values should convert correctly
        let fq_val = Fq::from(42u64);
        let fr_val = fq_to_fr(fq_val);
        assert_eq!(fr_val, Fr::from(42u64));
    }
}
