//! Constraint capture adapter: synthesize arkworks circuits and extract R1CS matrices.
//!
//! This implements the "Constraint Capture" pattern: we use arkworks as a circuit
//! compiler that outputs R1CS matrices, which we then feed to our Bulletproofs prover.

use ark_bls12_381::Fr;
use ark_relations::r1cs::{
    ConstraintMatrices, ConstraintSynthesizer, ConstraintSystem as ArkCS, SynthesisMode,
};

/// Result of synthesizing a circuit: the R1CS matrices and witness assignment.
pub struct CapturedR1CS {
    /// Number of public inputs (instance variables, excluding the constant 1)
    pub num_inputs: usize,
    /// Number of private witnesses
    pub num_witness: usize,
    /// Number of constraints
    pub num_constraints: usize,
    /// The constraint matrices (A, B, C in sparse format)
    pub matrices: ConstraintMatrices<Fr>,
    /// The full assignment: [1, public_inputs..., witnesses...]
    pub assignment: Vec<Fr>,
}

/// Synthesize a circuit and capture all R1CS data.
///
/// Creates an arkworks constraint system in proving mode, runs the circuit
/// synthesizer, checks satisfaction, and extracts the matrices and assignment.
pub fn capture_circuit<C: ConstraintSynthesizer<Fr>>(circuit: C) -> Result<CapturedR1CS, String> {
    let cs = ArkCS::<Fr>::new_ref();
    cs.set_mode(SynthesisMode::Prove {
        construct_matrices: true,
    });

    circuit
        .generate_constraints(cs.clone())
        .map_err(|e| format!("Circuit synthesis failed: {}", e))?;

    cs.finalize();

    let is_satisfied = cs
        .is_satisfied()
        .map_err(|e| format!("Satisfaction check failed: {}", e))?;
    if !is_satisfied {
        return Err("Circuit is not satisfied by the provided witness".to_string());
    }

    let num_inputs = cs.num_instance_variables() - 1; // exclude constant 1
    let num_witness = cs.num_witness_variables();
    let num_constraints = cs.num_constraints();

    let matrices = cs
        .to_matrices()
        .ok_or("Failed to extract constraint matrices")?;

    // Borrow inner CS to extract the full variable assignment
    let assignment = {
        let inner = cs.borrow().ok_or("Failed to borrow constraint system")?;
        let mut a =
            Vec::with_capacity(inner.instance_assignment.len() + inner.witness_assignment.len());
        a.extend_from_slice(&inner.instance_assignment);
        a.extend_from_slice(&inner.witness_assignment);
        a
    };

    Ok(CapturedR1CS {
        num_inputs,
        num_witness,
        num_constraints,
        matrices,
        assignment,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::One;
    use ark_r1cs_std::fields::fp::FpVar;
    use ark_r1cs_std::prelude::*;
    use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};

    /// Trivial circuit: a * b = c (a,b witnesses; c public input)
    struct MulCircuit {
        a: Fr,
        b: Fr,
    }

    impl ConstraintSynthesizer<Fr> for MulCircuit {
        fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
            let a_var = FpVar::new_witness(cs.clone(), || Ok(self.a))?;
            let b_var = FpVar::new_witness(cs.clone(), || Ok(self.b))?;
            let c_var = FpVar::new_input(cs.clone(), || Ok(self.a * self.b))?;

            let product = &a_var * &b_var;
            product.enforce_equal(&c_var)?;

            Ok(())
        }
    }

    #[test]
    fn test_capture_mul_circuit() {
        let circuit = MulCircuit {
            a: Fr::from(3u64),
            b: Fr::from(7u64),
        };

        let captured = capture_circuit(circuit).expect("capture should succeed");

        assert!(captured.num_constraints > 0, "Should have constraints");
        assert_eq!(
            captured.num_inputs, 1,
            "Should have 1 public input (product)"
        );
        assert!(captured.num_witness > 0, "Should have witnesses");

        // First element of assignment is the constant 1
        assert_eq!(captured.assignment[0], Fr::one());

        println!(
            "MulCircuit: {} constraints, {} inputs, {} witnesses",
            captured.num_constraints, captured.num_inputs, captured.num_witness
        );
    }

    #[test]
    fn test_capture_unsatisfied_circuit() {
        struct BadCircuit;

        impl ConstraintSynthesizer<Fr> for BadCircuit {
            fn generate_constraints(
                self,
                cs: ConstraintSystemRef<Fr>,
            ) -> Result<(), SynthesisError> {
                let a = FpVar::new_witness(cs.clone(), || Ok(Fr::from(3u64)))?;
                let b = FpVar::new_witness(cs.clone(), || Ok(Fr::from(7u64)))?;
                // Wrong: 3 * 7 != 22
                let c = FpVar::new_input(cs.clone(), || Ok(Fr::from(22u64)))?;

                let product = &a * &b;
                product.enforce_equal(&c)?;

                Ok(())
            }
        }

        let result = capture_circuit(BadCircuit);
        assert!(result.is_err(), "Should fail for unsatisfied circuit");
    }
}
