//! Constraint capture adapter: synthesize arkworks circuits and extract R1CS matrices.
//!
//! This implements the "Constraint Capture" pattern: we use arkworks as a circuit
//! compiler that outputs R1CS matrices, which we then feed to our Bulletproofs prover.
//! The adapter bridges the arkworks `ConstraintSynthesizer` trait with the IPA
//! proof system by extracting the full variable assignment and constraint matrices
//! from a synthesized circuit.

use ark_bls12_381::Fr;
use ark_relations::r1cs::{
    ConstraintMatrices, ConstraintSynthesizer, ConstraintSystem as ArkCS, SynthesisMode,
};

/// Result of synthesizing a circuit: the R1CS matrices and witness assignment.
///
/// Contains everything needed to produce an IPA proof: the constraint matrices
/// (for future full R1CS reduction) and the complete variable assignment
/// (used as the IPA `a`-vector in the current prototype).
pub struct CapturedR1CS {
    /// Number of public inputs (instance variables, excluding the constant 1).
    pub num_inputs: usize,
    /// Number of private witnesses.
    pub num_witness: usize,
    /// Number of constraints.
    pub num_constraints: usize,
    /// The constraint matrices (A, B, C in sparse format).
    pub matrices: ConstraintMatrices<Fr>,
    /// The full assignment: `[1, public_inputs..., witnesses...]`.
    pub assignment: Vec<Fr>,
}

/// Synthesize a circuit and capture all R1CS data.
///
/// Creates an arkworks constraint system in proving mode, runs the circuit
/// synthesizer, checks satisfaction, and extracts the matrices and assignment.
/// Returns an error if synthesis fails or the circuit is unsatisfied.
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

/// Conversion result: ark-spartan Instance + assignments extracted from a captured circuit.
pub struct SpartanData {
    /// The R1CS constraint system in ark-spartan format.
    pub instance: libspartan::Instance<Fr>,
    /// Witness (private) variable assignment.
    pub vars: libspartan::VarsAssignment<Fr>,
    /// Public input assignment.
    pub inputs: libspartan::InputsAssignment<Fr>,
    /// Number of R1CS constraints.
    pub num_cons: usize,
    /// Number of witness variables (num_vars in spartan).
    pub num_vars: usize,
    /// Number of public inputs.
    pub num_inputs: usize,
}

/// Convert a captured arkworks R1CS circuit to ark-spartan format.
///
/// Performs the column index remapping between arkworks ordering
/// (z = [1, public_inputs, witnesses]) and ark-spartan ordering
/// (z = [vars, 1, inputs]).
pub fn to_spartan(captured: &CapturedR1CS) -> Result<SpartanData, String> {
    let num_instance_vars = captured.num_inputs + 1; // +1 for constant 1
    let num_witness = captured.num_witness;
    let num_cons = captured.num_constraints;
    let num_inputs = captured.num_inputs;

    // Convert arkworks Matrix<Fr> (row-major with (coeff, col) pairs) to COO triples
    // with remapped column indices
    let convert_matrix = |ark_matrix: &[Vec<(Fr, usize)>]| -> Vec<(usize, usize, Fr)> {
        let mut triples = Vec::new();
        for (row, row_entries) in ark_matrix.iter().enumerate() {
            for &(coeff, ark_col) in row_entries {
                let spartan_col = if ark_col == 0 {
                    // constant 1 -> col num_witness in spartan
                    num_witness
                } else if ark_col < num_instance_vars {
                    // public input -> col num_witness + ark_col
                    num_witness + ark_col
                } else {
                    // witness -> col ark_col - num_instance_vars
                    ark_col - num_instance_vars
                };
                triples.push((row, spartan_col, coeff));
            }
        }
        triples
    };

    let a_triples = convert_matrix(&captured.matrices.a);
    let b_triples = convert_matrix(&captured.matrices.b);
    let c_triples = convert_matrix(&captured.matrices.c);

    let instance = libspartan::Instance::new(
        num_cons,
        num_witness,
        num_inputs,
        &a_triples,
        &b_triples,
        &c_triples,
    )
    .map_err(|e| format!("Failed to create Spartan instance: {:?}", e))?;

    // Split assignment into vars (witnesses) and inputs (public inputs)
    // Arkworks assignment: [1, pub_0, pub_1, ..., wit_0, wit_1, ...]
    // We need:
    //   inputs = [pub_0, pub_1, ...] (exclude constant 1)
    //   vars = [wit_0, wit_1, ...]
    let input_values: Vec<Fr> = captured.assignment[1..num_instance_vars].to_vec();
    let witness_values: Vec<Fr> = captured.assignment[num_instance_vars..].to_vec();

    let vars = libspartan::VarsAssignment::new(&witness_values)
        .map_err(|e| format!("Failed to create VarsAssignment: {:?}", e))?;
    let inputs = libspartan::InputsAssignment::new(&input_values)
        .map_err(|e| format!("Failed to create InputsAssignment: {:?}", e))?;

    Ok(SpartanData {
        instance,
        vars,
        inputs,
        num_cons,
        num_vars: num_witness,
        num_inputs,
    })
}

/// Convert an arkworks R1CS to a Spartan Instance without assignments.
/// Used by the verifier, which only needs the constraint structure + public inputs.
pub fn to_spartan_instance_only(
    captured: &CapturedR1CS,
) -> Result<(libspartan::Instance<Fr>, usize, usize, usize), String> {
    let data = to_spartan(captured)?;
    Ok((data.instance, data.num_cons, data.num_vars, data.num_inputs))
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
