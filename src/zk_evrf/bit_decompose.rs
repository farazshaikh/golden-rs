use ark_bls12_381::Fr;
use ark_ec::AdditiveGroup;
use ark_ff::{BigInteger, Field, One, PrimeField, Zero};

use super::nonnative::{ConstraintSystem, VarIndex};

/// Result of bit-decomposition: the allocated bit variables.
pub struct BitDecomposition {
    /// Variable indices for each bit: bits[0] is the LSB
    pub bits: Vec<VarIndex>,
    /// Variable index for the original value (k)
    pub value_var: VarIndex,
}

/// Decompose a scalar value into lambda+1 bits in the constraint system.
///
/// Per Golden paper Section 4.2:
/// - Allocates lambda+1 bit variables and the original value
/// - Constrains each bit: k_i * (k_i - 1) = 0
/// - Constrains recomposition: k = sum 2^i * k_i
///
/// Returns the BitDecomposition with variable indices.
///
/// lambda is the bit-length (e.g., 256 for a 256-bit scalar).
/// The value must fit in lambda+1 bits.
pub fn bit_decompose(
    cs: &mut ConstraintSystem,
    value: Fr,
    lambda: usize,
) -> BitDecomposition {
    // Get the bits of the value
    let value_bits = value.into_bigint().to_bits_le();

    // Allocate the value variable
    let value_var = cs.alloc_witness(value);

    // Allocate bit variables and constrain each to be 0 or 1
    let mut bits = Vec::with_capacity(lambda + 1);
    for i in 0..=lambda {
        let bit_val = if i < value_bits.len() && value_bits[i] {
            Fr::one()
        } else {
            Fr::zero()
        };
        let bit_var = cs.alloc_witness(bit_val);

        // Constraint: k_i * (k_i - 1) = 0
        // Equivalently: k_i * k_i = k_i
        // R1CS form: A = [k_i], B = [k_i], C = [k_i]
        cs.constrain(
            vec![(bit_var, Fr::one())],
            vec![(bit_var, Fr::one())],
            vec![(bit_var, Fr::one())],
        );

        bits.push(bit_var);
    }

    // Constraint: k = sum_{i=0}^{lambda} 2^i * k_i
    // R1CS form: (sum 2^i * k_i) * 1 = k
    let mut power_of_two = Fr::one();
    let mut recomp_terms = Vec::new();
    for i in 0..=lambda {
        recomp_terms.push((bits[i], power_of_two));
        power_of_two.double_in_place();
    }

    cs.constrain(
        recomp_terms,
        vec![(0, Fr::one())], // multiply by 1 (variable 0 = constant 1)
        vec![(value_var, Fr::one())],
    );

    BitDecomposition { bits, value_var }
}

/// Count the number of constraints for a bit decomposition.
/// lambda + 1 (bit constraints) + 1 (recomposition) = lambda + 2
pub fn constraint_count(lambda: usize) -> usize {
    lambda + 2
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::UniformRand;

    #[test]
    fn test_bit_decompose_small() {
        let mut cs = ConstraintSystem::new();
        let value = Fr::from(42u64); // 101010 in binary
        let lambda = 7; // 8 bits is enough

        let decomp = bit_decompose(&mut cs, value, lambda);

        // Should have lambda + 2 = 9 constraints
        assert_eq!(cs.num_constraints(), constraint_count(lambda));

        // All constraints should be satisfied
        assert!(cs.is_satisfied(), "Constraints not satisfied for value=42");

        // Check the bits are correct (42 = 0b00101010)
        assert_eq!(cs.witness[decomp.bits[0]], Fr::zero()); // bit 0
        assert_eq!(cs.witness[decomp.bits[1]], Fr::one()); // bit 1
        assert_eq!(cs.witness[decomp.bits[2]], Fr::zero()); // bit 2
        assert_eq!(cs.witness[decomp.bits[3]], Fr::one()); // bit 3
        assert_eq!(cs.witness[decomp.bits[4]], Fr::zero()); // bit 4
        assert_eq!(cs.witness[decomp.bits[5]], Fr::one()); // bit 5
    }

    #[test]
    fn test_bit_decompose_zero() {
        let mut cs = ConstraintSystem::new();
        let decomp = bit_decompose(&mut cs, Fr::zero(), 7);
        assert!(cs.is_satisfied());
        for &bit in &decomp.bits {
            assert_eq!(cs.witness[bit], Fr::zero());
        }
    }

    #[test]
    fn test_bit_decompose_one() {
        let mut cs = ConstraintSystem::new();
        let decomp = bit_decompose(&mut cs, Fr::one(), 7);
        assert!(cs.is_satisfied());
        assert_eq!(cs.witness[decomp.bits[0]], Fr::one());
        for &bit in &decomp.bits[1..] {
            assert_eq!(cs.witness[bit], Fr::zero());
        }
    }

    #[test]
    fn test_bit_decompose_random_fr() {
        // Test with a random Fr element (up to 255 bits)
        let mut rng = ark_std::test_rng();
        let value = Fr::rand(&mut rng);
        let lambda = 255; // Fr is ~255 bits

        let mut cs = ConstraintSystem::new();
        let _decomp = bit_decompose(&mut cs, value, lambda);

        // Constraint count: lambda + 2 = 257
        assert_eq!(cs.num_constraints(), 257);
        assert!(cs.is_satisfied(), "Constraints not satisfied for random Fr");
    }

    #[test]
    fn test_bit_decompose_constraint_count() {
        // Verify the paper's formula: lambda + 2
        for lambda in [7, 15, 31, 63, 127, 255] {
            let mut cs = ConstraintSystem::new();
            let _ = bit_decompose(&mut cs, Fr::from(1u64), lambda);
            assert_eq!(
                cs.num_constraints(),
                lambda + 2,
                "Wrong count for lambda={}",
                lambda
            );
        }
    }
}
