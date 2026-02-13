//! Exponentiation gadget for the Golden DKG eVRF ZK proof (Section 4.3).
//!
//! Implements elliptic curve point arithmetic (addition and doubling) using
//! arkworks' EmulatedFpVar for Fq-in-Fr non-native field arithmetic.
//!
//! The key idea: our R1CS is over Fr (the BLS12-381 scalar field), but point
//! coordinates live in Fq (the base field). EmulatedFpVar<Fq, Fr> handles
//! the non-native arithmetic automatically, generating the necessary limb
//! decomposition and range check constraints.

use ark_bls12_381::{Fq, Fr, G1Affine};
use ark_ff::{Field, Zero};
use ark_r1cs_std::{fields::emulated_fp::EmulatedFpVar, prelude::*};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};

/// Emulated Fq variable inside an Fr constraint system.
type FqVar = EmulatedFpVar<Fq, Fr>;

/// A G1 point represented in the circuit using emulated Fq coordinates.
pub struct PointVar {
    pub x: FqVar,
    pub y: FqVar,
}

impl PointVar {
    /// Allocate a G1 point as a private witness.
    pub fn new_witness(
        cs: ConstraintSystemRef<Fr>,
        point: G1Affine,
    ) -> Result<Self, SynthesisError> {
        let (x, y) = if point.infinity {
            (Fq::zero(), Fq::zero())
        } else {
            (point.x, point.y)
        };
        Ok(Self {
            x: FqVar::new_witness(cs.clone(), || Ok(x))?,
            y: FqVar::new_witness(cs, || Ok(y))?,
        })
    }

    /// Allocate a G1 point as a public input.
    pub fn new_input(cs: ConstraintSystemRef<Fr>, point: G1Affine) -> Result<Self, SynthesisError> {
        let (x, y) = if point.infinity {
            (Fq::zero(), Fq::zero())
        } else {
            (point.x, point.y)
        };
        Ok(Self {
            x: FqVar::new_input(cs.clone(), || Ok(x))?,
            y: FqVar::new_input(cs, || Ok(y))?,
        })
    }

    /// Enforce that this point equals another point.
    pub fn enforce_equal(&self, other: &Self) -> Result<(), SynthesisError> {
        self.x.enforce_equal(&other.x)?;
        self.y.enforce_equal(&other.y)?;
        Ok(())
    }
}

/// Point addition using the chord rule (P1 != P2, P1 != -P2).
///
/// Given P1 = (x1, y1) and P2 = (x2, y2) with x1 != x2:
///   s = (y2 - y1) / (x2 - x1)
///   x3 = s^2 - x1 - x2
///   y3 = s * (x1 - x3) - y1
///
/// The prover supplies the slope s as a witness; the circuit constrains:
///   1. s * (x2 - x1) = y2 - y1
///   2. x3 = s^2 - x1 - x2
///   3. y3 = s * (x1 - x3) - y1
pub fn point_add(
    cs: ConstraintSystemRef<Fr>,
    p1: &PointVar,
    p2: &PointVar,
    expected_result: G1Affine,
) -> Result<PointVar, SynthesisError> {
    let result = PointVar::new_witness(cs.clone(), expected_result)?;

    // Compute slope witness: s = (y2 - y1) / (x2 - x1)
    let x1_val = p1.x.value().unwrap_or(Fq::zero());
    let y1_val = p1.y.value().unwrap_or(Fq::zero());
    let x2_val = p2.x.value().unwrap_or(Fq::zero());
    let y2_val = p2.y.value().unwrap_or(Fq::zero());
    let s_val = if x2_val != x1_val {
        (y2_val - y1_val) * (x2_val - x1_val).inverse().unwrap()
    } else {
        Fq::zero()
    };
    let s = FqVar::new_witness(cs, || Ok(s_val))?;

    // Constraint 1: s * (x2 - x1) = (y2 - y1)
    let dx = &p2.x - &p1.x;
    let dy = &p2.y - &p1.y;
    let s_times_dx = &s * &dx;
    s_times_dx.enforce_equal(&dy)?;

    // Constraint 2: x3 = s^2 - x1 - x2
    let s_sq = &s * &s;
    let expected_x3 = &s_sq - &p1.x - &p2.x;
    result.x.enforce_equal(&expected_x3)?;

    // Constraint 3: y3 = s * (x1 - x3) - y1
    let x1_minus_x3 = &p1.x - &result.x;
    let s_times_diff = &s * &x1_minus_x3;
    let expected_y3 = &s_times_diff - &p1.y;
    result.y.enforce_equal(&expected_y3)?;

    Ok(result)
}

/// Point doubling using the tangent rule.
///
/// For BLS12-381 G1: y^2 = x^3 + 4, so the curve parameter a = 0.
///   s = 3*x1^2 / (2*y1)
///   x3 = s^2 - 2*x1
///   y3 = s * (x1 - x3) - y1
///
/// The prover supplies s as a witness; the circuit constrains:
///   1. s * (2 * y1) = 3 * x1^2
///   2. x3 = s^2 - 2*x1
///   3. y3 = s * (x1 - x3) - y1
pub fn point_double(
    cs: ConstraintSystemRef<Fr>,
    p: &PointVar,
    expected_result: G1Affine,
) -> Result<PointVar, SynthesisError> {
    let result = PointVar::new_witness(cs.clone(), expected_result)?;

    // Compute slope witness: s = 3*x^2 / (2*y)
    let x_val = p.x.value().unwrap_or(Fq::zero());
    let y_val = p.y.value().unwrap_or(Fq::zero());
    let three = Fq::from(3u64);
    let two = Fq::from(2u64);
    let s_val = if !y_val.is_zero() {
        (three * x_val * x_val) * (two * y_val).inverse().unwrap()
    } else {
        Fq::zero()
    };
    let s = FqVar::new_witness(cs, || Ok(s_val))?;

    // Constraint 1: s * (2 * y1) = 3 * x1^2
    let two_y = &p.y + &p.y;
    let s_times_2y = &s * &two_y;
    let x_sq = &p.x * &p.x;
    let three_x_sq = &x_sq + &x_sq + &x_sq;
    s_times_2y.enforce_equal(&three_x_sq)?;

    // Constraint 2: x3 = s^2 - 2*x1
    let s_sq = &s * &s;
    let two_x = &p.x + &p.x;
    let expected_x3 = &s_sq - &two_x;
    result.x.enforce_equal(&expected_x3)?;

    // Constraint 3: y3 = s * (x1 - x3) - y1
    let x_minus_x3 = &p.x - &result.x;
    let s_times_diff = &s * &x_minus_x3;
    let expected_y3 = &s_times_diff - &p.y;
    result.y.enforce_equal(&expected_y3)?;

    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_relations::r1cs::ConstraintSystem as ArkCS;

    #[test]
    fn test_point_add_circuit() {
        let p1 = G1Affine::generator();
        let scalar2 = Fr::from(42u64);
        let p2 = (G1Affine::generator() * scalar2).into_affine();

        // Expected sum
        let expected = (p1.into_group() + p2.into_group()).into_affine();

        let cs = ArkCS::<Fr>::new_ref();
        let p1_var = PointVar::new_witness(cs.clone(), p1).unwrap();
        let p2_var = PointVar::new_witness(cs.clone(), p2).unwrap();
        let result_var = point_add(cs.clone(), &p1_var, &p2_var, expected).unwrap();

        let expected_var = PointVar::new_witness(cs.clone(), expected).unwrap();
        result_var.enforce_equal(&expected_var).unwrap();

        assert!(
            cs.is_satisfied().unwrap(),
            "Point addition constraints not satisfied"
        );

        let num_constraints = cs.num_constraints();
        println!("Point addition constraints: {}", num_constraints);
        assert!(num_constraints > 0, "Should have some constraints");
    }

    #[test]
    fn test_point_double_circuit() {
        let p = G1Affine::generator();
        let expected = (p.into_group() + p.into_group()).into_affine();

        let cs = ArkCS::<Fr>::new_ref();
        let p_var = PointVar::new_witness(cs.clone(), p).unwrap();
        let result_var = point_double(cs.clone(), &p_var, expected).unwrap();

        let expected_var = PointVar::new_witness(cs.clone(), expected).unwrap();
        result_var.enforce_equal(&expected_var).unwrap();

        assert!(
            cs.is_satisfied().unwrap(),
            "Point doubling constraints not satisfied"
        );

        println!("Point doubling constraints: {}", cs.num_constraints());
    }
}
