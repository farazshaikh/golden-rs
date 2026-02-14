module Golden_dkg.Shamir.Spec

/// F* Specification Bridge for Shamir Secret Sharing
///
/// This module states the correctness properties of the extracted Shamir
/// implementation, mirroring the Lean 4 theorems in ShamirCorrectness.lean.
///
/// Each lemma here corresponds to a Lean theorem with the same algebraic
/// meaning. Phase 1 uses `admit()` for bodies (type-checked in --lax mode).
/// Phase 2 will replace `admit()` with actual F* proofs.

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives
open Core_models

/// Type alias for the BLS12-381 scalar field element (Fr).
let scalar = Ark_ff.Fields.Models.Fp.t_Fp
  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)

/// Type alias for a share: (node_id, share_value).
let share_t = (u32 & scalar)

/// Type alias for G1 affine point.
let g1_affine = Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config

// ============================================================================
// Specification predicates (abstract -- axiomatized for Phase 1)
// ============================================================================

/// A polynomial evaluates to `y` at field element `x`.
/// Mirrors Lean's `f.eval (v i)`.
assume val poly_eval_at :
  Golden_dkg.Shamir.t_Polynomial -> scalar -> scalar -> prop

/// The constant term of a polynomial (the secret).
/// Mirrors Lean's `f.eval 0`.
assume val poly_constant_term :
  Golden_dkg.Shamir.t_Polynomial -> scalar

/// Shares are valid evaluations: each (id, y) satisfies y = poly(Scalar::from(id)).
assume val shares_are_valid_evaluations :
  Golden_dkg.Shamir.t_Polynomial -> t_Slice share_t -> prop

/// Node IDs in the shares are distinct and nonzero.
assume val shares_have_distinct_ids :
  t_Slice share_t -> prop

/// The polynomial has degree < n (the number of shares).
assume val poly_degree_lt :
  Golden_dkg.Shamir.t_Polynomial -> nat -> prop

// ============================================================================
// Lemma 1: lagrange_interpolate_at_zero is correct
//
// Lean theorem: shamir_reconstruction (ShamirCorrectness.lean)
// Paper reference: Section 3.3, Recover(t, {(i, x_bar_i)})
//   "x = sum_{i in C} x_bar_i * L_i(0)
//    where L_i(0) = product_{j in C, j != i} j / (j - i)"
//
// What it protects against:
//   SECRET CORRUPTION -- if this is wrong, the reconstructed secret sk
//   would differ from the original, making the shared key unusable.
//   Any t honest participants must recover the exact same sk.
// ============================================================================

val lagrange_interpolate_at_zero_correct :
  poly: Golden_dkg.Shamir.t_Polynomial ->
  shares: t_Slice share_t ->
  Pure unit
    (requires
      shares_are_valid_evaluations poly shares /\
      shares_have_distinct_ids shares /\
      poly_degree_lt poly (Seq.length shares))
    (ensures fun _ ->
      Golden_dkg.Shamir.lagrange_interpolate_at_zero shares ==
      poly_constant_term poly)

let lagrange_interpolate_at_zero_correct poly shares = admit ()

// ============================================================================
// Lemma 2: generate_shares produces valid evaluations
//
// Lean theorem: golden_node_ids_injective (ShamirCorrectness.lean)
// Paper reference: Section 3.3, Share(x, n, t)
//   "Each share x_bar_i = f(i) for i in [n]"
//
// What it protects against:
//   DUPLICATE EVALUATION POINTS -- if two nodes get shares at the same
//   point, Lagrange interpolation fails (division by zero). This lemma
//   ensures node IDs {1, ..., n} map to distinct field elements.
// ============================================================================

val generate_shares_valid :
  poly: Golden_dkg.Shamir.t_Polynomial ->
  n: u32 ->
  Pure unit
    (requires n >. mk_u32 0)
    (ensures fun _ ->
      let shares = Golden_dkg.Shamir.generate_shares poly n in
      shares_have_distinct_ids (Alloc.Vec.impl_1__as_slice shares) /\
      shares_are_valid_evaluations poly (Alloc.Vec.impl_1__as_slice shares))

let generate_shares_valid poly n = admit ()

// ============================================================================
// Lemma 3: Polynomial evaluation via Horner's method is correct
//
// Lean theorem: shamir_interpolation_exact_everywhere (ShamirCorrectness.lean)
// Paper reference: Section 3.3
//
// What it protects against:
//   INCORRECT SHARE COMPUTATION -- if evaluate() computes wrong values,
//   shares won't lie on the polynomial, breaking reconstruction.
// ============================================================================

val polynomial_evaluate_correct :
  poly: Golden_dkg.Shamir.t_Polynomial ->
  x: scalar ->
  y: scalar ->
  Pure unit
    (requires poly_eval_at poly x y)
    (ensures fun _ ->
      Golden_dkg.Shamir.impl_Polynomial__evaluate poly x == y)

let polynomial_evaluate_correct poly x y = admit ()

// ============================================================================
// Lemma 4: The complete Shamir correctness chain
//
// Lean theorem: golden_dkg_shamir_correct (ShamirCorrectness.lean)
// Paper reference: Section 3.3 -- the full Share -> Recover roundtrip
//
// What it protects against:
//   END-TO-END FAILURE -- even if individual functions are correct,
//   composition could fail. This lemma states the complete property:
//   generate t shares, take any t of them, reconstruct -> get the secret.
// ============================================================================

val shamir_roundtrip_correct :
  poly: Golden_dkg.Shamir.t_Polynomial ->
  n: u32 ->
  Pure unit
    (requires
      n >. mk_u32 0 /\
      poly_degree_lt poly (Rust_primitives.Integers.v (cast n <: usize)))
    (ensures fun _ ->
      let all_shares = Golden_dkg.Shamir.generate_shares poly n in
      Golden_dkg.Shamir.lagrange_interpolate_at_zero
        (Alloc.Vec.impl_1__as_slice all_shares) ==
      poly_constant_term poly)

let shamir_roundtrip_correct poly n = admit ()
