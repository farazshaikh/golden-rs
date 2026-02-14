module Golden_dkg.Shamir.Spec

/// F* Specification Bridge for Shamir Secret Sharing
///
/// Phase 1 used `admit()` for all lemma bodies.
/// Phase 2 (this file):
///   - Proved 3 concrete lemmas WITHOUT admit (real proofs)
///   - Documented precise blockers for the remaining admits
///   - Added field axiom framework to the model files
///
/// The key Phase 2 change was replacing `assume val` typeclass instances
/// in Ark_ff.Fields.Models.Fp with concrete `let` definitions. This makes
/// `f_Output = t_Fp config n` visible to the type checker, which is required
/// for any proof that reasons through field arithmetic expressions.

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
assume val poly_eval_at :
  Golden_dkg.Shamir.t_Polynomial -> scalar -> scalar -> prop

/// The constant term of a polynomial (the secret).
assume val poly_constant_term :
  Golden_dkg.Shamir.t_Polynomial -> scalar

/// Shares are valid evaluations.
assume val shares_are_valid_evaluations :
  Golden_dkg.Shamir.t_Polynomial -> t_Slice share_t -> prop

/// Node IDs in the shares are distinct and nonzero.
assume val shares_have_distinct_ids :
  t_Slice share_t -> prop

/// The polynomial has degree < n.
assume val poly_degree_lt :
  Golden_dkg.Shamir.t_Polynomial -> nat -> prop

// ============================================================================
// Lemma 1: lagrange_interpolate_at_zero is correct
//
// STATUS: ADMITTED
// BLOCKER: Requires reasoning through double-nested fold_enumerated_slice
//   (outer loop over shares, inner loop computing Lagrange basis).
//   fold_enumerated_slice is an `assume val` (not a `let`), so F* cannot
//   unfold it. The invariant in the extracted code is `(fun _ _ -> true)`
//   (trivially true), giving zero information about the accumulator.
//   Proving this requires either:
//     (a) Hax emitting meaningful loop invariants (inv tracks partial sum)
//     (b) Defining fold_enumerated_slice as a concrete recursive function
//     (c) Proving a separate lemma about fold_enumerated_slice behavior
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
// STATUS: ADMITTED
// BLOCKER: Same fold_range invariant issue. The extracted code uses trivial
//   invariants. Also requires concrete definitions of shares_are_valid_evaluations
//   and shares_have_distinct_ids (currently abstract assume val predicates).
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
// STATUS: ADMITTED
// BLOCKER: Requires (a) concrete definition of poly_eval_at relating
//   mathematical polynomial evaluation to the Horner loop, and (b) a loop
//   invariant on fold_range tracking the partial Horner accumulator.
//   Cross-module definition unfolding of impl_Polynomial__evaluate also
//   fails -- F* does not automatically unfold definitions from other modules
//   at the depth needed to expose the fold_range body.
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
// STATUS: ADMITTED
// BLOCKER: Depends on Lemmas 1-3 above.
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

// ============================================================================
// ============================================================================
//
//   PHASE 2 PROVED LEMMAS (NO ADMITS)
//
//   The following lemmas are fully proved, demonstrating that the axiom
//   framework works for concrete reasoning about the extracted code.
//
// ============================================================================
// ============================================================================

open Ark_ff.Fields.Models.Fp

// ============================================================================
// Proved Lemma A: Empty polynomial evaluates to zero
//
// This proves that fold_range with 0 iterations returns init unchanged.
// The extracted code initializes result = Scalar::from(0u64), and when
// the coefficient vector is empty (n=0), the fold returns that initial value.
//
// PROOF TECHNIQUE: F* unfolds fold_range(0, 0, ...) -> init by definition.
// ============================================================================

val evaluate_empty_poly :
  x:scalar ->
  Lemma
    (let empty_poly : Golden_dkg.Shamir.t_Polynomial =
       { Golden_dkg.Shamir.f_coefficients =
           Alloc.Vec.impl__new #scalar () } in
     Golden_dkg.Shamir.impl_Polynomial__evaluate empty_poly x ==
       Core_models.Convert.f_from #scalar #u64 #FStar.Tactics.Typeclasses.solve (mk_u64 0))

#push-options "--fuel 1 --ifuel 2 --z3rlimit 50"
let evaluate_empty_poly x = ()
#pop-options

// ============================================================================
// Proved Lemma B: Polynomial degree is len - 1
//
// Purely structural property of the t_Polynomial type.
// ============================================================================

val degree_is_len_minus_one :
  poly:Golden_dkg.Shamir.t_Polynomial ->
  Lemma
    (requires Alloc.Vec.impl_1__len poly.Golden_dkg.Shamir.f_coefficients >. mk_usize 0)
    (ensures Golden_dkg.Shamir.impl_Polynomial__degree poly ==
             Alloc.Vec.impl_1__len poly.Golden_dkg.Shamir.f_coefficients -! mk_usize 1)

let degree_is_len_minus_one poly = ()

// ============================================================================
// Proved Lemma C: Field axiom -- 0*x + c == c
//
// Uses the field axioms from Ark_ff.Fields.Models.Fp to prove:
//   fp_add(fp_mul(fp_from_u64(0), x), c) == c
//
// This is the key algebraic step needed for the constant-polynomial case
// of Horner evaluation. It demonstrates that the axiom framework supports
// real algebraic reasoning.
//
// PROOF TECHNIQUE: Chain of field axiom applications:
//   1. fp_mul_zero_l: 0 * x == 0
//   2. fp_add_comm: 0 + c == c + 0
//   3. fp_add_zero: c + 0 == c
// ============================================================================

val zero_mul_x_plus_c_eq_c :
  c:scalar -> x:scalar ->
  Lemma (fp_add (fp_mul (fp_from_u64 (mk_u64 0)) x) c == c)

let zero_mul_x_plus_c_eq_c c x =
  fp_mul_zero_l x;
  fp_add_comm (fp_from_u64 (mk_u64 0)) c;
  fp_add_zero c

// ============================================================================
// Proved Lemma D: Horner evaluation of single-coefficient polynomial
//
// When the coefficient vector is [c] (one element), Horner's method computes:
//   init = from(0)
//   iteration 0: result = f_add(f_mul(init, x), c[0]) = add(mul(0, x), c)
//
// This proves that fold_range with 1 iteration correctly applies the body.
// Combined with Lemma C, this shows evaluate([c], x) == c for any x.
//
// NOTE: This uses a LOCAL copy of the Horner loop (same logic as
// impl_Polynomial__evaluate) because F* does not unfold cross-module
// definitions deeply enough. The proof that this local definition matches
// the extraction would require F* to normalize both to the same term.
//
// PROOF TECHNIQUE: F* unfolds fold_range(0, 1, ...) = body(init, 0).
// ============================================================================

/// Local Horner evaluation matching the extracted code's logic.
let horner_eval (coeffs : Alloc.Vec.t_Vec scalar Alloc.Alloc.t_Global) (x : scalar) : scalar =
  let result : scalar = fp_from_u64 (mk_u64 0) in
  let n : usize = Alloc.Vec.impl_1__len coeffs in
  Rust_primitives.Hax.Folds.fold_range (mk_usize 0) n
    (fun (result:scalar)
         (_:usize{Rust_primitives.Hax.Folds.fold_range_wf_index (mk_usize 0) n false (v _)}) ->
       True)
    result
    (fun (result:scalar)
         (idx:usize{v idx <= v n /\
                    Rust_primitives.Hax.Folds.fold_range_wf_index (mk_usize 0) n true (v idx) /\
                    True}) ->
       fp_add (fp_mul result x)
              (Rust_primitives.Sequence.seq_index
                (Alloc.Vec.Vec?._0 coeffs)
                ((n -! mk_usize 1) -! idx)))

/// Horner evaluation of [c] at any x gives fp_add(fp_mul(0, x), c).
val horner_eval_one_step :
  c:scalar -> x:scalar ->
  Lemma (
    let coeffs = Alloc.Vec.impl_1__push #scalar #Alloc.Alloc.t_Global
                   (Alloc.Vec.impl__new #scalar ()) c in
    horner_eval coeffs x == fp_add (fp_mul (fp_from_u64 (mk_u64 0)) x) c)

#push-options "--fuel 3 --ifuel 3 --z3rlimit 200"
let horner_eval_one_step c x = ()
#pop-options

/// Combining D and C: Horner evaluation of [c] at any x equals c.
val horner_eval_constant :
  c:scalar -> x:scalar ->
  Lemma (
    let coeffs = Alloc.Vec.impl_1__push #scalar #Alloc.Alloc.t_Global
                   (Alloc.Vec.impl__new #scalar ()) c in
    horner_eval coeffs x == c)

let horner_eval_constant c x =
  horner_eval_one_step c x;
  zero_mul_x_plus_c_eq_c c x
