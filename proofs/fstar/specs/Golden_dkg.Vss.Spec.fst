module Golden_dkg.Vss.Spec

/// F* Specification Bridge for Feldman VSS
///
/// This module states the correctness properties of the extracted VSS
/// implementation, mirroring the Lean 4 theorems in VSSCorrectness.lean.
///
/// Feldman VSS is the binding mechanism that prevents a malicious dealer
/// from distributing inconsistent shares. If verify_share passes for all
/// recipients, the shares are guaranteed to lie on the committed polynomial.

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives
open Core_models

/// Type aliases
let scalar = Ark_ff.Fields.Models.Fp.t_Fp
  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)

let g1_affine = Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config

let g1_projective = Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config

// ============================================================================
// Lemma 1: VSS Completeness -- honest shares always verify
//
// Lean theorem: feldman_vss_completeness (VSSCorrectness.lean)
// Paper reference: Section 3.4, VSS.Verify
//   "g^{f(j)} == product_{k=0}^{t-1} (C_k)^{j^k}"
//
// What it protects against:
//   FALSE REJECTION -- if verify_share incorrectly rejects honest shares,
//   the DKG protocol cannot complete. This lemma ensures that shares
//   produced by an honest dealer always pass verification.
//
// STATUS: ADMITTED (universally quantified -- cannot close with fuel)
// ENSURES: REAL (not True) -- states that verify_share returns true for
//   honestly-generated shares.
//
// BLOCKER: Both `commit` and `verify_share` use fold_range over the
//   polynomial's coefficients. The ensures requires showing that:
//     sum(C_k * x^k) == g * f(x)  where C_k = g * a_k
//   This is distributivity of scalar multiplication over group addition:
//     sum(g * a_k * x^k) == g * sum(a_k * x^k)
//   Even with fuel to unroll fold_range for small n, this is an algebraic
//   identity over SYMBOLIC field and group elements, not a computational
//   check. The proof requires EC group axioms (smul_add_scalar) applied
//   inductively at each loop step -- i.e., a loop invariant.
//
//   Restricted to Seq.length coefficients <= 5 to enable future
//   case-by-case proofs (as done for Shamir (2,2) and (3,3)).
//
// CONSTANT-POLYNOMIAL CASE (n=1):
//   For a single-coefficient polynomial [a0]:
//     commit produces [into_affine(smul(a0, g))]  (1 commitment element)
//     verify_share computes:
//       expected = Default + smul(a0*g, x^0=1) = 0 + smul(a0*g, 1) = a0*g
//       actual   = smul(a0, g)    (since evaluate [a0] at x = a0)
//     So expected == actual iff smul distributes correctly over into_affine.
//   This still requires reasoning through fold_range (commit builds Vec
//   via push) and proving into_affine/from_affine round-trips, which are
//   blocked by the same loop invariant issue plus affine<->projective
//   conversion opaqueness.
//
// CONCRETE EVIDENCE: ciphertext_check_identity (proved) demonstrates the
//   key algebraic identity smul(a+b, g) == g1_add(smul(a,g), smul(b,g))
//   which is the core of the inductive step.
// ============================================================================

val verify_share_completeness :
  poly: Golden_dkg.Shamir.t_Polynomial ->
  index: u32 ->
  Pure unit
    (requires
      index >. mk_u32 0 /\
      Seq.length (Alloc.Vec.Vec?._0 poly.Golden_dkg.Shamir.f_coefficients) <= 5)
    (ensures fun _ ->
      let commitment = Golden_dkg.Vss.commit poly in
      let commitment_slice = Alloc.Vec.impl_1__as_slice commitment in
      let share = Golden_dkg.Shamir.impl_Polynomial__evaluate poly
        (Core_models.Convert.f_from #scalar #u64 #FStar.Tactics.Typeclasses.solve
          (cast (index <: u32) <: u64)) in
      Golden_dkg.Vss.verify_share commitment_slice index share == true)

#push-options "--fuel 10 --ifuel 4 --z3rlimit 600"
let verify_share_completeness poly index =
  // To close for n=1 (constant polynomial [a0]):
  //   1. Unroll commit's fold_range(0, 1, ...) to get [into_affine(smul(a0, g))]
  //   2. Unroll verify_share's fold_range(0, 1, ...) to get
  //      expected = proj_default + smul(commitment[0], x^0=1)
  //   3. Show proj_default + smul(C0, 1) == smul(C0, 1)  [by ec_add_zero identity]
  //   4. Show smul(a0, g) == actual = smul(evaluate([a0], x), g)
  //   5. Need into_affine(smul(a0,g)) roundtrip + evaluate_constant_poly
  //
  // Steps 1-3 require fold_range unrolling through the commit/verify_share
  // extracted code, which uses typeclass dispatch (f_mul -> smul via impl).
  // Steps 4-5 require affine<->projective conversion axioms.
  // Both are blocked by opaque typeclass resolution across modules.
  admit ()
#pop-options

// ============================================================================
// Lemma 2: VSS Expected Share Commitment
//
// Lean theorem: vss_expected_eq_eval_smul (VSSCorrectness.lean)
// Paper reference: Section 3.4
//   "expected_share_commitment(C, j) = f(j) * g"
//
// What it protects against:
//   COMMITMENT FORGERY -- ensures the algebraic relationship between
//   the commitment vector and share values is correct. If this fails,
//   a malicious dealer could produce commitments that pass verification
//   for inconsistent shares.
//
// STATUS: ADMITTED (universally quantified -- same algebraic blocker)
// ENSURES: REAL (not True) -- states that expected_share_commitment equals
//   into_affine(smul(share, generator)). This is the strongest possible
//   ensures, connecting the group-level commitment computation to the
//   field-level share evaluation.
//
// BLOCKER: The expected_share_commitment function computes
//     result = sum_{k=0}^{n-1} C_k * x^k   (group operation)
//   and the claim is that this equals smul(share, generator) where
//     share = sum_{k=0}^{n-1} a_k * x^k     (field operation)
//   With C_k = smul(a_k, generator) (from commit), the identity is:
//     sum(smul(a_k, g) * x^k) == smul(sum(a_k * x^k), g)
//   This requires the EC module axiom (smul distributes over group add)
//   applied at each loop iteration -- a loop invariant, not fuel.
//
//   Concrete form: uses smul from the group model instead of abstract
//   is_scalar_mul_generator. into_affine is still opaque (the commitment
//   is stored in affine form after conversion from projective).
//
//   Restricted to Seq.length coefficients <= 5.
//
// CONSTANT-POLYNOMIAL CASE (n=1):
//   For [a0]:
//     commit produces [into_affine(smul(a0, g))]
//     expected_share_commitment computes:
//       result = Default + smul(commitment[0], x^0=1)
//              = g1_zero + smul(into_affine(smul(a0, g)), 1)
//     share = evaluate [a0] at x = a0  (by evaluate_constant_poly)
//     Need: g1_zero + smul(into_affine(smul(a0,g)), 1)
//           == into_affine(smul(a0, g))
//   This requires into_affine/from_affine roundtrip axioms and
//   ec_add_zero identity -- blocked by the same opaqueness as Lemma 1.
//
// CONCRETE EVIDENCE: smul_add_scalar (axiom) proves the core inductive
//   step: smul(a+b, P) == g1_add(smul(a, P), smul(b, P)).
// ============================================================================

open Ark_ec.Models.Short_weierstrass.Group

val expected_share_commitment_correct :
  poly: Golden_dkg.Shamir.t_Polynomial ->
  index: u32 ->
  Pure unit
    (requires
      index >. mk_u32 0 /\
      Seq.length (Alloc.Vec.Vec?._0 poly.Golden_dkg.Shamir.f_coefficients) <= 5)
    (ensures fun _ ->
      let commitment = Golden_dkg.Vss.commit poly in
      let commitment_slice = Alloc.Vec.impl_1__as_slice commitment in
      let share = Golden_dkg.Shamir.impl_Polynomial__evaluate poly
        (Core_models.Convert.f_from #scalar #u64 #FStar.Tactics.Typeclasses.solve
          (cast (index <: u32) <: u64)) in
      let expected = Golden_dkg.Vss.expected_share_commitment commitment_slice index in
      let g : g1_affine = Ark_ec.f_generator #g1_affine #FStar.Tactics.Typeclasses.solve () in
      // expected == into_affine(smul(share, g))
      // i.e., the expected commitment is the generator scaled by the share value
      expected == Ark_ec.f_into_affine #g1_projective #FStar.Tactics.Typeclasses.solve
        (smul share g))

#push-options "--fuel 10 --ifuel 4 --z3rlimit 600"
let expected_share_commitment_correct poly index =
  // To close for n=1 (constant polynomial [a0]):
  //   1. Unroll commit's fold_range(0, 1, ...):
  //      commitments = [into_affine(smul(a0, g))]
  //   2. Unroll expected_share_commitment's fold_range(0, 1, ...):
  //      result = proj_default + smul(commitment[0], x_pow=1)
  //             = g1_zero + smul(into_affine(smul(a0, g)), 1)
  //   3. By ec_add_zero: g1_zero + P == P
  //   4. By smul_one or scalar identity: smul(P, 1) == to_proj(P)
  //   5. Need into_affine/to_proj roundtrip axioms
  //
  // For general n: need inductive argument using smul_add_scalar:
  //   At step k: result_k = sum_{i=0}^{k-1} smul(a_i * x^i, g)
  //            = smul(sum_{i=0}^{k-1} a_i * x^i, g)
  //   Adding step k: result_{k+1} = result_k + smul(a_k * x^k, g)
  //                = smul(prev_sum + a_k*x^k, g)  [by smul_add_scalar]
  //   This is exactly the loop invariant, but hax emits trivial invariant.
  admit ()
#pop-options

// ============================================================================
// Lemma 3: Ciphertext Check Identity
//
// Lean theorem: golden_ciphertext_check (VSSCorrectness.lean)
// Paper reference: Round 1, line 12 of Figure 4
//   "(r + share) * g = r * g + share * g"
//
// What it protects against:
//   DECRYPTION VERIFICATION FAILURE -- Round 1 checks that the decrypted
//   share is consistent with the VSS commitment by verifying
//   z * g == R + share_commitment. This identity must hold for honest shares.
// ============================================================================

val ciphertext_check_identity :
  r_pad: scalar ->
  share: scalar ->
  g: g1_affine ->
  Lemma
    (ensures
      // (r + share) * g == r * g + share * g
      // Distributivity of scalar multiplication over field addition.
      Ark_ec.Models.Short_weierstrass.Group.smul
        (Ark_ff.Fields.Models.Fp.fp_add r_pad share) g ==
      Ark_ec.Models.Short_weierstrass.Group.g1_add
        (Ark_ec.Models.Short_weierstrass.Group.smul r_pad g)
        (Ark_ec.Models.Short_weierstrass.Group.smul share g))

let ciphertext_check_identity r_pad share g =
  Ark_ec.Models.Short_weierstrass.Group.smul_add_scalar r_pad share g
