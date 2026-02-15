module Golden_dkg.Refresh.Spec

/// F* Specification Bridge for Key Refresh Protocol
///
/// This module states the correctness properties of the extracted refresh
/// implementation, mirroring the Lean 4 theorems in RefreshCorrectness.lean.
///
/// Key refresh (Section 5.2) rotates shares without changing the secret.
/// Each participant generates a "zero-sharing" (polynomial with f(0)=0)
/// and adds it to their share. The secret is preserved because the sum
/// of zero-sharings is zero under Lagrange interpolation.

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives
open Core_models

/// Type aliases
let scalar = Ark_ff.Fields.Models.Fp.t_Fp
  (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
    Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)

let g1_affine = Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config

// ============================================================================
// Specification predicates
// ============================================================================

/// The polynomial has constant term equal to zero (zero-sharing).
/// Made concrete: coefficients[0] == fp_from_u64(0).
let is_zero_sharing (poly: Golden_dkg.Shamir.t_Polynomial) : prop =
  let s = Alloc.Vec.Vec?._0 poly.Golden_dkg.Shamir.f_coefficients in
  Seq.length s > 0 /\
  Seq.index s 0 == Ark_ff.Fields.Models.Fp.fp_from_u64 (mk_u64 0)

/// The Lagrange-weighted sum of deltas is zero.
assume val zero_sharing_sum_vanishes :
  (#n:nat) -> (lagrange_coeffs: (i:nat{i < n}) -> scalar) ->
  (deltas: (i:nat{i < n}) -> scalar) -> prop

/// Two scalars are equal (secret preserved).
assume val secret_preserved : scalar -> scalar -> prop

// ============================================================================
// Lemma 1: Zero-Sharing Polynomial Vanishes Under Interpolation
//
// Lean theorem: zero_polynomial_vanishes (RefreshCorrectness.lean)
// Paper reference: Section 5.2
//   "If f(0) = 0 and deg(f) < t, then Lagrange interpolation of
//    f's evaluations at 0 gives 0."
//
// What it protects against:
//   SECRET DRIFT -- if zero-sharings don't vanish, the aggregated
//   delta at the secret level would be nonzero, changing sk to sk + delta.
//   The shared public key PK = g^sk would no longer match the shares.
//
// STATUS: CLOSED (Phase 3 -- chains shamir_roundtrip_correct with is_zero_sharing)
// ENSURES: REAL (not True) -- states that interpolation returns fp_from_u64(0)
//
// PROOF: Specialization of shamir_roundtrip_correct to secret=0:
//   1. shamir_roundtrip_correct poly n  =>  interpolation == poly_constant_term poly
//   2. is_zero_sharing poly             =>  poly_constant_term poly == fp_from_u64 0
//   3. Transitivity                     =>  interpolation == fp_from_u64 0
// ============================================================================

val zero_sharing_vanishes :
  poly: Golden_dkg.Shamir.t_Polynomial ->
  n: u32 ->
  Pure unit
    (requires is_zero_sharing poly /\ n >. mk_u32 0)
    (ensures fun _ ->
      // Lagrange interpolation of zero-sharing evaluations at 0 gives 0.
      // This ensures is REAL: it states the interpolation result equals
      // fp_from_u64(0), which is the concrete field zero.
      let shares = Golden_dkg.Shamir.generate_shares poly n in
      Golden_dkg.Shamir.lagrange_interpolate_at_zero
        (Alloc.Vec.impl_1__as_slice shares) ==
      Ark_ff.Fields.Models.Fp.fp_from_u64 (mk_u64 0))

let zero_sharing_vanishes poly n =
  // Step 1: shamir_roundtrip_correct gives us:
  //   lagrange_interpolate_at_zero(generate_shares(poly, n)) == poly_constant_term(poly)
  Golden_dkg.Shamir.Spec.shamir_roundtrip_correct poly n;
  // Step 2: is_zero_sharing tells us coefficients[0] == fp_from_u64 0.
  //   poly_constant_term extracts coefficients[0] (= Seq.index s 0),
  //   and is_zero_sharing guarantees this equals fp_from_u64 0.
  //   Transitivity: interpolation == poly_constant_term poly == fp_from_u64 0.
  ()

// ============================================================================
// Lemma 2: Refresh Preserves the Secret
//
// Lean theorem: refresh_preserves_secret (RefreshCorrectness.lean)
// Paper reference: Section 5.2
//   "sum L_i * (sk_i + delta_i) = sum L_i * sk_i  when  sum L_i * delta_i = 0"
//
// What it protects against:
//   UNRECOVERABLE KEY CORRUPTION -- this is the fundamental refresh
//   invariant. If it fails, the refreshed shares reconstruct a DIFFERENT
//   secret than the original. Since no single party knows sk, there is
//   no way to recover -- the key is permanently lost.
//
//   This is the #1 most dangerous failure mode in the entire protocol.
// ============================================================================

/// Refresh preserves the secret (n=2 concrete case):
///   sum L_i * (sk_i + delta_i) = sum L_i * sk_i
///   when sum L_i * delta_i = 0 (zero-sharing condition).
val refresh_preserves_secret :
  l0:scalar -> l1:scalar ->
  sk0:scalar -> sk1:scalar ->
  delta0:scalar -> delta1:scalar ->
  Lemma
    (requires
      Ark_ff.Fields.Models.Fp.fp_add
        (Ark_ff.Fields.Models.Fp.fp_mul l0 delta0)
        (Ark_ff.Fields.Models.Fp.fp_mul l1 delta1) ==
      Ark_ff.Fields.Models.Fp.fp_from_u64 (mk_u64 0))
    (ensures
      Ark_ff.Fields.Models.Fp.fp_add
        (Ark_ff.Fields.Models.Fp.fp_mul l0 (Ark_ff.Fields.Models.Fp.fp_add sk0 delta0))
        (Ark_ff.Fields.Models.Fp.fp_mul l1 (Ark_ff.Fields.Models.Fp.fp_add sk1 delta1)) ==
      Ark_ff.Fields.Models.Fp.fp_add
        (Ark_ff.Fields.Models.Fp.fp_mul l0 sk0)
        (Ark_ff.Fields.Models.Fp.fp_mul l1 sk1))

let refresh_preserves_secret l0 l1 sk0 sk1 delta0 delta1 =
  let open Ark_ff.Fields.Models.Fp in
  fp_mul_dist l0 sk0 delta0;
  fp_mul_dist l1 sk1 delta1;
  let a = fp_mul l0 sk0 in
  let b = fp_mul l0 delta0 in
  let c = fp_mul l1 sk1 in
  let d = fp_mul l1 delta1 in
  fp_add_assoc a b (fp_add c d);
  fp_add_assoc b c d;
  fp_add_comm b c;
  fp_add_assoc c b d;
  fp_add_assoc a c (fp_add b d);
  fp_add_zero (fp_add a c)

// ============================================================================
// Lemma 3: Refresh Does Not Change the Public Key
//
// Lean theorem: refresh_pk_unchanged (RefreshCorrectness.lean)
// Paper reference: Section 5.2
//   "If all omega_j = 0, then sum omega_j * g = 0"
//
// What it protects against:
//   PUBLIC KEY MISMATCH -- if the public key changes after refresh,
//   external verifiers (who only know PK) would reject valid signatures
//   produced by the refreshed key shares.
// ============================================================================

val refresh_pk_unchanged :
  omega0: scalar -> omega1: scalar ->
  g: Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config ->
  Lemma
    (requires
      omega0 == Ark_ff.Fields.Models.Fp.fp_from_u64 (mk_u64 0) /\
      omega1 == Ark_ff.Fields.Models.Fp.fp_from_u64 (mk_u64 0))
    (ensures
      Ark_ec.Models.Short_weierstrass.Group.g1_add
        (Ark_ec.Models.Short_weierstrass.Group.smul omega0 g)
        (Ark_ec.Models.Short_weierstrass.Group.smul omega1 g) ==
      Ark_ec.Models.Short_weierstrass.Group.g1_zero)

let refresh_pk_unchanged omega0 omega1 g =
  // omega0 = 0, so smul(0, g) = g1_zero by smul_zero
  Ark_ec.Models.Short_weierstrass.Group.smul_zero g;
  // omega1 = 0, so smul(0, g) = g1_zero by smul_zero
  Ark_ec.Models.Short_weierstrass.Group.smul_zero g;
  // g1_zero + g1_zero = g1_zero by ec_add_zero_r
  Ark_ec.Models.Short_weierstrass.Group.ec_add_zero_r
    Ark_ec.Models.Short_weierstrass.Group.g1_zero

// ============================================================================
// Lemma 4: Refresh Actually Changes the Shares
//
// Lean theorem: refresh_shares_changed (RefreshCorrectness.lean)
// Paper reference: Section 5.2
//   "If delta != 0, then sk_old + delta != sk_old"
//
// What it protects against:
//   PROACTIVE SECURITY FAILURE -- the whole point of refresh is that
//   old shares become useless. If shares don't actually change, an
//   adversary who compromised shares before the refresh can still use
//   them after, defeating proactive security.
// ============================================================================

val refresh_shares_changed :
  sk_old: scalar -> delta: scalar ->
  Lemma
    (requires delta =!= Ark_ff.Fields.f_ZERO #FStar.Tactics.Typeclasses.solve)
    (ensures
      // sk_old + delta != sk_old
      Ark_ff.Fields.Models.Fp.fp_add sk_old delta =!= sk_old)

let refresh_shares_changed sk_old delta =
  // Proof by contradiction: if sk + delta == sk, then delta == 0.
  // (sk + delta) - sk == delta  by fp_add_sub_cancel
  // sk - sk == 0               by fp_sub_self
  // So delta == 0, contradicting the precondition.
  Ark_ff.Fields.Models.Fp.fp_add_sub_cancel sk_old delta
