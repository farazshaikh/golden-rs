module Ark_ec

open Rust_primitives

/// Curve trait operations:
/// - f_generator: returns the canonical generator point
/// - f_into_affine: converts Projective -> Affine

class t_AffineRepr (v_Self : Type0) = {
  f_generator_pre : unit -> Type0;
  f_generator_post : unit -> v_Self -> Type0;
  f_generator : x0: unit
    -> Prims.Pure v_Self (f_generator_pre x0) (fun result -> f_generator_post x0 result);
}

class t_CurveGroup (v_Self : Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method] f_Affine : Type0;
  f_into_affine_pre : v_Self -> Type0;
  f_into_affine_post : v_Self -> f_Affine -> Type0;
  f_into_affine : x0: v_Self
    -> Prims.Pure f_Affine (f_into_affine_pre x0) (fun result -> f_into_affine_post x0 result);
}

/// Instance: G1Affine has a generator
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_affine_repr_g1 :
  t_AffineRepr (Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config)

/// Instance: G1Projective can be converted to G1Affine
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_curve_group_g1 :
  t_CurveGroup (Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config)

/// f_into_group: converts Affine -> Projective (inverse of f_into_affine).
/// Specialized to BLS12-381 G1 since that's the only curve in use.
assume val f_into_group (#v_Self: Type0)
  (#[FStar.Tactics.Typeclasses.tcresolve ()] _inst: t_AffineRepr v_Self)
  (x: v_Self)
  : Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config

// ============================================================================
// Congruence axioms for opaque functions
// ============================================================================
//
// These state that into_affine, extract_x_as_scalar, and hash_to_curve
// are deterministic (congruent) functions. This is trivially true since
// they are pure Rust functions, but F* cannot deduce this for assume val
// declarations. Needed for the DH symmetry proof chain.

/// into_affine is congruent: same projective point -> same affine point.
/// Since f_into_affine is a typeclass method (assume val instance),
/// F* can't deduce congruence automatically.
assume val into_affine_congruent :
  p1:Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config ->
  p2:Ark_ec.Models.Short_weierstrass.Group.t_Projective Ark_bls12_381_.Curves.G1.t_Config ->
  Lemma (requires p1 == p2)
        (ensures f_into_affine p1 == f_into_affine p2)

/// DH commutativity at the affine level:
/// into_affine(pk_j * sk_i) == into_affine(pk_i * sk_j)
/// where pk_j = into_affine(g * sk_j) and pk_i = into_affine(g * sk_i).
/// Combines smul_field_comm with into_affine congruence.
assume val dh_affine_symmetric :
  sk_i:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) ->
  sk_j:Ark_ff.Fields.Models.Fp.t_Fp
    (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend
      Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4) ->
  g:Ark_ec.Models.Short_weierstrass.Affine.t_Affine Ark_bls12_381_.Curves.G1.t_Config ->
  Lemma (
    let pk_j = f_into_affine (Ark_ec.Models.Short_weierstrass.Group.affine_scalar_mul Ark_bls12_381_.Curves.G1.t_Config Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4) g sk_j) in
    let pk_i = f_into_affine (Ark_ec.Models.Short_weierstrass.Group.affine_scalar_mul Ark_bls12_381_.Curves.G1.t_Config Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4) g sk_i) in
    f_into_affine (Ark_ec.Models.Short_weierstrass.Group.affine_scalar_mul Ark_bls12_381_.Curves.G1.t_Config Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4) pk_j sk_i) ==
    f_into_affine (Ark_ec.Models.Short_weierstrass.Group.affine_scalar_mul Ark_bls12_381_.Curves.G1.t_Config Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4) pk_i sk_j))
