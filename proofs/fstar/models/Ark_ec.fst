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
