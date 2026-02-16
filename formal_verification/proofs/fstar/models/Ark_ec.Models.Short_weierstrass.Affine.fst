module Ark_ec.Models.Short_weierstrass.Affine

open Rust_primitives
open Ark_ff.Fields.Models.Fp
open Ark_ff.Fields.Models.Fp.Montgomery_backend

/// Affine point on a short Weierstrass curve.
/// Record type so F* can use `.f_infinity` and `.f_x` field access syntax.
///
/// The base field coordinates use Fq (6 limbs) matching BLS12-381.
/// The `config` parameter identifies the curve but doesn't affect the field types.

type t_Affine (config : Type0) = {
  f_x : t_Fp (t_MontBackend Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6);
  f_y : t_Fp (t_MontBackend Ark_bls12_381_.Fields.Fq.t_FqConfig (mk_usize 6)) (mk_usize 6);
  f_infinity : bool;
}

/// Default instance (point at infinity)
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_affine_default (config : Type0) : Core_models.Default.t_Default (t_Affine config)

/// PartialEq instance
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_affine_partial_eq (config : Type0) : Core_models.Cmp.t_PartialEq (t_Affine config) (t_Affine config)
