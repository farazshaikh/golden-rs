module Ark_ec.Models.Short_weierstrass.Group

open Rust_primitives
open Core_models

/// Projective point on a short Weierstrass curve (X:Y:Z homogeneous coords).
/// In arkworks: `ark_ec::models::short_weierstrass::Projective<P>`.

assume new type t_Projective (config : Type0) : eqtype

/// Arithmetic instances for Projective points:

/// Projective + Projective (point addition)
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_proj_add_assign (config : Type0) :
  Core_models.Ops.Arith.t_AddAssign (t_Projective config) (t_Projective config)

/// Affine * Scalar -> Projective (scalar multiplication)
open Ark_ff.Fields.Models.Fp
open Ark_ff.Fields.Models.Fp.Montgomery_backend

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_affine_scalar_mul (config : Type0) (fp_config : Type0) (n : usize) :
  Core_models.Ops.Arith.t_Mul
    (Ark_ec.Models.Short_weierstrass.Affine.t_Affine config)
    (t_Fp (t_MontBackend fp_config n) n)

/// Default for Projective (identity / point at infinity)
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_proj_default (config : Type0) :
  Core_models.Default.t_Default (t_Projective config)

/// PartialEq for Projective (point equality)
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_proj_partial_eq (config : Type0) :
  Core_models.Cmp.t_PartialEq (t_Projective config) (t_Projective config)
