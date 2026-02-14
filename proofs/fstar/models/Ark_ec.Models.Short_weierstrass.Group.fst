module Ark_ec.Models.Short_weierstrass.Group

open Rust_primitives
open Core_models

/// Projective point on a short Weierstrass curve (X:Y:Z homogeneous coords).
/// In arkworks: `ark_ec::models::short_weierstrass::Projective<P>`.

assume new type t_Projective (config : Type0) : eqtype

/// Arithmetic instances for Projective points:

/// Projective + Projective (point addition)
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_proj_add (config : Type0) :
  Core_models.Ops.Arith.t_Add (t_Projective config) (t_Projective config)

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_proj_add_assign (config : Type0) :
  Core_models.Ops.Arith.t_AddAssign (t_Projective config) (t_Projective config)

/// Projective += Affine (mixed addition)
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_proj_add_assign_affine (config : Type0) :
  Core_models.Ops.Arith.t_AddAssign (t_Projective config) (Ark_ec.Models.Short_weierstrass.Affine.t_Affine config)

/// Projective - Projective (point subtraction)
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_proj_sub (config : Type0) :
  Core_models.Ops.Arith.t_Sub (t_Projective config) (t_Projective config)

/// Negation: -Projective
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_proj_neg (config : Type0) :
  Core_models.Ops.Arith.t_Neg (t_Projective config)

/// Scalar multiplication instances
open Ark_ff.Fields.Models.Fp
open Ark_ff.Fields.Models.Fp.Montgomery_backend

/// Affine * Scalar -> Projective
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_affine_scalar_mul (config : Type0) (fp_config : Type0) (n : usize) :
  Core_models.Ops.Arith.t_Mul
    (Ark_ec.Models.Short_weierstrass.Affine.t_Affine config)
    (t_Fp (t_MontBackend fp_config n) n)

/// Projective * Scalar
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_proj_scalar_mul (config : Type0) (fp_config : Type0) (n : usize) :
  Core_models.Ops.Arith.t_Mul
    (t_Projective config)
    (t_Fp (t_MontBackend fp_config n) n)

/// Projective *= Scalar
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_proj_scalar_mul_assign (config : Type0) (fp_config : Type0) (n : usize) :
  Core_models.Ops.Arith.t_MulAssign
    (t_Projective config)
    (t_Fp (t_MontBackend fp_config n) n)

/// Default for Projective (identity / point at infinity)
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_proj_default (config : Type0) :
  Core_models.Default.t_Default (t_Projective config)

/// PartialEq for Projective (point equality)
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_proj_partial_eq (config : Type0) :
  Core_models.Cmp.t_PartialEq (t_Projective config) (t_Projective config)
