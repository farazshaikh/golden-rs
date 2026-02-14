module Ark_ff.Fields

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives
open Core_models

/// The arkworks Field trait, providing field-specific operations
/// beyond the standard Rust arithmetic operators.
///
/// The key operation for Shamir/VSS is `inverse()`, which computes
/// the multiplicative inverse of a field element (returns None for zero).
///
/// In the extracted code, this appears as:
///   Ark_ff.Fields.f_inverse #(t_Fp ...) #FStar.Tactics.Typeclasses.solve x

class t_Field (v_Self : Type0) = {
  f_ZERO : v_Self;
  f_ONE : v_Self;
  f_inverse_pre : v_Self -> Type0;
  f_inverse_post : v_Self -> Core_models.Option.t_Option v_Self -> Type0;
  f_inverse : x0: v_Self
    -> Prims.Pure (Core_models.Option.t_Option v_Self)
       (f_inverse_pre x0) (fun result -> f_inverse_post x0 result);
}

/// Typeclass instance for t_Fp (BLS12-381 scalar field).
/// Provides field inverse: returns Some(x^{-1}) for nonzero x, None for zero.
open Ark_ff.Fields.Models.Fp
open Ark_ff.Fields.Models.Fp.Montgomery_backend

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_field_for_fp (config : Type0) (n : usize) :
  t_Field (t_Fp (t_MontBackend config n) n)
