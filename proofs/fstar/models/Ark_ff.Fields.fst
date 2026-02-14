module Ark_ff.Fields

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives
open Core_models

/// The arkworks Field trait.
/// hax extracts field operations as standalone functions with typeclass instances.
/// f_ZERO, f_ONE, f_inverse are called as:
///   Ark_ff.Fields.f_ZERO #(t_Fp ...) #FStar.Tactics.Typeclasses.solve

class t_Field (v_Self : Type0) = {
  __f_ZERO : v_Self;
  __f_ONE : v_Self;
  __f_inverse : v_Self -> Core_models.Option.t_Option v_Self;
}

/// Standalone accessor functions matching hax's calling convention.
/// hax calls: Ark_ff.Fields.f_ZERO #FStar.Tactics.Typeclasses.solve
///
/// NOTE: These use `Prims.Pure` with trivial pre/post to help F* type
/// inference in if-then-else contexts where the return type is ambiguous.
/// f_ZERO: the typeclass instance is the ONLY implicit parameter.
/// hax calls: f_ZERO #FStar.Tactics.Typeclasses.solve
/// The `#solve` fills the tcresolve parameter. v_Self is inferred from the instance.
let f_ZERO (#[FStar.Tactics.Typeclasses.tcresolve ()] _i: t_Field 'a)
  : 'a = _i.__f_ZERO

let f_ONE (#[FStar.Tactics.Typeclasses.tcresolve ()] _i: t_Field 'a)
  : 'a = _i.__f_ONE

let f_inverse (#[FStar.Tactics.Typeclasses.tcresolve ()] _i: t_Field 'a)
  (x : 'a) : Core_models.Option.t_Option 'a = _i.__f_inverse x

/// Typeclass instance for t_Fp.
open Ark_ff.Fields.Models.Fp
open Ark_ff.Fields.Models.Fp.Montgomery_backend

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_field_for_fp (config : Type0) (n : usize) :
  t_Field (t_Fp (t_MontBackend config n) n)
