module Ark_ff.Fields

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives
open Core_models

/// The arkworks Field trait.
class t_Field (v_Self : Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method] __f_ZERO : v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method] __f_ONE : v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method] __f_inverse : v_Self -> Core_models.Option.t_Option v_Self;
}

/// Typeclass instance for t_Fp.
open Ark_ff.Fields.Models.Fp
open Ark_ff.Fields.Models.Fp.Montgomery_backend

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_field_for_fp (config : Type0) (n : usize) :
  t_Field (t_Fp (t_MontBackend config n) n)

/// f_ZERO: hax calls `f_ZERO #solve` with NO type implicits.
/// Result type is inferred from the `<: t_Fp (...)` ascription at call site.
/// The tcresolve is the ONLY implicit parameter.
///
/// TRICK: We don't use a type parameter at all. Instead we hardcode
/// the concrete BLS12-381 Fr scalar type (the only field used in golden-dkg).
/// In --lax mode this is sufficient because F* trusts type ascriptions.
let scalar_fr = t_Fp (t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)

assume val f_ZERO_fr :
  (#[FStar.Tactics.Typeclasses.tcresolve ()] _inst : t_Field scalar_fr) -> scalar_fr
assume val f_ONE_fr :
  (#[FStar.Tactics.Typeclasses.tcresolve ()] _inst : t_Field scalar_fr) -> scalar_fr

/// Map f_ZERO/f_ONE to the concrete versions.
/// hax calls: Ark_ff.Fields.f_ZERO #solve
/// The `#solve` fills tcresolve which resolves to impl_field_for_fp.
/// v_Self = scalar_fr is inferred from the return type ascription.
let f_ZERO (#[FStar.Tactics.Typeclasses.tcresolve ()] _i: t_Field scalar_fr) = f_ZERO_fr #_i
let f_ONE (#[FStar.Tactics.Typeclasses.tcresolve ()] _i: t_Field scalar_fr) = f_ONE_fr #_i

/// f_inverse: hax calls `f_inverse #Type #solve arg` -- has a type implicit.
/// Standard 2-implicit pattern (same as f_add, f_mul, etc.)
assume val f_inverse (#v_Self: Type0)
  (#[FStar.Tactics.Typeclasses.tcresolve ()] _inst : t_Field v_Self)
  (x : v_Self) : Core_models.Option.t_Option v_Self

// ============================================================================
// Phase 2: Field trait axioms connecting to the Fp model
// ============================================================================

/// f_ZERO_fr is the field zero, i.e., fp_from_u64(0)
assume val f_ZERO_fr_spec :
  (#[FStar.Tactics.Typeclasses.tcresolve ()] _inst : t_Field scalar_fr) ->
  Lemma (f_ZERO_fr #_inst == Ark_ff.Fields.Models.Fp.fp_from_u64 (mk_u64 0))

/// f_ONE_fr is the field one, i.e., fp_from_u64(1)
assume val f_ONE_fr_spec :
  (#[FStar.Tactics.Typeclasses.tcresolve ()] _inst : t_Field scalar_fr) ->
  Lemma (f_ONE_fr #_inst == Ark_ff.Fields.Models.Fp.fp_from_u64 (mk_u64 1))

/// f_inverse on a nonzero element returns Some(inv) where inv is the
/// multiplicative inverse: x * inv == 1_F.
/// On zero, it returns None.
assume val f_inverse_spec :
  x:scalar_fr ->
  Lemma (
    let zero = Ark_ff.Fields.Models.Fp.fp_from_u64 #_ #(mk_usize 4) (mk_u64 0) in
    let one  = Ark_ff.Fields.Models.Fp.fp_from_u64 #_ #(mk_usize 4) (mk_u64 1) in
    if x = zero then
      f_inverse x == Core_models.Option.Option_None
    else
      (exists (inv : scalar_fr).
        f_inverse x == Core_models.Option.Option_Some inv /\
        Ark_ff.Fields.Models.Fp.fp_mul x inv == one)
  )
