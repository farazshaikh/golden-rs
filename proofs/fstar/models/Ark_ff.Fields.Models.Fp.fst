module Ark_ff.Fields.Models.Fp

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives
open Core_models

/// Abstract prime field element type.
///
/// In the Rust code, this is `ark_ff::models::fp::Fp<MontBackend<Config, N>, N>`.
/// We model it as an opaque type with field axioms.
///
/// The type parameters:
///   config -- the Montgomery backend configuration (determines the prime modulus)
///   n      -- the number of 64-bit limbs (4 for BLS12-381 Fr, 6 for Fq)
assume new type t_Fp (config : Type0) (n : usize) : eqtype

/// Typeclass instances for arithmetic operations on t_Fp.
/// These are resolved by FStar.Tactics.Typeclasses.tcresolve in the extracted code.
///
/// The pre/post conditions are trivially true (no overflow possible in a field).
/// For full verification (Phase 3), these would be strengthened with field axioms.

/// --- Addition: a + b ---
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_fp_add (config : Type0) (n : usize) :
  Core_models.Ops.Arith.t_Add (t_Fp config n) (t_Fp config n)

/// --- Subtraction: a - b ---
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_fp_sub (config : Type0) (n : usize) :
  Core_models.Ops.Arith.t_Sub (t_Fp config n) (t_Fp config n)

/// --- Multiplication: a * b ---
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_fp_mul (config : Type0) (n : usize) :
  Core_models.Ops.Arith.t_Mul (t_Fp config n) (t_Fp config n)

/// --- AddAssign: a += b ---
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_fp_add_assign (config : Type0) (n : usize) :
  Core_models.Ops.Arith.t_AddAssign (t_Fp config n) (t_Fp config n)

/// --- MulAssign: a *= b ---
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_fp_mul_assign (config : Type0) (n : usize) :
  Core_models.Ops.Arith.t_MulAssign (t_Fp config n) (t_Fp config n)

/// --- From<u64>: Scalar::from(42u64) ---
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_fp_from_u64 (config : Type0) (n : usize) :
  Core_models.Convert.t_From (t_Fp config n) u64
