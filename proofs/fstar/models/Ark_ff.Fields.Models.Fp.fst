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

// ============================================================================
// Phase 2: Abstract field model
//
// Concrete field operation wrappers. These are the ground-truth operations
// on field elements. They are `assume val` (opaque) but return t_Fp directly,
// avoiding the associated-type problem of typeclasses.
// ============================================================================

/// Field addition wrapper: a + b in F_p.
assume val fp_add (#config : Type0) (#n : usize) :
  t_Fp config n -> t_Fp config n -> t_Fp config n

/// Field subtraction wrapper: a - b in F_p.
assume val fp_sub (#config : Type0) (#n : usize) :
  t_Fp config n -> t_Fp config n -> t_Fp config n

/// Field multiplication wrapper: a * b in F_p.
assume val fp_mul (#config : Type0) (#n : usize) :
  t_Fp config n -> t_Fp config n -> t_Fp config n

/// From<u64> wrapper: embed a u64 into F_p.
assume val fp_from_u64 (#config : Type0) (#n : usize) : u64 -> t_Fp config n

// ============================================================================
// Typeclass instances for arithmetic operations on t_Fp.
//
// CRITICAL CHANGE for Phase 2: These are now CONCRETE `let` definitions
// (not `assume val`). This makes f_Output = t_Fp config n visible to the
// type checker, which is required for any proof that reasons through field
// arithmetic expressions in the extracted code.
//
// The actual computation delegates to fp_add/fp_sub/fp_mul/fp_from_u64
// which are still opaque (assume val), so we don't lose abstraction.
// ============================================================================

/// --- Addition: a + b ---
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_fp_add (config : Type0) (n : usize) :
  Core_models.Ops.Arith.t_Add (t_Fp config n) (t_Fp config n) =
  {
    f_Output = t_Fp config n;
    f_add_pre = (fun (a : t_Fp config n) (b : t_Fp config n) -> True);
    f_add_post = (fun (a : t_Fp config n) (b : t_Fp config n) (out : t_Fp config n) -> True);
    f_add = fun (a : t_Fp config n) (b : t_Fp config n) -> fp_add a b
  }

/// --- Subtraction: a - b ---
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_fp_sub (config : Type0) (n : usize) :
  Core_models.Ops.Arith.t_Sub (t_Fp config n) (t_Fp config n) =
  {
    f_Output = t_Fp config n;
    f_sub_pre = (fun (a : t_Fp config n) (b : t_Fp config n) -> True);
    f_sub_post = (fun (a : t_Fp config n) (b : t_Fp config n) (out : t_Fp config n) -> True);
    f_sub = fun (a : t_Fp config n) (b : t_Fp config n) -> fp_sub a b
  }

/// --- Multiplication: a * b ---
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_fp_mul (config : Type0) (n : usize) :
  Core_models.Ops.Arith.t_Mul (t_Fp config n) (t_Fp config n) =
  {
    f_Output = t_Fp config n;
    f_mul_pre = (fun (a : t_Fp config n) (b : t_Fp config n) -> True);
    f_mul_post = (fun (a : t_Fp config n) (b : t_Fp config n) (out : t_Fp config n) -> True);
    f_mul = fun (a : t_Fp config n) (b : t_Fp config n) -> fp_mul a b
  }

/// --- AddAssign: a += b (same as add, returns new value) ---
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_fp_add_assign (config : Type0) (n : usize) :
  Core_models.Ops.Arith.t_AddAssign (t_Fp config n) (t_Fp config n) =
  {
    f_add_assign_pre = (fun (a : t_Fp config n) (b : t_Fp config n) -> True);
    f_add_assign_post = (fun (a : t_Fp config n) (b : t_Fp config n) (out : t_Fp config n) -> True);
    f_add_assign = fun (a : t_Fp config n) (b : t_Fp config n) -> fp_add a b
  }

/// --- MulAssign: a *= b (same as mul, returns new value) ---
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_fp_mul_assign (config : Type0) (n : usize) :
  Core_models.Ops.Arith.t_MulAssign (t_Fp config n) (t_Fp config n) =
  {
    f_mul_assign_pre = (fun (a : t_Fp config n) (b : t_Fp config n) -> True);
    f_mul_assign_post = (fun (a : t_Fp config n) (b : t_Fp config n) (out : t_Fp config n) -> True);
    f_mul_assign = fun (a : t_Fp config n) (b : t_Fp config n) -> fp_mul a b
  }

/// --- From<u64>: Scalar::from(42u64) ---
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_fp_from_u64 (config : Type0) (n : usize) :
  Core_models.Convert.t_From (t_Fp config n) u64 =
  {
    f_from_pre = (fun (v : u64) -> True);
    f_from_post = (fun (v : u64) (out : t_Fp config n) -> True);
    f_from = fun (v : u64) -> fp_from_u64 v
  }

// ============================================================================
// Integer interpretation for reasoning about field element equality
// ============================================================================

/// The prime modulus for a given field configuration.
assume val fp_prime (config : Type0) (n : usize) : pos

/// The prime is at least 2.
assume val fp_prime_ge_2 : config:Type0 -> n:usize ->
  Lemma (fp_prime config n >= 2)

/// Abstract interpretation: field element -> nat in [0, p).
assume val fp_to_int (#config : Type0) (#n : usize) : t_Fp config n -> nat

/// Bounded.
assume val fp_to_int_bounded : #config:Type0 -> #n:usize -> x:t_Fp config n ->
  Lemma (fp_to_int x < fp_prime config n)

/// Injective.
assume val fp_to_int_injective : #config:Type0 -> #n:usize ->
  x:t_Fp config n -> y:t_Fp config n ->
  Lemma (fp_to_int x == fp_to_int y <==> x == y)

/// Canonical element from integer.
assume val fp_of_int (#config : Type0) (#n : usize) : int -> t_Fp config n

/// fp_of_int spec.
assume val fp_of_int_spec : #config:Type0 -> #n:usize -> v:int ->
  Lemma (fp_to_int (fp_of_int #config #n v) == v % fp_prime config n)

/// Roundtrip.
assume val fp_roundtrip : #config:Type0 -> #n:usize -> x:t_Fp config n ->
  Lemma (fp_of_int #config #n (fp_to_int x) == x)

// ============================================================================
// Modular arithmetic axioms for the wrappers
// ============================================================================

/// fp_to_int(a + b) == (fp_to_int a + fp_to_int b) % p
assume val fp_add_spec : #config:Type0 -> #n:usize ->
  a:t_Fp config n -> b:t_Fp config n ->
  Lemma (fp_to_int (fp_add a b) == (fp_to_int a + fp_to_int b) % fp_prime config n)

/// fp_to_int(a - b) == (fp_to_int a - fp_to_int b) % p
assume val fp_sub_spec : #config:Type0 -> #n:usize ->
  a:t_Fp config n -> b:t_Fp config n ->
  Lemma (fp_to_int (fp_sub a b) == (fp_to_int a - fp_to_int b) % fp_prime config n)

/// fp_to_int(a * b) == (fp_to_int a * fp_to_int b) % p
assume val fp_mul_spec : #config:Type0 -> #n:usize ->
  a:t_Fp config n -> b:t_Fp config n ->
  Lemma (fp_to_int (fp_mul a b) == (fp_to_int a * fp_to_int b) % fp_prime config n)

/// fp_to_int(from_u64(v)) == v % p
assume val fp_from_u64_spec : #config:Type0 -> #n:usize -> v:u64 ->
  Lemma (fp_to_int (fp_from_u64 #config #n v) == Rust_primitives.Integers.v v % fp_prime config n)

// ============================================================================
// Derived algebraic properties
// ============================================================================

/// 0_F has int value 0
assume val fp_zero_int : #config:Type0 -> #n:usize -> unit ->
  Lemma (fp_to_int (fp_from_u64 #config #n (mk_u64 0)) == 0)

/// 1_F has int value 1
assume val fp_one_int : #config:Type0 -> #n:usize -> unit ->
  Lemma (fp_to_int (fp_from_u64 #config #n (mk_u64 1)) == 1)

/// a + 0 == a
assume val fp_add_zero : #config:Type0 -> #n:usize -> a:t_Fp config n ->
  Lemma (fp_add a (fp_from_u64 #config #n (mk_u64 0)) == a)

/// 0 * a == 0
assume val fp_mul_zero_l : #config:Type0 -> #n:usize -> a:t_Fp config n ->
  Lemma (fp_mul (fp_from_u64 #config #n (mk_u64 0)) a == fp_from_u64 #config #n (mk_u64 0))

/// a * 1 == a
assume val fp_mul_one : #config:Type0 -> #n:usize -> a:t_Fp config n ->
  Lemma (fp_mul a (fp_from_u64 #config #n (mk_u64 1)) == a)

/// a + b == b + a
assume val fp_add_comm : #config:Type0 -> #n:usize ->
  a:t_Fp config n -> b:t_Fp config n ->
  Lemma (fp_add a b == fp_add b a)

/// a * b == b * a
assume val fp_mul_comm : #config:Type0 -> #n:usize ->
  a:t_Fp config n -> b:t_Fp config n ->
  Lemma (fp_mul a b == fp_mul b a)

/// (a + b) + c == a + (b + c)
assume val fp_add_assoc : #config:Type0 -> #n:usize ->
  a:t_Fp config n -> b:t_Fp config n -> c:t_Fp config n ->
  Lemma (fp_add (fp_add a b) c == fp_add a (fp_add b c))

/// (a * b) * c == a * (b * c)
assume val fp_mul_assoc : #config:Type0 -> #n:usize ->
  a:t_Fp config n -> b:t_Fp config n -> c:t_Fp config n ->
  Lemma (fp_mul (fp_mul a b) c == fp_mul a (fp_mul b c))

/// a * (b + c) == a*b + a*c
assume val fp_mul_dist : #config:Type0 -> #n:usize ->
  a:t_Fp config n -> b:t_Fp config n -> c:t_Fp config n ->
  Lemma (fp_mul a (fp_add b c) == fp_add (fp_mul a b) (fp_mul a c))

// ============================================================================
// Additional derived properties (Phase 2.5)
// ============================================================================

/// 1 * a == a (left identity for multiplication)
assume val fp_mul_one_l : #config:Type0 -> #n:usize -> a:t_Fp config n ->
  Lemma (fp_mul (fp_from_u64 #config #n (mk_u64 1)) a == a)

/// 0 + a == a (left identity for addition)
assume val fp_add_zero_l : #config:Type0 -> #n:usize -> a:t_Fp config n ->
  Lemma (fp_add (fp_from_u64 #config #n (mk_u64 0)) a == a)

/// a - a == 0
assume val fp_sub_self : #config:Type0 -> #n:usize -> a:t_Fp config n ->
  Lemma (fp_sub a a == fp_from_u64 #config #n (mk_u64 0))

/// a - b + b == a (cancellation)
assume val fp_sub_add_cancel : #config:Type0 -> #n:usize ->
  a:t_Fp config n -> b:t_Fp config n ->
  Lemma (fp_add (fp_sub a b) b == a)

/// a * 0 == 0 (right zero for multiplication)
assume val fp_mul_zero_r : #config:Type0 -> #n:usize -> a:t_Fp config n ->
  Lemma (fp_mul a (fp_from_u64 #config #n (mk_u64 0)) == fp_from_u64 #config #n (mk_u64 0))

/// Right distributivity: (a + b) * c == a*c + b*c
assume val fp_mul_dist_r : #config:Type0 -> #n:usize ->
  a:t_Fp config n -> b:t_Fp config n -> c:t_Fp config n ->
  Lemma (fp_mul (fp_add a b) c == fp_add (fp_mul a c) (fp_mul b c))

/// NOTE: Inverse axioms (fp_inverse_exists, fp_mul_inverse) live in
/// Golden_dkg.Shamir.Spec.fst to avoid circular dependency with Ark_ff.Fields.
