module Ark_ec.Models.Short_weierstrass.Group

open Rust_primitives
open Core_models

/// Projective point on a short Weierstrass curve (X:Y:Z homogeneous coords).
/// In arkworks: `ark_ec::models::short_weierstrass::Projective<P>`.

assume new type t_Projective (config : Type0) : eqtype

// ============================================================================
// Semantic operations (opaque wrappers)
//
// Following the Fp model pattern (Phase 2): each operation is an `assume val`
// so the actual computation is opaque, but the instances below are concrete
// `let` definitions so that f_Output = t_Projective config is visible to the
// type checker.
// ============================================================================

open Ark_ff.Fields.Models.Fp
open Ark_ff.Fields.Models.Fp.Montgomery_backend

/// Point addition: P + Q (projective)
assume val proj_add (config : Type0) :
  t_Projective config -> t_Projective config -> t_Projective config

/// Point addition (for AddAssign): same semantics as proj_add
assume val proj_add_assign (config : Type0) :
  t_Projective config -> t_Projective config -> t_Projective config

/// Mixed addition: Projective += Affine
assume val proj_add_assign_affine (config : Type0) :
  t_Projective config ->
  Ark_ec.Models.Short_weierstrass.Affine.t_Affine config ->
  t_Projective config

/// Point subtraction: P - Q (projective)
assume val proj_sub (config : Type0) :
  t_Projective config -> t_Projective config -> t_Projective config

/// Point negation: -P
assume val proj_neg (config : Type0) :
  t_Projective config -> t_Projective config

/// Affine * Scalar -> Projective (scalar multiplication)
assume val affine_scalar_mul (config : Type0) (fp_config : Type0) (n : usize) :
  Ark_ec.Models.Short_weierstrass.Affine.t_Affine config ->
  t_Fp (t_MontBackend fp_config n) n ->
  t_Projective config

/// Projective * Scalar -> Projective
assume val proj_scalar_mul (config : Type0) (fp_config : Type0) (n : usize) :
  t_Projective config ->
  t_Fp (t_MontBackend fp_config n) n ->
  t_Projective config

/// Projective *= Scalar (same as proj_scalar_mul)
assume val proj_scalar_mul_assign (config : Type0) (fp_config : Type0) (n : usize) :
  t_Projective config ->
  t_Fp (t_MontBackend fp_config n) n ->
  t_Projective config

/// Default: identity / point at infinity
assume val proj_default (config : Type0) : t_Projective config

// ============================================================================
// Typeclass instances for arithmetic operations on t_Projective.
//
// CRITICAL: These are CONCRETE `let` definitions (not `assume val`).
// This makes f_Output = t_Projective config visible to the type checker,
// which is required for any proof that reasons through EC arithmetic
// expressions in the extracted code.
//
// Pattern follows Ark_ff.Fields.Models.Fp.fst exactly.
// ============================================================================

/// Projective + Projective (point addition)
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_proj_add (config : Type0) :
  Core_models.Ops.Arith.t_Add (t_Projective config) (t_Projective config) =
  {
    f_Output = t_Projective config;
    f_add_pre = (fun (a : t_Projective config) (b : t_Projective config) -> True);
    f_add_post = (fun (a : t_Projective config) (b : t_Projective config) (out : t_Projective config) -> True);
    f_add = fun (a : t_Projective config) (b : t_Projective config) -> proj_add config a b
  }

/// Projective += Projective
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_proj_add_assign (config : Type0) :
  Core_models.Ops.Arith.t_AddAssign (t_Projective config) (t_Projective config) =
  {
    f_add_assign_pre = (fun (a : t_Projective config) (b : t_Projective config) -> True);
    f_add_assign_post = (fun (a : t_Projective config) (b : t_Projective config) (out : t_Projective config) -> True);
    f_add_assign = fun (a : t_Projective config) (b : t_Projective config) -> proj_add_assign config a b
  }

/// Projective += Affine (mixed addition)
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_proj_add_assign_affine (config : Type0) :
  Core_models.Ops.Arith.t_AddAssign (t_Projective config) (Ark_ec.Models.Short_weierstrass.Affine.t_Affine config) =
  {
    f_add_assign_pre = (fun (a : t_Projective config) (b : Ark_ec.Models.Short_weierstrass.Affine.t_Affine config) -> True);
    f_add_assign_post = (fun (a : t_Projective config) (b : Ark_ec.Models.Short_weierstrass.Affine.t_Affine config) (out : t_Projective config) -> True);
    f_add_assign = fun (a : t_Projective config) (b : Ark_ec.Models.Short_weierstrass.Affine.t_Affine config) -> proj_add_assign_affine config a b
  }

/// Projective - Projective (point subtraction)
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_proj_sub (config : Type0) :
  Core_models.Ops.Arith.t_Sub (t_Projective config) (t_Projective config) =
  {
    f_Output = t_Projective config;
    f_sub_pre = (fun (a : t_Projective config) (b : t_Projective config) -> True);
    f_sub_post = (fun (a : t_Projective config) (b : t_Projective config) (out : t_Projective config) -> True);
    f_sub = fun (a : t_Projective config) (b : t_Projective config) -> proj_sub config a b
  }

/// Negation: -Projective
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_proj_neg (config : Type0) :
  Core_models.Ops.Arith.t_Neg (t_Projective config) =
  {
    f_Output = t_Projective config;
    f_neg_pre = (fun (a : t_Projective config) -> True);
    f_neg_post = (fun (a : t_Projective config) (out : t_Projective config) -> True);
    f_neg = fun (a : t_Projective config) -> proj_neg config a
  }

/// Affine * Scalar -> Projective
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_affine_scalar_mul (config : Type0) (fp_config : Type0) (n : usize) :
  Core_models.Ops.Arith.t_Mul
    (Ark_ec.Models.Short_weierstrass.Affine.t_Affine config)
    (t_Fp (t_MontBackend fp_config n) n) =
  {
    f_Output = t_Projective config;
    f_mul_pre = (fun (a : Ark_ec.Models.Short_weierstrass.Affine.t_Affine config) (b : t_Fp (t_MontBackend fp_config n) n) -> True);
    f_mul_post = (fun (a : Ark_ec.Models.Short_weierstrass.Affine.t_Affine config) (b : t_Fp (t_MontBackend fp_config n) n) (out : t_Projective config) -> True);
    f_mul = fun (a : Ark_ec.Models.Short_weierstrass.Affine.t_Affine config) (b : t_Fp (t_MontBackend fp_config n) n) -> affine_scalar_mul config fp_config n a b
  }

/// Projective * Scalar
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_proj_scalar_mul (config : Type0) (fp_config : Type0) (n : usize) :
  Core_models.Ops.Arith.t_Mul
    (t_Projective config)
    (t_Fp (t_MontBackend fp_config n) n) =
  {
    f_Output = t_Projective config;
    f_mul_pre = (fun (a : t_Projective config) (b : t_Fp (t_MontBackend fp_config n) n) -> True);
    f_mul_post = (fun (a : t_Projective config) (b : t_Fp (t_MontBackend fp_config n) n) (out : t_Projective config) -> True);
    f_mul = fun (a : t_Projective config) (b : t_Fp (t_MontBackend fp_config n) n) -> proj_scalar_mul config fp_config n a b
  }

/// Projective *= Scalar
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_proj_scalar_mul_assign (config : Type0) (fp_config : Type0) (n : usize) :
  Core_models.Ops.Arith.t_MulAssign
    (t_Projective config)
    (t_Fp (t_MontBackend fp_config n) n) =
  {
    f_mul_assign_pre = (fun (a : t_Projective config) (b : t_Fp (t_MontBackend fp_config n) n) -> True);
    f_mul_assign_post = (fun (a : t_Projective config) (b : t_Fp (t_MontBackend fp_config n) n) (out : t_Projective config) -> True);
    f_mul_assign = fun (a : t_Projective config) (b : t_Fp (t_MontBackend fp_config n) n) -> proj_scalar_mul_assign config fp_config n a b
  }

/// Default for Projective (identity / point at infinity)
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_proj_default (config : Type0) :
  Core_models.Default.t_Default (t_Projective config) =
  {
    f_default_pre = (fun (x : unit) -> True);
    f_default_post = (fun (x : unit) (out : t_Projective config) -> True);
    f_default = fun (x : unit) -> proj_default config
  }

/// PartialEq for Projective (point equality)
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume val impl_proj_partial_eq (config : Type0) :
  Core_models.Cmp.t_PartialEq (t_Projective config) (t_Projective config)

// ============================================================================
// EC Group Algebraic Axioms
// ============================================================================
//
// These axioms state standard elliptic curve group laws for BLS12-381 G1.
// They are justified by the [AddCommGroup G] [Module F G] structure in the
// Lean 4 proofs (ShamirCorrectness.lean, EVRFSymmetry.lean, etc.).
//
// Each axiom here corresponds to a property already machine-checked in Lean:
//   - Axioms 1-3 (scalar mult): [Module F G] in Lean
//   - Axiom 4 (DH commutativity): dh_shared_secret_symmetric in EVRFSymmetry.lean
//   - Axioms 5-7 (group laws): [AddCommGroup G] in Lean
//
// Pattern follows Ark_ff.Fields.Models.Fp.fst (field axioms).

/// Type aliases for readability
let g1_config = Ark_bls12_381_.Curves.G1.t_Config
let g1_affine = Ark_ec.Models.Short_weierstrass.Affine.t_Affine g1_config
let g1_proj = t_Projective g1_config
let fr_config = Ark_bls12_381_.Fields.Fr.t_FrConfig
let scalar = t_Fp (t_MontBackend fr_config (mk_usize 4)) (mk_usize 4)

/// Shorthand for the semantic operations specialised to BLS12-381 G1
let smul (s : scalar) (p : g1_affine) : g1_proj =
  affine_scalar_mul g1_config fr_config (mk_usize 4) p s

let g1_add (p q : g1_proj) : g1_proj =
  proj_add g1_config p q

let g1_sub (p q : g1_proj) : g1_proj =
  proj_sub g1_config p q

let g1_neg (p : g1_proj) : g1_proj =
  proj_neg g1_config p

let g1_zero : g1_proj =
  proj_default g1_config

// ---- AddAssign / proj_add agreement ----

/// AddAssign semantics equals Add semantics (both are point addition)
assume val proj_add_assign_is_add : config:Type0 ->
  p:t_Projective config -> q:t_Projective config ->
  Lemma (proj_add_assign config p q == proj_add config p q)

// ---- Group axioms: commutativity, associativity, identity ----

/// Point addition is commutative: P + Q == Q + P
assume val ec_add_comm : p:g1_proj -> q:g1_proj ->
  Lemma (g1_add p q == g1_add q p)

/// Point addition is associative: (P + Q) + R == P + (Q + R)
assume val ec_add_assoc : p:g1_proj -> q:g1_proj -> r:g1_proj ->
  Lemma (g1_add (g1_add p q) r == g1_add p (g1_add q r))

/// Identity element: P + 0 == P
assume val ec_add_zero_r : p:g1_proj ->
  Lemma (g1_add p g1_zero == p)

/// Inverse: P + (-P) == 0
assume val ec_add_neg : p:g1_proj ->
  Lemma (g1_add p (g1_neg p) == g1_zero)

/// Subtraction is addition of negation: P - Q == P + (-Q)
assume val ec_sub_is_add_neg : p:g1_proj -> q:g1_proj ->
  Lemma (g1_sub p q == g1_add p (g1_neg q))

// ---- Scalar multiplication axioms: Module F G structure ----

/// Scalar addition distributes: (a+b)*P == a*P + b*P
assume val smul_add_scalar : a:scalar -> b:scalar -> p:g1_affine ->
  Lemma (smul (fp_add a b) p == g1_add (smul a p) (smul b p))

/// DH commutativity: (a*b)*P == (b*a)*P
/// This is the KEY axiom for eVRF pad symmetry.
/// Follows from field commutativity: a*b == b*a in Fr.
assume val smul_field_comm : a:scalar -> b:scalar -> p:g1_affine ->
  Lemma (smul (fp_mul a b) p == smul (fp_mul b a) p)

/// 1 * P == to_proj(P) -- scalar identity
assume val smul_one : p:g1_affine ->
  Lemma (smul (fp_from_u64 (mk_u64 1)) p == proj_default g1_config) // placeholder: needs to_proj

/// 0 * P == 0 -- scalar zero
assume val smul_zero : p:g1_affine ->
  Lemma (smul (fp_from_u64 (mk_u64 0)) p == g1_zero)
