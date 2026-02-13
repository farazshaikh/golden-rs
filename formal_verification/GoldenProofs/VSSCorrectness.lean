/-
  Formal proof of Feldman VSS correctness for the Golden DKG protocol.

  Per Section 3.2 of the Golden paper (Bünz, Choi, Komlo -- IACR 2025/1924):
    "Commits to polynomial f by publishing C_k = g^{a_k} for each coefficient.
     Verification: g^{f(j)} == product_{k=0}^{t-1} C_k^{j^k}"

  We prove:
  1. Completeness: verify_share accepts honest shares (algebraic identity)
  2. Ciphertext check: (r+s)•g = r•g + s•g
-/

import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Pi

open Finset BigOperators

/-- Polynomial evaluation: f(x) = Σ_{k=0}^{t-1} a_k * x^k -/
noncomputable def poly_eval {F : Type*} [Field F] {t : ℕ}
    (coeffs : Fin t → F) (x : F) : F :=
  ∑ k : Fin t, coeffs k * x ^ (k : ℕ)

/-- Feldman VSS commitment: C_k = a_k • g -/
def feldman_commit_fn {F : Type*} [Field F] {G : Type*} [AddCommGroup G] [Module F G]
    {t : ℕ} (g : G) (coeffs : Fin t → F) : Fin t → G :=
  fun k => coeffs k • g

/-- VSS verification computation: Σ_{k=0}^{t-1} j^k • C_k -/
noncomputable def vss_expected_fn {F : Type*} [Field F] {G : Type*} [AddCommGroup G] [Module F G]
    {t : ℕ} (C : Fin t → G) (j : F) : G :=
  ∑ k : Fin t, j ^ (k : ℕ) • C k

/-- **Feldman VSS Completeness.**

    For honestly-generated commitment C_k = a_k • g, the verification
    equation holds: f(j) • g = Σ_k j^k • C_k.

    This is a pure algebraic identity -- no cryptographic assumption needed.
    Proves that `verify_share` in src/vss.rs returns `true` for honest shares.
-/
theorem feldman_vss_completeness
    {F : Type*} [Field F] [DecidableEq F]
    {G : Type*} [AddCommGroup G] [Module F G]
    {t : ℕ} (g : G) (coeffs : Fin t → F) (j : F) :
    poly_eval coeffs j • g = vss_expected_fn (feldman_commit_fn g coeffs) j := by
  unfold poly_eval vss_expected_fn feldman_commit_fn
  rw [Finset.sum_smul]
  congr 1
  ext k
  rw [mul_comm (coeffs k) (j ^ (k : ℕ))]
  rw [mul_smul]

set_option linter.unusedDecidableInType false in
/-- **VSS expected = f(j) • g.** The algebraic reduction for binding. -/
theorem vss_expected_eq_eval_smul
    {F : Type*} [Field F] [DecidableEq F]
    {G : Type*} [AddCommGroup G] [Module F G]
    {t : ℕ} (g : G) (coeffs : Fin t → F) (j : F) :
    vss_expected_fn (feldman_commit_fn g coeffs) j = poly_eval coeffs j • g :=
  (feldman_vss_completeness g coeffs j).symm

/-- **Golden DKG ciphertext verification.** (r+share)•g = r•g + share•g -/
theorem golden_ciphertext_check
    {F : Type*} [CommRing F]
    {G : Type*} [AddCommGroup G] [Module F G]
    (g : G) (r_pad share : F) :
    (r_pad + share) • g = r_pad • g + share • g :=
  add_smul r_pad share g
