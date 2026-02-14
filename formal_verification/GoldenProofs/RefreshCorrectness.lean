/-
  Formal proof of key refresh correctness for the Golden DKG protocol.

  Per Section 5.2 of the Golden paper (Bunz, Choi, Komlo -- IACR 2025/1924):
    "Instead of sampling omega_i at random, set omega_i = 0.
     Check that A_{j,0} equals the group identity for all j."

  The refresh protocol runs a zero-secret DKG: each node shares omega = 0,
  producing delta shares that sum to zero. Adding these deltas to existing
  shares rotates them while preserving the original secret sk.

  We prove:
  1. Zero polynomial evaluates to zero at the origin (refresh invariant)
  2. Refresh preserves the secret (adding zero-sharing deltas is transparent)
  3. Refresh PK contribution is zero (identity commitments vanish)
  4. New shares differ from old (probabilistic, axiomatized)

  These correspond to `round0_refresh` and `round1_refresh`
  in src/protocol.rs of the Rust implementation.
-/

import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Pi

open Polynomial Lagrange Finset BigOperators

/-!
## Part 1: Zero Polynomial Vanishes Under Interpolation

If a polynomial f has f(0) = 0 and degree < |S|, then
Lagrange interpolation of its evaluations also yields 0 at the origin.
This is the mathematical core of the refresh invariant: each node's
zero-sharing polynomial contributes 0 to the reconstructed secret.
-/

section ZeroPolynomial

variable {ι : Type*} [DecidableEq ι]
variable {F : Type*} [Field F]
variable {s : Finset ι} {v : ι → F}

/-- **Zero polynomial vanishes under interpolation.**
    Paper: Section 5.2 (Key Refresh)
    Paper quote: "Instead of sampling omega_i at random, set omega_i = 0"

    If f(0) = 0 and f has degree < |S|, then Lagrange interpolation
    of f's evaluations also yields 0 at the origin.

    In plain English: when a node shares the secret "zero" using Shamir,
    the resulting shares reconstruct to zero. This is the mathematical
    core of key refresh: each node contributes a zero-sharing, and the
    sum of zeros is zero, so the original secret is unchanged.

    Protects against: secret drift during refresh. If zero-sharing did
    not actually reconstruct to zero, each refresh round would silently
    change the shared secret, eventually making the key unrecoverable.

    Rust: `round0_refresh` in src/protocol.rs line 351: `omega = Scalar::ZERO`
-/
theorem zero_polynomial_vanishes
    (f : F[X])
    (hvs : Set.InjOn v s)
    (hdeg : f.degree < #s)
    (hzero : f.eval 0 = 0) :
    (Lagrange.interpolate s v (fun i => f.eval (v i))).eval 0 = 0 := by
  -- By Mathlib's eq_interpolate, f = its Lagrange interpolant
  have heq : f = Lagrange.interpolate s v (fun i => f.eval (v i)) :=
    Lagrange.eq_interpolate hvs hdeg
  -- Evaluate both sides at 0
  rw [← heq]
  exact hzero

end ZeroPolynomial

/-!
## Part 2: Refresh Preserves the Secret

The refresh protocol adds zero-sharing deltas to existing shares.
Since the deltas reconstruct to 0, the sum `sk' = sk + 0 = sk` is preserved.

We model this algebraically: if the original shares reconstruct sk,
and the delta shares reconstruct 0, then the refreshed shares
reconstruct sk + 0 = sk.
-/

section RefreshPreservesSecret

variable {F : Type*} [Field F]

/-- **Refresh preserves the secret.**
    Paper: Section 5.2 (Proactive Key Refresh)

    Adding zero-sharing deltas to existing shares does not change the
    reconstructed secret: sum L_i * (sk_i + delta_i) = sum L_i * sk_i
    when sum L_i * delta_i = 0.

    In plain English: after a refresh, the shared private key sk is
    exactly the same as before. Only the individual shares change.
    Any t participants can still reconstruct the same signing key.

    Protects against: secret corruption during proactive refresh.
    Key refresh is used to limit the window of exposure: even if an
    attacker steals t-1 shares, they become useless after refresh.
    But if refresh changed the secret, the group's signing key would
    be destroyed. This theorem guarantees refresh is "transparent."

    Rust: `round1_refresh` in src/protocol.rs lines 535, 551
-/
theorem refresh_preserves_secret
    {n : ℕ}
    (L : Fin n → F) -- Lagrange coefficients
    (sk : Fin n → F) -- original shares
    (delta : Fin n → F) -- zero-sharing deltas
    (h_delta_zero : ∑ i : Fin n, L i * delta i = 0) :
    ∑ i : Fin n, L i * (sk i + delta i) =
    ∑ i : Fin n, L i * sk i := by
  -- Distribute: L_i * (sk_i + delta_i) = L_i * sk_i + L_i * delta_i
  simp only [mul_add]
  -- Split the sum
  rw [Finset.sum_add_distrib]
  -- The delta sum is 0
  rw [h_delta_zero]
  ring

end RefreshPreservesSecret

/-!
## Part 3: Refresh PK Contribution Is Zero

In the refresh protocol, each node's commitment A_{j,0} = g^{f_j(0)} = g^0 = identity.
Therefore the sum of all A_{j,0} = identity, and the PK contribution from refresh is zero.
This is checked in round1_refresh (protocol.rs:453-461).
-/

section RefreshPKUnchanged

variable {F : Type*} [CommRing F]
variable {G : Type*} [AddCommGroup G] [Module F G]

/-- **Refresh PK is unchanged.**
    Paper: Section 5.2 -- "Check that A_{j,0} equals the group identity for all j"

    If all omega_j = 0, then sum omega_j * g = identity. The public key
    PK = PK_old + identity = PK_old is unchanged.

    In plain English: after refresh, the public key stays the same.
    External verifiers (e.g., a blockchain) do not need to update
    anything -- the group's public key is permanent.

    Protects against: public key instability. If PK changed on every
    refresh, all existing signatures, certificates, and on-chain
    registrations would be invalidated. The protocol enforces PK
    stability by checking A_{j,0} = identity in round1_refresh.

    Rust: `round1_refresh` in src/protocol.rs lines 453-461
-/
theorem refresh_pk_unchanged
    {n : ℕ}
    (g : G)
    (omega : Fin n → F)
    (h_all_zero : ∀ i, omega i = 0) :
    ∑ i : Fin n, omega i • g = 0 := by
  simp [h_all_zero, zero_smul]

end RefreshPKUnchanged

/-!
## Part 4: Refreshed Shares Differ (Probabilistic)

With overwhelming probability, the zero-sharing deltas are nonzero
at individual evaluation points (even though they sum to 0 at the origin).
This is axiomatized -- the probability argument requires a probabilistic
framework (e.g., VCV-io) that is beyond the scope of algebraic verification.
-/

section RefreshSharesChanged

variable {F : Type*} [Field F]

/-- **Refreshed shares differ from originals.**
    Paper: Section 5.2 -- implicit (the point of refresh is share rotation)

    If any delta is nonzero, sk_old + delta != sk_old. With overwhelming
    probability (1 - 1/|F|), the delta for each node is nonzero.

    In plain English: refresh actually rotates the shares. Old shares
    become useless -- an attacker who stole shares before the refresh
    cannot combine them with shares stolen after the refresh.

    Protects against: mobile adversary (proactive security model).
    The adversary can steal up to t-1 shares in each epoch. As long
    as they do not steal t shares in a SINGLE epoch, the key is safe.
    Share rotation is what resets the adversary's progress.

    Rust: main.rs lines 224-229 (assertion that shares changed)
-/
theorem refresh_shares_changed
    {sk_old delta : F}
    (h_nonzero : delta ≠ 0) :
    sk_old + delta ≠ sk_old := by
  intro h
  apply h_nonzero
  -- From h : sk_old + delta = sk_old, derive delta = 0
  -- Subtract sk_old from both sides: delta = 0
  have : sk_old + delta - sk_old = sk_old - sk_old := by rw [h]
  simp only [add_sub_cancel_left, sub_self] at this
  exact this

end RefreshSharesChanged
