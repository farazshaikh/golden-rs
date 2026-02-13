/-
  Task 5: eVRF DH symmetry proof.

  Per Section 4.2 of the Golden paper (IACR 2025/1924):
    "Party i calls: derive_pad(sk_i, PK_j, msg, beta)
     Party j calls: derive_pad(sk_j, PK_i, msg, beta)
     Both get the same (r, R) output thanks to DH symmetry:
       PK_j * sk_i == g^{sk_j * sk_i} == PK_i * sk_j"

  We prove:
  1. DH shared secret is symmetric: sk_i • pk_j = sk_j • pk_i
  2. Therefore derive_pad outputs are identical for both parties
  3. This is the correctness foundation for eVRF-based encryption in Golden

  Corresponds to `derive_pad` in src/evrf.rs and the test
  `test_symmetric_pad_derivation` in src/evrf.rs.
-/

import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Tactic.Ring

/-!
## DH Symmetry: Core Lemma

In a group G with scalar field F, if pk_j = sk_j • g and pk_i = sk_i • g,
then sk_i • pk_j = sk_j • pk_i. This is commutativity of the scalar action.
-/

section DHSymmetry

variable {F : Type*} [CommRing F]
variable {G : Type*} [AddCommGroup G] [Module F G]

/-- **DH shared secret symmetry.**

    sk_i • (sk_j • g) = sk_j • (sk_i • g)

    This is the foundational property that makes the eVRF pad symmetric:
    both parties derive the same shared secret S from their respective
    secret keys and the other's public key.

    Proof: by the module axiom `smul_comm` (or equivalently,
    `(a * b) • g = (b * a) • g` from commutativity of F).
-/
theorem dh_shared_secret_symmetric (g : G) (sk_i sk_j : F) :
    sk_i • (sk_j • g) = sk_j • (sk_i • g) := by
  rw [← mul_smul, ← mul_smul, mul_comm]

/-- **DH symmetry via public keys.**

    If pk_j = sk_j • g and pk_i = sk_i • g, then sk_i • pk_j = sk_j • pk_i.

    This is exactly the property stated in src/evrf.rs:
      `PK_j * sk_i == g^{sk_j * sk_i} == PK_i * sk_j`
-/
theorem dh_symmetry_via_pk (g : G) (sk_i sk_j : F)
    (pk_i : G) (hpk_i : pk_i = sk_i • g)
    (pk_j : G) (hpk_j : pk_j = sk_j • g) :
    sk_i • pk_j = sk_j • pk_i := by
  rw [hpk_j, hpk_i]
  exact dh_shared_secret_symmetric g sk_i sk_j

end DHSymmetry

/-!
## derive_pad Symmetry

Since derive_pad is a deterministic function of the DH shared secret S,
and S is symmetric, the entire output (r, R) is symmetric.

We model derive_pad abstractly: given S, the output is determined by
a chain of deterministic operations (extract_x, scalar_mul, extract_x, linear_combination).
-/

section DerivePadSymmetry

variable {F : Type*} [CommRing F]
variable {G : Type*} [AddCommGroup G] [Module F G]

/-- Abstract model of derive_pad: a deterministic function from the
    DH shared secret S to the pad (r, R).

    Matches src/evrf.rs derive_pad steps 2-7:
      k = extract_x(S)
      T1 = k • H1, T2 = k • H2
      r1 = extract_x(T1), r2 = extract_x(T2)
      r = beta * r1 + r2
      R = r • g
-/
structure DerivePadOutput (F : Type*) (G : Type*) where
  r : F
  r_commitment : G

variable (extract_x : G → F) (H₁ H₂ g_commit : G) (beta : F)

/-- Deterministic pad computation from the shared secret S. -/
noncomputable def compute_pad (S : G) : DerivePadOutput F G :=
  let k := extract_x S
  let T1 := k • H₁
  let T2 := k • H₂
  let r1 := extract_x T1
  let r2 := extract_x T2
  let r := beta * r1 + r2
  let R := r • g_commit
  ⟨r, R⟩

/-- **derive_pad symmetry theorem.**

    derive_pad(sk_i, pk_j, msg, beta) = derive_pad(sk_j, pk_i, msg, beta)

    Since compute_pad is a deterministic function of S, and S is the same
    for both parties (by DH symmetry), the outputs are identical.

    This is the formal statement of what `test_symmetric_pad_derivation`
    in src/evrf.rs verifies empirically.
-/
theorem derive_pad_symmetric (g : G) (sk_i sk_j : F)
    (pk_i : G) (hpk_i : pk_i = sk_i • g)
    (pk_j : G) (hpk_j : pk_j = sk_j • g) :
    compute_pad extract_x H₁ H₂ g_commit beta (sk_i • pk_j) =
    compute_pad extract_x H₁ H₂ g_commit beta (sk_j • pk_i) := by
  -- The DH shared secrets are equal
  have hS : sk_i • pk_j = sk_j • pk_i :=
    dh_symmetry_via_pk g sk_i sk_j pk_i hpk_i pk_j hpk_j
  -- Since compute_pad is deterministic, equal inputs give equal outputs
  rw [hS]

/-- **Corollary: both the pad scalar r and commitment R are symmetric.** -/
theorem derive_pad_r_symmetric (g : G) (sk_i sk_j : F)
    (pk_i : G) (hpk_i : pk_i = sk_i • g)
    (pk_j : G) (hpk_j : pk_j = sk_j • g) :
    (compute_pad extract_x H₁ H₂ g_commit beta (sk_i • pk_j)).r =
    (compute_pad extract_x H₁ H₂ g_commit beta (sk_j • pk_i)).r := by
  have := derive_pad_symmetric extract_x H₁ H₂ g_commit beta g sk_i sk_j pk_i hpk_i pk_j hpk_j
  exact congrArg DerivePadOutput.r this

theorem derive_pad_commitment_symmetric (g : G) (sk_i sk_j : F)
    (pk_i : G) (hpk_i : pk_i = sk_i • g)
    (pk_j : G) (hpk_j : pk_j = sk_j • g) :
    (compute_pad extract_x H₁ H₂ g_commit beta (sk_i • pk_j)).r_commitment =
    (compute_pad extract_x H₁ H₂ g_commit beta (sk_j • pk_i)).r_commitment := by
  have := derive_pad_symmetric extract_x H₁ H₂ g_commit beta g sk_i sk_j pk_i hpk_i pk_j hpk_j
  exact congrArg DerivePadOutput.r_commitment this

end DerivePadSymmetry

/-!
## Connection to Golden DKG Protocol

In the Golden DKG (Section 5.2, Figure 4):
- Round 0, line 5: Party i computes `derive_pad(sk_i, PK_j, msg_i, beta)`
  to get `(r_{i,j}, R_{i,j})` for encrypting share to party j.
- Round 1, line 11: Party j computes `derive_pad(sk_j, PK_i, msg_i, beta)`
  to re-derive `(r_{i,j}, _, _)` for decrypting.

By `derive_pad_symmetric`, both calls produce the same `r_{i,j}`, so:
  `z_{i,j} - r_{i,j} = (r_{i,j} + x_bar_{i,j}) - r_{i,j} = x_bar_{i,j}`

The decrypted share equals the original share. This is the correctness
of the encryption/decryption scheme in the Golden DKG.
-/

section GoldenEncryptionCorrectness

variable {F : Type*} [CommRing F]

/-- **Golden DKG encryption-decryption correctness.**

    If both parties derive the same pad r, then:
      decrypt(encrypt(share, r)) = share

    encrypt: z = r + share
    decrypt: share' = z - r = (r + share) - r = share
-/
theorem golden_encrypt_decrypt (r share : F) :
    (r + share) - r = share := by
  ring

end GoldenEncryptionCorrectness
