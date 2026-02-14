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
    Paper: Section 4.2 (eVRF Evaluate), step 1: "S = DH.GetSharedKey(sk, PK')"

    sk_i * (sk_j * g) = sk_j * (sk_i * g). The Diffie-Hellman shared
    secret is the same regardless of which party computes it.

    In plain English: when Alice computes sk_Alice * PK_Bob, and Bob
    computes sk_Bob * PK_Alice, they get the same point S. This is
    the foundation of all DH-based encryption.

    Protects against: decryption failure. If DH were not symmetric,
    the recipient could not re-derive the encryption pad, and every
    encrypted share would be unrecoverable -- permanently destroying
    the key material.

    Rust: `derive_pad` in src/evrf.rs line 93: `let s = (peer_pk * sk).into_affine()`
-/
theorem dh_shared_secret_symmetric (g : G) (sk_i sk_j : F) :
    sk_i • (sk_j • g) = sk_j • (sk_i • g) := by
  rw [← mul_smul, ← mul_smul, mul_comm]

/-- **DH symmetry via public keys.**
    Paper: Section 4.2, implicit in "S = DH.GetSharedKey(sk_i, PK_j)"

    If pk_j = sk_j * g and pk_i = sk_i * g, then sk_i * pk_j = sk_j * pk_i.

    In plain English: you only need the other party's public key (not their
    secret key) to compute the shared secret. Both parties arrive at the
    same S using only public information from each other.

    Protects against: the same decryption failure as above, but stated in
    terms of public keys rather than raw scalars -- matching the actual API.

    Rust: src/evrf.rs line 81: "PK_j * sk_i == g^{sk_j * sk_i} == PK_i * sk_j"
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
    Paper: Section 4.2 (eVRF Evaluate) -- the entire Evaluate algorithm

    derive_pad(sk_i, pk_j, msg, beta) = derive_pad(sk_j, pk_i, msg, beta).
    The full eVRF output (pad r and commitment R) is identical for both parties.

    In plain English: when node i encrypts a share for node j, node j can
    independently re-derive the exact same encryption pad to decrypt it.
    No communication is needed beyond the initial broadcast -- this is what
    makes Golden a ONE-ROUND protocol with no back-and-forth.

    Protects against: share loss due to asymmetric encryption. If the
    encryption and decryption pads differed, the decrypted share would
    be garbage, silently corrupting the node's key share. Since there is
    no complaints round in Golden, this corruption would be undetectable
    until reconstruction fails.

    Rust: `derive_pad` in src/evrf.rs, tested by `test_symmetric_pad_derivation`
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

/-- **Corollary: the pad scalar r is symmetric.**
    Paper: Section 4.2, step 4: "alpha = beta * ... + ..."

    The encryption pad r (used to mask the Shamir share) is the same
    for both parties. This is the value that actually encrypts/decrypts.

    Protects against: the share being unrecoverable after encryption.
    r is used as: z = r + share (encrypt), share = z - r (decrypt).
    If r differed between parties, decryption would yield garbage. -/
theorem derive_pad_r_symmetric (g : G) (sk_i sk_j : F)
    (pk_i : G) (hpk_i : pk_i = sk_i • g)
    (pk_j : G) (hpk_j : pk_j = sk_j • g) :
    (compute_pad extract_x H₁ H₂ g_commit beta (sk_i • pk_j)).r =
    (compute_pad extract_x H₁ H₂ g_commit beta (sk_j • pk_i)).r := by
  have := derive_pad_symmetric extract_x H₁ H₂ g_commit beta g sk_i sk_j pk_i hpk_i pk_j hpk_j
  exact congrArg DerivePadOutput.r this

/-- **Corollary: the commitment R is symmetric.**
    Paper: Section 4.2, step 5: "R = g^alpha"

    The public commitment R = r * g is the same for both parties.
    This is broadcast publicly and used by the verifier to check the
    ZK proof (R_eVRF). If R differed, the proof would not verify.

    Protects against: proof verification failure. The verifier checks
    R_eVRF against the published R. If the prover and verifier disagreed
    on R, verification would fail and the protocol would abort. -/
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
    Paper: Figure 4, Round 0 line 7 (encrypt) and Round 1 line 11 (decrypt)

    decrypt(encrypt(share, r)) = share. Specifically:
      encrypt: z = r + share    (Round 0, line 7: z_{i,j} = r_{i,j} + x_bar_{i,j})
      decrypt: share = z - r    (Round 1, line 11: x_bar_{j,i} = z_{j,i} - r_{j,i})

    In plain English: the eVRF-based encryption is a one-time pad. Adding
    the pad r to encrypt and subtracting it to decrypt perfectly recovers
    the original Shamir share. Combined with derive_pad_symmetric, this
    proves the entire encrypt-transmit-decrypt pipeline is lossless.

    Protects against: silent share corruption. If encryption were not
    perfectly invertible, nodes would end up with wrong shares. Since
    Golden has no complaints round, corrupted shares are undetectable
    until threshold reconstruction fails -- potentially losing the key.

    Rust: src/protocol.rs line 73 (encrypt) and line 301 (decrypt)
-/
theorem golden_encrypt_decrypt (r share : F) :
    (r + share) - r = share := by
  ring

end GoldenEncryptionCorrectness
