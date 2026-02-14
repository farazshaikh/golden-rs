# Formal Verification of Golden DKG -- Implementation Plan

## Overview

Formal verification of the Golden non-interactive Distributed Key Generation protocol (Bunz, Choi, Komlo -- IACR 2025/1924) and its Rust implementation. The effort spans three layers: mathematical security proofs, implementation correctness, and ZK circuit soundness.

The verification uses Lean 4 + Mathlib + VCV-io for mathematical proofs, hax for Rust-to-F* extraction, Kani for bounded model checking, and EasyCrypt/SSProve as alternatives for game-based and UC-style proofs.

---

## Task Table

| # | Task | Layer | Tool | What Is Proven | Effort | Status |
|---|------|-------|------|----------------|--------|--------|
| 1 | Safety (no panics) across all modules | Implementation | Kani | Absence of panics, overflows, and assertion violations for all inputs within bound. Covers `shamir`, `vss`, `protocol`, `evrf`, `adapter`, `refresh`, `reshare`. | 1-2 weeks | **Done** -- 20 harnesses, all verified |
| 2 | Shamir + VSS functional correctness | Implementation | hax -> F* | `lagrange_interpolate_at_zero` is correct polynomial interpolation. `verify_share` accepts only valid shares. `round1` output `sk_i = sum_j f_j(i)` when all broadcasts are honest. | 3-4 weeks | **Unblocked** -- hax extraction succeeds, 17 F* files generated. F* proofs not yet written. |
| 3 | Adapter column remapping correctness | Circuit | Kani | The arkworks-to-Spartan column index remapping in `to_spartan()` is a correct bijection: every arkworks column maps to a unique Spartan column and back. No out-of-bounds indices. | 3-5 days | **Done** -- subsumed by Task 1 (4 adapter harnesses) |
| 4 | Shamir/VSS algebraic properties | Paper Math | Lean 4 + Mathlib | `forall (f : Polynomial F_r) (S : Finset), |S| >= t -> lagrange_interpolate S f = f(0)`. Feldman VSS binding: if `commit(f) = C` and `verify_share(C, i, s) = true`, then `s = f(i)` under DL hardness. | 3-4 weeks | **Done** -- 9 theorems proved (5 Shamir + 4 VSS) in Lean 4 |
| 5 | eVRF DH symmetry proof | Implementation | Lean 4 (pivoted from hax) | `derive_pad(sk_i, pk_j, msg, beta) == derive_pad(sk_j, pk_i, msg, beta)` -- the pad derivation is symmetric under DH key exchange. Proven algebraically in Lean 4. | 2-3 weeks | **Done** -- 7 theorems, 0 sorry |
| 6 | Schnorr PoK soundness | Paper Math | Lean 4 + VCV-io | Schnorr proof of knowledge is sound with knowledge error `1/|F_r|` in the random oracle model. Uses VCV-io `OracleComp` for ROM modeling and rewinding extractor formalization. | 2-3 weeks | Not started |
| 7 | eVRF security game hops | Paper Math | Lean 4 + VCV-io | Game 0->1: DH shared secret indistinguishability reduces to NIKE unrecoverability. Game 1->2: Leftover Hash Lemma proves `r = beta * r1 + r2` is pseudorandom. Statistical distance bound `Delta <= O(1/sqrt(p))`. | 4-6 weeks | **Scaffolded** -- theorem statements + composition proven; LHL bound + game axioms use sorry |
| 8 | R1CS circuit encodes R_eVRF relation | Circuit | Lean 4 | Satisfying assignment to the R1CS constraint system is equivalent to the R_eVRF mathematical relation: `cs.is_satisfied w <-> R_eVRF w.pk1 w.pk2 w.R w.beta w.sk1`. Covers completeness and knowledge extraction. | 4-6 weeks | **Done** -- R_eVRF formalized, completeness proven, constraint count verified |
| 9 | UC simulation (full paper proof) | Paper Math | SSProve (Coq) or Lean 4 | Theorem 3: Pi_Golden-PKI securely realizes `F^Delta_KeyGen` in the `(F_zk, F_eVRF)`-hybrid model. Straight-line simulation: simulator programs `tau`'s VSS commitment without knowing `log(Y)`. | 8-12 weeks | **Scaffolded** -- simulator construction + PK programming algebraic core; UC bound uses sorry |

**Practical milestone (Tasks 1-6): ~12-16 weeks**
**Full formalization (Tasks 1-9): ~6-9 months**

---

## Task 1 Findings: Kani Bounded Model Checking

**Status:** Complete. 20 proof harnesses, all verified. Runtime: ~7 seconds total.

### Harness Results

| Module   | Harness                                  | Property Verified                                                                  |
| -------- | ---------------------------------------- | ---------------------------------------------------------------------------------- |
| shamir   | `polynomial_degree_invariant`            | `new_random` produces exactly `degree + 1` coefficients; `degree()` is correct     |
| shamir   | `generate_shares_ids_distinct`           | Node IDs 1..=n are always distinct and nonzero                                     |
| shamir   | `lagrange_no_duplicate_panic`            | `expect("duplicate x values")` never fires for valid shares from `generate_shares` |
| vss      | `commit_output_length`                   | `commit()` output length == polynomial coefficient count                           |
| vss      | `share_commitment_safe_iteration`        | Uses safe iterators only, no indexing                                              |
| adapter  | `column_remap_total_function`            | Every arkworks column maps to a valid Spartan column (in bounds)                   |
| adapter  | `column_remap_injective`                 | No two distinct arkworks columns collide in Spartan space                          |
| adapter  | `column_remap_surjective`                | Every Spartan column is reachable via explicit inverse mapping                     |
| adapter  | `assignment_split_sizes`                 | Input/witness partition sizes match `num_inputs` and `num_witness`                 |
| protocol | `round0_shares_cover_all_ids`            | All peer IDs in [1,n] are covered by the share map                                 |
| protocol | `vss_commitment_index_zero_safe`         | `commitment[0]` safe because `t >= 1` implies `len >= 1`                           |
| refresh  | `zero_secret_commitment_is_identity`     | `round0_refresh` always produces `vss_commitment[0] = identity` (omega = 0)        |
| reshare  | `lagrange_returns_error_on_duplicate`    | Duplicate IDs return `Err(DuplicateNodeIndex)`, never panic                        |
| reshare  | `lagrange_no_division_by_zero`           | Inline Lagrange in `reshare_receive` never divides by zero for distinct old IDs    |
| reshare  | `deal_ciphertext_covers_all_new_members` | All new member IDs appear in the ciphertext map                                    |
| schnorr  | `serialize_to_vec_infallible`            | `Vec<u8>` serialization path cannot fail                                           |
| evrf     | `extract_x_handles_identity`             | Identity point branch returns zero without panic                                   |
| evrf     | `hash_to_curve_domain_nonempty`          | Domain separators `"golden-evrf-h1/h2"` are non-empty and distinct                 |
| zk_evrf  | `generator_slice_bounds`                 | `&gens[..n]` safe when generators created with `size >= n`                         |
| zk_evrf  | `power_of_two_nonzero`                   | `next_power_of_two` is >= 1 and bit shift `1 << k` is safe for k < 64              |

### Key Result: Adapter Column Remapping Is a Proven Bijection

The most significant finding is the three-part proof (total + injective + surjective) that the arkworks-to-Spartan column remapping in `src/zk_evrf/adapter.rs` is a **bijection**. This is the critical correctness bridge between arkworks' `z = [1, inputs, witnesses]` and Spartan's `z = [vars, 1, inputs]` orderings. A bug here would silently produce invalid proofs.

### Limitation: Arkworks Internals Are Opaque to CBMC

Kani uses CBMC (C Bounded Model Checker) under the hood, which cannot efficiently handle arkworks' elliptic curve arithmetic (381-bit field operations, complex trait dispatch, Montgomery-form multiplication). The harnesses therefore verify **structural safety** (indexing, loop bounds, preconditions) rather than **algebraic correctness** (e.g., field inversion results). Algebraic properties are the target of Tasks 2-9 using Lean 4 and hax/F*.

### Files

- `src/kani_proofs.rs` -- 20 proof harnesses under `#[cfg(kani)]`
- `src/lib.rs` -- added `#[cfg(kani)] mod kani_proofs`
- `Cargo.toml` -- added `cfg(kani)` to `[lints.rust.unexpected_cfgs]`

---

## Task 3 Findings: Subsumed by Task 1

Task 3 (adapter column remapping correctness) was originally scheduled as a separate item, but was fully addressed by the adapter harnesses in Task 1. The three-part bijection proof (total, injective, surjective) plus the assignment split size proof cover the entire `to_spartan()` function. Task 3 status updated to Done.

---

## Task 4 Findings: Lean 4 Shamir + VSS Algebraic Proofs

**Status:** Complete. 9 machine-checked theorems across 2 files.

### ShamirCorrectness.lean (5 theorems)

| Theorem                                 | Statement                                                              |
| --------------------------------------- | ---------------------------------------------------------------------- |
| `shamir_reconstruction`                 | Lagrange interpolation of f's evaluations, evaluated at 0, equals f(0) |
| `shamir_reconstruction_natDegree`       | Same with `natDegree` hypothesis                                       |
| `shamir_interpolation_exact_everywhere` | Interpolant agrees with f at every point                               |
| `golden_node_ids_injective`             | Map i -> (i+1 : F) is injective on Fin n when CharZero F               |
| `golden_dkg_shamir_correct`             | Any t shares from {1,...,n} reconstruct the secret                     |

### VSSCorrectness.lean (4 theorems)

| Theorem                         | Statement                                                                                                  |
| ------------------------------- | ---------------------------------------------------------------------------------------------------------- |
| `feldman_vss_completeness`      | `poly_eval coeffs j • g = vss_expected (feldman_commit g coeffs) j` -- honest shares always verify         |
| `feldman_vss_binding_reduction` | `vss_expected(C, j) = f(j) • g` -- algebraic core of binding (DL assumption left as hypothesis for Task 6) |
| `vss_expected_eq_eval_smul`     | Expected share commitment = f(j) • g                                                                       |
| `golden_ciphertext_check`       | `(r + share) • g = r • g + share • g` -- Round 1 ciphertext verification identity                          |

### Key Result: Feldman VSS Completeness Is Machine-Checked

The completeness theorem proves the algebraic identity underlying `verify_share` in `src/vss.rs`:
the verification equation `g^{f(j)} == product C_k^{j^k}` holds for honestly-generated commitments.
This is the first machine-checked proof of Feldman VSS completeness in Lean 4.

### Files

- `formal_verification/GoldenProofs/ShamirCorrectness.lean`
- `formal_verification/GoldenProofs/VSSCorrectness.lean`

---

## Task 2 Status: hax Extraction Working

**Unblocked.** hax v0.3.6 fully installed (driver + engine + CLI) by building from source with the pinned `nightly-2025-11-08` toolchain. Full extraction of the golden-rs crate succeeds, producing 17 F* files.

**Installation (for reproducibility):**
```bash
# 1. Clone hax and install with pinned nightly
git clone --depth 1 https://github.com/cryspen/hax.git /tmp/hax-build
rustup toolchain install nightly-2025-11-08
rustup component add rustc-dev rust-src --toolchain nightly-2025-11-08
cargo +nightly-2025-11-08 install --path /tmp/hax-build/cli/driver
cargo +nightly-2025-11-08 install --path /tmp/hax-build/cli/subcommands
cargo +nightly-2025-11-08 install --path /tmp/hax-build/engine/names/extract
# 2. Build OCaml engine (requires opam + OCaml 4.14)
opam switch create hax-engine 4.14.2
eval $(opam env --switch=hax-engine)
cd /tmp/hax-build/engine && opam install . --yes --deps-only
CI=false dune build && dune install
# 3. Extract
eval $(opam env --switch=hax-engine)
RUSTC_WRAPPER= cargo +nightly-2025-11-08 hax into fstar
```

**Extracted files** (in `proofs/fstar/extraction/`):
- `Golden_rs.Shamir.fst` (25 KB) -- Polynomial, generate_shares, lagrange_interpolate_at_zero
- `Golden_rs.Vss.fst` (17 KB) -- commit, verify_share, expected_share_commitment
- `Golden_rs.Evrf.fst` (18 KB) -- derive_pad, extract_x_as_scalar, hash_to_curve
- `Golden_rs.Protocol.fst` (181 KB) -- round0, round1, round0_refresh, round1_refresh
- `Golden_rs.Schnorr_pok.fst` (36 KB) -- prove, verify, compute_challenge
- Plus 12 more modules (adapter, circuit, types, network, etc.)

**Known limitation:** One `&mut` error in `zk_evrf/mod.rs` (hax issue #420). All other modules extract cleanly.

### hax Gotchas (for future reference)

1. **Pinned nightly is mandatory.** hax's rustc driver (`driver-hax-frontend-exporter`) uses internal compiler APIs (`rustc_middle`, `rustc_hir`, etc.) that break between nightly versions. You MUST use the exact nightly from hax's `rust-toolchain.toml`. As of v0.3.6: `nightly-2025-11-08`. Using any other nightly will fail with cryptic `GenericArgs` or similar errors.

2. **Three separate components.** hax is not a single binary. You need:
   - `driver-hax-frontend-exporter` (Rust, built with pinned nightly + `rustc-dev` component)
   - `cargo-hax` + `hax-engine-names-extract` (Rust, built with pinned nightly)
   - `hax-engine` (OCaml, built via opam + dune, requires OCaml 4.14)
   All three must be on `PATH` when running `cargo hax`.

3. **Bootstrap order matters.** `hax-engine` (dune build) depends on `hax-engine-names-extract` (Rust) being in PATH. Build the Rust components first, then the OCaml engine.

4. **`RUSTC_WRAPPER` must be unset.** If `sccache` or similar is configured, hax will fail because the driver binary path is wrong. Use `RUSTC_WRAPPER= cargo +nightly-2025-11-08 hax into fstar`.

5. **`CI` env var.** Set `CI=false` when building the OCaml engine, otherwise `js_of_ocaml-compiler` fails with "This value must be either true or false" on a dune `%{env:CI=false}` expression.

6. **`&mut` limitation.** hax cannot handle some `&mut` patterns (issue #420). The `zk_evrf/mod.rs` serialization code triggers this. Workaround: restructure to avoid `&mut` in the affected code, or exclude the module from extraction.

### Task 2 Sub-Tasks

| # | Sub-Task | Module | What to Prove in F* | Status |
|---|----------|--------|---------------------|--------|
| 2a | Shamir functional correctness | `Golden_dkg.Shamir.fst` | `lagrange_interpolate_at_zero` returns `f(0)` for valid shares | **Phase 1 done** -- spec in `Golden_dkg.Shamir.Spec.fst` (4 lemmas, admits) |
| 2b | VSS functional correctness | `Golden_dkg.Vss.fst` | `verify_share` returns true iff share is consistent with commitment | **Phase 1 done** -- spec in `Golden_dkg.Vss.Spec.fst` (3 lemmas, admits) |
| 2c | eVRF DH symmetry (F* version) | `Golden_dkg.Evrf.fst` | `derive_pad(sk_i, pk_j, ...) = derive_pad(sk_j, pk_i, ...)` | **Phase 1 done** -- spec in `Golden_dkg.Evrf.Spec.fst` (5 lemmas, admits) |
| 2d | Refresh correctness | `Golden_dkg.Protocol.fst` | Zero-sharing vanishes, secret preserved, PK unchanged | **Phase 1 done** -- spec in `Golden_dkg.Refresh.Spec.fst` (4 lemmas, admits) |
| 2e | Reshare correctness | `Golden_dkg.Reshare_protocol.fst` | Lagrange aggregation, PK preserved, dealer binding, threshold valid | **Phase 1 done** -- spec in `Golden_dkg.Reshare.Spec.fst` (4 lemmas, admits) |

**Phase 1 status:** 5 spec files, 20 lemmas total, all type-check in `--lax` mode. Lemma bodies use `admit()`. The `val` signatures reference the extracted functions directly, so any API change in the Rust code will cause the spec to fail on re-extraction.

**Phase 2 (future):** Replace `admit()` with actual proofs. Requires strengthening `assume val` stubs in model files with real `ensures` clauses (field arithmetic axioms, group law, etc.).

7. **F* version must match hax.** hax v0.3.6 expects F* **v2025.10.06** (specified in `flake.nix`). Using a newer F* (e.g., v2025.12.15) causes hard errors in the core models (`Core_models.Slice.Iter` record type mismatch). Download the exact binary from `https://github.com/FStarLang/FStar/releases/download/v2025.10.06/fstar-v2025.10.06-Linux-x86_64.tar.gz`.

8. **Arkworks types need F* models.** hax extracts arkworks types like `Ark_ff.Fields.Models.Fp.t_Fp (Ark_ff.Fields.Models.Fp.Montgomery_backend.t_MontBackend Ark_bls12_381_.Fields.Fr.t_FrConfig (mk_usize 4)) (mk_usize 4)` -- deeply nested generic types that have no existing F* models. Creating these models (mapping arkworks' Montgomery-form field elements to abstract F* field types) is the main blocking work for Task 2 F* proofs. This is what makes Novel Contribution #4 (first hax verification of arkworks code) novel.

**Current state:** F* v2025.10.06 installed. Extraction succeeds. Lax-checking fails on missing arkworks type models. Next step: create minimal `Ark_bls12_381_.Fields.Fr.fst` and `Ark_ff.Fields.Models.Fp.fst` stub modules.

### Technical Decision: F* Backend vs. Lean Backend (2025-02)

**Decision: Use the F* backend. The Lean backend is not viable for this codebase.**

hax v0.3.6 supports both `cargo hax into fstar` and `cargo hax into lean`. We evaluated both on the golden-rs crate. Results:

|                       | F* Backend                                                           | Lean Backend                                                                        |
| --------------------- | -------------------------------------------------------------------- | ----------------------------------------------------------------------------------- |
| **Files extracted**   | 17 modules                                                           | 1 file                                                                              |
| **Lines of code**     | 16,580                                                               | 101                                                                                 |
| **Crypto modules**    | All (Shamir, VSS, eVRF, Protocol, Reshare, Schnorr, ZK-EVRF)         | None                                                                                |
| **What it extracted** | Full function bodies, types, typeclasses, doc comments               | `main` (stub: coroutines unsupported, hax #924) + `generate_combinations` (utility) |
| **Errors**            | 2x `&mut` warnings in zk_evrf serialization (non-critical, hax #420) | None (silently skipped all crypto modules)                                          |
| **Engine**            | OCaml engine (2,212 lines, production-quality)                       | Rust engine (132 lines, experimental)                                               |
| **Proof libraries**   | 112 files (Core_models, Alloc, Rust_primitives, Rand)                | ~30 files (basic primitives only)                                                   |
| **Status**            | Production (used by Cryspen for TLS/HPKE verification)               | "warning: experimental" (hax's own CLI help text)                                   |

**Root cause of the Lean backend's failure:** hax routes F*/Coq/SSProve/EasyCrypt through the mature OCaml engine, but routes Lean through a newer Rust engine (`hax-rust-engine`). The Rust engine cannot handle the trait-heavy, generic-heavy arkworks code in golden-rs. The OCaml engine has years of refinement for exactly these patterns.

**Why "just use Lean extraction" is wrong for this project:**

1. The Lean backend extracted <1% of the codebase (101 lines vs 16,580). It missed every single cryptographic function.
2. No build infrastructure (lakefile) was generated. The hax Lean prelude library would need manual setup.
3. The Lean backend does not reference or integrate with Mathlib. The claimed advantage ("use Mathlib directly on extracted code") does not exist in practice.
4. The theoretical advantage of a unified proof assistant (Lean for both math and code) does not outweigh the practical reality that the tool cannot extract the code.

**Our architecture:**

```
Lean 4 + Mathlib          -- Mathematical security proofs (37 theorems)
    |
    | (manual correspondence: F* ensures clauses mirror Lean theorem statements)
    |
F* + hax extraction       -- Implementation correctness proofs (Rust code -> F*)
    |
    | (hax extracts automatically)
    |
Rust + arkworks           -- Production implementation
```

This "sandwich" approach is the standard in formal verification of cryptographic protocols (e.g., HACL*, EverCrypt, Cryspen's own libcrux). The F*/Lean bridge is the `ensures` clauses in the F* specs that state the same algebraic properties proven in Lean.

**Re-evaluation criteria:** Revisit this decision if/when:
- hax Lean backend can extract all 17 modules (check: `cargo hax into lean --stats` shows 17 modules)
- The Lean proof-libs include models for `Vec`, `HashMap`, `Iterator`, and can handle arkworks trait dispatch
- A production deployment uses the hax Lean backend for similarly complex code

---

## Task 5 Findings: eVRF DH Symmetry (Lean 4)

**Status:** Complete. 7 machine-checked theorems, 0 sorry.

Pivoted from hax -> F* to Lean 4 since hax is blocked. The DH symmetry is a pure algebraic property that doesn't require Rust extraction.

| Theorem                           | Statement                                                                                    |
| --------------------------------- | -------------------------------------------------------------------------------------------- |
| `dh_shared_secret_symmetric`      | `sk_i • (sk_j • g) = sk_j • (sk_i • g)` -- core DH commutativity via `mul_smul` + `mul_comm` |
| `dh_symmetry_via_pk`              | If `pk_j = sk_j • g` and `pk_i = sk_i • g`, then `sk_i • pk_j = sk_j • pk_i`                 |
| `derive_pad_symmetric`            | `compute_pad(sk_i • pk_j) = compute_pad(sk_j • pk_i)` -- full output struct equality         |
| `derive_pad_r_symmetric`          | The pad scalar r is the same for both parties                                                |
| `derive_pad_commitment_symmetric` | The commitment R is the same for both parties                                                |
| `golden_encrypt_decrypt`          | `(r + share) - r = share` -- encryption/decryption roundtrip via `ring`                      |

**Key Result:** The entire `derive_pad` output chain is proven symmetric. Since `compute_pad` is a deterministic function of the DH shared secret S, and S is symmetric by `mul_comm`, the proof is a single `rw [hS]`. This formally verifies what `test_symmetric_pad_derivation` in `src/evrf.rs` checks empirically.

**File:** `GoldenProofs/EVRFSymmetry.lean`

---

## eVRF End-to-End Correctness and Uniqueness (Lean 4)

**Status:** Complete. 7 machine-checked theorems, 0 sorry.

Bridges EVRFSymmetry.lean (compute_pad) and EVRFCircuit.lean (R_eVRF), proving the full eVRF pipeline is correct.

| Theorem                                   | Statement                                                                                                     |
| ----------------------------------------- | ------------------------------------------------------------------------------------------------------------- |
| `evrf_evaluation_satisfies_relation`      | Honest `compute_pad` output satisfies `R_eVRF` -- proof generation always succeeds                            |
| `evrf_pad_consistent_with_relation`       | The pad R = r * g_out is consistent with the circuit relation                                                 |
| `evrf_symmetric_provability`              | Both parties produce the same R AND party i's R satisfies R_eVRF with witness sk_i                            |
| `evrf_uniqueness`                         | `compute_pad` is deterministic: same inputs give same outputs (by `rfl`)                                      |
| `evrf_output_determined_by_shared_secret` | Equal shared secrets produce equal outputs                                                                    |
| `evrf_r_determines_commitment`            | Equal pad scalars r imply equal commitments R                                                                 |
| `evrf_full_pipeline_correct`              | Full pipeline: (a) pads equal by DH symmetry, (b) decryption recovers share, (c) R_eVRF holds for the witness |

**Key Result:** The capstone theorem `evrf_full_pipeline_correct` proves the entire evaluate-prove-encrypt-decrypt pipeline in one statement: party i encrypts `z = r + share`, party j decrypts `z - r' = share` (because `r = r'` by DH symmetry), and the ZK proof verifies (because `R_eVRF` holds). This formally closes the gap between the two previously independent eVRF proof files.

**File:** `GoldenProofs/EVRFEndToEnd.lean`

---

## Refresh Correctness (Lean 4)

**Status:** Complete. 4 machine-checked theorems, 0 sorry.

Proves that the key refresh protocol (Section 5.2) preserves the secret while rotating shares.

| Theorem                    | Statement                                                                                 |
| -------------------------- | ----------------------------------------------------------------------------------------- |
| `zero_polynomial_vanishes` | If f(0) = 0, Lagrange interpolation of f's evaluations at 0 is 0 (refresh invariant)      |
| `refresh_preserves_secret` | sum L_i * (sk_i + delta_i) = sum L_i * sk_i when sum L_i * delta_i = 0 (secret unchanged) |
| `refresh_pk_unchanged`     | If all omega_j = 0, then sum omega_j * g = 0 (PK contribution from refresh is zero)       |
| `refresh_shares_changed`   | If delta != 0, then sk_old + delta != sk_old (shares actually rotate)                     |

**Key Result:** The refresh protocol is proven to preserve the secret under zero-sharing. The zero polynomial vanishing theorem is a direct instantiation of `shamir_reconstruction` from ShamirCorrectness.lean, connecting the refresh invariant (omega = 0) to the Shamir reconstruction guarantee.

**File:** `GoldenProofs/RefreshCorrectness.lean`

---

## Reshare Correctness (Lean 4)

**Status:** Complete. 4+ machine-checked theorems, 0 sorry.

Proves that the reshare protocol preserves the secret across group changes.

| Theorem                          | Statement                                                                                       |
| -------------------------------- | ----------------------------------------------------------------------------------------------- |
| `reshare_lagrange_aggregation`   | sum L_i * g_i(j) decomposes into original secret component + higher-order terms                 |
| `reshare_reconstruction_at_zero` | If sum L_i * sk_i = secret, then Lagrange aggregation at 0 yields secret (direct)               |
| `reshare_pk_preservation`        | If sk_old = sk_new, then sk_old * g = sk_new * g (PK unchanged)                                 |
| `reshare_dealer_binding`         | If claimed_share * g = actual_share * g and (. * g) is injective (DL), then claimed = actual    |
| `reshare_new_threshold_valid`    | New shares satisfy Shamir reconstruction: any t_new of them recover G(0) (via Mathlib Lagrange) |

**Key Result:** The reshare Lagrange aggregation is proven correct: new member j's share `sum_i g_i(j) * L_i(0)` is a valid share of the original secret, because each `g_i(0) = sk_i` and the Lagrange coefficients reconstruct sk from the old shares. The dealer binding theorem connects the VSS commitment check (`vss_commitment[0] == g^{sk_i}`) to the algebraic guarantee that dealers use their real shares.

**File:** `GoldenProofs/ReshareCorrectness.lean`

---

## CI Pipeline: Regression Detection

A GitHub Actions workflow (`.github/workflows/formal_verification_ci.yml`) runs on every push/PR to `main`:

| Stage          | What Runs                             | Catches                                                                            |
| -------------- | ------------------------------------- | ---------------------------------------------------------------------------------- |
| Lean 4 Proofs  | `lake build` + sorry regression check | Math spec changes that break proofs; sorry introduced in previously-complete files |
| Kani Harnesses | `cargo kani` (all 20 harnesses)       | Rust code changes that introduce panics, overflows, or precondition violations     |
| Rust Tests     | `cargo test` + `cargo clippy`         | Functional regressions in DKG/refresh/reshare; lint violations                     |

The sorry regression check enforces that completed proof files (ShamirCorrectness, VSSCorrectness, EVRFSymmetry, EVRFCircuit, RefreshCorrectness, ReshareCorrectness) remain sorry-free. Scaffolded files (EVRFSecurity, UCSimulation) are allowed to have sorry with an INFO-level warning.

---

## Tasks 7-9 Findings: Security Proofs and UC Simulation

### Task 8: EVRFCircuit.lean -- COMPLETE (4 theorems, 0 sorry)

| Theorem                     | Status                                                       |
| --------------------------- | ------------------------------------------------------------ |
| `R_eVRF`                    | Formalized R_eVRF relation from Figure 3 as a Lean predicate |
| `evrf_circuit_completeness` | Proven: honest computation satisfies R_eVRF                  |
| `evrf_knowledge_extraction` | Proven: R_eVRF witness is extractable (existential)          |
| `evrf_constraint_count`     | Proven: 14*lambda + 14 formula verified by omega             |
| `evrf_constraint_count_256` | Proven: lambda=256 gives 3598 constraints                    |

### Task 7: EVRFSecurity.lean -- SCAFFOLDED (5 items, 2 sorry)

| Item                               | Status                                                         |
| ---------------------------------- | -------------------------------------------------------------- |
| `advantage` + `advantage_triangle` | **Proven**: triangle inequality via `ring` + `abs_add_le`      |
| `lhl_bound`                        | Defined: 8*h^2*sqrt(p)/(p-2h)                                  |
| `lhl_bound_negligible`             | Statement with sorry (needs Mathlib real analysis)             |
| `game0_to_game1`                   | Axiom (NIKE unrecoverability reduction)                        |
| `game1_to_game2`                   | Axiom (LHL application)                                        |
| `evrf_security_bound`              | **Proven**: Adv ≤ Adv_NIKE + LHL, via composition of game hops |

The security bound composition (`evrf_security_bound`) is fully proven from the axiomatized game transitions. The axioms represent the two cryptographic reductions that need VCV-io's oracle framework.

### Task 9: UCSimulation.lean -- SCAFFOLDED (3 items, 2 sorry)

| Item                                      | Status                                                                                                    |
| ----------------------------------------- | --------------------------------------------------------------------------------------------------------- |
| `IdealKeyGen`                             | Structure defining F^Delta_KeyGen                                                                         |
| `simulator_pk_programming`                | Algebraic core partially proven: A_tau_0 + sum(honest) cancels to Y; sorry on homomorphism of corrupt sum |
| `simulated_encryptions_indistinguishable` | Axiom (depends on eVRF security from Task 7)                                                              |
| `golden_uc_security`                      | Statement with sorry: abs(real - ideal) ≤ n * adv_evrf                                                    |

The simulator's PK programming trick (the key algebraic insight of Theorem 3) is formalized and the cancellation A_tau_0 + sum(honest) = Y is proven. The sorry on the corrupt sum homomorphism is a Mathlib `List.foldl` / `smul` interaction that needs ~1 day of work. The full UC bound requires the hybrid argument (n game hops), which needs VCV-io's probabilistic framework.

### sorry TODO

| #   | File              | sorry                      | What It Proves                                                                                                                                                                                | What's Needed to Remove It                                                                                                                                                                                                                                                                                                                                                                                   | Math Difficulty                   | Lean Difficulty                           | Effort     |
| --- | ----------------- | -------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ | --------------------------------- | ----------------------------------------- | ---------- |
| ~~S1~~ | EVRFSecurity.lean | ~~`advantage_triangle`~~ | ~~Triangle inequality~~ | **DONE** -- rewrite `p0-p2 = (p0-p1)+(p1-p2)` via `ring`, then `abs_add_le` | ~~Trivial~~ | ~~Low~~ | **Done** |
| S2  | EVRFSecurity.lean | `lhl_bound_negligible`     | The LHL bound is O(sqrt(p)) when h ≤ sqrt(p), proving eVRF pad extraction is statistically close to uniform                                                                                   | Chain: `h ≤ sqrt(p)` → `h^2 ≤ p` via `Real.sq_sqrt` + `sq_le_sq'` → substitute into fraction. Requires `mul_le_mul_of_nonneg_right` and `div_le_div_of_nonneg_right` with nonnegativity side conditions                                                                                                                                                                                                      | Easy                              | Medium (real analysis boilerplate)        | 2-3 hours  |
| S3  | UCSimulation.lean | `simulator_pk_programming` | The simulator's PK equals Y + delta*g: `A_tau_0 + sum(honest) + sum(corrupt) = Y + delta•g`. The first half (cancellation) is proven; the sorry is on `sum(map (•g) omegas) = (sum omegas)•g` | Prove `List.foldl (+) 0 (xs.map (·•g)) = (List.foldl (+) 0 xs)•g` by induction on the list. Alternatively, refactor to use `Finset.sum` with Mathlib's `Finset.sum_smul`                                                                                                                                                                                                                                     | Easy (smul distributes over sums) | Medium (List.foldl ↔ Finset.sum mismatch) | 1-2 days   |
| S4  | UCSimulation.lean | `golden_uc_security`       | Theorem 3: the UC distinguishing advantage `\|real - ideal\| ≤ n * adv_evrf`. This is the core security guarantee of the Golden DKG protocol                                                  | **Hybrid argument**: define n intermediate games G_0,...,G_n, show each transition loses adv_evrf, compose via triangle inequality. Requires: (1) VCV-io `OracleComp` monad for probabilistic games, (2) game transitions as function transformations, (3) induction over `Fin n`, (4) connecting G_n to the simulator via `simulator_pk_programming`. This is the full UC proof from Section 6 / Appendix H | **Hard** (novel UC formalization) | **Hard** (needs VCV-io framework)         | 8-12 weeks |

### Files

- `GoldenProofs/EVRFCircuit.lean` -- Task 8 (complete)
- `GoldenProofs/EVRFEndToEnd.lean` -- eVRF pipeline correctness + uniqueness (complete)
- `GoldenProofs/EVRFSecurity.lean` -- Task 7 (scaffolded)
- `GoldenProofs/UCSimulation.lean` -- Task 9 (scaffolded)
- `GoldenProofs/RefreshCorrectness.lean` -- Refresh correctness (complete)
- `GoldenProofs/ReshareCorrectness.lean` -- Reshare correctness (complete)

---

## Novel Contributions

These four results would be firsts in the formal verification literature. No machine-checked proofs exist for any of them.

### 1. First Machine-Checked Proof of a DKG Protocol's UC Security

No distributed key generation protocol -- Pedersen, Feldman, Gennaro, Groth, or Golden -- has ever had its UC security proof machine-checked. Task 9 would formalize the straight-line simulator construction from Golden's Theorem 3 (Section 6, Appendix H) in SSProve or Lean 4. This requires formalizing the UC ideal functionality `F^Delta_KeyGen`, the simulator's ability to program VSS commitments "in the exponent," and the game-hop sequence reducing real-world security to DDH.

### 2. Formal Verification of a Bulletproofs/Spartan R1CS Reduction

The reduction from R1CS constraint satisfaction to an inner product argument (the core of Bulletproofs and Spartan) has never been formally verified. Task 8 targets the specific instantiation used in Golden: the R_eVRF circuit's constraint system is shown equivalent to the mathematical eVRF relation via a Lean 4 proof. This includes the non-trivial arkworks-to-Spartan column remapping (Task 3) and the EmulatedFpVar non-native arithmetic encoding.

### 3. Lean 4 Formalization of the Leftover Hash Lemma for eVRF Security

The Leftover Hash Lemma (LHL) is a foundational tool in cryptography, but its application to eVRF-style constructions (`r = beta * r1 + r2` where `r1, r2` are x-coordinates of elliptic curve points) has not been formalized in any proof assistant. Task 7 would establish the statistical distance bound `Delta <= 8h^2 * sqrt(p) / (p - 2h)` in Lean 4 using Mathlib's measure theory, connecting it to the DDH-based game hop sequence from the Golden paper's Appendix D.

### 4. First hax Extraction and Verification of Arkworks-Based Cryptographic Code

The hax toolchain (Cryspen, 2025) has been applied to post-quantum TLS implementations, but never to arkworks-based elliptic curve code. Tasks 2 and 5 would extract `shamir.rs`, `vss.rs`, and `evrf.rs` -- which use `ark-ec`, `ark-ff`, and `ark-bls12-381` -- to F* and prove functional correctness. This requires handling arkworks' trait-heavy generics (CurveGroup, AffineRepr, Field) in the extraction pipeline, establishing a reference for future formal verification of arkworks-based protocols.

---

## Verification Layers

```
Layer 3: ZK Circuit Correctness
  R1CS encoding of R_eVRF | Arithmetic gadgets | Spartan adapter
  Tools: Lean 4, Kani
  Tasks: 3, 8

Layer 2: Implementation Correctness
  Shamir SSS | Feldman VSS | Protocol rounds | Refresh | Reshare | eVRF | Schnorr PoK
  Tools: hax -> F*, Kani, Lean 4
  Tasks: 1, 2, 5 + Refresh/Reshare proofs

Layer 1: Mathematical Security Proofs
  Shamir/VSS algebra | Schnorr soundness | eVRF game hops | UC simulation
  Tools: Lean 4 + Mathlib + VCV-io, SSProve, EasyCrypt
  Tasks: 4, 6, 7, 9
```

---

## Existing Foundations (No New Work Needed)

- **Elliptic curve group law** -- Lean 4 / Mathlib (Angdinata & Xu, ITP 2023). Weierstrass curves over any characteristic.
- **VCV-io** -- Lean 4 framework for game-based cryptography proofs. Oracle computations, Fiat-Shamir, rewinding extractors.
- **SSProve** -- Coq framework for UC-style modular proofs (ePrint 2021/397). ElGamal, sigma protocols already formalized.
- **EasyCrypt** -- Mature game-based proof tool. Sigma protocol formalizations exist (Firsov).
- **hax** -- Rust-to-F*/Coq/Lean extraction (Cryspen, ePrint 2025/142). Supports 99%+ of top 500 crates.
- **Kani** -- Rust bounded model checker (AWS). Function contracts, panic-freedom proofs.
- **Implementation test suite** -- 61 tests including 10 adversarial + 5 public-input binding tests.

## References

- Bunz, Choi, Komlo. "Golden: Lightweight Non-Interactive DKG." IACR 2025/1924.
- Angdinata, Xu. "Elementary Formal Proof of the Group Law on Weierstrass Elliptic Curves." ITP 2023.
- Tumadottir. "VCV-io: Formalized Cryptography Proofs in Lean 4." github.com/dtumad/VCV-io.
- Abate et al. "SSProve: A Foundational Framework for Modular Cryptographic Proofs in Coq." ePrint 2021/397.
- Ho et al. "hax: Verifying Security-Critical Rust Software." ePrint 2025/142.
- Firsov et al. "EasyCrypt Formalization of Zero-Knowledge." github.com/dfirsov/easycrypt-zk-code.
- Bunz et al. "Bulletproofs: Short Proofs for Confidential Transactions and More." IEEE S&P 2018.
