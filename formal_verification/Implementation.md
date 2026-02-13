# Formal Verification of Golden DKG -- Implementation Plan

## Overview

Formal verification of the Golden non-interactive Distributed Key Generation protocol (Bunz, Choi, Komlo -- IACR 2025/1924) and its Rust implementation. The effort spans three layers: mathematical security proofs, implementation correctness, and ZK circuit soundness.

The verification uses Lean 4 + Mathlib + VCV-io for mathematical proofs, hax for Rust-to-F* extraction, Kani for bounded model checking, and EasyCrypt/SSProve as alternatives for game-based and UC-style proofs.

---

## Task Table

| # | Task | Layer | Tool | What Is Proven | Effort | Status |
|---|------|-------|------|----------------|--------|--------|
| 1 | Safety (no panics) across all modules | Implementation | Kani | Absence of panics, overflows, and assertion violations for all inputs within bound. Covers `shamir`, `vss`, `protocol`, `evrf`, `adapter`. | 1-2 weeks | Not started |
| 2 | Shamir + VSS functional correctness | Implementation | hax -> F* | `lagrange_interpolate_at_zero` is correct polynomial interpolation. `verify_share` accepts only valid shares. `round1` output `sk_i = sum_j f_j(i)` when all broadcasts are honest. | 3-4 weeks | Not started |
| 3 | Adapter column remapping correctness | Circuit | Kani | The arkworks-to-Spartan column index remapping in `to_spartan()` is a correct bijection: every arkworks column maps to a unique Spartan column and back. No out-of-bounds indices. | 3-5 days | Not started |
| 4 | Shamir/VSS algebraic properties | Paper Math | Lean 4 + Mathlib | `forall (f : Polynomial F_r) (S : Finset), |S| >= t -> lagrange_interpolate S f = f(0)`. Feldman VSS binding: if `commit(f) = C` and `verify_share(C, i, s) = true`, then `s = f(i)` under DL hardness. | 3-4 weeks | Not started |
| 5 | eVRF DH symmetry proof | Implementation | hax -> F* | `derive_pad(sk_i, pk_j, msg, beta) == derive_pad(sk_j, pk_i, msg, beta)` -- the pad derivation is symmetric under DH key exchange. Extracted from Rust source and proven in F*. | 2-3 weeks | Not started |
| 6 | Schnorr PoK soundness | Paper Math | Lean 4 + VCV-io | Schnorr proof of knowledge is sound with knowledge error `1/|F_r|` in the random oracle model. Uses VCV-io `OracleComp` for ROM modeling and rewinding extractor formalization. | 2-3 weeks | Not started |
| 7 | eVRF security game hops | Paper Math | Lean 4 + VCV-io | Game 0->1: DH shared secret indistinguishability reduces to NIKE unrecoverability. Game 1->2: Leftover Hash Lemma proves `r = beta * r1 + r2` is pseudorandom. Statistical distance bound `Delta <= O(1/sqrt(p))`. | 4-6 weeks | Not started |
| 8 | R1CS circuit encodes R_eVRF relation | Circuit | Lean 4 | Satisfying assignment to the R1CS constraint system is equivalent to the R_eVRF mathematical relation: `cs.is_satisfied w <-> R_eVRF w.pk1 w.pk2 w.R w.beta w.sk1`. Covers completeness and knowledge extraction. | 4-6 weeks | Not started |
| 9 | UC simulation (full paper proof) | Paper Math | SSProve (Coq) or Lean 4 | Theorem 3: Pi_Golden-PKI securely realizes `F^Delta_KeyGen` in the `(F_zk, F_eVRF)`-hybrid model. Straight-line simulation: simulator programs `tau`'s VSS commitment without knowing `log(Y)`. | 8-12 weeks | Not started |

**Practical milestone (Tasks 1-6): ~12-16 weeks**
**Full formalization (Tasks 1-9): ~6-9 months**

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
  Shamir SSS | Feldman VSS | Protocol rounds | eVRF | Schnorr PoK
  Tools: hax -> F*, Kani
  Tasks: 1, 2, 5

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
