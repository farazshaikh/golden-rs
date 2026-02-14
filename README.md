# golden-rs

Rust implementation of the **Golden** non-interactive Distributed Key Generation protocol with machine-checked formal verification.

**Paper:** [Golden: Lightweight Non-Interactive Distributed Key Generation](https://eprint.iacr.org/2025/1924) -- Bunz, Choi, Komlo (IACR 2025/1924)

## Overview

Golden achieves public verifiability in a single broadcast round using an exponent Verifiable Random Function (eVRF) built on Diffie-Hellman key exchange. No ElGamal, Paillier, or class-group encryption. Security relies only on discrete-log/DDH assumptions over BLS12-381.

## Workspace

| Crate | Description |
|-------|-------------|
| [`golden-dkg`](golden-dkg/) | Pure cryptographic library -- all protocol logic, no async |
| [`golden-demo`](golden-demo/) | Demo application with async network simulation |

## Protocols

| Protocol | Module | Description |
|----------|--------|-------------|
| **DKG** | [`golden_dkg::dkg`](golden-dkg/src/dkg.rs) | One-round distributed key generation (Section 5, Figure 4) |
| **Refresh** | [`golden_dkg::refresh`](golden-dkg/src/refresh.rs) | Proactive share rotation -- same group, rotate shares (Section 5.2) |
| **Reshare** | [`golden_dkg::reshare`](golden-dkg/src/reshare.rs) | Membership change -- transfer secret to a new group |

## Formal Verification

The implementation is backed by a multi-layered formal verification effort:

| Layer | Tool | What | Status |
|-------|------|------|--------|
| Paper math | Lean 4 + Mathlib | 37 theorems proving the paper's cryptographic claims | Complete (0 sorry in core files) |
| Spec bridge | F* | 20 lemmas mirroring Lean theorems against extracted Rust code | Phase 1 complete (type-checked) |
| Code extraction | hax + F* | 18 modules extracted from Rust, all pass F* lax-checking | 18/18 PASS |
| Panic-freedom | Kani | 20 proof harnesses covering all modules | All verified |
| Functional tests | cargo test | 51 tests including adversarial scenarios | All pass |

```
Lean 4 (paper math)  <-->  F* specs  <-->  F* extraction  <-->  Rust code
     37 theorems          20 lemmas       18/18 modules        51 tests
```

See [`formal_verification/README.md`](formal_verification/README.md) for the full verification chain diagram and details.

## Security

- **Schnorr PoK** on PKI registration (Appendix F) -- prevents rogue-key attacks
- **ark-spartan NIZK** for eVRF proofs (Section 3.4) -- R1CS satisfiability with public-input binding
- **RFC 9380** hash-to-curve (Wahby-Boneh map for BLS12-381 G1)
- **Session IDs** for replay protection across DKG/refresh/reshare sessions
- **SecretScalar** zeroization on drop for all secret key material

## Build

```bash
cargo build --workspace
cargo test --workspace
```

51 tests, 0 clippy warnings. BLS12-381 via arkworks 0.5.

## Architecture

```
golden-dkg/src/          Pure crypto library
  lib.rs                 Public API: dkg, refresh, reshare, schnorr_pok, shamir, types, zk_evrf
  dkg.rs                 DKG public API: create_dealing, verify_dealing, complete
  refresh.rs             Refresh public API: create_dealing, verify_dealing, complete
  reshare.rs             Reshare public API: deal, verify_dealing, receive
  shamir.rs              Shamir secret sharing (Section 3.3)
  vss.rs                 Feldman VSS commitments (Section 3.2)
  evrf.rs                eVRF pad derivation via NIKE (Section 4)
  schnorr_pok.rs         PKI proof of knowledge (Appendix F)
  protocol.rs            Internal: DKG + refresh round logic
  reshare_protocol.rs    Internal: reshare round logic
  types.rs               MessageHeader, Round0Msg, ReshareMsg, DkgOutput, etc.
  error.rs               DkgError, ReshareError
  zk_evrf/               R_eVRF circuit + ark-spartan NIZK (Section 4.3)
    mod.rs               prove_evrf, verify_evrf, batch variants
    circuit.rs           R_eVRF and batch eVRF circuits (Figure 3)
    adapter.rs           Arkworks-to-Spartan R1CS conversion
    bit_decompose.rs     Bit-decomposition gadget
    exponentiation.rs    Point exponentiation gadget (non-native Fq)
    nonnative.rs         Non-native field arithmetic (Appendix E)

golden-demo/src/         Demo application
  main.rs                DKG -> Refresh -> Reshare pipeline
  node.rs                Async DKG/refresh participant
  network.rs             Broadcast channel simulation
  reshare_node.rs        Async reshare participant
  reshare_network.rs     Reshare broadcast channel

formal_verification/     Formal verification
  README.md              Verification chain diagram and overview
  Implementation.md      Full task table, findings, and plan
  GoldenProofs/          Lean 4 proof files (37 theorems)

proofs/fstar/            F* verification artifacts
  extraction/            18 hax-extracted F* modules
  specs/                 5 F* specification files (20 lemmas)
  models/                Arkworks type stubs for F*
  hax-libs/              Patched hax proof libraries
```

## References

- Bunz, Choi, Komlo. [Golden: Lightweight Non-Interactive Distributed Key Generation](https://eprint.iacr.org/2025/1924). IACR 2025/1924.
- [hax](https://hax.cryspen.com/) -- Rust-to-F* extraction for formal verification.
- [Lean 4 + Mathlib](https://leanprover-community.github.io/mathlib4_docs/) -- Theorem prover with comprehensive math library.
- [Kani](https://model-checking.github.io/kani/) -- Rust bounded model checker.
