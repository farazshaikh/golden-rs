# Formal Verification of Golden DKG

Machine-checked proofs of correctness and security for the Golden non-interactive Distributed Key Generation protocol and its Rust implementation.

## What This Is

Golden (Bunz, Choi, Komlo -- IACR 2025/1924) is a one-round DKG protocol achieving public verifiability via a novel exponent Verifiable Random Function (eVRF). This directory contains the formal verification effort: proving that the mathematical claims in the paper are correct, the Rust implementation faithfully realizes the paper's algorithms, and the ZK proof circuit correctly encodes the eVRF relation.

## Structure

```
formal_verification/
  README.md              -- This file
  Implementation.md      -- Task table, novel contributions, and detailed plan
  lean/                  -- Lean 4 proofs (Mathlib + VCV-io)
  fstar/                 -- F* proofs from hax extraction
  kani/                  -- Kani proof harnesses
```

## Three Verification Layers

### Layer 1: Mathematical Security Proofs (Lean 4 + VCV-io)

Machine-check the paper's security theorems:
- Shamir secret sharing correctness (polynomial interpolation)
- Feldman VSS binding (under DL hardness)
- Schnorr PoK soundness in the random oracle model
- eVRF security via DDH + Leftover Hash Lemma game hops
- UC security: Golden realizes F^Delta_KeyGen (Theorem 3)

### Layer 2: Implementation Correctness (hax + Kani)

Prove the Rust code matches the paper:
- Extract `shamir.rs`, `vss.rs`, `evrf.rs` to F* via hax, prove functional specs
- Kani proof harnesses for panic-freedom across all modules
- DH symmetry of eVRF pad derivation
- Protocol round correctness: `sk_i = sum_j f_j(i)`

### Layer 3: Circuit Soundness (Lean 4 + Kani)

Prove the ZK proof system is correct:
- R1CS constraint system is equivalent to the R_eVRF mathematical relation
- Arkworks-to-Spartan column remapping is a correct bijection
- Completeness and knowledge soundness of the circuit encoding

## Tools

| Tool | Purpose | Targets |
|------|---------|---------|
| **Lean 4 + Mathlib** | Algebraic properties (polynomials, EC group law, fields) | Shamir, VSS, circuit semantics |
| **VCV-io** | Game-based cryptography proofs (oracle model, reductions) | Schnorr PoK, eVRF security, DDH |
| **SSProve** | UC-style modular proofs in Coq | UC simulation (Theorem 3) |
| **hax** | Rust-to-F* extraction for implementation proofs | shamir.rs, vss.rs, evrf.rs |
| **Kani** | Bounded model checking for Rust safety | Panic-freedom, adapter correctness |

## Status

See [Implementation.md](Implementation.md) for the full task table and current status.

## Novel Contributions

This effort targets four results that would be firsts in the formal verification literature:

1. **First machine-checked UC security proof of any DKG protocol**
2. **First formal verification of a Bulletproofs/Spartan R1CS reduction**
3. **First Lean 4 formalization of the Leftover Hash Lemma for eVRF**
4. **First hax extraction and verification of arkworks-based cryptographic code**

## References

- [Golden paper](https://eprint.iacr.org/2025/1924) -- Bunz, Choi, Komlo. IACR 2025/1924.
- [VCV-io](https://github.com/dtumad/VCV-io) -- Formalized cryptography proofs in Lean 4.
- [SSProve](https://eprint.iacr.org/2021/397) -- Modular cryptographic proofs in Coq.
- [hax](https://hax.cryspen.com/) -- Rust formal verification toolchain.
- [Kani](https://model-checking.github.io/kani/) -- Rust bounded model checker.
- [Mathlib EC](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.html) -- Formal elliptic curve group law.
