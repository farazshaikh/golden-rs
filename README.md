# golden-rs

Rust implementation of the **Golden** non-interactive Distributed Key Generation protocol.

**Paper:** [Golden: Lightweight Non-Interactive Distributed Key Generation](https://eprint.iacr.org/2025/1924) -- Bünz, Choi, Komlo (IACR 2025/1924)

## Overview

Golden achieves public verifiability in a single broadcast round using an exponent Verifiable Random Function (eVRF) built on Diffie-Hellman key exchange. No ElGamal, Paillier, or class-group encryption. Security relies only on discrete-log/DDH assumptions over BLS12-381.

## Protocols

| Protocol | Description |
|----------|-------------|
| **DKG** | One-round distributed key generation. Nodes sample secrets, create Shamir shares, encrypt via eVRF pads, and broadcast. Public verifiability -- no complaints round. |
| **Refresh** | Proactive share rotation. Shares change, global secret and public key stay the same. |
| **Reshare** | Membership change. Transfer the secret to a new group with different (n, t) parameters. |

## Security

- **Schnorr PoK** on PKI registration (Appendix F) -- prevents rogue-key attacks
- **ark-spartan NIZK** for eVRF proofs (Section 3.4 / [15]) -- R1CS satisfiability with public-input binding
- **RFC 9380** hash-to-curve (Wahby-Boneh map for BLS12-381 G1)
- **OsRng** for all production key material

## Proof System

Per Golden Section 3.4: "We use Bulletproofs [15] to prove R1CS satisfiability." The R_eVRF circuit (Section 4.3, Figure 3) is synthesized via arkworks, then proved and verified using [ark-spartan](https://github.com/arkworks-rs/spartan)'s NIZK system. This provides:

- Sound R1CS-to-IPA reduction (Spartan protocol, avoids the completeness-soundness gap in the 2018 Bulletproofs paper)
- Public-input binding: the verifier re-synthesizes the circuit with claimed public inputs (pk1, pk2, R, beta) and checks the proof against them
- Merlin transcripts for correct Fiat-Shamir transform

## Build

```bash
cargo build --release
cargo test
```

61 tests, 0 clippy warnings. BLS12-381 via arkworks 0.5.

## Architecture

```
src/
├── shamir.rs            Shamir secret sharing (Section 3.3)
├── vss.rs               Feldman VSS commitments (Section 3.2)
├── evrf.rs              eVRF pad derivation via NIKE (Section 4)
├── schnorr_pok.rs       PKI proof of knowledge (Appendix F)
├── protocol.rs          DKG + refresh rounds (Section 5, Figure 4)
├── reshare.rs           Membership-change resharing
├── zk_evrf/             R_eVRF circuit + ark-spartan NIZK prove/verify (Section 4.3)
│   ├── circuit.rs       R_eVRF and batch eVRF circuits (Figure 3, Section 4.4)
│   ├── adapter.rs       Arkworks-to-Spartan R1CS conversion
│   ├── bit_decompose.rs Bit-decomposition gadget
│   ├── exponentiation.rs Point exponentiation gadget (non-native Fq)
│   └── nonnative.rs     Non-native field arithmetic (Appendix E)
├── bulletproofs/        Reference IPA implementation (Section 3.4)
├── network.rs           Broadcast channel + peer discovery
├── reshare_network.rs   Old/new group broadcast for resharing
├── node.rs              DKG/refresh participant (tokio task)
├── reshare_node.rs      Reshare participant (old dealer / new receiver)
├── types.rs             Shared types with Borsh serialization
└── main.rs              Integration test: DKG -> Refresh -> Reshare pipeline
```

## Details

See [Implementation.md](Implementation.md) for paper coverage, security properties, proof system design, deviations from the paper, and remaining TODOs.
