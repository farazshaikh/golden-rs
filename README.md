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
- **Bulletproofs IPA** verification for eVRF proofs (Section 4) -- native verification on BLS12-381
- **RFC 9380** hash-to-curve (Wahby-Boneh map for BLS12-381 G1)
- **OsRng** for all production key material

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
├── bulletproofs/        IPA prover/verifier (Section 3.4)
├── zk_evrf/             R_eVRF circuit + proof system (Section 4.3, Appendix E)
├── network.rs           Broadcast channel + peer discovery
├── reshare_network.rs   Old/new group broadcast for resharing
├── node.rs              DKG/refresh participant (tokio task)
├── reshare_node.rs      Reshare participant (old dealer / new receiver)
├── types.rs             Shared types with Borsh serialization
└── main.rs              Integration test: DKG -> Refresh -> Reshare pipeline
```

## Details

See [Implementation.md](Implementation.md) for paper coverage, security properties, native vs on-chain verification, deviations from the paper, and remaining TODOs.
