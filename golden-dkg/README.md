# golden-dkg

Pure-crypto Rust library implementing the **Golden** non-interactive Distributed Key Generation protocol from [Bünz, Choi, Komlo (IACR 2025/1924)](https://eprint.iacr.org/2025/1924).

Golden achieves public verifiability in a single broadcast round using an exponent Verifiable Random Function (eVRF) built on Diffie-Hellman key exchange. Security relies only on discrete-log/DDH assumptions over BLS12-381.

## Features

- **One-round DKG**: single broadcast, no interactive rounds
- **Public verifiability**: anyone can verify dealings without secret information
- **No trusted setup**: transparent proof system via Spartan NIZK
- **Proactive refresh**: rotate shares without changing the public key
- **Membership change**: reshare secret to a new participant group
- **Formally verified**: 38 Lean 4 theorems, 18 F\* extraction modules, 20 Kani harnesses

## Usage

```rust
use golden_dkg::{dkg, types::*};
use std::collections::HashMap;
use ark_ff::UniformRand;

let mut rng = rand::rngs::OsRng;
let alice = Participant::new(1, &mut rng);
let bob = Participant::new(2, &mut rng);

let mut peers = HashMap::new();
peers.insert(alice.id, alice.pk);
peers.insert(bob.id, bob.pk);

let config = DkgConfig {
    n: 2, t: 2,
    beta: Scalar::rand(&mut rng),
    session_id: SessionId::random(&mut rng),
};

let dealing = dkg::create_dealing(&alice, &config, &peers, &mut rng).unwrap();
```

See the [crate documentation](https://docs.rs/golden-dkg) for the full API.

## Formal Verification

This crate includes multi-layer formal verification:

- **Lean 4 + Mathlib**: 38 machine-checked theorems proving the paper's algebraic properties
- **hax + F\***: Rust source extracted to 18 F\* modules with specification bridge proofs
- **Kani**: 20 bounded model checking harnesses for panic-freedom

Run the verification pipeline: `make verify` (requires Lean 4, F\* v2025.10.06, hax v0.3.6).

## License

MIT OR Apache-2.0
