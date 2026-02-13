# Golden DKG Prototype

Rust prototype of the **Golden** non-interactive Distributed Key Generation protocol.

Based on: [Golden: Lightweight Non-Interactive Distributed Key Generation](https://eprint.iacr.org/2025/1924)
by Benedikt Bünz, Kevin Choi, and Chelsea Komlo.

## What this implements

- **Shamir Secret Sharing** with Lagrange interpolation
- **Feldman VSS** commitments for verifiable polynomial commitments
- **Simplified eVRF** using Diffie-Hellman shared secrets for encrypted share distribution
- **Tokio-based node abstraction** with broadcast channels simulating a network
- **Full DKG protocol** (Round 0 + Round 1) with threshold reconstruction verification

## What is deferred

- **Bulletproofs ZK proofs** for the eVRF (see `TODO_ZK_PROOFS.md`)
- **BLS threshold signatures** (pending separate paper)
- Standards-compliant hash-to-curve (uses hash-and-multiply prototype)

## Build and Run

```bash
# Build
cargo build --release

# Run the DKG test (spawns 5 nodes, threshold 3)
cargo run --release

# Run unit tests
cargo test
```

## Architecture

```
src/
├── lib.rs          # Module declarations
├── main.rs         # Integration test: spawn n nodes, verify DKG output
├── types.rs        # NodeId, Round0Msg, Ciphertext, DkgOutput
├── shamir.rs       # Polynomial, share generation, Lagrange interpolation
├── vss.rs          # Feldman VSS: commit, verify_share, expected_share_commitment
├── evrf.rs         # Simplified eVRF: DH pad derivation (no ZK proof)
├── network.rs      # Broadcast channel + peer discovery table
├── node.rs         # Node struct with async run() lifecycle
└── protocol.rs     # Round 0 (generate+encrypt) and Round 1 (verify+decrypt+aggregate)
```

## Protocol Flow

1. Each node generates an identity keypair and registers with the network
2. **Round 0**: Each node samples a secret, creates Shamir shares, encrypts them
   with eVRF-derived pads, and broadcasts the encrypted shares + VSS commitment
3. **Round 1**: Each node verifies all ciphertexts against VSS commitments,
   decrypts its own shares by re-deriving eVRF pads, and aggregates into
   its final secret key share
4. All nodes derive the shared public key PK from the VSS commitments

## Curve

Uses **BLS12-381** via the arkworks ecosystem (`ark-bls12-381` 0.5).
