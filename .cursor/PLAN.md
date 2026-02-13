# Golden DKG Prototype -- Master Plan

## Overview

Rust prototype of the Golden non-interactive Distributed Key Generation protocol.
Nodes run as tokio tasks, communicate over broadcast channels, use arkworks BLS12-381.
ZK proofs deferred (TODO). BLS threshold signatures stubbed for a future paper.

Paper: "Golden: Lightweight Non-Interactive Distributed Key Generation"
(Bünz, Choi, Komlo -- https://eprint.iacr.org/2025/1924)

## Subagent Protocol -- MANDATORY

Before implementing ANY phase, every subagent MUST:

1. **Read the paper first:** Read `papers/golden_dkg.md` in the project root before writing any code.
2. **Read the relevant phase plan** from `.cursor/plans/` if one exists for the current task.
3. **Cross-reference Figure 4** (Section 5.2 protocol pseudocode in the paper) for Round0/Round1 correctness.
4. **Reference Section 4** for eVRF construction details (Evaluate, Verify, R_eVRF relation).
5. **Reference Section 3.3** for Shamir secret sharing and Lagrange interpolation definitions.
6. **Reference Section 5.3** for batch optimizations (batch proving, batch verification).
7. **Quote the relevant paper section** in code comments when implementing protocol-critical logic.

The paper is the source of truth. If the plan and the paper disagree, the paper wins.

## Plans

All plans are stored in `.cursor/plans/` within this project:

- `golden_dkg_prototype_3539a933.plan.md` -- Original prototype plan (Phases 1-8)
- `golden_dkg_prototype_7870b8e2.plan.md` -- Updated prototype plan
- `paper_reference_setup_3cb46de2.plan.md` -- Paper reference setup
- `key_resharing_implementation_28059129.plan.md` -- Key refresh (proactive share rotation via zero secret sharing)

## Project Structure

```
/wrk/tmt/goldenkeysharing/
├── Cargo.toml
├── README.md
├── TODO_ZK_PROOFS.md
├── papers/
│   └── golden_dkg.md   # Full paper reference -- READ THIS FIRST
├── .cursor/
│   ├── PLAN.md          # This file -- master plan
│   └── plans/           # Phase-specific plans
└── src/
    ├── lib.rs          # Re-exports
    ├── main.rs         # Test harness: spawn n=5, t=3, verify
    ├── types.rs        # NodeId, Round0Msg, Ciphertext, DkgOutput
    ├── shamir.rs       # Polynomial, shares, Lagrange interpolation
    ├── vss.rs          # Feldman VSS commitments
    ├── evrf.rs         # Simplified eVRF (DH pad, no ZK proof)
    ├── network.rs      # Broadcast channel + peer discovery
    ├── node.rs         # Node struct, async run()
    └── protocol.rs     # Round0 + Round1 logic
```

## Crypto Types (BLS12-381)

- Scalar field: `ark_bls12_381::Fr`
- G1 projective: `ark_bls12_381::G1Projective`
- G1 affine: `ark_bls12_381::G1Affine`
- Generator: `G1Affine::generator()`
- x-coordinate extraction: `point.into_affine().x` -> `Fq`, reduce mod r via BigInt conversion

## Phases

### Phase 1: Scaffold
Create Cargo.toml with dependencies, src/lib.rs with module declarations,
src/types.rs with core type definitions, and empty stubs for all other modules.
**Verify:** `cargo build` succeeds.

### Phase 2: Shamir Secret Sharing
Implement src/shamir.rs:
- `Polynomial` struct: `Vec<Fr>` coefficients, `new_random(secret, degree, rng)`, `evaluate(x)`
- `share(poly, n)` -> `Vec<(u32, Fr)>`
- `lagrange_interpolate_at_zero(shares: &[(u32, Fr)]) -> Fr`
**Verify:** `cargo test -p goldenkeysharing shamir` -- create secret, share among 5, reconstruct from any 3.

### Phase 3: Feldman VSS
Implement src/vss.rs:
- `commit(poly: &Polynomial) -> Vec<G1Affine>` -- compute `g^{a_k}` for each coefficient
- `verify_share(commitment, index, share) -> bool` -- check `g^{share} == product(A_k^{j^k})`
**Verify:** `cargo test -p goldenkeysharing vss` -- commit, verify valid share, reject tampered share.

### Phase 4: Simplified eVRF
Implement src/evrf.rs:
- `derive_pad(sk: Fr, peer_pk: G1Affine, msg: &[u8], beta: Fr) -> (Fr, G1Affine)`
  1. S = peer_pk * sk (DH shared secret)
  2. k = int(S.x) mod r
  3. T1 = H1(msg)^k, T2 = H2(msg)^k (hash-to-curve with domain separation)
  4. r = beta * int(T1.x mod r) + int(T2.x mod r)
  5. Return (r, g^r)
- Two parties calling derive_pad with swapped (sk, PK) must get identical r.
**Verify:** `cargo test -p goldenkeysharing evrf` -- two keypairs, derive_pad from both sides, assert equal.

### Phase 5: Network Layer
Implement src/network.rs:
- `Network` struct with `tokio::sync::broadcast::Sender<Round0Msg>`,
  `Arc<RwLock<HashMap<NodeId, G1Affine>>>` peer table, and `Arc<Barrier>`
- `register(id, pk) -> broadcast::Receiver<Round0Msg>` -- add to peer table, return receiver
- `broadcast(msg)` -- send to broadcast channel
- `get_peers() -> HashMap<NodeId, G1Affine>` -- snapshot peer table
- `wait_ready()` -- barrier wait
**Verify:** `cargo test -p goldenkeysharing network` -- register 3 nodes, broadcast, all receive.

### Phase 6: Protocol Logic
Implement src/protocol.rs:
- `round0(id, n, t, sk, peers, beta, rng) -> (Round0Msg, Fr)` where Fr is own share x_{i,i}
  1. Sample omega, build polynomial, compute VSS commitment
  2. For each peer: derive eVRF pad, encrypt share z = r + f(j)
  3. Return broadcast message and own retained share
- `round1(id, sk, peers, own_share, msgs, beta) -> Result<DkgOutput, Error>`
  1. For each msg_j, for each peer k: verify g^{z_{j,k}} == R_{j,k} * X_{j,k}
  2. Decrypt own shares: re-derive r_{j,i}, compute x_{j,i} = z_{j,i} - r_{j,i}
  3. Aggregate: sk_i = sum of all shares for self
  4. Derive PK = product of A_{j,0}, derive PK_shares
**Verify:** `cargo build` succeeds (integration tested in Phase 7).

### Phase 7: Node + Integration
Implement src/node.rs and src/main.rs:
- `Node { id, n, t, sk, pk, beta, network, receiver }`
- `async fn run(self) -> DkgOutput` -- wait_ready, round0, broadcast, collect n-1 msgs, round1
- main.rs: spawn 5 nodes (t=3), collect outputs, assert:
  1. All nodes agree on PK
  2. All nodes agree on all public key shares
  3. ALL C(5,3)=10 combinations of 3-out-of-5 shares reconstruct the SAME sk, and g^sk == PK
  4. Each node's public key share matches g^{sk_i}
  5. Print timing and success summary
**Verify:** `cargo run --release` passes all assertions including exhaustive combination check.

### Phase 8: Cleanup
- Create TODO_ZK_PROOFS.md documenting what the Bulletproofs eVRF circuit requires
- Create README.md with build/run instructions
- `cargo fmt && cargo clippy` -- fix all warnings
**Verify:** `cargo clippy --workspace` clean, `cargo run --release` still passes.
