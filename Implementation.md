# Golden DKG -- Implementation Notes

## Paper

This implements the **Golden** non-interactive Distributed Key Generation protocol from [Bünz, Choi, Komlo (IACR 2025/1924)](https://eprint.iacr.org/2025/1924). Golden achieves public verifiability in a single broadcast round using a novel exponent Verifiable Random Function (eVRF) built on Diffie-Hellman key exchange, avoiding ElGamal/Paillier/class-group encryption entirely. Security relies only on discrete-log/DDH assumptions over BLS12-381.

## Three Protocols

### 1. DKG (Distributed Key Generation)

One-round protocol where n nodes each sample a random secret, create Shamir shares, encrypt them using eVRF-derived pads, and broadcast. Every node verifies all broadcasts (public verifiability -- no complaints round needed), decrypts its shares, and aggregates into its secret key share sk_i. The global secret sk = sum(omega_i) is never known by any single party. All C(n,t) combinations of t shares reconstruct the same sk.

### 2. Refresh (Proactive Share Rotation)

Same Golden protocol but with omega_i = 0 for all participants (zero secret sharing). Each node's share gets a random delta added, but since all deltas sum to zero at x=0, the global sk and PK are unchanged. Round 1 includes an additional check: A_{j,0} must equal the identity point (verifying f_j(0) = 0). Shares rotate; secret stays.

### 3. Reshare (Membership Change)

Transfers the secret from an old group (n_old, t_old) to a new group (n_new, t_new). Each old member deals its existing share sk_i under a new polynomial of degree t_new - 1, encrypted via eVRF to new members. New members aggregate using Lagrange interpolation over old member indices. Supports adding nodes, removing nodes, and changing the threshold -- all while preserving sk and PK.

## Security Properties

### PKI Proof of Knowledge (Appendix F)

Every node must prove knowledge of its secret key when registering its public key with the network. Implemented as a non-interactive Schnorr proof of knowledge via Fiat-Shamir:

1. Prover samples nonce k, computes R = g^k
2. Challenge c = H("golden-schnorr-pok" || g || PK || R)
3. Response s = k + c * sk
4. Verifier checks g^s == R + c * PK

Registration is rejected if the PoK fails. This prevents rogue-key attacks where an adversary registers a public key as a function of honest parties' keys to bias the DKG output.

### eVRF Zero-Knowledge Proofs

Full Bulletproofs IPA verification for eVRF proofs. The prover synthesizes an R1CS circuit (sk bit-decomposition, non-native Fq point arithmetic) and commits to the assignment via Pedersen commitments over deterministic generators. The verifier:

1. Reconstructs generators from the proof's declared size (n = 2^k)
2. Replays the Fiat-Shamir transcript with the stored commitment P
3. Runs the Inner Product Argument verifier against P

Tampered proofs (mutated IPA scalars or commitment) are rejected.

### Randomness

All production key material (identity keypairs, polynomial coefficients, Schnorr nonces) uses `OsRng` -- the OS-provided cryptographically secure random number generator. Deterministic test RNG (`ark_std::test_rng()`) is confined to `#[cfg(test)]` modules only.

## Native vs On-Chain Verification

The paper's Bulletproofs eVRF proof system (Section 4) describes a two-curve architecture: G_in (BLS12-381 G1) for DKG operations and G_out (a companion curve) for the proof system. This G_out requirement exists because the Bulletproofs R1CS operates over G_out's scalar field, which must equal G_in's base field.

**The problem:** BLS12-381 has no known companion curve with matching order. Constructing one via Complex Multiplication is computationally infeasible for a 381-bit prime (the Hilbert class polynomial would have degree ~2^191).

**Our resolution:** Native verification. Nodes verify Bulletproofs proofs by running the IPA verifier directly on BLS12-381 G1 -- no companion curve needed. The R1CS operates over Fr (255-bit scalar field) with non-native Fq (381-bit base field) arithmetic via arkworks' audited `EmulatedFpVar`. The "Constraint Capture" pattern uses arkworks as a circuit compiler, extracting R1CS matrices for our custom Bulletproofs prover.

**On-chain path (documented, not implemented):** Wrap the Bulletproof verifier inside a Groth16 circuit over BLS12-381. ~50K constraints, <1s prover time, ~250K gas on-chain. Alternative: Halo-style atomic accumulation for cycle-free recursion.

## Deviations from the Paper

**Terminology:** The paper uses "key resharing" for what the threshold crypto literature calls "key refresh" (proactive share rotation with zero secret sharing). We separated the concepts: "refresh" = same group, rotated shares; "reshare" = membership change.

**Hash-to-curve:** The paper specifies random oracles H_1, H_2 mapping to G_in. We implement RFC 9380 compliant hash-to-curve using the Wahby-Boneh (WB) map for BLS12-381 G1 via `ark_ec::hashing::MapToCurveBasedHasher`. Domain-separated: `"golden-evrf-h1"` and `"golden-evrf-h2"`.

**eVRF circuit:** The paper achieves 3598 Fq-level constraints (14*lambda + 14 for lambda=256). Our implementation has higher Fr-level constraint count due to EmulatedFpVar's non-native arithmetic overhead (~7K constraints per point operation). The logical circuit structure matches the paper; the expansion is a known cost of the Appendix E / native-verification approach.

**Batch proofs:** Implemented per Section 5.3 -- one proof per node covering all n-1 eVRF evaluations, with shared sk_1 bit-decomposition. Proof size scales logarithmically.

## Codebase

13 modules, 61 tests (including 10 adversarial). BLS12-381 via arkworks 0.5. Borsh serialization for all network types. Tokio async nodes communicating over broadcast channels. Zero clippy warnings.

| Module            | Purpose                                                             |
| ----------------- | ------------------------------------------------------------------- |
| `shamir`          | Polynomial secret sharing, Lagrange interpolation                   |
| `vss`             | Feldman Verifiable Secret Sharing (polynomial commitments)          |
| `evrf`            | eVRF pad derivation with RFC 9380 hash-to-curve                     |
| `schnorr_pok`     | Schnorr proof of knowledge for PKI registration                     |
| `network`         | Simulated broadcast + peer discovery (DKG/refresh)                  |
| `reshare_network` | Broadcast network for old/new group resharing                       |
| `node`            | DKG/refresh participant (tokio task)                                |
| `reshare_node`    | Reshare participant (old dealer / new receiver)                     |
| `protocol`        | DKG round0/round1, refresh round0/round1                            |
| `reshare`         | Reshare deal/receive logic                                          |
| `bulletproofs`    | IPA prover/verifier, Fiat-Shamir transcript, generators             |
| `zk_evrf`         | R1CS circuit (non-native Fq), constraint capture, eVRF prove/verify |
| `types`           | Shared types with Borsh serialization                               |

### Implemented (Paper Coverage)

| Paper Section             | What                                                                           | Status |
| ------------------------- | ------------------------------------------------------------------------------ | ------ |
| 3.1 Shamir Secret Sharing | Polynomial sharing + Lagrange interpolation                                    | Done   |
| 3.2 Feldman VSS           | Polynomial commitments, share verification                                     | Done   |
| 3.3 Bulletproofs          | IPA prover + verifier over BLS12-381 G1                                        | Done   |
| 4.2 eVRF Definition       | NIKE pad derivation (DH shared secret -> x-coord -> hash-to-curve)             | Done   |
| 4.3 R_eVRF Relation       | Circuit: bit-decompose sk, point exponentiation, extract x-coords              | Done   |
| 4.4 Circuit Structure     | Bit-decomposition gadget, exponentiation gadget, non-native Fq                 | Done   |
| 4.6 Batch Optimization    | One proof for n-1 eVRF evals, shared sk bit-decomposition                      | Done   |
| 5.1 PKI + PoK             | Schnorr proof of knowledge on registration (Appendix F)                        | Done   |
| 5.2 Golden Protocol       | Round 0 (share + encrypt + broadcast) + Round 1 (verify + decrypt + aggregate) | Done   |
| 5.2 Key Refresh           | Zero-secret-sharing variant, A_{j,0} = identity check                          | Done   |
| App E                     | Native verification (G_in = G_out, non-native arithmetic)                      | Done   |

### Additional Features

| Feature | Status |
|---------|--------|
| Reshare: shrink (5,3)->(4,2), grow (4,2)->(7,4) | Done |
| RFC 9380 hash-to-curve (WB map for BLS12-381 G1) | Done |
| Malicious participant detection | Done (10 adversarial tests) |
| Production randomness (OsRng) | Done |
| Borsh serialization for all network types | Done |
| Exhaustive C(n,t) reconstruction verification | Done |

### TODO

| #   | Item                                      | Description                                                                                                                                                                                                                                                                                           |
| --- | ----------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| 1   | Public-input binding in eVRF verification | `verify_evrf` checks IPA against stored commitment P but does not re-derive P from public inputs (pk1, pk2, R, beta). A malicious prover could supply a valid IPA proof for a different circuit. Fix: verifier re-synthesizes circuit with public inputs, reconstructs expected P, checks it matches. |
| 2   | R1CS-to-IPA reduction module              | `bulletproofs/r1cs.rs` is a TODO stub. The reduction (Section 3.4: random linear combination of constraint rows to inner product relation) is baked into the prove/verify flow but not factored out as a standalone module.                                                                           |
| 3   | Benchmarks                                | Paper provides specific performance numbers (Table 1: 223 kb bandwidth, 13.5s for n=50). No benchmarks exist to compare against.                                                                                                                                                                      |

### Out of Scope

| Item                                    | Reason                                                                                           |
| --------------------------------------- | ------------------------------------------------------------------------------------------------ |
| BLS threshold signatures                | Separate paper; DKG output (secret shares) is the input to this next phase                       |
| Real networking (NATS, libp2p)          | Currently simulated with tokio broadcast channels; production transport is a separate concern    |
| Persistent state / share storage        | No disk persistence of shares; depends on deployment target                                      |
| On-chain verification (Groth16 wrapper) | Documented path (~50K constraints, ~250K gas), not implemented; requires Ethereum/L2 integration |
| Reshare across disjoint networks        | Paper assumes old and new groups can communicate; cross-network bridging is deployment-specific  |
