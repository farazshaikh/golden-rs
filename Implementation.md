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

### eVRF Zero-Knowledge Proofs (ark-spartan NIZK)

Per Golden paper Section 3.4: "We use Bulletproofs [15] to prove R1CS satisfiability."

The R_eVRF circuit (Section 4.3, Figure 3) is synthesized via arkworks into R1CS matrices, then converted to [ark-spartan](https://github.com/arkworks-rs/spartan) format and proved using the Spartan NIZK proof system. This provides:

1. **Sound R1CS reduction**: The Spartan protocol correctly reduces R1CS constraint satisfaction to an inner product argument, avoiding the completeness-soundness gap identified in the original 2018 Bulletproofs paper (see "Bulletproofs for R1CS: Bridging the Completeness-Soundness Gap" 2025).
2. **Public-input binding**: The verifier re-synthesizes the R_eVRF circuit with the claimed public inputs (pk1, pk2, R, beta) using `EVRFCircuit::for_verification()`, converts to a Spartan Instance, and calls `proof.verify(&instance, &inputs)`. A proof generated for different public inputs is rejected.
3. **Merlin transcripts**: Correct Fiat-Shamir transform via the Merlin transcript protocol, matching the dalek-cryptography standard.

The arkworks-to-Spartan conversion handles the column index remapping between arkworks' `z = [1, inputs, witnesses]` and Spartan's `z = [vars, 1, inputs]` orderings.

### Randomness

All production key material (identity keypairs, polynomial coefficients, Schnorr nonces) uses `OsRng` -- the OS-provided cryptographically secure random number generator. Deterministic test RNG (`ark_std::test_rng()`) is confined to `#[cfg(test)]` modules only.

## Native vs On-Chain Verification

The paper's eVRF proof system (Section 4) describes a two-curve architecture: G_in (BLS12-381 G1) for DKG operations and G_out (a companion curve) for the proof system. This G_out requirement exists because the Bulletproofs R1CS operates over G_out's scalar field, which must equal G_in's base field.

**The problem:** BLS12-381 has no known companion curve with matching order. Constructing one via Complex Multiplication is computationally infeasible for a 381-bit prime (the Hilbert class polynomial would have degree ~2^191).

**Our resolution:** Native verification. Nodes verify proofs by running the Spartan NIZK verifier directly on BLS12-381 G1 -- no companion curve needed. The R1CS operates over Fr (255-bit scalar field) with non-native Fq (381-bit base field) arithmetic via arkworks' audited `EmulatedFpVar`. The "Constraint Capture" pattern uses arkworks as a circuit compiler, extracting R1CS matrices which are then converted to ark-spartan format for proving and verification.

**On-chain path (documented, not implemented):** Wrap the proof verifier inside a Groth16 circuit over BLS12-381. ~50K constraints, <1s prover time, ~250K gas on-chain. Alternative: Halo-style atomic accumulation for cycle-free recursion.

## Deviations from the Paper

**Terminology:** The paper uses "key resharing" for what the threshold crypto literature calls "key refresh" (proactive share rotation with zero secret sharing). We separated the concepts: "refresh" = same group, rotated shares; "reshare" = membership change.

**Hash-to-curve:** The paper specifies random oracles H_1, H_2 mapping to G_in. We implement RFC 9380 compliant hash-to-curve using the Wahby-Boneh (WB) map for BLS12-381 G1 via `ark_ec::hashing::MapToCurveBasedHasher`. Domain-separated: `"golden-evrf-h1"` and `"golden-evrf-h2"`.

**Proof system:** The paper says "use Bulletproofs [15]". We use ark-spartan's NIZK system instead of a direct implementation of the 2018 Bulletproofs R1CS protocol. The 2018 paper has a known completeness-soundness gap (see "Bridging the Gap" 2025). ark-spartan provides a production-quality R1CS-to-IPA reduction with correct transcript management and public-input binding.

**eVRF circuit:** The paper achieves 3598 Fq-level constraints (14*lambda + 14 for lambda=256). Our implementation has higher Fr-level constraint count due to EmulatedFpVar's non-native arithmetic overhead (~7K constraints per point operation). The logical circuit structure matches the paper; the expansion is a known cost of the Appendix E / native-verification approach.

**Batch proofs:** Implemented per Section 5.3 -- one proof per node covering all n-1 eVRF evaluations, with shared sk_1 bit-decomposition. Proof size scales logarithmically.

## Codebase

13 modules, 61 tests (including 10 adversarial + 3 public-input binding). BLS12-381 via arkworks 0.5. ark-spartan for NIZK proofs. Borsh serialization for all network types. Tokio async nodes communicating over broadcast channels. Zero clippy warnings.

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
| `bulletproofs`    | Reference IPA prover/verifier (Section 3.4)                         |
| `zk_evrf`         | R_eVRF circuit, constraint capture, ark-spartan NIZK prove/verify   |
| `types`           | Shared types with Borsh serialization                               |

### Implemented (Paper Coverage)

| Paper Section             | What                                                                           | Status |
| ------------------------- | ------------------------------------------------------------------------------ | ------ |
| 3.1 Shamir Secret Sharing | Polynomial sharing + Lagrange interpolation                                    | Done   |
| 3.2 Feldman VSS           | Polynomial commitments, share verification                                     | Done   |
| 3.4 Bulletproofs [15]     | R1CS satisfiability via ark-spartan NIZK (Spartan R1CS-to-IPA reduction)       | Done   |
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
| Public-input binding in eVRF verification | Done (ark-spartan NIZK, 3 adversarial tests) |
| Production randomness (OsRng) | Done |
| Borsh serialization for all network types | Done |
| Exhaustive C(n,t) reconstruction verification | Done |

### TODO

| #   | Item       | Description                                                                                                                      |
| --- | ---------- | -------------------------------------------------------------------------------------------------------------------------------- |
| 1   | Benchmarks | Paper provides specific performance numbers (Table 1: 223 kb bandwidth, 13.5s for n=50). No benchmarks exist to compare against. |

### Out of Scope

| Item                                    | Reason                                                                                           |
| --------------------------------------- | ------------------------------------------------------------------------------------------------ |
| BLS threshold signatures                | Separate paper; DKG output (secret shares) is the input to this next phase                       |
| Real networking (NATS, libp2p)          | Currently simulated with tokio broadcast channels; production transport is a separate concern    |
| Persistent state / share storage        | No disk persistence of shares; depends on deployment target                                      |
| On-chain verification (Groth16 wrapper) | Documented path (~50K constraints, ~250K gas), not implemented; requires Ethereum/L2 integration |
| Reshare across disjoint networks        | Paper assumes old and new groups can communicate; cross-network bridging is deployment-specific  |
