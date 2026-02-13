# Golden: Lightweight Non-Interactive Distributed Key Generation

**Authors:** Benedikt Bünz (NYU), Kevin Choi (Seoul National University), Chelsea Komlo (University of Waterloo & NEAR One)

**Source:** https://eprint.iacr.org/2025/1924.pdf

---

## Abstract

Golden is a non-interactive Distributed Key Generation (DKG) protocol. The core innovation is how it achieves public verifiability in a lightweight manner, allowing all participants to non-interactively verify that all other participants followed the protocol correctly. Golden can be performed with only one round of (broadcast) communication.

Golden outputs Shamir secret shares of a field element sk in Z_p to all participants, and a public key PK = g^sk that is a discrete-logarithm commitment to sk. The security of Golden requires only the hardness of discrete-logarithm assumptions.

For 50 participants, Golden requires only 223 kb bandwidth and 13.5 seconds of total runtime, compared to ElGamal-based non-interactive DKG which requires 27.8 MB bandwidth and 40.5 seconds.

As a building block, Golden defines a new exponent Verifiable Random Function (eVRF) that uses a non-interactive key exchange (NIKE) to derive a Diffie-Hellman shared secret key, proving correctness with respect to the corresponding DH public keys.

---

## 1. Core Concepts

### 1.1 DKG Output

- Each participant i gets a secret key share sk_i (Shamir share of sk)
- The global secret key: sk = sum_{j=1}^{n} omega_j
- The public key: PK = g^sk
- Each sk_i = sum_{j=1}^{n} f_j(i), where f_j(0) = omega_j

### 1.2 Security Model

Golden realizes F^Delta_KeyGen -- an ideal functionality where a rushing adversary can bias the key by an additive value Delta, but only by choosing their contributions as a function of honest participants' broadcast messages. This is the standard security notion for one-round DKGs (full security is impossible per Katz's impossibility result).

Proven UC-secure via straight-line simulation. Requires only DL/DDH assumptions.

---

## 2. Performance Comparison

| Participants | Golden Communication | Golden Runtime | Groth DKG Communication | Groth DKG Runtime |
|---|---|---|---|---|
| 2 | 1.7 kb | 0.4 s | 59.4 kb | 3.9 s |
| 10 | 22 kb | 2.4 s | 1.3 MB | 5.6 s |
| 50 | 223 kb | 13.5 s | 27.8 MB | 40.5 s |
| 100 | 699 kb | 35.8 s | 108.6 MB | 130.8 s |

---

## 3. Preliminaries

### 3.1 Shamir Secret Sharing (Section 3.3)

A polynomial f(x) = a_0 + a_1*x + a_2*x^2 + ... + a_{t-1}*x^{t-1} of degree t-1 over a field F can be interpolated by t points.

**Lagrange polynomial:**

L_i(x) = product_{j in eta, j != i} (x - x_j) / (x_i - x_j)

**Interpolation:**

f(x_tilde) = sum_{k in eta} f(x_k) * L_k(x_tilde)

**Share(x, n, t):**
1. Define polynomial f(Z) = x + a_1*Z + ... + a_{t-1}*Z^{t-1} with random a_1,...,a_{t-1}
2. Each share x_bar_i = f(i) for i in [n]

**Recover(t, {(i, x_bar_i)}):**
- x = sum_{i in C} x_bar_i * L_i(0)
- where L_i(0) = product_{j in C, j != i} j / (j - i)

### 3.2 Feldman VSS

Commits to polynomial f by publishing C_k = g^{a_k} for each coefficient.
Verification: g^{f(j)} == product_{k=0}^{t-1} C_k^{j^k}

### 3.3 Bulletproofs Argument System (Section 3.4)

Proves computation in R1CS form. For the eVRF relation R_eVRF:
- Total constraints: 14*lambda + 14 = 3598 for lambda = 256
- Proof size: 2*log2(N+M) + 3 group elements and 3 field elements
- ~29 group elements for one statement

---

## 4. The eVRF Construction (Section 4)

### 4.1 Notation

- E(F_p): Elliptic curve over F_p
- G_in: Subgroup of E(F_p) of prime order s
- G_out: Subgroup of different curve with order p
- g_in, g_out: Generators
- H_{G_in,1}, H_{G_in,2}: Random oracles mapping to G_in
- beta: Public field element in F_p (leftover hash lemma constant)

### 4.2 eVRF Definition (eVRF^dagger)

**Setup(1^lambda) -> par:**
- Generate (E(F_p), p, G_in, s, g_in) from DH.Setup
- Set par = (E(F_p), p, G_in, s, g_in, G_out, g_out, H_1, H_2, beta)

**KeyGen() -> (sk, PK):**
- (sk, PK) = DH.KeyGen(), PK in G_in

**Evaluate(sk, x) -> (alpha, A, pi):**
1. Parse (msg, PK') = x
2. S = DH.GetSharedKey(sk, PK')        -- DH shared secret
3. k_0 = S.X                            -- x-coordinate of S
4. k = int(k_0)                          -- cast to integer
5. alpha = beta * (H_1(msg)^k).X + (H_2(msg)^k).X
6. A = g_out^alpha                       -- commitment
7. pi = ZK proof for R_eVRF             -- Bulletproofs proof
8. Output (alpha, A, pi)

**Verify(PK, x, A, pi):**
- Parse (msg, PK') = x
- Verify R_eVRF relation

### 4.3 R_eVRF Relation (Figure 3)

Public inputs: PK_1, PK_2, msg, beta, R
Private witness: sk_1

Steps:
0. PK_1 == g_in^{sk_1}
1. S = PK_2^{sk_1}
2. k_0 = S.X
3. k = int(k_0)
4. T_1 = H_1(msg)^k
5. T_2 = H_2(msg)^k
6. r_1 = int(T_1.X)
7. r_2 = int(T_2.X)
8. r = beta * r_1 + r_2
9. R = g_out^r

### 4.4 Circuit Structure

- **Bit-decomposition gadget:** lambda + 2 constraints per decomposition
- **Exponentiation gadget:** 3*lambda + 2 constraints per exponentiation
- **Total:** 2*(lambda+2) + 4*(3*lambda+2) + 2 = 14*lambda + 14 = 3598

### 4.5 Batch Optimizations (Section 4.6)

| Statements | Constraints | Prover | Verifier | Proof Size | Batch Verify |
|---|---|---|---|---|---|
| 1 | 3598 | 0.3s | 0.1s | 1.5kb | 0.1s |
| 9 | 24158 | 1.8s | 0.5s | 1.9kb | 0.6s |
| 49 | 126958 | 6.8s | 2.5s | 2.1kb | 6.7s |
| 99 | 255458 | 13.5s | 4.8s | 2.2kb | 22.1s |

For batch proving n-1 statements: reuse sk_1 bit-decomposition and g^{sk_1} gadget.
Per-statement cost drops from 14*lambda+14 to ~10*lambda+10 (~29% reduction).

---

## 5. Golden Protocol (Section 5)

### 5.1 PKI Requirement

Each party i maintains (sk_i^I, PK_i^I) where PK_i^I = g^{sk_i^I} in G_in.
Must prove knowledge of sk_i^I when registering.

### 5.2 Protocol Description (Figure 4) -- CRITICAL REFERENCE

```
Round0(n, t, i, sk_i^I, {(j, PK_j^I)}):
  1. omega_i <- random Z_p
  2. {x_bar_{i,j}}, C_bar_i = (A_{i,0},...,A_{i,t-1}) <- Shamir.Share(omega_i, n, t)
  3. msg_i <- random {0,1}^lambda
  4. for j in [n], j != i:
  5.   (r_{i,j}, R_{i,j}, pi_{i,j}) <- eVRF.Evaluate(sk_i^I, (msg_i, PK_j^I))
  6.   z_{i,j} <- r_{i,j} + x_bar_{i,j}    // Encrypt share
  7.   sigma_{i,j} <- (R_{i,j}, z_{i,j})
  8. st_i <- x_bar_{i,i}                     // Keep own share
  9. bmsg_i <- {(msg_i, C_bar_i, sigma_{i,j}, pi_{i,j})} for j != i
  10. Broadcast bmsg_i

Round1(n, t, i, sk_i^I, {(j, PK_j^I)}, {bmsg_j}, st_i):
  1. x_bar_{i,i} <- st_i
  2. for j in [n], j != i:
  3.   Parse bmsg_j -> {(msg_j, C_bar_j, sigma_{j,k}, pi_{j,k})}
  4.   Parse C_bar_j -> (A_{j,0},...,A_{j,t-1}); sigma_{j,k} -> (R_{j,k}, z_{j,k})
  5. for j in [n], j != i:
  6.   for k in [n], k != j:
  7.     ABORT if eVRF.Verify(PK_j^I, (msg_j, PK_k^I), R_{j,k}, pi_{j,k}) != 1
  8.     X_bar_{j,k} <- product_{l=0}^{t-1} A_{j,l}^{k^l}    // commitment g^{f_j(k)}
  9.     ABORT if g^{z_{j,k}} != R_{j,k} * X_bar_{j,k}         // ciphertext check
  10. for j in [n], j != i:
  11.   (r_{j,i}, _, _) <- eVRF.Evaluate(sk_i^I, (msg_j, PK_j^I))
  12.   x_bar_{j,i} <- z_{j,i} - r_{j,i}    // Decrypt share
  13. sk_i <- sum_{j=1}^{n} x_bar_{j,i}
  14. for l in [n]:
  15.   PK_l <- product_{k=1}^{n} X_bar_{k,l}
  16. PK <- product_{k=1}^{n} A_{k,0}        // = g^{sum omega_k}
  17. return (PK, {PK_j}, sk_i)
```

### 5.3 Key Resharing (Section 5.2)

> **Terminology note:** The paper uses "key resharing" for this operation, but in the broader literature this is more precisely called **key refresh** or **proactive secret sharing** -- the group membership and (n, t) parameters stay the same, only the shares rotate. True "resharing" typically refers to transferring the secret to a different group with possibly different (n', t').

Golden supports key refresh (share rotation while keeping sk and PK the same):
1. Instead of sampling omega_i at random, set omega_i = 0
2. Check that A_{j,0} equals the group identity for all j (verifying f_j(0) = 0)

### 5.4 Optimized Golden via Batching (Section 5.3)

- Batch proving: one proof for n-1 eVRF evaluations (not n-1 separate proofs)
- Proof size scales logarithmically: 1.5kb for 1 statement, 2.2kb for 99
- Batch verification: share MSM cost across n-1 proof verifications

| Participants | Comm (unopt) | Comm (opt) | Runtime (unopt) | Runtime (opt) |
|---|---|---|---|---|
| 2 | 1.7 kb | 1.7 kb | 0.4 s | 0.4 s |
| 10 | 126 kb | 22 kb | 9.3 s | 2.4 s |
| 50 | 3.7 MB | 223 kb | 209 s | 13.5 s |
| 100 | 15.1 MB | 699 kb | 823 s | 35.8 s |

---

## 6. Security Proof (Section 6, Appendix H)

**Theorem 3:** Pi_Golden-PKI securely realizes F^Delta_KeyGen in the (F_zk, F_eVRF)-hybrid model.

**Proof structure (game hops):**
- Game 0: Real execution
- Game 1: Replace PKI with F_eVRF + F_zk (indistinguishable)
- Game 2: Replace eVRF with F_eVRF ideal functionality (by eVRF security)
- Game 3: Define simulator SIM that:
  - Simulates honest parties' Round 0 honestly (except party tau)
  - For tau: sets A_{tau,0} = Y * product(A_{k,0})^{-1} for honest k != tau
  - Simulates encryptions to honest parties by sampling z uniformly
  - After Round 0: decrypts corrupt parties' contributions to derive Delta
  - PK = Y * g^Delta, satisfying F^Delta_KeyGen

**Key insight:** The simulator can program tau's VSS commitment "in the exponent" without knowing the discrete log of Y, because it can derive all commitments from the t-1 known corrupt shares plus A_{tau,0}.

---

## 7. Appendices Summary

### A. F_eVRF Ideal Functionality
- Register, Query, Evaluate oracles
- Honest parties: sample random alpha, set A = g^alpha
- Corrupt parties: use their registered function f_j

### B. NIKE (Non-Interactive Key Exchange)
- Setup, KeyGen, GetSharedKey
- Correctness: GetSharedKey(sk1, PK2) = GetSharedKey(sk2, PK1)
- Security: session-key unrecoverability

### C. Leftover Hash Lemma
- Used to show r = beta * r1 + r2 is pseudorandom
- Statistical distance bound: Delta <= 8h^2*sqrt(p) / (p - 2h) = O(1/sqrt(p))

### D. eVRF Security Proof
- Game 0 -> Game 1: Replace DH shared secret with random (reduce to NIKE security)
- Game 1 -> Game 2: Replace r with truly random (leftover hash lemma)
- Advantage bound: Adv <= Adv_DH^unrec + O(1/sqrt(p))

### E. Alternative Construction
- Can set G_in = G_out at cost of more constraints (non-native arithmetic)

### F. PKI Functionality
- F_pki: KeyGen, Register (with proof of knowledge), Query
- Concrete realization: Chaum-Pedersen proof in CRS model

---

## References (Key)

- [12] Boneh et al. "Exponent-VRFs and Their Applications" EUROCRYPT 2025
- [15] Bünz et al. "Bulletproofs" IEEE S&P 2018
- [48] Groth. "Non-interactive distributed key generation and key resharing" 2021
- [54] Katz. "Round Optimal Robust Distributed Key Generation" 2023
- [56] Komlo & Goldberg. "FROST: Flexible Round-Optimized Schnorr Threshold Signatures" SAC 2020
- [71] Shamir. "How to Share a Secret" 1979
