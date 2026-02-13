# TODO: Bulletproofs eVRF Zero-Knowledge Proofs

The current prototype skips the zero-knowledge proof component of the eVRF.
In the full Golden protocol, each node generates a Bulletproofs proof demonstrating
that the eVRF pad was correctly derived. This enables public verifiability --
anyone can check that all participants followed the protocol correctly.

## What needs to be implemented

### eVRF Relation (R_eVRF)

The ZK proof must demonstrate, for public inputs (PK_1, PK_2, msg, beta, R):

0. PK_1 == g^{sk_1}                        -- identity key consistency
1. S = PK_2^{sk_1}                          -- DH shared secret
2. k = int(S.x)                             -- x-coordinate extraction
3. T_1 = H_1(msg)^k                         -- hash-to-curve exponentiation
4. T_2 = H_2(msg)^k                         -- hash-to-curve exponentiation
5. r_1 = int(T_1.x), r_2 = int(T_2.x)      -- x-coordinate extraction
6. r = beta * r_1 + r_2                     -- leftover hash lemma
7. R = g^r                                  -- commitment

### Circuit structure (Bulletproofs R1CS)

- **Bit-decomposition gadget**: Decompose sk_1 and k into lambda+1 bits (lambda=256)
  - Constraints: lambda + 2 per decomposition
- **Exponentiation gadget**: Prove g^{sk_1}, PK_2^{sk_1}, H_1^k, H_2^k
  - Uses precomputed lookup points and incremental chord-rule construction
  - Constraints: 3*lambda + 2 per exponentiation
- **Total**: 2*(lambda+2) + 4*(3*lambda+2) + 2 = 14*lambda + 14 = 3598 constraints

### Recommended implementation path

1. Use the `ark-r1cs-std` crate for R1CS gadgets
2. Use `ark-relations` for constraint system definition
3. Either implement Bulletproofs directly or use a Groth16/Marlin backend
4. Implement batch proving (one proof for n-1 eVRF evaluations) per Section 5.3
5. Implement batch verification per Bulletproofs (share MSM cost across proofs)

### Batch optimization

- Single proof for n-1 statements: reuse sk_1 bit-decomposition and g^{sk_1} gadget
- Reduces per-statement cost from 14*lambda+14 to ~10*lambda+10 constraints
- Proof size scales logarithmically: 29 group elements for 1 statement, 43 for 99

### References

- Golden paper: https://eprint.iacr.org/2025/1924
- Bulletproofs: https://eprint.iacr.org/2017/1066
- arkworks R1CS: https://github.com/arkworks-rs/r1cs-std
