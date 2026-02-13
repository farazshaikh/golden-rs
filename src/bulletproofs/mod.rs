//! Bulletproofs Inner Product Argument system per Section 3.4 of the Golden paper.
//!
//! Per Section 3.4 of the Golden paper (IACR 2025/1924):
//! > "Proves computation in R1CS form. Proof size: 2*log2(N+M) + 3 group elements
//! > and 3 field elements."
//!
//! This module provides the cryptographic proof infrastructure used by the eVRF
//! ZK proofs. The Inner Product Argument (IPA) from Bünz et al. 2018 enables
//! logarithmic-sized proofs for inner product relations over Pedersen vector
//! commitments, which the R1CS layer (stub) reduces to.

pub mod generators;
pub mod ipa;
pub mod r1cs;
pub mod transcript;
pub mod types;
