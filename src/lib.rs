//! # Golden DKG
//!
//! Implementation of the Golden non-interactive Distributed Key Generation protocol
//! from Bünz, Choi, Komlo (IACR 2025/1924).
//!
//! Golden achieves public verifiability in a single broadcast round using an exponent
//! Verifiable Random Function (eVRF) built on Diffie-Hellman key exchange. Security
//! relies only on discrete-log/DDH assumptions over BLS12-381.
//!
//! ## Modules
//!
//! - [`shamir`] -- Shamir secret sharing (Section 3.3)
//! - [`vss`] -- Feldman Verifiable Secret Sharing (Section 3.3)
//! - [`evrf`] -- eVRF pad derivation via NIKE (Section 4)
//! - [`schnorr_pok`] -- PKI proof of knowledge (Appendix F)
//! - [`protocol`] -- DKG and refresh protocol rounds (Section 5, Figure 4)
//! - [`reshare`] -- Membership-change resharing
//! - [`zk_evrf`] -- R_eVRF circuit and ark-spartan NIZK proof system (Section 4.3, [15])
//! - [`network`] -- Simulated broadcast channel
//! - [`node`] -- DKG participant abstraction
//! - [`types`] -- Shared data types with Borsh serialization

#![warn(missing_docs)]

pub mod evrf;
pub mod network;
pub mod node;
pub mod protocol;
pub mod reshare;
pub mod reshare_network;
pub mod reshare_node;
pub mod schnorr_pok;
pub mod shamir;
pub mod types;
pub mod vss;
pub mod zk_evrf;
