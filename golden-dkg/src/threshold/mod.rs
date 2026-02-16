//! Threshold BLS signatures, vetKeys IBE, and drand-compatible beacon.
//!
//! Built on top of the Golden DKG key shares. Provides:
//! - [`signing`] -- Partial signing, Lagrange combination, pairing verification
//! - [`beacon`] -- drand-compatible message digests and hash-to-curve
//! - [`cache`] -- Precomputed Lagrange coefficient cache
//! - [`ibe`] -- vetKeys Identity-Based Encryption (Boneh-Franklin + transport encryption)
//! - [`dkg`] -- Bridge from `golden_dkg::dkg::DkgOutput` to threshold `KeyShare`/`GroupInfo`
//! - [`types`] -- `KeyShare`, `GroupInfo`, `PartialSignature`, `ThresholdSignature`, `Beacon`

pub mod types;
pub mod signing;
pub mod beacon;
pub mod cache;
pub mod dkg;
pub mod ibe;
