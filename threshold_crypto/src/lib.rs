//! BLS12-381 threshold signatures with drand-compatible beacon format.
//!
//! This crate provides a clean API for threshold BLS signing built on top of
//! [`golden_dkg`]. It separates the pure cryptographic operations (signing,
//! verification, Lagrange interpolation, beacon construction) from any
//! display or CLI concerns.
//!
//! # Modules
//!
//! - [`types`] -- Core data structures: `KeyShare`, `GroupInfo`, `PartialSignature`,
//!   `ThresholdSignature`, `Beacon`, `BeaconMode`.
//! - [`signing`] -- Partial signing, combination, and verification.
//! - [`beacon`] -- drand-compatible message digests, hash-to-curve, and randomness derivation.
//! - [`cache`] -- Precomputed Lagrange coefficient cache for fast multi-round signing.
//! - [`dkg`] -- Bridge from `golden_dkg::DkgOutput` to this crate's `KeyShare`/`GroupInfo`.
//!
//! # Example
//!
//! ```rust,no_run
//! use threshold_crypto::{dkg, signing, beacon, cache};
//!
//! let (shares, group) = dkg::run_dkg(10, 7);
//! let node_ids: Vec<_> = shares.iter().map(|s| s.id).collect();
//! let lc = cache::LagrangeCache::new(&node_ids, group.threshold, 1);
//!
//! let digest = beacon::digest_message(1, None);
//! let msg_hash = beacon::hash_to_g2(&digest);
//!
//! let partials: Vec<_> = shares.iter()
//!     .map(|s| signing::partial_sign(&msg_hash, s))
//!     .collect();
//!
//! let sig = signing::combine(&partials, &node_ids, &lc);
//! assert!(signing::verify(&msg_hash, &sig, &group.public_key));
//! ```

pub mod types;
pub mod signing;
pub mod beacon;
pub mod cache;
pub mod dkg;
pub mod ibe;
