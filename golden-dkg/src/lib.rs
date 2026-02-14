//! # golden-dkg
//!
//! Pure-crypto library implementing the **Golden** non-interactive Distributed Key
//! Generation protocol from [Bünz, Choi, Komlo (IACR 2025/1924)](https://eprint.iacr.org/2025/1924).
//!
//! Golden achieves public verifiability in a single broadcast round using an exponent
//! Verifiable Random Function (eVRF) built on Diffie-Hellman key exchange. Security
//! relies only on discrete-log/DDH assumptions over BLS12-381. The output is Shamir
//! secret shares of a field element `sk` distributed to all participants, together with
//! a public key `PK = g^sk`.
//!
//! ## Protocols
//!
//! | Protocol | Module | Description |
//! |----------|--------|-------------|
//! | DKG | [`dkg`] | One-round distributed key generation (Section 5, Figure 4) |
//! | Refresh | [`refresh`] | Proactive share rotation -- same group, rotate shares (Section 5.2) |
//! | Reshare | [`reshare`] | Membership change -- transfer secret to a new group |
//!
//! ## Quick Start
//!
//! ```rust,no_run
//! use golden_dkg::{dkg, types::*};
//! use std::collections::HashMap;
//! use ark_bls12_381::G1Affine;
//! use ark_ff::UniformRand;
//!
//! # fn main() -> Result<(), golden_dkg::error::DkgError> {
//! let mut rng = rand::rngs::OsRng;
//!
//! // 1. Each participant generates an identity keypair + proof of knowledge
//! let alice = Participant::new(1, &mut rng);
//! let bob = Participant::new(2, &mut rng);
//!
//! // 2. Build peer map (in real code, exchange PKs over an authenticated channel)
//! let mut peers = HashMap::new();
//! peers.insert(alice.id, alice.pk);
//! peers.insert(bob.id, bob.pk);
//!
//! // 3. Configure the session
//! let config = DkgConfig {
//!     n: 2,
//!     t: 2,
//!     beta: Scalar::rand(&mut rng),
//!     session_id: SessionId::random(&mut rng),
//! };
//!
//! // 4. Round 0: each participant creates a dealing
//! let alice_dealing = dkg::create_dealing(&alice, &config, &peers, &mut rng)?;
//! let bob_dealing = dkg::create_dealing(&bob, &config, &peers, &mut rng)?;
//!
//! // 5. Broadcast dealing.message to all participants (network layer)
//!
//! // 6. Verify received dealings (publicly verifiable -- anyone can check)
//! dkg::verify_dealing(&bob_dealing.message, &peers, &config)?;
//! dkg::verify_dealing(&alice_dealing.message, &peers, &config)?;
//!
//! // 7. Complete: decrypt shares and produce DKG output
//! let mut alice_received = HashMap::new();
//! alice_received.insert(bob.id, bob_dealing.message.clone());
//! let alice_output = dkg::complete(&alice, &alice_dealing, &alice_received, &peers, &config)?;
//!
//! // alice_output.public_key  -- the shared group public key PK = g^sk
//! // alice_output.secret_share -- Alice's secret key share sk_i
//! // alice_output.public_key_shares -- per-participant public key shares PK_j = g^{sk_j}
//! # Ok(())
//! # }
//! ```
//!
//! ## Feature Flags
//!
//! | Feature | Description |
//! |---------|-------------|
//! | `borsh` | Enable [Borsh](https://borsh.io/) serialization for all message types |
//!
//! ## Security Properties
//!
//! - **Public verifiability**: all participants (and external observers) can verify
//!   all dealings non-interactively without any secret information
//! - **No trusted setup**: transparent proof system via ark-spartan NIZK
//! - **DL/DDH only**: security relies on discrete-log and decisional Diffie-Hellman
//!   assumptions (no pairings, no random oracle model for the core protocol)
//! - **Replay protection**: [`types::SessionId`] nonces prevent replaying old messages
//! - **Rogue-key protection**: Schnorr proof of knowledge ([`schnorr_pok`]) on PKI
//!   registration prevents adversarial key choices
//! - **Secret zeroization**: secret keys are zeroed from memory on drop via
//!   [`types::SecretScalar`]
//!
//! ## Paper Reference
//!
//! > Benedikt Bünz, Kevin Choi, Chelsea Komlo.
//! > "Golden: Lightweight Non-Interactive Distributed Key Generation."
//! > IACR ePrint 2025/1924.
//! > <https://eprint.iacr.org/2025/1924>

#![warn(missing_docs)]

pub mod dkg;
pub mod error;
pub mod refresh;
pub mod reshare;
pub mod schnorr_pok;
pub mod shamir;
pub mod types;
pub mod zk_evrf;

// Internal modules (pub(crate) -- not part of public API)
pub(crate) mod evrf;
pub(crate) mod protocol;
pub(crate) mod reshare_protocol;
pub(crate) mod vss;
