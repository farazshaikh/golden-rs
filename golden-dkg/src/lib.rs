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
//! ## Formal Verification
//!
//! This crate has multi-layer formal verification covering the paper math, the Rust
//! implementation, and the bridge between them. See `formal_verification/README.md` for
//! the full verification chain diagram and detailed status
//! (`formal_verification/README.md` in the repository root).
//!
//! ### Approach
//!
//! The verification uses three tools in a "sandwich" architecture:
//!
//! **Top layer -- Lean 4 + Mathlib (paper math):** 38 machine-checked theorems prove
//! the algebraic properties stated in the paper: Shamir reconstruction, Feldman VSS
//! completeness, eVRF DH symmetry, refresh/reshare correctness, eVRF circuit
//! completeness, security game hops, and the LHL bound. These are pure math proofs
//! that hold in any field/group satisfying the standard algebraic axioms.
//!
//! **Bottom layer -- hax + F\* (Rust implementation):** The [`hax`](https://github.com/hacspec/hax)
//! tool extracts the Rust source code into 18 F\* modules. F\* lax-checks all modules,
//! verifying that the extracted code is well-typed against the arkworks type models.
//! Non-crypto code (serialization, memory zeroization) is excluded via `#[hax_lib::exclude]`.
//!
//! **Bridge layer -- F\* specification files:** 6 F\* spec files state the correctness
//! properties (mirroring the Lean theorems) and prove the extracted Rust code satisfies
//! them. Key proofs include: eVRF pad symmetry (DH commutativity through the full
//! `derive_pad` function), encrypt/decrypt roundtrip, Lagrange interpolation correctness
//! for concrete cases (n=2,3), VSS ciphertext check (EC distributivity), and refresh/reshare
//! algebraic invariants.
//!
//! Additionally, 20 [Kani](https://model-checking.github.io/kani/) bounded model checking
//! harnesses prove panic-freedom and structural invariants across all modules.
//!
//! ### Remaining Items
//!
//! Two items are intentionally left unproved:
//!
//! - **`reshare_dealer_binding`** (F\*, `assume val`): States that if `g^a == g^b` then
//!   `a == b`. This is the Discrete Logarithm hardness assumption -- a standard
//!   cryptographic assumption that cannot be proved, only assumed.
//!
//! - **`golden_uc_security`** (Lean, `sorry`): The full UC composition theorem bounding
//!   the distinguishing advantage as `|prob_real - prob_ideal| <= n * adv_evrf`. This
//!   requires 8-12 weeks of research-level formalization using probabilistic frameworks
//!   (VCV-io or SSProve). The statement is complete; the proof infrastructure is in place.
//!
//! ### Running the Verification Pipeline
//!
//! After any code change, run the full verification suite:
//!
//! ```bash
//! # Full verification (cargo test + Lean + hax re-extraction + F* lax-check)
//! make verify
//!
//! # Quick check (cargo test + Lean only, ~2 min)
//! make verify-quick
//!
//! # Force full re-run (clears cached stamps)
//! make -C formal_verification clean && make verify
//! ```
//!
//! Prerequisites: Lean 4 via [elan](https://github.com/leanprover/elan), F\* v2025.10.06,
//! hax v0.3.6 with `opam switch hax-engine`. See `formal_verification/README.md` for
//! installation details.
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

// Feature-gated modules. These are NOT part of the DKG formal verification
// target (hax extracts only the core DKG modules above). The threshold and
// consensus modules have their own verification path.

/// Threshold BLS signatures, vetKeys IBE, and drand-compatible beacon.
/// Enabled by the `threshold` feature (on by default).
#[cfg(feature = "threshold")]
pub mod threshold;

/// Simplex BFT consensus -- pure state machine core.
/// Enabled by the `consensus` feature (on by default).
#[cfg(feature = "consensus")]
pub mod consensus;
