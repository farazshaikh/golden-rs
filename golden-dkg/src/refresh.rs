//! Proactive share rotation (key refresh) per Section 5.2 of the Golden paper.
//!
//! Implements the Golden key refresh protocol from Section 5.2 of the paper
//! (Bünz, Choi, Komlo, [IACR 2025/1924](https://eprint.iacr.org/2025/1924)).
//!
//! Key refresh rotates all secret key shares while preserving the global secret
//! `sk` and public key `PK = g^sk`. This is also known as "proactive secret
//! sharing" -- it limits the window during which a compromised share is useful
//! to the attacker.
//!
//! # Zero-Secret Sharing Mechanism
//!
//! The refresh protocol is structurally identical to the DKG protocol with one
//! critical difference: instead of sampling a random `omega_i`, each participant
//! sets `omega_i = 0`. This means:
//!
//! - The Shamir polynomial `f_i(x)` has constant term `f_i(0) = 0`
//! - The VSS commitment's first element `A_{i,0} = g^0 = identity`
//! - The shares `x_bar_{i,j} = f_i(j)` are "delta" values that sum to zero
//!
//! Verification checks that `A_{j,0}` is the group identity for all dealers
//! (Section 5.2 constraint). After completion, each participant adds their
//! aggregated delta to their existing share: `sk_i' = sk_i + sum_j delta_{j,i}`.
//! Since `sum_j f_j(0) = 0`, the global secret is preserved: `sum_i sk_i' = sk`.
//!
//! # Usage
//!
//! The API mirrors [`crate::dkg`] -- call [`create_dealing`], broadcast,
//! [`verify_dealing`], then [`complete`] -- but [`complete`] takes the
//! `existing_output` from a prior DKG or refresh round.

use std::collections::HashMap;

use ark_bls12_381::G1Affine;
use ark_ec::{AffineRepr, CurveGroup};
use ark_std::rand::Rng;

use crate::error::DkgError;
use crate::protocol;
use crate::types::{DkgConfig, DkgDealing, DkgOutput, NodeId, Participant, Round0Msg};

/// Generate a refresh dealing (zero-secret sharing, Section 5.2).
///
/// Identical to [`crate::dkg::create_dealing`] except the secret contribution
/// `omega_i` is fixed to zero instead of being sampled randomly. The resulting
/// shares are "delta" values that will be added to existing shares during
/// [`complete`].
///
/// # Parameters
///
/// - `participant` -- the caller's identity (keypair + ID)
/// - `config` -- session parameters (n, t, beta, session_id); should use the
///   same `n` and `t` as the original DKG
/// - `peers` -- map of all participant IDs to identity public keys
/// - `rng` -- cryptographic random number generator
///
/// # Returns
///
/// A [`DkgDealing`] where `private_share` is the caller's own delta share
/// (`f_i(i)` with `f_i(0) = 0`).
///
/// # Errors
///
/// Returns [`DkgError`] if eVRF proof generation fails.
pub fn create_dealing(
    participant: &Participant,
    config: &DkgConfig,
    peers: &HashMap<NodeId, G1Affine>,
    rng: &mut impl Rng,
) -> Result<DkgDealing, DkgError> {
    let (msg, own_delta) = protocol::round0_refresh(
        participant.id,
        config.n,
        config.t,
        participant.sk.inner(),
        peers,
        config.beta,
        rng,
        config.session_id,
    );
    Ok(DkgDealing {
        own_vss_commitment: msg.dkg_header.vss_commitment.clone(),
        message: msg,
        private_share: own_delta,
    })
}

/// Verify a refresh dealing from another participant.
///
/// In addition to the standard ciphertext consistency checks (same as
/// [`crate::dkg::verify_dealing`]), this verifies the **zero-secret invariant**
/// from Section 5.2: the first VSS commitment coefficient `A_{j,0}` must be the
/// group identity element (`g^0`), ensuring `f_j(0) = 0`.
///
/// # Checks performed
///
/// 1. **Session ID** -- matches `config.session_id`
/// 2. **Zero-secret** -- `dealing.vss_commitment[0]` is the point at infinity
/// 3. **Ciphertext consistency** -- `g^{z_{j,k}} == R_{j,k} * X_bar_{j,k}`
///    for each recipient `k`
///
/// # Errors
///
/// - [`DkgError::SessionMismatch`] -- session ID mismatch (possible replay)
/// - [`DkgError::ZeroSecretViolation`] -- `A_{j,0}` is not the identity;
///   the sender is attempting to shift the global secret
/// - [`DkgError::CiphertextVerificationFailed`] -- ciphertext/VSS mismatch
pub fn verify_dealing(
    dealing: &Round0Msg,
    _peers: &HashMap<NodeId, G1Affine>,
    config: &DkgConfig,
) -> Result<(), DkgError> {
    if dealing.dkg_header.session_id != config.session_id {
        return Err(DkgError::SessionMismatch {
            sender: dealing.dkg_header.from,
        });
    }

    // Zero-secret check: A_{j,0} must be identity
    if !dealing.dkg_header.vss_commitment[0].infinity {
        return Err(DkgError::ZeroSecretViolation {
            sender: dealing.dkg_header.from,
        });
    }

    // Ciphertext consistency (same as DKG)
    for (&recipient_id, ct) in &dealing.dkg_header.ciphertexts {
        let expected =
            crate::vss::expected_share_commitment(&dealing.dkg_header.vss_commitment, recipient_id);
        let lhs = (G1Affine::generator() * ct.encrypted_share).into_affine();
        let rhs = (ct.r_commitment.into_group() + expected.into_group()).into_affine();
        if lhs != rhs {
            return Err(DkgError::CiphertextVerificationFailed {
                sender: dealing.dkg_header.from,
                recipient: recipient_id,
            });
        }
    }

    Ok(())
}

/// Complete the refresh protocol: apply zero-sharing deltas to existing shares.
///
/// Decrypts each peer's delta share, aggregates across all dealers, and adds
/// the result to the participant's existing secret key share:
/// `sk_i' = sk_i + sum_j delta_{j,i}`.
///
/// The public key `PK` is preserved (since `sum_j f_j(0) = 0`), but all
/// individual shares are rotated. Per-participant public key shares are
/// recomputed: `PK_j' = PK_j * g^{sum_k delta_{k,j}}`.
///
/// # Preconditions
///
/// - All peer dealings must have been verified via [`verify_dealing`].
/// - `existing_output` must be the [`DkgOutput`] from the most recent DKG or
///   refresh round for this group.
///
/// # Parameters
///
/// - `participant` -- the caller's identity
/// - `own_dealing` -- the caller's own [`DkgDealing`] from [`create_dealing`]
/// - `peer_dealings` -- verified refresh messages from all other participants
/// - `peers` -- all participant IDs mapped to identity public keys
/// - `config` -- session parameters
/// - `existing_output` -- the [`DkgOutput`] to refresh (shares will be rotated)
///
/// # Returns
///
/// A new [`DkgOutput`] with rotated shares but the same `public_key`.
///
/// # Errors
///
/// Returns [`DkgError`] if share decryption or aggregation fails.
pub fn complete(
    participant: &Participant,
    own_dealing: &DkgDealing,
    peer_dealings: &HashMap<NodeId, Round0Msg>,
    peers: &HashMap<NodeId, G1Affine>,
    config: &DkgConfig,
    existing_output: &DkgOutput,
) -> Result<DkgOutput, DkgError> {
    protocol::round1_refresh(
        participant.id,
        participant.sk.inner(),
        peers,
        own_dealing.private_share,
        own_dealing.own_vss_commitment.clone(),
        peer_dealings,
        config.beta,
        existing_output.secret_share,
        existing_output.public_key,
        &existing_output.public_key_shares,
        config.session_id,
    )
}
