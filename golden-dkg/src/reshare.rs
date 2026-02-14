//! Membership-change resharing: transfer a shared secret to a new group.
//!
//! Resharing allows an existing group of `n` participants (the "old group") to
//! transfer their shared secret `sk` to a new group of `n'` participants (the
//! "new group"), possibly with different membership and a different threshold `t'`.
//! After resharing, the new group holds Shamir shares of the **same** secret `sk`
//! under the new `(n', t')` parameters, while the old group's shares become
//! useless.
//!
//! Unlike DKG and refresh, resharing involves two distinct roles:
//!
//! - **Old members** ([`create_dealing`]): each old member re-shares their
//!   existing secret share `sk_i` to the new group using a fresh degree-(t'-1)
//!   polynomial `g_i(x)` where `g_i(0) = sk_i`. They broadcast a [`ReshareMsg`]
//!   containing VSS commitments and encrypted sub-shares for each new member.
//!
//! - **New members** ([`complete`]): each new member collects at least `t_old`
//!   reshare messages, verifies them against the old group's known public key
//!   shares, decrypts the sub-shares, and performs Lagrange interpolation to
//!   recover their new share of `sk`.
//!
//! The [`verify_dealing`] function checks that the old member's VSS commitment
//! is consistent with their known public key share `PK_i = g^{sk_i}`.

use std::collections::HashMap;

use ark_bls12_381::G1Affine;
use ark_std::rand::Rng;

use crate::error::ReshareError;
use crate::reshare_protocol;
use crate::types::{DkgOutput, NodeId, Participant, ReshareMsg, Scalar, SessionId};

/// Old member creates a reshare dealing for the new group.
///
/// The old member re-shares their existing secret key share `old_share` (= `sk_i`)
/// to the new group by creating a fresh degree-(t_new - 1) Shamir polynomial
/// `g_i(x)` with `g_i(0) = old_share`, then encrypting each new member's
/// sub-share using eVRF-derived pads.
///
/// # Parameters
///
/// - `old_participant` -- the old member's identity
/// - `old_share` -- the old member's secret key share `sk_i` from the previous DKG
/// - `new_members` -- map of new-group member IDs to their identity public keys
/// - `t_new` -- threshold for the new group
/// - `beta` -- public parameter for the leftover hash lemma
/// - `session_id` -- unique session identifier for this reshare
/// - `rng` -- cryptographic random number generator
///
/// # Returns
///
/// A [`ReshareMsg`] to broadcast to the new group.
///
/// # Errors
///
/// Returns [`ReshareError`] if message construction fails.
pub fn create_dealing(
    old_participant: &Participant,
    old_share: Scalar,
    new_members: &HashMap<NodeId, G1Affine>,
    t_new: u32,
    beta: Scalar,
    session_id: SessionId,
    rng: &mut impl Rng,
) -> Result<ReshareMsg, ReshareError> {
    Ok(reshare_protocol::reshare_deal(
        old_participant.id,
        old_share,
        old_participant.sk.inner(),
        new_members,
        t_new,
        beta,
        rng,
        session_id,
    ))
}

/// Verify a reshare dealing from an old-group member.
///
/// Checks that the dealing's first VSS commitment coefficient `A_{i,0}` matches
/// the old member's known public key share `PK_i = g^{sk_i}`. This ensures the
/// old member is re-sharing their actual secret share (not an arbitrary value).
///
/// # Parameters
///
/// - `dealing` -- the [`ReshareMsg`] received from an old-group member
/// - `old_pk_shares` -- public key shares from the old DKG output
///   (`DkgOutput::public_key_shares`), keyed by old-group [`NodeId`]
/// - `session_id` -- expected session identifier
///
/// # Errors
///
/// - [`ReshareError::SessionMismatch`] -- dealing has a different session ID
/// - [`ReshareError::CiphertextVerificationFailed`] -- `commitment[0]` does not
///   match the sender's known public key share (sender is dishonest or using
///   the wrong share)
pub fn verify_dealing(
    dealing: &ReshareMsg,
    old_pk_shares: &HashMap<NodeId, G1Affine>,
    session_id: SessionId,
) -> Result<(), ReshareError> {
    if dealing.reshare_header.session_id != session_id {
        return Err(ReshareError::SessionMismatch {
            sender: dealing.reshare_header.from,
        });
    }

    // Check commitment[0] matches old PK share
    if let Some(&expected_pk_share) = old_pk_shares.get(&dealing.reshare_header.from) {
        if dealing.reshare_header.vss_commitment[0] != expected_pk_share {
            return Err(ReshareError::CiphertextVerificationFailed {
                sender: dealing.reshare_header.from,
                recipient: 0,
            });
        }
    }

    Ok(())
}

/// New member completes resharing from verified old-group dealings.
///
/// The new member collects at least `t_old` verified [`ReshareMsg`] messages,
/// decrypts the sub-shares addressed to them, and performs Lagrange interpolation
/// to recover their new share of the global secret `sk`. The resulting
/// [`DkgOutput`] has the same `public_key` as the old group's output.
///
/// # Parameters
///
/// - `new_participant` -- the new member's identity
/// - `dealings` -- verified [`ReshareMsg`] messages from old-group members,
///   keyed by old-group sender [`NodeId`] (need at least `t_old` dealings)
/// - `old_members` -- map of old-group member IDs to their identity public keys
/// - `original_pk` -- the shared public key `PK` from the old group's DKG output
/// - `old_pk_shares` -- per-participant public key shares from the old DKG
/// - `t_old` -- the old group's threshold parameter
/// - `beta` -- public parameter for the leftover hash lemma
/// - `session_id` -- session identifier (must match the dealings)
///
/// # Returns
///
/// A [`DkgOutput`] with the new member's secret share of `sk` under the new
/// group's `(n', t')` parameters.
///
/// # Errors
///
/// - [`ReshareError::InsufficientDealers`] -- fewer than `t_old` dealings received
/// - [`ReshareError::MissingCiphertext`] -- a dealer didn't include this recipient
/// - [`ReshareError::NoMessages`] -- no dealings received at all
#[allow(clippy::too_many_arguments)]
pub fn complete(
    new_participant: &Participant,
    dealings: &HashMap<NodeId, ReshareMsg>,
    old_members: &HashMap<NodeId, G1Affine>,
    original_pk: G1Affine,
    old_pk_shares: &HashMap<NodeId, G1Affine>,
    t_old: u32,
    beta: Scalar,
    session_id: SessionId,
) -> Result<DkgOutput, ReshareError> {
    reshare_protocol::reshare_receive(
        new_participant.id,
        new_participant.sk.inner(),
        old_members,
        dealings,
        beta,
        original_pk,
        old_pk_shares,
        t_old,
        session_id,
    )
}
