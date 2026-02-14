//! High-level DKG API: one-round distributed key generation.
//!
//! Implements the Golden DKG protocol from Section 5 (Figure 4) of the paper
//! (Bünz, Choi, Komlo, [IACR 2025/1924](https://eprint.iacr.org/2025/1924)).
//!
//! The protocol proceeds in two logical rounds:
//!
//! 1. **Round 0** ([`create_dealing`]): each participant samples a random secret
//!    `omega_i`, creates Shamir shares encrypted via eVRF-derived pads, and
//!    broadcasts the resulting [`Round0Msg`].
//! 2. **Verification** ([`verify_dealing`]): every participant (or observer) can
//!    publicly verify all received dealings without any secret information.
//! 3. **Round 1** ([`complete`]): each participant decrypts the shares addressed
//!    to them, aggregates across all dealers, and derives their secret key share
//!    `sk_i` and the shared public key `PK = g^{sum omega_j}`.
//!
//! All three functions are pure -- they perform no I/O and require no network
//! access. The caller is responsible for broadcasting messages and collecting
//! peer dealings.

use std::collections::HashMap;

use ark_bls12_381::G1Affine;
use ark_ec::{AffineRepr, CurveGroup};
use ark_std::rand::Rng;

use crate::error::DkgError;
use crate::protocol;
use crate::types::{DkgConfig, DkgDealing, DkgOutput, NodeId, Participant, Round0Msg};

/// Generate a DKG dealing (Round 0 of Figure 4 in the Golden paper).
///
/// Each participant calls this once per session. The function:
/// 1. Samples a random secret contribution `omega_i`
/// 2. Creates a degree-(t-1) Shamir polynomial with `omega_i` as the constant term
/// 3. Encrypts each peer's share using an eVRF-derived pad from a DH shared secret
/// 4. Generates a batched eVRF proof covering all encrypted shares
///
/// # Parameters
///
/// - `participant` -- the caller's identity (keypair + ID)
/// - `config` -- session parameters (n, t, beta, session_id)
/// - `peers` -- map of **all** participant IDs to their identity public keys
///   (including the caller themselves)
/// - `rng` -- cryptographic random number generator
///
/// # Returns
///
/// A [`DkgDealing`] containing:
/// - `message` -- the [`Round0Msg`] to **broadcast** to all peers
/// - `private_share` -- the caller's own Shamir share (`x_bar_{i,i} = f_i(i)`),
///   which **must be kept secret** and passed to [`complete`]
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
    let (msg, own_share) = protocol::round0(
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
        private_share: own_share,
    })
}

/// Verify a dealing received from another participant.
///
/// This is the **public verifiability** check from Round 1 (Figure 4, lines 5-9)
/// of the Golden paper. It can be performed by any party (including observers
/// who are not participants) using only public information.
///
/// # Checks performed
///
/// 1. **Session ID** -- the dealing's session ID matches the expected `config.session_id`
/// 2. **Ciphertext consistency** -- for each recipient `k`:
///    `g^{z_{j,k}} == R_{j,k} * X_bar_{j,k}` where `X_bar_{j,k}` is the
///    Feldman VSS share commitment (Figure 4, line 9)
/// 3. **eVRF proof** -- the batched eVRF proof (if present) verifies that all
///    pads were correctly derived from DH shared secrets (Figure 4, line 7)
///
/// # Parameters
///
/// - `dealing` -- the [`Round0Msg`] received from the sender
/// - `peers` -- the same peer map used in [`create_dealing`] (all participant PKs)
/// - `config` -- session parameters
///
/// # Errors
///
/// - [`DkgError::SessionMismatch`] -- dealing has a different session ID (possible replay)
/// - [`DkgError::CiphertextVerificationFailed`] -- a ciphertext is inconsistent
///   with the VSS commitment (sender is malicious or message was corrupted)
/// - [`DkgError::ProofError`] -- the eVRF proof failed verification
pub fn verify_dealing(
    dealing: &Round0Msg,
    peers: &HashMap<NodeId, G1Affine>,
    config: &DkgConfig,
) -> Result<(), DkgError> {
    if dealing.dkg_header.session_id != config.session_id {
        return Err(DkgError::SessionMismatch {
            sender: dealing.dkg_header.from,
        });
    }

    // Verify each ciphertext against VSS commitment
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

    // Verify eVRF proofs
    let sender_pk = peers
        .get(&dealing.dkg_header.from)
        .copied()
        .ok_or_else(|| DkgError::ProofError(format!("unknown sender {}", dealing.dkg_header.from)))?;

    if let Some(ref batch_proof) = dealing.batch_evrf_proof {
        let peers_for_verify: Vec<(NodeId, G1Affine)> = dealing
            .dkg_header
            .ciphertexts
            .keys()
            .map(|&pid| (pid, peers[&pid]))
            .collect();
        let pad_commitments: Vec<(NodeId, G1Affine)> = dealing
            .dkg_header
            .ciphertexts
            .iter()
            .map(|(&pid, ct)| (pid, ct.r_commitment))
            .collect();
        match crate::zk_evrf::verify_evrf_batch(
            sender_pk,
            &peers_for_verify,
            &pad_commitments,
            config.beta,
            batch_proof,
        ) {
            Ok(true) => {}
            Ok(false) => {
                return Err(DkgError::ProofError(format!(
                    "batch eVRF verification failed for sender {}",
                    dealing.dkg_header.from
                )));
            }
            Err(e) => return Err(DkgError::ProofError(e)),
        }
    }

    Ok(())
}

/// Complete the DKG protocol (Round 1 of Figure 4: decryption + aggregation).
///
/// Decrypts each peer's encrypted share addressed to this participant by
/// re-deriving the eVRF pad from the DH shared secret (Figure 4, lines 10-12),
/// then aggregates all shares across dealers to produce the final secret key
/// share `sk_i = sum_j x_bar_{j,i}` and the shared public key
/// `PK = product_j A_{j,0}` (Figure 4, lines 13-17).
///
/// # Preconditions
///
/// - All peer dealings in `peer_dealings` **must** have been verified via
///   [`verify_dealing`] before calling this function. Passing unverified
///   dealings may produce incorrect or insecure output.
/// - `peers` must be the same peer map used in [`create_dealing`].
///
/// # Parameters
///
/// - `participant` -- the caller's identity
/// - `own_dealing` -- the caller's own [`DkgDealing`] from [`create_dealing`]
/// - `peer_dealings` -- verified [`Round0Msg`] messages from all other participants,
///   keyed by sender [`NodeId`]
/// - `peers` -- all participant IDs mapped to identity public keys
/// - `config` -- session parameters
///
/// # Returns
///
/// A [`DkgOutput`] containing:
/// - `public_key` -- the shared group public key `PK = g^sk`
/// - `public_key_shares` -- per-participant public key shares `PK_j = g^{sk_j}`
/// - `secret_share` -- this participant's secret key share `sk_i`
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
) -> Result<DkgOutput, DkgError> {
    protocol::round1(
        participant.id,
        participant.sk.inner(),
        peers,
        own_dealing.private_share,
        own_dealing.own_vss_commitment.clone(),
        peer_dealings,
        config.beta,
        config.session_id,
    )
}
