//! Error types for the Golden DKG protocol.
//!
//! Two error enums cover the protocol operations:
//!
//! - [`DkgError`] -- errors from DKG ([`crate::dkg`]) and refresh ([`crate::refresh`])
//! - [`ReshareError`] -- errors from membership-change resharing ([`crate::reshare`])
//!
//! In general, verification errors indicate a malicious or misbehaving participant
//! (or message corruption). The error payloads include the offending participant's
//! [`NodeId`] so the caller can identify and exclude them.

use crate::types::NodeId;

/// Error type for DKG and refresh protocol operations.
///
/// Returned by functions in [`crate::dkg`] and [`crate::refresh`].
/// Verification errors (ciphertext, proof, session) indicate a malicious or
/// misbehaving participant whose dealing should be rejected.
#[derive(Debug)]
pub enum DkgError {
    /// A ciphertext failed the `g^{z_{j,k}} == R_{j,k} * X_bar_{j,k}` consistency
    /// check (Figure 4, line 9 of the Golden paper).
    ///
    /// The sender's encrypted share for the given recipient is inconsistent with
    /// their VSS commitment. The caller should reject the sender's entire dealing.
    CiphertextVerificationFailed {
        /// The node that sent the malformed ciphertext.
        sender: NodeId,
        /// The intended recipient of the ciphertext.
        recipient: NodeId,
    },
    /// An expected ciphertext was missing from a sender's dealing message.
    ///
    /// The sender's [`Round0Msg`](crate::types::Round0Msg) did not contain an
    /// encrypted share for the expected recipient. This is either a protocol
    /// violation or message truncation. The caller should reject the dealing.
    MissingCiphertext {
        /// The node whose message lacked the ciphertext.
        sender: NodeId,
        /// The node that was expecting a ciphertext.
        recipient: NodeId,
    },
    /// During refresh, the first VSS commitment coefficient `A_{j,0}` was not the
    /// group identity element (Section 5.2 violation).
    ///
    /// This means the sender is not performing a zero-secret sharing and is
    /// attempting to shift the global secret `sk`. The caller should reject the
    /// dealing and may want to exclude the sender from future sessions.
    ZeroSecretViolation {
        /// The node that violated the zero-secret invariant.
        sender: NodeId,
    },
    /// The number of peers did not match the expected `n`.
    ///
    /// Check that the `peers` map passed to [`crate::dkg::create_dealing`]
    /// contains exactly `config.n` entries (including the caller).
    PeerCountMismatch {
        /// Expected peer count (from `DkgConfig::n`).
        expected: u32,
        /// Actual peer count provided.
        got: usize,
    },
    /// Failed to receive a broadcast message from a peer.
    ///
    /// This is a transport-layer error -- the caller should check network
    /// connectivity and retry or abort the session.
    BroadcastReceiveFailed {
        /// The node that failed to receive.
        node: NodeId,
        /// Description of the receive failure.
        reason: String,
    },
    /// PKI registration failed (invalid Schnorr proof of knowledge).
    ///
    /// The participant's proof of knowledge did not verify against their claimed
    /// public key. This prevents rogue-key attacks (Appendix F). The caller
    /// should reject the participant's registration.
    RegistrationFailed {
        /// The node whose registration failed.
        node: NodeId,
        /// Description of the registration failure.
        reason: String,
    },
    /// The dealing's session ID does not match the expected value.
    ///
    /// This is a replay protection check. The dealing may be from a different
    /// session or a replay of an old message. The caller should reject the dealing.
    SessionMismatch {
        /// The node that sent the mismatched session ID.
        sender: NodeId,
    },
    /// eVRF proof generation or verification failed.
    ///
    /// During [`crate::dkg::create_dealing`]: proof generation encountered an
    /// internal error (e.g., R1CS constraint system failure).
    /// During [`crate::dkg::verify_dealing`]: the eVRF proof did not verify,
    /// meaning the sender did not correctly derive the encryption pads.
    /// The caller should reject the dealing.
    ProofError(
        /// Description of the proof failure.
        String,
    ),
}

impl std::fmt::Display for DkgError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl std::error::Error for DkgError {}

/// Error type for membership-change resharing operations.
///
/// Returned by functions in [`crate::reshare`]. These errors cover both the
/// old member's dealing creation and the new member's completion phase.
#[derive(Debug)]
pub enum ReshareError {
    /// A reshare dealing's VSS commitment does not match the sender's known
    /// public key share.
    ///
    /// During [`crate::reshare::verify_dealing`]: `commitment[0] != PK_i` where
    /// `PK_i` is the sender's public key share from the old DKG output. The
    /// sender is dishonest or using the wrong share. Reject the dealing.
    CiphertextVerificationFailed {
        /// The old-group dealer that sent the bad dealing.
        sender: NodeId,
        /// The new-group member the ciphertext was intended for (0 for commitment check).
        recipient: NodeId,
    },
    /// An expected ciphertext was missing from a reshare dealing.
    ///
    /// The old-group dealer's [`ReshareMsg`](crate::types::ReshareMsg) did not
    /// include an encrypted sub-share for this new-group member. Reject the dealing.
    MissingCiphertext {
        /// The dealer whose message lacked the ciphertext.
        sender: NodeId,
        /// The new-group member that was expecting a ciphertext.
        recipient: NodeId,
    },
    /// Fewer than `t_old` old-group dealers participated in the reshare.
    ///
    /// At least `t_old` dealings are required for the new member to reconstruct
    /// their share via Lagrange interpolation. The caller should wait for more
    /// dealings or abort the session.
    InsufficientDealers {
        /// Minimum number of dealers required (= `t_old`).
        needed: u32,
        /// Actual number of valid dealings received.
        got: u32,
    },
    /// Failed to receive a broadcast message from an old-group member.
    ///
    /// Transport-layer error. Check connectivity and retry.
    BroadcastReceiveFailed {
        /// The node that failed to receive.
        node: NodeId,
        /// Description of the receive failure.
        reason: String,
    },
    /// PKI registration failed for a new-group member.
    ///
    /// The participant's Schnorr proof of knowledge did not verify. Reject
    /// the registration.
    RegistrationFailed {
        /// The node whose registration failed.
        node: NodeId,
        /// Description of the registration failure.
        reason: String,
    },
    /// Duplicate node indices encountered during Lagrange interpolation.
    ///
    /// Two old-group dealers have the same [`NodeId`], which would cause a
    /// division-by-zero in the Lagrange basis computation. This indicates a
    /// protocol setup error.
    DuplicateNodeIndex {
        /// The duplicate node index.
        index: NodeId,
    },
    /// No reshare messages were received from the old group at all.
    ///
    /// The new member cannot complete the reshare protocol without at least
    /// `t_old` dealings. Check that old-group members are online and broadcasting.
    NoMessages,
    /// The reshare dealing's session ID does not match the expected value.
    ///
    /// Possible replay attack or configuration mismatch. Reject the dealing.
    SessionMismatch {
        /// The node that sent the mismatched session ID.
        sender: NodeId,
    },
}

impl std::fmt::Display for ReshareError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl std::error::Error for ReshareError {}
