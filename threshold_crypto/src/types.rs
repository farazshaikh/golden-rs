//! Core threshold cryptography types.
//!
//! These are pure crypto types with no display or CLI dependencies.
//! They represent the data structures for BLS12-381 threshold signing
//! with drand-compatible beacon output.

use ark_bls12_381::{Fr, G1Affine, G2Affine};
use golden_dkg::types::NodeId;

/// Information about the threshold group derived from DKG output.
///
/// Contains the shared public key and the BFT parameters (threshold, group size).
#[derive(Clone, Debug)]
pub struct GroupInfo {
    /// The shared group public key `PK = g^{sk}` (BLS12-381 G1).
    pub public_key: G1Affine,
    /// Minimum number of signers needed to produce a valid threshold signature.
    pub threshold: u32,
    /// Total number of nodes in the group.
    pub num_nodes: u32,
}

/// A single node's share of the group secret key.
///
/// Each node holds one `KeyShare` after DKG completes.  Any `threshold`
/// nodes can combine their partial signatures into a full threshold signature.
#[derive(Clone, Debug)]
pub struct KeyShare {
    /// This node's identifier (1-indexed, matches the Shamir evaluation point).
    pub id: NodeId,
    /// This node's secret key share `sk_i` (BLS12-381 scalar).
    pub secret: Fr,
    /// The group parameters this share belongs to.
    pub group_info: GroupInfo,
}

/// A partial BLS signature produced by a single signer.
///
/// Created by [`crate::signing::partial_sign`]. Collect at least `threshold`
/// of these and pass them to [`crate::signing::combine`] to get a
/// [`ThresholdSignature`].
#[derive(Clone, Debug)]
pub struct PartialSignature {
    /// The node that produced this partial signature.
    pub signer: NodeId,
    /// The partial BLS signature `sigma_i = H(m)^{sk_i}` (G2 point).
    pub signature: G2Affine,
}

/// A combined threshold BLS signature.
///
/// Produced by [`crate::signing::combine`] from `>= threshold` partial
/// signatures.  Verifiable against the group public key via
/// [`crate::signing::verify`].
#[derive(Clone, Debug)]
pub struct ThresholdSignature {
    /// The combined BLS signature `sigma = H(m)^{sk}` (G2 point).
    pub signature: G2Affine,
}

/// A random beacon output for a single round.
///
/// Compatible with the [drand](https://drand.love/) beacon wire format.
/// Each beacon contains a deterministic signature over the round number
/// (and optionally the previous signature), plus derived randomness.
#[derive(Clone, Debug)]
pub struct Beacon {
    /// The round number (monotonically increasing).
    pub round: u64,
    /// The previous round's signature bytes (present in [`BeaconMode::Chained`], absent in unchained).
    pub previous_signature: Option<Vec<u8>>,
    /// The threshold BLS signature over the round message (compressed G2).
    pub signature: Vec<u8>,
    /// Derived randomness: `SHA-256(signature)`.
    pub randomness: [u8; 32],
}

/// Beacon chaining mode.
///
/// Determines how the message to sign is constructed each round.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BeaconMode {
    /// Chained mode: `message = SHA-256(prev_signature || round_be_8bytes)`.
    ///
    /// Each round's output depends on the previous round, forming a hash chain.
    Chained,
    /// Unchained mode: `message = SHA-256(round_be_8bytes)`.
    ///
    /// Each round is independent -- useful when you don't need sequential ordering.
    Unchained,
}
