//! Core types for the Simplex BFT consensus protocol.
//!
//! Paper reference: Chan & Pass 2023, "Simplex Consensus" (Section 2).
//!
//! Types are split into three groups:
//! 1. Protocol data structures (Block, Certificate, etc.) -- from the paper
//! 2. Replica I/O (Message, StateTransition, Outgoing) -- the state machine API
//! 3. Configuration (NetworkConfig, ChainState)

use ark_bls12_381::{G1Affine, G2Affine};
use golden_dkg::types::NodeId;

// ── Protocol data structures (Paper Section 2) ─────────────────────────

/// A view (iteration) number in the Simplex protocol.
/// Paper: "The protocol runs in sequential iterations h = 1, 2, 3, ..."
pub type View = u64;

/// A 32-byte block hash (SHA-256).
pub type BlockHash = [u8; 32];

/// A consensus block proposed by a leader in a given view.
///
/// Paper: "A block b is a tuple (h, parent, txs)".
#[derive(Clone, Debug, PartialEq)]
pub struct Block {
    /// The view this block was proposed in.
    /// Paper: "h -- the height of the block"
    pub view: View,
    /// Hash of the parent block (or genesis hash [0;32] for view 1).
    /// Paper: "parent -- the hash of a parent blockchain"
    pub parent_hash: BlockHash,
    /// Arbitrary payload data.
    /// Paper: "txs -- an arbitrary sequence of strings"
    pub payload: Vec<u8>,
    /// The node that proposed this block.
    pub proposer: NodeId,
}

/// The kind of certificate produced in a view.
#[derive(Clone, Debug)]
pub enum CertKind {
    /// A notarization certificate for a block.
    /// Paper: "A notarization for a block b is a set of signed messages
    /// <vote, h, b> from >= 2n/3 unique processes."
    Notarization(BlockHash),
    /// A nullification certificate (dummy block notarized).
    /// Paper: "The special dummy block of height h is the tuple ⊥_h."
    Nullification,
    /// A finalization certificate for a block.
    /// Paper: "A finalization for a height h is a set of signed messages
    /// <finalize, h> from >= 2n/3 unique processes."
    Finalization(BlockHash),
}

/// A threshold BLS certificate (combined from >= 2f+1 partial signatures).
#[derive(Clone, Debug)]
pub struct Certificate {
    pub view: View,
    pub kind: CertKind,
    /// The combined threshold BLS signature (G2 point).
    pub signature: G2Affine,
}

// ── Replica I/O: the state machine API ─────────────────────────────────

/// A message that a Replica can receive from the network (or local timer).
///
/// These correspond to the protocol steps in Paper Section 2.1.
#[derive(Clone, Debug)]
pub enum Message {
    /// Paper Step 1: Leader proposal.
    /// "<propose, h, b_0, ..., b_h, S>"
    Proposal {
        block: Block,
    },

    /// Paper Step 3: A notarization vote from another node.
    /// "<vote, h, b_h>"
    Vote {
        view: View,
        block_hash: BlockHash,
        signer: NodeId,
        partial: threshold_crypto::types::PartialSignature,
    },

    /// Paper Step 2: Local timer T_h fired.
    /// The replica should vote for the dummy block.
    Timeout {
        view: View,
    },

    /// Paper Step 2: A nullification vote from another node.
    /// "<vote, h, ⊥_h>"
    NullifyVote {
        view: View,
        signer: NodeId,
        partial: threshold_crypto::types::PartialSignature,
    },

    /// Paper Step 4: A finalize vote from another node.
    /// "<finalize, h>"
    FinalizeVote {
        view: View,
        signer: NodeId,
        partial: threshold_crypto::types::PartialSignature,
    },

    /// Paper Step 4: A notarized blockchain of height h was observed.
    /// This allows the replica to enter iteration h+1 even if it didn't
    /// see the individual votes (e.g., relayed by another node).
    Notarization {
        view: View,
        block: Block,
        certificate: Certificate,
    },
}

/// The state transition produced by a Replica after processing a Message.
///
/// Paper Section 2.1, Steps 3-5.
#[derive(Clone, Debug)]
pub enum StateTransition {
    /// Block was notarized at this height (got >= 2n/3 votes).
    /// Paper: "A notarized block is a block augmented with a notarization."
    Notarized {
        view: View,
        block_hash: BlockHash,
    },

    /// Block was finalized (notarized + >= 2n/3 finalize votes).
    /// Paper Step 5: "output LOG <- linearize(b_0, ..., b_h')"
    Finalized {
        view: View,
        block_hash: BlockHash,
    },

    /// View was nullified (dummy block reached >= 2n/3 votes).
    /// Paper: "vote for the dummy block" -> notarized dummy -> next iteration.
    Nullified {
        view: View,
    },

    /// Proposal was rejected.
    Rejected {
        view: View,
        reason: RejectReason,
    },

    /// No state change yet (accumulating votes, waiting for threshold).
    Pending,
}

/// Why a proposal was rejected by this replica.
#[derive(Clone, Debug)]
pub enum RejectReason {
    /// The proposer is not the designated leader L_h for this view.
    /// Paper Step 3: "On seeing the first proposal from L_h..."
    WrongLeader,
    /// The block's parent_hash doesn't match this replica's chain tip.
    /// Paper Step 3: "check that b_0, ..., b_h is a valid blockchain"
    BadParentHash,
    /// The message is for a different view than the replica's current view.
    WrongView,
    /// This replica already voted in this view (one vote per iteration).
    /// Paper Step 3: honest node votes for "the first proposal".
    AlreadyVoted,
}

/// An outgoing message that the Replica wants to broadcast.
///
/// The caller (engine / network layer) is responsible for delivering these
/// to other replicas or the network.
#[derive(Clone, Debug)]
pub enum Outgoing {
    /// Broadcast <vote, h, b_h> to all peers.
    /// Paper Step 3: "multicast <vote, h, b_h>"
    Vote {
        view: View,
        block_hash: BlockHash,
        partial: threshold_crypto::types::PartialSignature,
    },

    /// Broadcast <vote, h, ⊥_h> to all peers (dummy/timeout vote).
    /// Paper Step 2: "vote for the dummy block by multicasting <vote, h, ⊥_h>"
    NullifyVote {
        view: View,
        partial: threshold_crypto::types::PartialSignature,
    },

    /// Broadcast <finalize, h> to all peers.
    /// Paper Step 4: "cancel T_h and multicast <finalize, h>"
    FinalizeVote {
        view: View,
        partial: threshold_crypto::types::PartialSignature,
    },

    /// Relay the notarized blockchain to all peers.
    /// Paper Step 4: "p multicasts its view of the notarized blockchain"
    RelayNotarization {
        view: View,
        block: Block,
        certificate: Certificate,
    },
}

// ── Configuration ──────────────────────────────────────────────────────

/// Network configuration: public parameters for all replicas.
///
/// Paper: "a bare PKI" (Section 2).
#[derive(Clone)]
pub struct NetworkConfig {
    /// Total number of nodes.
    pub n: u32,
    /// Threshold for quorum (2f + 1).
    pub t: u32,
    /// Maximum Byzantine faults tolerated (f < n/3).
    pub f: u32,
    /// Group public key from DKG.
    pub group_pk: G1Affine,
}

/// Tracks the local chain state of a replica across views.
#[derive(Clone, Debug)]
pub struct ChainState {
    /// The latest finalized block hash (genesis = all zeros).
    pub tip_hash: BlockHash,
    /// The current VRF seed for leader election (genesis = all zeros).
    pub vrf_seed: [u8; 32],
    /// Number of blocks finalized so far.
    pub finalized_count: u64,
    /// Number of nullified views so far.
    pub nullified_count: u64,
}

impl ChainState {
    /// Create the genesis chain state.
    pub fn genesis() -> Self {
        Self {
            tip_hash: [0u8; 32],
            vrf_seed: [0u8; 32],
            finalized_count: 0,
            nullified_count: 0,
        }
    }
}

// ── Helpers ────────────────────────────────────────────────────────────

/// Compute the SHA-256 hash of a block.
pub fn block_hash(block: &Block) -> BlockHash {
    use sha2::{Digest, Sha256};
    let mut hasher = Sha256::new();
    hasher.update(block.view.to_be_bytes());
    hasher.update(block.parent_hash);
    hasher.update(&block.payload);
    hasher.update(block.proposer.to_be_bytes());
    let result = hasher.finalize();
    let mut hash = [0u8; 32];
    hash.copy_from_slice(&result);
    hash
}
