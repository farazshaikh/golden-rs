//! Core types for the Simplex BFT consensus protocol.
//!
//! Paper reference: Chan & Pass 2023, "Simplex Consensus"
//! <https://eprint.iacr.org/2023/463.pdf>, Section 2.
//!
//! # Paper-to-Code Mapping (Data Structures, Section 2, pages 8-9)
//!
//! | Paper | Code |
//! |-------|------|
//! | "A block b is a tuple (h, parent, txs)" | [`Block`] `{ view, parent_hash, payload, proposer }` |
//! | "The genesis block b_0 := (0, empty, empty)" | [`ChainState::genesis()`] with `tip_hash: [0; 32]` |
//! | "The dummy block ⊥_h := (h, ⊥, ⊥)" | Sentinel `[0u8; 32]` in `Replica::notarized_in_view` |
//! | "A notarization: signed `<vote, h, b>` from >= 2n/3" | [`CertKind::Notarization`] + `Replica::try_notarize()` |
//! | "A finalization: signed `<finalize, h>` from >= 2n/3" | [`CertKind::Finalization`] + `Replica::try_finalize()` |
//! | "H: collision-resistant hash function" | [`block_hash()`] using SHA-256 |

use ark_bls12_381::{G1Affine, G2Affine};
use crate::types::NodeId;

// ── Protocol data structures (Paper Section 2) ─────────────────────────

/// A view (iteration) number in the Simplex protocol.
///
/// Paper: "The protocol runs in sequential iterations h = 1, 2, 3, ..."
/// Each iteration has exactly one designated leader and produces either
/// a notarized block or a notarized dummy block.
pub type View = u64;

/// A 32-byte block hash (SHA-256).
///
/// Paper: "H : {0,1}* -> {0,1}* is a publicly known collision-resistant
/// hash function." We instantiate H with SHA-256.
pub type BlockHash = [u8; 32];

/// A consensus block proposed by a leader in a given view.
///
/// Paper (Section 2, page 8): "A block b is a tuple (h, parent, txs),
/// where h is the height, parent is the hash of a parent blockchain,
/// and txs is an arbitrary sequence of strings."
///
/// We add `proposer` to identify the leader who created the block.
#[derive(Clone, Debug, PartialEq)]
pub struct Block {
    /// The view (= height h) this block was proposed in.
    /// Paper: "h -- the height of the block"
    pub view: View,

    /// Hash of the parent block (or genesis hash `[0;32]` for view 1).
    /// Paper: "parent -- the hash of a parent blockchain"
    pub parent_hash: BlockHash,

    /// Arbitrary payload data (transactions).
    /// Paper: "txs -- an arbitrary sequence of strings"
    pub payload: Vec<u8>,

    /// The node that proposed this block.
    pub proposer: NodeId,
}

/// The kind of certificate produced in a view.
///
/// Paper (Section 2, pages 8-9): The protocol produces three kinds of
/// quorum certificates, each requiring >= 2n/3 signed messages.
#[derive(Clone, Debug)]
pub enum CertKind {
    /// A notarization certificate for a real block.
    ///
    /// Paper: "A notarization for a block b is a set of signed messages
    /// `<vote, h, b>` from >= 2n/3 unique processes p in [n], where h is
    /// the height of the block b."
    Notarization(BlockHash),

    /// A nullification certificate (dummy block notarized).
    ///
    /// Paper: "The special dummy block of height h is the tuple ⊥_h :=
    /// (h, ⊥, ⊥). This is an empty block that will be inserted into the
    /// blockchain at heights where no agreement is reached."
    Nullification,

    /// A finalization certificate for a block.
    ///
    /// Paper: "A finalization for a height h is a set of signed messages
    /// `<finalize, h>` from >= 2n/3 unique processes p in [n]. We say
    /// that a block of height h is finalized if it is notarized and
    /// accompanied by a finalization for h."
    Finalization(BlockHash),
}

/// A threshold BLS certificate (combined from >= 2f+1 partial signatures).
///
/// Paper: certificates are sets of 2n/3 signed messages. We use threshold
/// BLS signatures so the certificate is a single combined G2 point.
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
/// These correspond to the protocol steps in Paper Section 2.1 (pages 9-10).
///
/// # Paper-to-Code Mapping (Protocol Messages)
///
/// | Paper Message | Variant |
/// |---------------|---------|
/// | `<propose, h, b_0..b_h, S>` (Step 1) | [`Proposal`](Message::Proposal) |
/// | `<vote, h, b_h>` (Step 3) | [`Vote`](Message::Vote) |
/// | `<vote, h, ⊥_h>` (Step 2, timer fires) | [`NullifyVote`](Message::NullifyVote) |
/// | Timer T_h fires (Step 2) | [`Timeout`](Message::Timeout) |
/// | `<finalize, h>` (Step 4) | [`FinalizeVote`](Message::FinalizeVote) |
/// | Relayed notarized blockchain (Step 4) | [`Notarization`](Message::Notarization) |
/// | "If p = L_h, propose" (Step 1) | [`ProposeRequest`](Message::ProposeRequest) |
#[derive(Clone, Debug)]
pub enum Message {
    /// Paper Step 1: Leader proposal `<propose, h, b_0, ..., b_h, S>`.
    Proposal { block: Block },

    /// Paper Step 3: A notarization vote `<vote, h, b_h>` from another node.
    Vote {
        view: View,
        block_hash: BlockHash,
        signer: NodeId,
        partial: crate::threshold::types::PartialSignature,
    },

    /// Paper Step 2: Local timer T_h fired.
    ///
    /// Paper: "Each process p starts a new timer T_h, set to fire locally
    /// after 3*Delta time. If T_h fires, vote for the dummy block."
    /// The timer itself is external; this message triggers the vote.
    Timeout { view: View },

    /// Paper Step 2: A nullification vote `<vote, h, ⊥_h>` from another node.
    NullifyVote {
        view: View,
        signer: NodeId,
        partial: crate::threshold::types::PartialSignature,
    },

    /// Paper Step 4: A finalize vote `<finalize, h>` from another node.
    ///
    /// Paper: "If the timer T_h did not fire yet: cancel T_h and multicast
    /// `<finalize, h>`."
    FinalizeVote {
        view: View,
        signer: NodeId,
        partial: crate::threshold::types::PartialSignature,
    },

    /// Paper Step 4: A relayed notarized blockchain of height h.
    ///
    /// Paper: "On seeing a notarized blockchain of height h, enter
    /// iteration h+1. At the same time, p multicasts its view of the
    /// notarized blockchain to everyone else."
    Notarization {
        view: View,
        block: Block,
        certificate: Certificate,
    },

    /// Request this replica to propose a block for the given view.
    ///
    /// Paper Step 1: "If p = L_h, p multicasts a single proposal."
    /// The replica checks it IS the leader and builds the block from
    /// its own chain state (`parent_hash = self.chain_state.tip_hash`).
    ProposeRequest {
        view: View,
        payload: Vec<u8>,
    },
}

/// The state transition produced by a Replica after processing a Message.
///
/// # Paper-to-Code Mapping (State Transitions)
///
/// | Paper Concept | Variant |
/// |---------------|---------|
/// | "A notarized block" (>= 2n/3 votes) | [`Notarized`](StateTransition::Notarized) |
/// | "A finalized block" (notarized + >= 2n/3 finalize) | [`Finalized`](StateTransition::Finalized) |
/// | Notarized dummy block ⊥_h | [`Nullified`](StateTransition::Nullified) |
#[derive(Clone, Debug)]
pub enum StateTransition {
    /// Block notarized at this height (>= 2n/3 votes).
    /// Paper: "A notarized block is a block augmented with a notarization."
    Notarized { view: View, block_hash: BlockHash },

    /// Block finalized (notarized + >= 2n/3 finalize votes).
    /// Paper Step 5: "output LOG <- linearize(b_0, ..., b_h')"
    Finalized { view: View, block_hash: BlockHash },

    /// Dummy block notarized (>= 2n/3 dummy votes). View nullified.
    /// Paper: "vote for the dummy block -> notarized dummy -> next iteration."
    Nullified { view: View },

    /// Proposal rejected (invalid leader, bad parent, duplicate vote).
    Rejected { view: View, reason: RejectReason },

    /// No state change yet (accumulating votes, waiting for threshold).
    Pending,
}

/// Why a proposal was rejected by this replica.
///
/// Each reason corresponds to a validation check in Paper Section 2.1, Step 3.
#[derive(Clone, Debug)]
pub enum RejectReason {
    /// Proposer is not the designated leader L_h.
    /// Paper Step 3: "On seeing the first proposal from L_h..."
    WrongLeader,

    /// Block's parent_hash doesn't match this replica's chain tip.
    /// Paper Step 3: "check that b_0, ..., b_h is a valid blockchain"
    BadParentHash,

    /// Message is for a different view than this replica's current view.
    WrongView,

    /// This replica already voted in this view.
    /// Paper Step 3: honest node votes for "the first proposal" only.
    /// Safety invariant: Lemma 3.2 requires at most one non-dummy vote per height.
    AlreadyVoted,
}

/// An outgoing message that the Replica wants to broadcast.
///
/// The caller (engine / network layer) delivers these to other replicas.
///
/// # Paper-to-Code Mapping (Outgoing Messages)
///
/// | Paper Action | Variant |
/// |-------------|---------|
/// | "multicast `<vote, h, b_h>`" (Step 3) | [`Vote`](Outgoing::Vote) |
/// | "multicast `<vote, h, ⊥_h>`" (Step 2) | [`NullifyVote`](Outgoing::NullifyVote) |
/// | "multicast `<finalize, h>`" (Step 4) | [`FinalizeVote`](Outgoing::FinalizeVote) |
/// | "multicasts notarized blockchain" (Step 4) | [`RelayNotarization`](Outgoing::RelayNotarization) |
/// | "multicasts proposal" (Step 1) | [`Proposal`](Outgoing::Proposal) |
#[derive(Clone, Debug)]
pub enum Outgoing {
    /// Broadcast `<vote, h, b_h>` to all peers.
    /// Paper Step 3: "If all checks pass, multicast `<vote, h, b_h>`."
    Vote {
        view: View,
        block_hash: BlockHash,
        partial: crate::threshold::types::PartialSignature,
    },

    /// Broadcast `<vote, h, ⊥_h>` to all peers (dummy/timeout vote).
    /// Paper Step 2: "vote for the dummy block by multicasting `<vote, h, ⊥_h>`."
    NullifyVote {
        view: View,
        partial: crate::threshold::types::PartialSignature,
    },

    /// Broadcast `<finalize, h>` to all peers.
    /// Paper Step 4: "cancel T_h and multicast `<finalize, h>`."
    FinalizeVote {
        view: View,
        partial: crate::threshold::types::PartialSignature,
    },

    /// Relay the notarized blockchain to all peers.
    /// Paper Step 4: "p multicasts its view of the notarized blockchain."
    RelayNotarization {
        view: View,
        block: Block,
        certificate: Certificate,
    },

    /// A block proposal to broadcast to all peers.
    /// Paper Step 1: "leader multicasts `<propose, h, b_0..b_h, S>`."
    Proposal { block: Block },
}

// ── Configuration ──────────────────────────────────────────────────────

/// Network configuration: public parameters for all replicas.
///
/// Paper (Section 2, page 8): "a bare PKI" setup where each process has
/// a keypair and all public keys are known.
#[derive(Clone)]
pub struct NetworkConfig {
    /// Total number of nodes.
    pub n: u32,
    /// Threshold for quorum (2f + 1). Paper: ">= 2n/3 unique processes."
    pub t: u32,
    /// Maximum Byzantine faults tolerated. Paper: "f < n/3."
    pub f: u32,
    /// Group public key from DKG.
    pub group_pk: G1Affine,
}

/// Tracks the local chain state of a replica across views.
///
/// Paper: Each process "keeps track of which iteration h it is currently in,
/// and also stores all of the notarized blocks and messages that it has seen."
/// We simplify to just the tip hash, VRF seed, and counters.
#[derive(Clone, Debug)]
pub struct ChainState {
    /// Hash of the latest notarized non-dummy block (genesis = `[0; 32]`).
    /// Paper: the tip of the "notarized blockchain."
    pub tip_hash: BlockHash,
    /// VRF seed for leader election, derived from the last notarization's
    /// combined threshold signature.
    pub vrf_seed: [u8; 32],
    /// Number of blocks finalized (notarized + 2n/3 finalize votes).
    pub finalized_count: u64,
    /// Number of views nullified (dummy block notarized).
    pub nullified_count: u64,
}

impl ChainState {
    /// Create the genesis chain state.
    /// Paper: "Define the genesis block to be b_0 := (0, empty, empty)."
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
///
/// Paper: "H : {0,1}* -> {0,1}* is a collision-resistant hash function."
/// Used to chain blocks (parent_hash) and identify blocks in certificates.
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
