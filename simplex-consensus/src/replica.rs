//! Replica -- pure state machine for one Simplex consensus participant.
//!
//! This is the formal verification target. The single entry point is
//! [`Replica::apply_message`], which processes one [`Message`] and returns
//! a [`StateTransition`] plus any [`Outgoing`] messages to broadcast.
//!
//! The Replica has NO I/O, NO timers, NO networking. The caller is
//! responsible for delivering messages and triggering timeouts.
//!
//! # Protocol Steps (Paper Section 2.1, pages 9-10)
//!
//! | Step | Paper Quote | Handler |
//! |------|-------------|---------|
//! | 1 | "If p = L_h, p multicasts a single proposal" | [`handle_propose_request`] |
//! | 2 | "If T_h fires, vote for dummy `<vote, h, ⊥_h>`" | [`handle_timeout`] |
//! | 3 | "On seeing first proposal from L_h, vote `<vote, h, b_h>`" | [`handle_proposal`] |
//! | 4 | "On seeing notarized chain of height h, enter h+1" | [`try_notarize`] / [`handle_notarization`] |
//! | 4 | "If timer did NOT fire, multicast `<finalize, h>`" | [`try_notarize`] line 457 |
//! | 5 | "Whenever p sees finalized blockchain, output LOG" | [`try_finalize`] |
//!
//! # Safety Invariants (Paper Section 2.2, Section 3.2)
//!
//! **Lemma 3.2**: Two distinct non-dummy blocks CANNOT both be notarized at
//! the same height (with f < n/3). Enforced by [`voted_in_view`]: each replica
//! votes for at most ONE non-dummy block per iteration.
//!
//! **Lemma 3.3**: If height h is finalized, dummy ⊥_h CANNOT be notarized.
//! Enforced by [`finalize_sent`] and [`dummy_sent`]: a replica sends EITHER
//! `<finalize, h>` OR `<vote, h, ⊥_h>`, NEVER both.
//!
//! **Theorem 3.1** (Consistency): If Alice finalizes a chain ending at h, and
//! Bob finalizes a longer chain, Alice's chain is a prefix of Bob's. Follows
//! from Lemmas 3.2 + 3.3 + collision-resistant [`block_hash()`].
//!
//! # Message Flow
//!
//! ```text
//! ProposeRequest -> Replica (leader) -> Outgoing::Proposal + Vote
//!     |
//!     v
//! Proposal -> Replica (voter) -> Outgoing::Vote
//!     |
//!     v
//! Vote -> Replica (accumulate) -> [>= 2n/3] -> FinalizeVote + RelayNotarization
//!     |                                              |
//!     v                                              v
//! FinalizeVote -> [>= 2n/3] -> Finalized     Notarization -> advance_view
//!
//! OR (timeout path):
//!
//! Timeout -> Replica -> NullifyVote
//!     |
//!     v
//! NullifyVote -> [>= 2n/3] -> Nullified -> advance_view
//! ```

use std::collections::HashMap;

use golden_dkg::types::NodeId;
use threshold_crypto::beacon;
use threshold_crypto::signing;
use threshold_crypto::types::{KeyShare, PartialSignature};

use crate::types::*;
use crate::vrf;

/// A Simplex consensus replica (one participant's state machine).
///
/// Paper (Section 2.1): "each process p keeps track of which iteration h
/// it is currently in, and also stores all of the notarized blocks and
/// messages that it has seen thus far."
pub struct Replica {
    /// This replica's node identifier (1-indexed).
    id: NodeId,
    /// This replica's threshold key share.
    share: KeyShare,
    /// Network configuration (n, t, f, group_pk).
    config: NetworkConfig,

    // ── Per-view state (reset on advance_view) ──────────────────────────

    /// Current view (iteration) this replica is in.
    /// Paper: "The protocol runs in sequential iterations h = 1, 2, 3, ..."
    current_view: View,

    /// Whether this replica has voted for a non-dummy block in the current view.
    ///
    /// **Safety (Lemma 3.2)**: An honest process signs at most one of
    /// `(vote, h, b_h)` and `(vote, h, b'_h)`. This flag enforces that.
    voted_in_view: bool,

    /// Whether this replica's timer has fired in the current view.
    /// Paper Step 2: "If T_h fires, vote for the dummy block."
    timer_fired: bool,

    /// Whether this replica has sent `<finalize, h>` in this view.
    ///
    /// **Safety (Lemma 3.3)**: An honest process signs at most one of
    /// `<finalize, h>` or `<vote, h, ⊥_h>`. The `finalize_sent` and
    /// `dummy_sent` flags together enforce this mutual exclusion.
    finalize_sent: bool,

    /// Whether this replica has sent `<vote, h, ⊥_h>` in this view.
    ///
    /// **Safety (Lemma 3.3)**: see `finalize_sent` above.
    dummy_sent: bool,

    /// The block this replica voted for in this view (if any).
    voted_block: Option<Block>,

    /// All blocks seen in this view (by hash), for notarization tracking.
    ///
    /// Paper Step 4: "On seeing a notarized blockchain of height h" --
    /// a replica accepts notarization even for blocks it didn't vote for.
    /// Storing all seen blocks allows this.
    known_blocks: HashMap<BlockHash, Block>,

    // ── Vote accumulators (per view) ────────────────────────────────────

    /// Notarization votes received: `block_hash -> [(signer, partial_sig)]`.
    /// Paper: "A notarization for block b is `<vote, h, b>` from >= 2n/3."
    notarize_votes: HashMap<BlockHash, Vec<(NodeId, PartialSignature)>>,

    /// Nullification (dummy) votes received.
    /// Paper: "`<vote, h, ⊥_h>` from >= 2n/3 processes."
    nullify_votes: Vec<(NodeId, PartialSignature)>,

    /// Finalize votes received.
    /// Paper: "`<finalize, h>` from >= 2n/3 processes."
    finalize_votes: Vec<(NodeId, PartialSignature)>,

    /// Whether a block has been notarized in this view (to avoid re-processing).
    /// `Some(block_hash)` for a real block, `Some([0;32])` for dummy.
    notarized_in_view: Option<BlockHash>,

    // ── Chain state ─────────────────────────────────────────────────────

    /// This replica's local chain state.
    chain_state: ChainState,
}

impl Replica {
    /// Create a new Replica in the genesis state.
    ///
    /// Paper: "each process starts in iteration h = 1."
    pub fn new(id: NodeId, share: KeyShare, config: NetworkConfig) -> Self {
        Self {
            id,
            share,
            config,
            current_view: 1,
            voted_in_view: false,
            timer_fired: false,
            finalize_sent: false,
            dummy_sent: false,
            voted_block: None,
            known_blocks: HashMap::new(),
            notarize_votes: HashMap::new(),
            nullify_votes: Vec::new(),
            finalize_votes: Vec::new(),
            notarized_in_view: None,
            chain_state: ChainState::genesis(),
        }
    }

    // ── Public API ──────────────────────────────────────────────────────

    /// Process one message. Returns the state transition and any outgoing
    /// messages the replica wants to broadcast.
    ///
    /// This is the ONLY entry point for the state machine.
    pub fn apply_message(&mut self, msg: Message) -> (StateTransition, Vec<Outgoing>) {
        match msg {
            Message::Proposal { block } => self.handle_proposal(block),
            Message::Vote { view, block_hash, signer, partial } => {
                self.handle_vote(view, block_hash, signer, partial)
            }
            Message::Timeout { view } => self.handle_timeout(view),
            Message::NullifyVote { view, signer, partial } => {
                self.handle_nullify_vote(view, signer, partial)
            }
            Message::FinalizeVote { view, signer, partial } => {
                self.handle_finalize_vote(view, signer, partial)
            }
            Message::Notarization { view, block, certificate } => {
                self.handle_notarization(view, block, certificate)
            }
            Message::ProposeRequest { view, payload } => {
                self.handle_propose_request(view, payload)
            }
        }
    }

    /// Current view the replica is in.
    pub fn current_view(&self) -> View {
        self.current_view
    }

    /// Current chain state (tip hash, VRF seed, counters).
    pub fn chain_state(&self) -> &ChainState {
        &self.chain_state
    }

    /// This replica's node ID.
    pub fn id(&self) -> NodeId {
        self.id
    }

    /// Who is the designated leader for the current view.
    ///
    /// Paper (Section 2.1): "L_h := H*(h) mod n, where H* is a random
    /// leader election oracle." We use the VRF seed from the previous
    /// notarization as input to SHA-256.
    pub fn leader_for(&self, _view: View) -> NodeId {
        vrf::elect_leader(&self.chain_state.vrf_seed, self.config.n)
    }

    /// Access this replica's threshold key share (for vetKD operations).
    pub fn key_share(&self) -> &KeyShare {
        &self.share
    }

    /// Access this replica's network config.
    pub fn network_config(&self) -> &NetworkConfig {
        &self.config
    }

    // ── vetKD: Encrypted key share production ────────────────────────────
    //
    // DFINITY vetKeys reference: "Each node uses its share of the master key
    // to compute an encrypted share of the derived key, which is encrypted
    // with the user's transport public key."
    // (https://docs.internetcomputer.org/references/vetkeys-overview)
    //
    // vetKeys paper, Section 5.3, pi_vetbls-agg2, Figure 9 (p.27):
    // "On (sid, encsign, m, tpk), S_i computes sigma_i = H(m)^{sk_i},
    //  encrypts sigma_i as (C1, C2, C3) = (g1^r, g2^r, tpk^r * sigma_i)"

    /// Produce an encrypted key share for the given identity.
    ///
    /// Mirrors DFINITY's per-node behavior in `vetkd_derive_key`:
    /// each node computes its partial BLS signature on the identity,
    /// encrypts it under the user's transport public key, and returns
    /// the encrypted share. The share is publicly verifiable via pairing
    /// without revealing the partial signature.
    ///
    /// This is a **pure function** on the replica's key share -- no
    /// consensus state is modified, no messages are queued.
    pub fn vetkd_encrypted_key_share(
        &self,
        identity: &[u8],
        tpk: &threshold_crypto::ibe::TransportPublicKey,
    ) -> threshold_crypto::ibe::EncryptedKeyShare {
        let mut rng = rand::thread_rng();
        threshold_crypto::ibe::encrypt_key_share(
            &self.share,
            identity,
            tpk,
            &mut rng,
        )
    }

    // ── Step 1: Leader Proposal (Paper Section 2.1, Step 1) ─────────────
    //
    // Paper: "If p = L_h, p multicasts a single proposal of the form
    // <propose, h, b_0, ..., b_{h-1}, b_h, S>. Here, b_0,...,b_h is p's
    // choice of a blockchain of height h, where (b_0,...,b_{h-1}, S) is
    // a notarized parent blockchain, and b_h != ⊥_h."

    /// Handle a request to propose a block (leader only).
    ///
    /// The replica checks it IS the designated leader, builds a block from
    /// its own `chain_state.tip_hash`, votes for it, and returns both
    /// [`Outgoing::Proposal`] and [`Outgoing::Vote`].
    fn handle_propose_request(
        &mut self,
        view: View,
        payload: Vec<u8>,
    ) -> (StateTransition, Vec<Outgoing>) {
        if view != self.current_view {
            return (StateTransition::Pending, vec![]);
        }
        let leader = self.leader_for(view);
        if leader != self.id {
            return (StateTransition::Pending, vec![]);
        }

        // Build block from OWN chain state -- no external state needed.
        let block = Block {
            view,
            parent_hash: self.chain_state.tip_hash,
            payload,
            proposer: self.id,
        };

        // Leader also votes for its own block (Paper Step 3).
        let bh = block_hash(&block);
        self.voted_in_view = true;
        self.voted_block = Some(block.clone());
        self.known_blocks.insert(bh, block.clone());
        let sig = self.sign_vote(view, &bh);
        self.notarize_votes.entry(bh).or_default().push((self.id, sig.clone()));

        (StateTransition::Pending, vec![
            Outgoing::Proposal { block },
            Outgoing::Vote { view, block_hash: bh, partial: sig },
        ])
    }

    // ── Step 3: Notarizing Proposals (Paper Section 2.1, Step 3) ────────
    //
    // Paper: "On seeing the first proposal of the form
    // <propose, h, b_0, ..., b_h, S>_{L_h}, check that b_h != ⊥_h,
    // that b_0,...,b_h is a valid blockchain, and that (b_0,...,b_{h-1},S)
    // is a notarized blockchain. If all checks pass, multicast <vote, h, b_h>."

    /// Handle an incoming proposal from the leader.
    ///
    /// Validates: correct view, correct leader (L_h), not already voted,
    /// and valid parent chain (parent_hash matches tip). If all pass,
    /// produces [`Outgoing::Vote`].
    ///
    /// **Lemma 3.2 enforcement**: `voted_in_view` prevents double-voting.
    fn handle_proposal(&mut self, block: Block) -> (StateTransition, Vec<Outgoing>) {
        let view = block.view;

        if view != self.current_view {
            return (StateTransition::Rejected { view, reason: RejectReason::WrongView }, vec![]);
        }

        // Store block for potential later notarization (Paper Step 4).
        self.known_blocks.insert(block_hash(&block), block.clone());

        // Paper: "On seeing the first proposal from L_h" -- must be from leader.
        let leader = self.leader_for(view);
        if block.proposer != leader {
            return (StateTransition::Rejected { view, reason: RejectReason::WrongLeader }, vec![]);
        }

        // Lemma 3.2: at most one non-dummy vote per iteration.
        if self.voted_in_view {
            return (StateTransition::Rejected { view, reason: RejectReason::AlreadyVoted }, vec![]);
        }

        // Paper: "check that b_0,...,b_h is a valid blockchain"
        if block.parent_hash != self.chain_state.tip_hash {
            return (StateTransition::Rejected { view, reason: RejectReason::BadParentHash }, vec![]);
        }

        // All checks pass: vote.
        self.voted_in_view = true;
        self.voted_block = Some(block.clone());

        let bh = block_hash(&block);
        let sig = self.sign_vote(view, &bh);
        self.notarize_votes.entry(bh).or_default().push((self.id, sig.clone()));

        let mut outgoing = vec![Outgoing::Vote { view, block_hash: bh, partial: sig }];

        // Check if this vote pushed the block to notarization threshold.
        let (transition, extra) = self.try_notarize(view, bh, &block);
        outgoing.extend(extra);

        (transition, outgoing)
    }

    // ── Step 2: Timeout / Dummy Vote (Paper Section 2.1, Step 2) ────────
    //
    // Paper: "Each process p starts a new timer T_h, set to fire locally
    // after 3*Delta time. If T_h fires, vote for the dummy block by
    // multicasting <vote, h, ⊥_h>."

    /// Handle timer firing: produce a dummy (nullification) vote.
    ///
    /// **Lemma 3.3 enforcement**: if `finalize_sent` or `dummy_sent` is
    /// already true, this is a no-op. An honest node NEVER sends both
    /// `<finalize, h>` and `<vote, h, ⊥_h>`.
    fn handle_timeout(&mut self, view: View) -> (StateTransition, Vec<Outgoing>) {
        if view != self.current_view {
            return (StateTransition::Pending, vec![]);
        }

        // Lemma 3.3: never both finalize and vote-dummy.
        if self.finalize_sent || self.dummy_sent {
            return (StateTransition::Pending, vec![]);
        }

        self.timer_fired = true;
        self.dummy_sent = true;

        let sig = self.sign_dummy(view);
        self.nullify_votes.push((self.id, sig.clone()));

        let mut outgoing = vec![Outgoing::NullifyVote { view, partial: sig }];
        let (transition, extra) = self.try_nullify(view);
        outgoing.extend(extra);

        (transition, outgoing)
    }

    // ── Vote accumulation ───────────────────────────────────────────────

    /// Accumulate a notarization vote `<vote, h, b_h>` from another node.
    ///
    /// Paper Step 4: "On seeing a notarized blockchain of height h, enter
    /// iteration h+1." Accepts notarization for ANY block at the current
    /// height, even one this replica didn't vote for.
    fn handle_vote(
        &mut self,
        view: View,
        bh: BlockHash,
        signer: NodeId,
        partial: PartialSignature,
    ) -> (StateTransition, Vec<Outgoing>) {
        if view != self.current_view { return (StateTransition::Pending, vec![]); }
        if self.notarized_in_view.is_some() { return (StateTransition::Pending, vec![]); }

        // Deduplicate: each signer counted at most once.
        let votes = self.notarize_votes.entry(bh).or_default();
        if votes.iter().any(|(id, _)| *id == signer) {
            return (StateTransition::Pending, vec![]);
        }
        votes.push((signer, partial));

        // Check threshold for ANY known block (not just the one we voted for).
        if let Some(block) = self.known_blocks.get(&bh).cloned() {
            return self.try_notarize(view, bh, &block);
        }

        (StateTransition::Pending, vec![])
    }

    /// Accumulate a nullification vote `<vote, h, ⊥_h>` from another node.
    fn handle_nullify_vote(
        &mut self,
        view: View,
        signer: NodeId,
        partial: PartialSignature,
    ) -> (StateTransition, Vec<Outgoing>) {
        if view != self.current_view { return (StateTransition::Pending, vec![]); }
        if self.nullify_votes.iter().any(|(id, _)| *id == signer) {
            return (StateTransition::Pending, vec![]);
        }
        self.nullify_votes.push((signer, partial));
        self.try_nullify(view)
    }

    // ── Step 4: Finalize votes (Paper Section 2.1, Step 4) ──────────────
    //
    // Paper: "If the timer T_h did not fire yet: cancel T_h and multicast
    // <finalize, h>." The finalize vote is collected here.

    /// Accumulate a finalize vote `<finalize, h>` from another node.
    ///
    /// Paper Step 5: When >= 2n/3 finalize votes are collected for height h
    /// where a block is already notarized, the block is finalized.
    fn handle_finalize_vote(
        &mut self,
        view: View,
        signer: NodeId,
        partial: PartialSignature,
    ) -> (StateTransition, Vec<Outgoing>) {
        // Accept for current view or the one just left (pipelining).
        if view != self.current_view && view != self.current_view.saturating_sub(1) {
            return (StateTransition::Pending, vec![]);
        }
        if self.finalize_votes.iter().any(|(id, _)| *id == signer) {
            return (StateTransition::Pending, vec![]);
        }
        self.finalize_votes.push((signer, partial));
        self.try_finalize(view)
    }

    // ── Step 4: Notarization relay (Paper Section 2.1, Step 4) ──────────
    //
    // Paper: "On seeing a notarized blockchain of height h, enter iteration
    // h+1. At the same time, p multicasts its view of the notarized
    // blockchain to everyone else."

    /// Handle a relayed notarization from another node.
    ///
    /// Accepts the notarization even if this replica didn't vote for the
    /// block. This is how honest nodes catch up after missing a proposal.
    fn handle_notarization(
        &mut self,
        view: View,
        block: Block,
        _certificate: Certificate,
    ) -> (StateTransition, Vec<Outgoing>) {
        if view != self.current_view { return (StateTransition::Pending, vec![]); }
        if self.notarized_in_view.is_some() { return (StateTransition::Pending, vec![]); }

        let bh = block_hash(&block);
        self.notarized_in_view = Some(bh);
        self.chain_state.tip_hash = bh;

        // Paper Step 4: if timer has NOT fired, send <finalize, h>.
        // Lemma 3.3: never both finalize and dummy.
        let mut outgoing = Vec::new();
        if !self.timer_fired && !self.finalize_sent {
            self.finalize_sent = true;
            let sig = self.sign_finalize(view);
            self.finalize_votes.push((self.id, sig.clone()));
            outgoing.push(Outgoing::FinalizeVote { view, partial: sig });
        }

        // Paper Step 4: "p multicasts its view of the notarized blockchain."
        outgoing.push(Outgoing::RelayNotarization {
            view, block: block.clone(), certificate: _certificate,
        });

        self.advance_view();
        (StateTransition::Notarized { view, block_hash: bh }, outgoing)
    }

    // ── Threshold checks ────────────────────────────────────────────────

    /// Check if notarization votes for a block reached >= 2n/3.
    ///
    /// Paper: "A notarization for a block b is a set of signed messages
    /// `<vote, h, b>` from >= 2n/3 unique processes."
    ///
    /// On reaching threshold:
    /// 1. Mark block as notarized
    /// 2. Update `chain_state.tip_hash`
    /// 3. If timer has NOT fired, send `<finalize, h>` (Paper Step 4, Lemma 3.3)
    /// 4. Derive VRF seed from the combined threshold signature
    /// 5. Relay the notarized blockchain
    /// 6. Advance to next view
    fn try_notarize(
        &mut self,
        view: View,
        bh: BlockHash,
        block: &Block,
    ) -> (StateTransition, Vec<Outgoing>) {
        if self.notarized_in_view.is_some() {
            return (StateTransition::Pending, vec![]);
        }

        let threshold = self.config.t as usize;
        let count = self.notarize_votes.get(&bh).map_or(0, |v| v.len());
        if count < threshold {
            return (StateTransition::Pending, vec![]);
        }

        // Threshold reached: block is notarized (NOT finalized yet).
        // Paper: notarization != finalization. Finalization requires a
        // SECOND round of >= 2n/3 <finalize, h> votes (Step 5).
        self.notarized_in_view = Some(bh);
        self.chain_state.tip_hash = bh;

        // Paper Step 4: if timer has NOT fired, send <finalize, h>.
        // Lemma 3.3: never both finalize and dummy.
        let mut outgoing = Vec::new();
        if !self.timer_fired && !self.finalize_sent {
            self.finalize_sent = true;
            let sig = self.sign_finalize(view);
            self.finalize_votes.push((self.id, sig.clone()));
            outgoing.push(Outgoing::FinalizeVote { view, partial: sig });
        }

        // Combine partial sigs into threshold signature for VRF seed.
        let partials: Vec<PartialSignature> = self.notarize_votes.get(&bh)
            .unwrap().iter().map(|(_, p)| p.clone()).collect();
        let combined = signing::combine_dynamic(&partials, threshold);
        let cert = Certificate {
            view, kind: CertKind::Notarization(bh), signature: combined.signature,
        };

        // Derive VRF seed for next leader election.
        let sig_bytes = beacon::g2_to_bytes(&combined.signature);
        let vrf_seed = beacon::derive_randomness(&sig_bytes);
        self.chain_state.vrf_seed = vrf_seed;

        // Paper Step 4: "p multicasts its view of the notarized blockchain."
        outgoing.push(Outgoing::RelayNotarization {
            view, block: block.clone(), certificate: cert,
        });

        self.advance_view();
        (StateTransition::Notarized { view, block_hash: bh }, outgoing)
    }

    /// Check if nullify (dummy) votes reached >= 2n/3.
    ///
    /// Paper: "If T_h fires, vote <vote, h, ⊥_h>." When >= 2n/3 dummy
    /// votes are collected, the dummy block is notarized and all nodes
    /// advance to iteration h+1. The tip_hash does NOT change (dummy
    /// blocks don't extend the chain content).
    fn try_nullify(&mut self, view: View) -> (StateTransition, Vec<Outgoing>) {
        if self.notarized_in_view.is_some() {
            return (StateTransition::Pending, vec![]);
        }

        let threshold = self.config.t as usize;
        if self.nullify_votes.len() < threshold {
            return (StateTransition::Pending, vec![]);
        }

        self.notarized_in_view = Some([0u8; 32]); // sentinel for dummy

        // Derive VRF seed from the nullification.
        let partials: Vec<PartialSignature> = self.nullify_votes.iter()
            .map(|(_, p)| p.clone()).collect();
        let combined = signing::combine_dynamic(&partials, threshold);
        let sig_bytes = beacon::g2_to_bytes(&combined.signature);
        let vrf_seed = beacon::derive_randomness(&sig_bytes);
        self.chain_state.vrf_seed = vrf_seed;

        // tip_hash does NOT change on nullification.
        self.chain_state.nullified_count += 1;

        self.advance_view();
        (StateTransition::Nullified { view }, vec![])
    }

    /// Check if finalize votes reached >= 2n/3.
    ///
    /// Paper Step 5: "Whenever p sees a finalized blockchain b_0,...,b_{h'},
    /// output the contents LOG <- linearize(b_0,...,b_{h'})."
    ///
    /// A block is finalized when it is notarized AND has >= 2n/3 finalize votes.
    fn try_finalize(&mut self, view: View) -> (StateTransition, Vec<Outgoing>) {
        let threshold = self.config.t as usize;
        if self.finalize_votes.len() < threshold {
            return (StateTransition::Pending, vec![]);
        }

        self.chain_state.finalized_count += 1;
        let bh = self.notarized_in_view.unwrap_or([0u8; 32]);
        (StateTransition::Finalized { view, block_hash: bh }, vec![])
    }

    // ── View management ─────────────────────────────────────────────────

    /// Advance to the next view, resetting all per-view state.
    ///
    /// Paper: "enter iteration h+1" -- each process advances independently.
    fn advance_view(&mut self) {
        self.current_view += 1;
        self.voted_in_view = false;
        self.timer_fired = false;
        self.finalize_sent = false;
        self.dummy_sent = false;
        self.voted_block = None;
        self.known_blocks.clear();
        self.notarize_votes.clear();
        self.nullify_votes.clear();
        self.finalize_votes.clear();
        self.notarized_in_view = None;
    }

    // ── Cryptographic signing ───────────────────────────────────────────

    /// Sign `<vote, h, b_h>` -- a notarization vote bound to a specific block.
    fn sign_vote(&self, view: View, bh: &BlockHash) -> PartialSignature {
        let mut msg = view.to_be_bytes().to_vec();
        msg.extend_from_slice(bh);
        let digest = beacon::digest_message(view, Some(&msg));
        let msg_hash = beacon::hash_to_g2(&digest);
        signing::partial_sign(&msg_hash, &self.share)
    }

    /// Sign `<vote, h, ⊥_h>` -- a nullification (dummy) vote.
    fn sign_dummy(&self, view: View) -> PartialSignature {
        let msg = vrf::vrf_message(view);
        let digest = beacon::digest_message(view, Some(&msg));
        let msg_hash = beacon::hash_to_g2(&digest);
        signing::partial_sign(&msg_hash, &self.share)
    }

    /// Sign `<finalize, h>` -- a finalization vote.
    fn sign_finalize(&self, view: View) -> PartialSignature {
        let mut msg = b"finalize-".to_vec();
        msg.extend_from_slice(&view.to_be_bytes());
        let digest = beacon::digest_message(view, Some(&msg));
        let msg_hash = beacon::hash_to_g2(&digest);
        signing::partial_sign(&msg_hash, &self.share)
    }
}
