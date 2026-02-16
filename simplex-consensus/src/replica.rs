//! Replica -- the pure state machine for one Simplex consensus participant.
//!
//! This is the formal verification target. The single entry point is
//! [`Replica::apply_message`], which processes one [`Message`] and returns
//! a [`StateTransition`] plus any [`Outgoing`] messages to broadcast.
//!
//! The Replica has NO I/O, NO timers, NO networking. The caller is
//! responsible for delivering messages and triggering timeouts.
//!
//! ## Protocol steps (Paper Section 2.1)
//!
//! 1. Leader L_h proposes `<propose, h, b_0..b_h, S>`.
//! 2. Timer T_h fires -> vote `<vote, h, ⊥_h>` (dummy).
//! 3. On first valid proposal from L_h -> vote `<vote, h, b_h>`.
//! 4. On seeing notarized chain of height h -> enter h+1.
//!    If timer did NOT fire -> send `<finalize, h>`.
//! 5. Block finalized when notarized + >= 2n/3 finalize votes.
//!
//! ## Safety invariants
//!
//! - An honest replica votes for AT MOST ONE non-dummy block per view
//!   (Paper Lemma 3.2).
//! - An honest replica sends EITHER `<finalize, h>` OR `<vote, h, ⊥_h>`,
//!   NEVER both (Paper Lemma 3.3).

use std::collections::HashMap;

use golden_dkg::types::NodeId;
use threshold_crypto::beacon;
use threshold_crypto::signing;
use threshold_crypto::types::{KeyShare, PartialSignature};

use crate::types::*;
use crate::vrf;

/// A Simplex consensus replica (one participant's state machine).
pub struct Replica {
    /// This replica's node identifier (1-indexed).
    id: NodeId,
    /// This replica's threshold key share.
    share: KeyShare,
    /// Network configuration (n, t, f, group_pk).
    config: NetworkConfig,

    // ── Per-view state ──────────────────────────────────────────────────

    /// Current view (iteration) this replica is in.
    current_view: View,
    /// Whether this replica has voted for a non-dummy block in the current view.
    /// Paper: "votes for at most one non-dummy block per iteration" (Lemma 3.2).
    voted_in_view: bool,
    /// Whether this replica's timer has fired in the current view.
    /// Paper: "If T_h fires, vote for the dummy block" (Step 2).
    timer_fired: bool,
    /// Whether this replica has already sent a finalize vote in this view.
    finalize_sent: bool,
    /// Whether this replica has already sent a dummy vote in this view.
    dummy_sent: bool,
    /// The block this replica voted for in this view (if any).
    voted_block: Option<Block>,
    /// All blocks seen in this view (by hash), for notarization tracking.
    /// Paper Step 4: "On seeing a notarized blockchain of height h" --
    /// a replica accepts notarization even for blocks it didn't vote for.
    known_blocks: HashMap<BlockHash, Block>,

    // ── Vote accumulators (per view) ────────────────────────────────────

    /// Notarization votes received: block_hash -> list of partial sigs.
    notarize_votes: HashMap<BlockHash, Vec<(NodeId, PartialSignature)>>,
    /// Nullification (dummy) votes received.
    nullify_votes: Vec<(NodeId, PartialSignature)>,
    /// Finalize votes received.
    finalize_votes: Vec<(NodeId, PartialSignature)>,

    /// Whether a block has been notarized in this view (to avoid re-processing).
    notarized_in_view: Option<BlockHash>,

    // ── Chain state ─────────────────────────────────────────────────────

    /// This replica's local chain state.
    chain_state: ChainState,
}

impl Replica {
    /// Create a new Replica in the genesis state.
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
        }
    }

    /// Current view the replica is in.
    pub fn current_view(&self) -> View {
        self.current_view
    }

    /// Current chain state.
    pub fn chain_state(&self) -> &ChainState {
        &self.chain_state
    }

    /// This replica's node ID.
    pub fn id(&self) -> NodeId {
        self.id
    }

    /// Who is the designated leader for a given view.
    /// Paper: "L_h := H*(h) mod n"
    pub fn leader_for(&self, _view: View) -> NodeId {
        vrf::elect_leader(&self.chain_state.vrf_seed, self.config.n)
    }

    // ── Step 1 + 3: Handle proposal (Paper Section 2.1, Steps 1 & 3) ───

    /// Paper Step 3: "On seeing the first proposal of the form
    /// <propose, h, b_0, ..., b_h, S>_{L_h}, check that b_h != ⊥_h,
    /// that b_0,...,b_h is a valid blockchain, and that (b_0,...,b_{h-1},S)
    /// is a notarized blockchain. If all checks pass, multicast <vote, h, b_h>."
    fn handle_proposal(&mut self, block: Block) -> (StateTransition, Vec<Outgoing>) {
        let view = block.view;

        // Wrong view: ignore.
        if view != self.current_view {
            return (StateTransition::Rejected { view, reason: RejectReason::WrongView }, vec![]);
        }

        // Always store the block so we can accept a notarization for it later.
        // Paper Step 4: "On seeing a notarized blockchain of height h" --
        // a replica needs the block data to process the notarization.
        self.known_blocks.insert(block_hash(&block), block.clone());

        // Paper: "On seeing the first proposal from L_h" -- check proposer.
        let leader = self.leader_for(view);
        if block.proposer != leader {
            return (StateTransition::Rejected { view, reason: RejectReason::WrongLeader }, vec![]);
        }

        // Already voted in this view (one vote per iteration).
        if self.voted_in_view {
            return (StateTransition::Rejected { view, reason: RejectReason::AlreadyVoted }, vec![]);
        }

        if block.parent_hash != self.chain_state.tip_hash {
            return (StateTransition::Rejected { view, reason: RejectReason::BadParentHash }, vec![]);
        }

        // All checks pass: vote for this block.
        self.voted_in_view = true;
        self.voted_block = Some(block.clone());
        self.known_blocks.insert(block_hash(&block), block.clone());

        let bh = block_hash(&block);
        let sig = self.sign_vote(view, &bh);

        // Add our own vote to the accumulator.
        self.notarize_votes.entry(bh).or_default().push((self.id, sig.clone()));

        let mut outgoing = vec![Outgoing::Vote {
            view,
            block_hash: bh,
            partial: sig,
        }];

        // Check if our vote pushed this block to notarization threshold.
        let (transition, extra) = self.try_notarize(view, bh, &block);
        outgoing.extend(extra);

        (transition, outgoing)
    }

    // ── Step 2: Handle timeout (Paper Section 2.1, Step 2) ──────────────

    /// Paper Step 2: "Each process p starts a new timer T_h, set to fire
    /// locally after 3Δ time. If T_h fires, vote for the dummy block by
    /// multicasting <vote, h, ⊥_h>."
    fn handle_timeout(&mut self, view: View) -> (StateTransition, Vec<Outgoing>) {
        if view != self.current_view {
            return (StateTransition::Pending, vec![]);
        }

        // Paper Lemma 3.3: never both finalize and vote-dummy.
        // If we already sent finalize, we must not send dummy.
        if self.finalize_sent || self.dummy_sent {
            return (StateTransition::Pending, vec![]);
        }

        self.timer_fired = true;
        self.dummy_sent = true;

        let sig = self.sign_dummy(view);
        self.nullify_votes.push((self.id, sig.clone()));

        let mut outgoing = vec![Outgoing::NullifyVote {
            view,
            partial: sig,
        }];

        // Check if dummy reached threshold.
        let (transition, extra) = self.try_nullify(view);
        outgoing.extend(extra);

        (transition, outgoing)
    }

    // ── Step 3: Handle vote from another node ───────────────────────────

    /// Accumulate a notarization vote from another node.
    fn handle_vote(
        &mut self,
        view: View,
        bh: BlockHash,
        signer: NodeId,
        partial: PartialSignature,
    ) -> (StateTransition, Vec<Outgoing>) {
        if view != self.current_view {
            return (StateTransition::Pending, vec![]);
        }
        if self.notarized_in_view.is_some() {
            return (StateTransition::Pending, vec![]);
        }

        // Deduplicate: don't count the same signer twice.
        let votes = self.notarize_votes.entry(bh).or_default();
        if votes.iter().any(|(id, _)| *id == signer) {
            return (StateTransition::Pending, vec![]);
        }
        votes.push((signer, partial));

        // Check threshold. Paper Step 4: "On seeing a notarized blockchain
        // of height h, enter iteration h+1." A replica accepts notarization
        // for ANY block at its current height, even one it didn't vote for.
        if let Some(block) = self.known_blocks.get(&bh).cloned() {
            return self.try_notarize(view, bh, &block);
        }

        // Don't have the block data yet -- can't build notarization.
        // Votes are accumulated; notarization will be checked if/when
        // the block arrives via a Proposal or Notarization message.
        (StateTransition::Pending, vec![])
    }

    // ── Step 2: Handle nullify vote from another node ───────────────────

    fn handle_nullify_vote(
        &mut self,
        view: View,
        signer: NodeId,
        partial: PartialSignature,
    ) -> (StateTransition, Vec<Outgoing>) {
        if view != self.current_view {
            return (StateTransition::Pending, vec![]);
        }

        // Deduplicate.
        if self.nullify_votes.iter().any(|(id, _)| *id == signer) {
            return (StateTransition::Pending, vec![]);
        }
        self.nullify_votes.push((signer, partial));

        self.try_nullify(view)
    }

    // ── Step 4: Handle finalize vote from another node ──────────────────

    /// Paper Step 4: accumulate finalize votes. When threshold reached,
    /// the block at this height is finalized.
    fn handle_finalize_vote(
        &mut self,
        view: View,
        signer: NodeId,
        partial: PartialSignature,
    ) -> (StateTransition, Vec<Outgoing>) {
        // Finalize votes may arrive for the view we just left (pipelining).
        // Accept them if they're for our current view or the one we just notarized.
        if view != self.current_view && view != self.current_view.saturating_sub(1) {
            return (StateTransition::Pending, vec![]);
        }

        // Deduplicate.
        if self.finalize_votes.iter().any(|(id, _)| *id == signer) {
            return (StateTransition::Pending, vec![]);
        }
        self.finalize_votes.push((signer, partial));

        self.try_finalize(view)
    }

    // ── Step 4: Handle notarization relay from another node ─────────────

    /// Paper Step 4: "On seeing a notarized blockchain of height h,
    /// enter iteration h+1."
    ///
    /// A replica accepts a notarization even if it didn't vote for the block.
    /// This is how honest nodes recover from not having seen the proposal.
    fn handle_notarization(
        &mut self,
        view: View,
        block: Block,
        _certificate: Certificate,
    ) -> (StateTransition, Vec<Outgoing>) {
        if view != self.current_view {
            return (StateTransition::Pending, vec![]);
        }
        if self.notarized_in_view.is_some() {
            return (StateTransition::Pending, vec![]);
        }

        let bh = block_hash(&block);
        self.notarized_in_view = Some(bh);

        // Update chain state with the notarized block.
        self.chain_state.tip_hash = bh;

        // Paper Step 4: if timer has NOT fired, send <finalize, h>.
        let mut outgoing = Vec::new();
        if !self.timer_fired && !self.finalize_sent {
            self.finalize_sent = true;
            let sig = self.sign_finalize(view);
            self.finalize_votes.push((self.id, sig.clone()));
            outgoing.push(Outgoing::FinalizeVote { view, partial: sig });
        }

        // Relay the notarized blockchain.
        // Paper Step 4: "p multicasts its view of the notarized blockchain"
        outgoing.push(Outgoing::RelayNotarization {
            view,
            block: block.clone(),
            certificate: _certificate,
        });

        // Advance to next view.
        self.advance_view();

        (StateTransition::Notarized { view, block_hash: bh }, outgoing)
    }

    // ── Internal: threshold checks ──────────────────────────────────────

    /// Check if notarization votes for a block reached threshold.
    ///
    /// Paper: "A notarization for a block b is a set of signed messages
    /// <vote, h, b> from >= 2n/3 unique processes."
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

        // Threshold reached: block is notarized.
        self.notarized_in_view = Some(bh);

        // Update chain state.
        self.chain_state.tip_hash = bh;

        // Paper Step 4: if timer has NOT fired, send <finalize, h>.
        // Paper Lemma 3.3: never both finalize and dummy.
        let mut outgoing = Vec::new();
        if !self.timer_fired && !self.finalize_sent {
            self.finalize_sent = true;
            let sig = self.sign_finalize(view);
            self.finalize_votes.push((self.id, sig.clone()));
            outgoing.push(Outgoing::FinalizeVote { view, partial: sig });
        }

        // Build and relay the notarization certificate.
        let partials: Vec<PartialSignature> = self.notarize_votes.get(&bh)
            .unwrap()
            .iter()
            .map(|(_, p)| p.clone())
            .collect();
        let combined = signing::combine_dynamic(&partials, threshold);
        let cert = Certificate {
            view,
            kind: CertKind::Notarization(bh),
            signature: combined.signature,
        };

        // Derive VRF seed from the notarization signature.
        let sig_bytes = beacon::g2_to_bytes(&combined.signature);
        let vrf_seed = beacon::derive_randomness(&sig_bytes);
        self.chain_state.vrf_seed = vrf_seed;

        outgoing.push(Outgoing::RelayNotarization {
            view,
            block: block.clone(),
            certificate: cert,
        });

        // Advance to next view.
        self.advance_view();

        (StateTransition::Notarized { view, block_hash: bh }, outgoing)
    }

    /// Check if nullify (dummy) votes reached threshold.
    fn try_nullify(&mut self, view: View) -> (StateTransition, Vec<Outgoing>) {
        if self.notarized_in_view.is_some() {
            return (StateTransition::Pending, vec![]);
        }

        let threshold = self.config.t as usize;
        if self.nullify_votes.len() < threshold {
            return (StateTransition::Pending, vec![]);
        }

        // Dummy block notarized: nullify this view.
        // Paper: on seeing notarized dummy, enter next iteration.
        self.notarized_in_view = Some([0u8; 32]); // sentinel for dummy

        // Derive VRF seed from the nullification.
        let partials: Vec<PartialSignature> = self.nullify_votes.iter()
            .map(|(_, p)| p.clone())
            .collect();
        let combined = signing::combine_dynamic(&partials, threshold);
        let sig_bytes = beacon::g2_to_bytes(&combined.signature);
        let vrf_seed = beacon::derive_randomness(&sig_bytes);
        self.chain_state.vrf_seed = vrf_seed;

        // Note: tip_hash does NOT change on nullification (dummy doesn't extend chain).

        self.advance_view();

        (StateTransition::Nullified { view }, vec![])
    }

    /// Check if finalize votes reached threshold.
    ///
    /// Paper Step 5: "Whenever p sees a finalized blockchain b_0,...,b_{h'},
    /// output the contents LOG <- linearize(b_0,...,b_{h'})."
    fn try_finalize(&mut self, view: View) -> (StateTransition, Vec<Outgoing>) {
        let threshold = self.config.t as usize;
        if self.finalize_votes.len() < threshold {
            return (StateTransition::Pending, vec![]);
        }

        // A block at this height is finalized.
        self.chain_state.finalized_count += 1;

        // Find the block hash that was notarized at this view.
        let bh = self.notarized_in_view.unwrap_or([0u8; 32]);

        (StateTransition::Finalized { view, block_hash: bh }, vec![])
    }

    // ── Internal: view management ───────────────────────────────────────

    /// Advance to the next view, resetting per-view state.
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

    // ── Internal: cryptographic signing ─────────────────────────────────

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
