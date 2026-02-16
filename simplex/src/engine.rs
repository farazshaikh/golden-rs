//! ConsensusEngine -- simulation harness that drives N Replicas.
//!
//! This module is NOT in scope for formal verification. It manages:
//! - N Replica instances (from simplex-consensus)
//! - Message routing between replicas
//! - Byzantine behavior injection (from naughty.rs)
//! - Timeout generation
//! - Display-friendly result aggregation
//!
//! The honest protocol logic lives entirely in simplex_consensus::replica.

use std::collections::HashMap;
use std::time::Instant;

use golden_dkg::types::NodeId;
use threshold_crypto::beacon;
use threshold_crypto::cache::LagrangeCache;
use threshold_crypto::signing;
use threshold_crypto::types::{GroupInfo, KeyShare};

use simplex_consensus::replica::Replica;
use simplex_consensus::types::*;
use simplex_consensus::vrf;

use crate::naughty::{self, ByzantineBehavior, ProposalAction, Scenario, VoteAction};

// ── Display-oriented types (simulation only, not consensus core) ────────

/// The outcome of a view, packaged for display.
/// This is a simulation concept, not part of the consensus protocol.
#[derive(Clone, Debug)]
pub enum ViewOutcome {
    Finalized {
        block: Block,
        cert: Certificate,
        vrf_seed: [u8; 32],
    },
    Nullified {
        cert: Certificate,
        vrf_seed: [u8; 32],
    },
}

/// Result from running a single view, including timing and per-node info.
pub struct ViewResult {
    pub outcome: ViewOutcome,
    pub latency_ms: f64,
    pub leader: NodeId,
    pub node_actions: Vec<NodeAction>,
    pub fake_proposal_attempted: bool,
    pub equivocation_attempted: bool,
    pub diverged: bool,
}

/// What a single node did during a view (for display).
pub struct NodeAction {
    pub id: NodeId,
    pub behavior: ByzantineBehavior,
    pub role: NodeRole,
    pub voted: bool,
    pub double_voted: bool,
    pub rejected_proposal: bool,
}

#[derive(Clone, Copy)]
pub enum NodeRole {
    Leader,
    Voter,
}

// ── ChainState for display (mirrors consensus ChainState) ───────────────

/// Display-level chain state (wraps the consensus ChainState).
#[derive(Clone, Debug)]
pub struct EngineChainState {
    pub tip_hash: BlockHash,
    pub vrf_seed: [u8; 32],
    pub finalized_count: u64,
    pub nullified_count: u64,
}

impl EngineChainState {
    fn genesis() -> Self {
        Self { tip_hash: [0u8; 32], vrf_seed: [0u8; 32], finalized_count: 0, nullified_count: 0 }
    }
    fn apply(&mut self, outcome: &ViewOutcome) {
        match outcome {
            ViewOutcome::Finalized { block, vrf_seed, .. } => {
                self.tip_hash = block_hash(block);
                self.vrf_seed = *vrf_seed;
                self.finalized_count += 1;
            }
            ViewOutcome::Nullified { vrf_seed, .. } => {
                self.vrf_seed = *vrf_seed;
                self.nullified_count += 1;
            }
        }
    }
}

// ── Engine ──────────────────────────────────────────────────────────────

pub struct ConsensusEngine {
    /// The N replicas (each is a Replica from simplex-consensus).
    pub replicas: Vec<Replica>,
    /// Per-node behavior assignments (simulation-only).
    pub behaviors: HashMap<NodeId, ByzantineBehavior>,
    /// Engine's global chain state (for leader election VRF seed, display).
    pub chain_state: EngineChainState,
    /// Network config passed to replicas.
    config: NetworkConfig,
    /// Threshold (2f+1).
    #[allow(dead_code)]
    threshold: usize,
    /// Active scenario.
    scenario: Scenario,
    /// Key shares (needed for Byzantine force_sign).
    shares: HashMap<NodeId, KeyShare>,
}

impl ConsensusEngine {
    pub fn new(
        key_shares: Vec<KeyShare>,
        group_info: GroupInfo,
        _cache: LagrangeCache,
        scenario: Scenario,
        f: u32,
    ) -> Self {
        let n = key_shares.len() as u32;
        let t = 2 * f + 1;
        let behaviors = naughty::assign_behaviors(scenario, n, f);

        let config = NetworkConfig {
            n,
            t,
            f,
            group_pk: group_info.public_key,
        };

        let mut replicas = Vec::new();
        let mut shares_map = HashMap::new();
        for ks in &key_shares {
            replicas.push(Replica::new(ks.id, ks.clone(), config.clone()));
            shares_map.insert(ks.id, ks.clone());
        }

        Self {
            replicas,
            behaviors,
            chain_state: EngineChainState::genesis(),
            config,
            threshold: t as usize,
            scenario,
            shares: shares_map,
        }
    }

    fn behavior(&self, id: NodeId) -> ByzantineBehavior {
        self.behaviors.get(&id).copied().unwrap_or(ByzantineBehavior::Honest)
    }

    fn is_honest(&self, id: NodeId) -> bool {
        !self.behavior(id).is_byzantine()
    }

    /// Check if all honest replicas agree on the same tip hash.
    fn check_divergence(&self) -> bool {
        let mut honest_tips = Vec::new();
        for r in &self.replicas {
            if self.is_honest(r.id()) {
                honest_tips.push(r.chain_state().tip_hash);
            }
        }
        if honest_tips.len() < 2 { return false; }
        let first = honest_tips[0];
        honest_tips.iter().any(|tip| *tip != first)
    }

    /// Byzantine force-sign: sign a vote for a block without validation.
    fn force_sign_vote(&self, node_id: NodeId, view: View, bh: &BlockHash) -> threshold_crypto::types::PartialSignature {
        let share = &self.shares[&node_id];
        let mut msg = view.to_be_bytes().to_vec();
        msg.extend_from_slice(bh);
        let digest = beacon::digest_message(view, Some(&msg));
        let msg_hash = beacon::hash_to_g2(&digest);
        signing::partial_sign(&msg_hash, share)
    }

    /// Run one view of the Simplex protocol.
    ///
    /// This orchestrates the N replicas by routing messages between them.
    /// Byzantine behavior is injected here -- replicas themselves are always honest.
    pub fn run_view(&mut self, view: View) -> ViewResult {
        let t0 = Instant::now();
        let n = self.replicas.len();

        // ── Leader election ─────────────────────────────────────────────
        // Paper: L_h := H*(h) mod n. Use the first honest replica's VRF
        // seed so the engine and replicas always agree on who the leader is.
        let replica_vrf_seed = self.replicas.iter()
            .find(|r| self.is_honest(r.id()))
            .map(|r| r.chain_state().vrf_seed)
            .unwrap_or(self.chain_state.vrf_seed);
        let leader = vrf::elect_leader(&replica_vrf_seed, n as u32);
        let leader_beh = self.behavior(leader);

        let proposal_action = naughty::should_propose(leader_beh, true, view);

        let mut fake_proposal_attempted = false;
        let mut equivocation_attempted = false;

        // Check for fake leaders
        for r in &self.replicas {
            if r.id() != leader {
                let beh = self.behavior(r.id());
                if let ProposalAction::FakePropose = naughty::should_propose(beh, false, view) {
                    fake_proposal_attempted = true;
                }
            }
        }

        // ── Phase 1: Leader proposes ────────────────────────────────────
        // Use the first honest replica's tip for the block parent_hash.
        // Byzantine leaders in the real protocol would have the same tip
        // (they receive the same notarizations), but in our sim their
        // Replicas may lag because they bypass apply_message.
        let leader_tip = self.replicas.iter()
            .find(|r| self.is_honest(r.id()))
            .map(|r| r.chain_state().tip_hash)
            .unwrap_or([0u8; 32]);

        let (block_a, block_b) = match proposal_action {
            ProposalAction::Propose => {
                let block = Block {
                    view,
                    parent_hash: leader_tip,
                    payload: format!("block-v{}-by-{}", view, leader).into_bytes(),
                    proposer: leader,
                };
                (Some(block.clone()), Some(block))
            }
            ProposalAction::Skip => (None, None),
            ProposalAction::Equivocate => {
                equivocation_attempted = true;
                let ba = Block {
                    view,
                    parent_hash: leader_tip,
                    payload: format!("equivoc-A-v{}-by-{}", view, leader).into_bytes(),
                    proposer: leader,
                };
                let bb = Block {
                    view,
                    parent_hash: leader_tip,
                    payload: format!("equivoc-B-v{}-by-{}", view, leader).into_bytes(),
                    proposer: leader,
                };
                (Some(ba), Some(bb))
            }
            ProposalAction::FakePropose => {
                fake_proposal_attempted = true;
                (None, None)
            }
        };

        // Map each node to the block it receives (equivocation = alternating partitions).
        let node_ids: Vec<NodeId> = self.replicas.iter().map(|r| r.id()).collect();
        let mut node_block: HashMap<NodeId, Option<Block>> = HashMap::new();
        for (idx, &nid) in node_ids.iter().enumerate() {
            if equivocation_attempted {
                if idx % 2 == 0 {
                    node_block.insert(nid, block_a.clone());
                } else {
                    node_block.insert(nid, block_b.clone());
                }
            } else {
                node_block.insert(nid, block_a.clone());
            }
        }

        // ── Phase 2: Feed proposals to replicas, collect votes ──────────
        // Votes collected: block_hash -> list of (signer, partial)
        let mut collected_votes: HashMap<BlockHash, Vec<(NodeId, threshold_crypto::types::PartialSignature)>> = HashMap::new();
        let mut collected_nullify: Vec<(NodeId, threshold_crypto::types::PartialSignature)> = Vec::new();
        let mut node_actions: Vec<NodeAction> = Vec::new();

        for &nid in &node_ids {
            let beh = self.behavior(nid);
            let is_leader = nid == leader;
            let role = if is_leader { NodeRole::Leader } else { NodeRole::Voter };
            let vote_action = naughty::should_vote(beh, view);

            match vote_action {
                VoteAction::Abstain => {
                    node_actions.push(NodeAction {
                        id: nid, behavior: beh, role,
                        voted: false, double_voted: false, rejected_proposal: false,
                    });
                }
                VoteAction::Vote | VoteAction::DoubleVote => {
                    if let Some(ref block) = node_block[&nid] {
                        if beh == ByzantineBehavior::Capitulator {
                            // Capitulators bypass the replica -- force-sign directly.
                            let bh = block_hash(block);
                            let sig = self.force_sign_vote(nid, view, &bh);
                            collected_votes.entry(bh).or_default().push((nid, sig));

                            // Double-vote for the other block too.
                            if matches!(vote_action, VoteAction::DoubleVote) && equivocation_attempted {
                                let other = if node_block[&nid] == block_a {
                                    &block_b
                                } else {
                                    &block_a
                                };
                                if let Some(ref other_blk) = other {
                                    let other_bh = block_hash(other_blk);
                                    let other_sig = self.force_sign_vote(nid, view, &other_bh);
                                    collected_votes.entry(other_bh).or_default().push((nid, other_sig));
                                }
                            }

                            node_actions.push(NodeAction {
                                id: nid, behavior: beh, role,
                                voted: true,
                                double_voted: matches!(vote_action, VoteAction::DoubleVote),
                                rejected_proposal: false,
                            });
                        } else {
                            // Honest node: feed proposal through the Replica.
                            let replica = self.replicas.iter_mut().find(|r| r.id() == nid).unwrap();
                            let (transition, outgoing) = replica.apply_message(Message::Proposal {
                                block: block.clone(),
                            });

                            let mut voted = false;
                            let mut rejected = false;

                            for out in &outgoing {
                                match out {
                                    Outgoing::Vote { block_hash: bh, partial, .. } => {
                                        collected_votes.entry(*bh).or_default().push((nid, partial.clone()));
                                        voted = true;
                                    }
                                    _ => {}
                                }
                            }

                            if matches!(transition, StateTransition::Rejected { .. }) {
                                rejected = true;
                                // Rejected -> timeout (vote dummy).
                                let (_, timeout_out) = replica.apply_message(Message::Timeout { view });
                                for out in &timeout_out {
                                    if let Outgoing::NullifyVote { partial, .. } = out {
                                        collected_nullify.push((nid, partial.clone()));
                                    }
                                }
                            }

                            node_actions.push(NodeAction {
                                id: nid, behavior: beh, role,
                                voted: voted || rejected,
                                double_voted: false,
                                rejected_proposal: rejected,
                            });
                        }
                    } else {
                        // No proposal -> timeout.
                        let replica = self.replicas.iter_mut().find(|r| r.id() == nid).unwrap();
                        let (_, timeout_out) = replica.apply_message(Message::Timeout { view });
                        for out in &timeout_out {
                            if let Outgoing::NullifyVote { partial, .. } = out {
                                collected_nullify.push((nid, partial.clone()));
                            }
                        }
                        node_actions.push(NodeAction {
                            id: nid, behavior: beh, role,
                            voted: true,
                            double_voted: matches!(vote_action, VoteAction::DoubleVote),
                            rejected_proposal: false,
                        });
                    }
                }
            }
        }

        // ── Phase 2b: Ensure all replicas know about all blocks ─────────
        // In equivocation, each partition only saw one block. Route the
        // "other" block to each replica so known_blocks has both. The
        // replica will reject it (AlreadyVoted) but store the block data
        // for notarization tracking (Paper Step 4).
        if equivocation_attempted {
            if let (Some(ref ba), Some(ref bb)) = (&block_a, &block_b) {
                for &nid in &node_ids {
                    let beh = self.behavior(nid);
                    if beh == ByzantineBehavior::Capitulator { continue; }
                    let replica = self.replicas.iter_mut().find(|r| r.id() == nid).unwrap();
                    // Send both blocks -- replica stores them in known_blocks
                    let _ = replica.apply_message(Message::Proposal { block: ba.clone() });
                    let _ = replica.apply_message(Message::Proposal { block: bb.clone() });
                }
            }
        }

        // ── Phase 3: Route votes to all replicas ────────────────────────
        // Feed collected votes into each replica so they can reach notarization.
        // IMPORTANT: Route each replica's OWN block's votes FIRST so that in
        // the equivocation case, each partition notarizes its own block before
        // seeing the other partition's block reach threshold.
        for &nid in &node_ids {
            let replica = self.replicas.iter_mut().find(|r| r.id() == nid).unwrap();
            // First: route votes for the block this node was shown
            let my_bh = node_block.get(&nid).and_then(|b| b.as_ref()).map(block_hash);
            if let Some(mbh) = my_bh {
                if let Some(votes) = collected_votes.get(&mbh) {
                    for (signer, partial) in votes {
                        if *signer == nid { continue; }
                        let _ = replica.apply_message(Message::Vote {
                            view, block_hash: mbh, signer: *signer, partial: partial.clone(),
                        });
                    }
                }
            }
            // Then: route votes for all other blocks
            for (bh, votes) in &collected_votes {
                if my_bh == Some(*bh) { continue; } // already routed above
                for (signer, partial) in votes {
                    if *signer == nid { continue; }
                    let _ = replica.apply_message(Message::Vote {
                        view, block_hash: *bh, signer: *signer, partial: partial.clone(),
                    });
                }
            }
        }

        // Route nullify votes.
        for &nid in &node_ids {
            let replica = self.replicas.iter_mut().find(|r| r.id() == nid).unwrap();
            for (signer, partial) in &collected_nullify {
                if *signer == nid { continue; }
                let _ = replica.apply_message(Message::NullifyVote {
                    view,
                    signer: *signer,
                    partial: partial.clone(),
                });
            }
        }

        // ── Phase 3b: Timeout any replicas still stuck in current view ───
        // In the real protocol, timers fire after 3*Delta. In our sim,
        // if a replica hasn't advanced after vote routing, it means
        // neither block reached threshold -> force timeout so the view
        // can be nullified and the replica can advance.
        let mut extra_nullify: Vec<(NodeId, threshold_crypto::types::PartialSignature)> = Vec::new();
        for &nid in &node_ids {
            let replica = self.replicas.iter_mut().find(|r| r.id() == nid).unwrap();
            if replica.current_view() == view {
                // Still in this view -> trigger timeout (Paper Step 2: timer fires)
                let (_, timeout_out) = replica.apply_message(Message::Timeout { view });
                for out in &timeout_out {
                    if let Outgoing::NullifyVote { partial, .. } = out {
                        extra_nullify.push((nid, partial.clone()));
                    }
                }
            }
        }

        // Route extra nullify votes to all replicas still in this view
        if !extra_nullify.is_empty() {
            // Also add capitulator nullify votes so honest replicas can
            // reach the nullification threshold even in capitulation mode.
            for &nid in &node_ids {
                let beh = self.behavior(nid);
                if beh == ByzantineBehavior::Capitulator {
                    let share = &self.shares[&nid];
                    let msg = vrf::vrf_message(view);
                    let digest = beacon::digest_message(view, Some(&msg));
                    let msg_hash = beacon::hash_to_g2(&digest);
                    let sig = signing::partial_sign(&msg_hash, share);
                    extra_nullify.push((nid, sig));
                }
            }

            for &nid in &node_ids {
                let replica = self.replicas.iter_mut().find(|r| r.id() == nid).unwrap();
                if replica.current_view() == view {
                    for (signer, partial) in &extra_nullify {
                        if *signer == nid { continue; }
                        let _ = replica.apply_message(Message::NullifyVote {
                            view,
                            signer: *signer,
                            partial: partial.clone(),
                        });
                    }
                }
            }
        }

        // ── Phase 4: Collect finalize votes and route them ──────────────
        // Replicas that notarized will have emitted FinalizeVote in their
        // outgoing. But since we already advanced them via vote routing,
        // we need to check if they produced finalize votes. For simplicity,
        // since our replicas auto-emit finalize when they notarize, we
        // collect finalize votes by checking which replicas advanced.
        // Actually, the finalize votes were emitted during try_notarize()
        // inside the vote routing above. Let's re-collect by querying state.

        // For the simulation display, determine the canonical outcome.
        // Check which blocks got notarized (replicas that advanced to view+1).
        let mut notarized_blocks: Vec<BlockHash> = Vec::new();
        let mut _any_nullified = false;

        for r in &self.replicas {
            if self.is_honest(r.id()) {
                if r.current_view() > view {
                    // This replica advanced -- it notarized something.
                    let tip = r.chain_state().tip_hash;
                    if tip == [0u8; 32] || tip == self.chain_state.tip_hash {
                        // tip unchanged -> nullified
                        _any_nullified = true;
                    } else if !notarized_blocks.contains(&tip) {
                        notarized_blocks.push(tip);
                    }
                }
            }
        }

        // Build display outcome from the first honest replica's state.
        let first_honest = self.replicas.iter()
            .find(|r| self.is_honest(r.id()))
            .unwrap();
        let new_vrf_seed = first_honest.chain_state().vrf_seed;

        let display_outcome = if !notarized_blocks.is_empty() {
            let bh = notarized_blocks[0];
            let block = if block_a.as_ref().map(|b| block_hash(b)) == Some(bh) {
                block_a.clone().unwrap()
            } else if block_b.as_ref().map(|b| block_hash(b)) == Some(bh) {
                block_b.clone().unwrap()
            } else {
                // Fallback: construct a placeholder
                Block { view, parent_hash: [0u8; 32], payload: vec![], proposer: leader }
            };
            ViewOutcome::Finalized {
                block,
                cert: Certificate { view, kind: CertKind::Finalization(bh), signature: ark_bls12_381::G2Affine::default() },
                vrf_seed: new_vrf_seed,
            }
        } else {
            ViewOutcome::Nullified {
                cert: Certificate { view, kind: CertKind::Nullification, signature: ark_bls12_381::G2Affine::default() },
                vrf_seed: new_vrf_seed,
            }
        };

        // Update engine's global state.
        self.chain_state.apply(&display_outcome);

        // Check divergence.
        let diverged = self.check_divergence();

        let latency_ms = t0.elapsed().as_secs_f64() * 1000.0;

        ViewResult {
            outcome: display_outcome,
            latency_ms,
            leader,
            node_actions,
            fake_proposal_attempted,
            equivocation_attempted,
            diverged,
        }
    }
}
