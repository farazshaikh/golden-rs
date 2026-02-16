//! ConsensusEngine -- pure message router for Simplex simulation.
//!
//! This module is NOT in scope for formal verification. It is a dumb
//! message delivery loop: for each view, it triggers proposal, delivers
//! messages between replicas, and reads replica states for display.
//!
//! **Zero global state.** All decisions happen inside the Replica
//! (simplex-consensus). Byzantine behavior is injected by the naughty
//! filter which manipulates messages in transit.

use std::collections::{HashMap, VecDeque};
use std::time::Instant;

use golden_dkg::types::NodeId;
use threshold_crypto::cache::LagrangeCache;
use threshold_crypto::types::{GroupInfo, KeyShare};

use crate::replica::Replica;
use crate::types::*;

use crate::sim::naughty::{self, ByzantineBehavior, Delivery, FilterContext, Scenario};

// ── Display-oriented types (simulation only) ────────────────────────────

/// The outcome of a view, packaged for display.
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

/// Result from running a single view.
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

// ── Engine ──────────────────────────────────────────────────────────────

pub struct ConsensusEngine {
    /// The N replicas (each is a pure state machine from simplex-consensus).
    pub replicas: Vec<Replica>,
    /// Per-node behavior assignments (simulation-only).
    pub behaviors: HashMap<NodeId, ByzantineBehavior>,
    /// Key shares for Byzantine force-signing.
    shares: HashMap<NodeId, KeyShare>,
    /// All node IDs (sorted).
    node_ids: Vec<NodeId>,
    /// Scenario (for display).
    #[allow(dead_code)]
    scenario: Scenario,
    /// f parameter.
    #[allow(dead_code)]
    f: u32,
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
        let mut node_ids = Vec::new();
        for ks in &key_shares {
            replicas.push(Replica::new(ks.id, ks.clone(), config.clone()));
            shares_map.insert(ks.id, ks.clone());
            node_ids.push(ks.id);
        }
        node_ids.sort();

        Self {
            replicas,
            behaviors,
            shares: shares_map,
            node_ids,
            scenario,
            f,
        }
    }

    fn behavior(&self, id: NodeId) -> ByzantineBehavior {
        self.behaviors.get(&id).copied().unwrap_or(ByzantineBehavior::Honest)
    }

    fn is_honest(&self, id: NodeId) -> bool {
        !self.behavior(id).is_byzantine()
    }

    fn replica_mut(&mut self, id: NodeId) -> &mut Replica {
        self.replicas.iter_mut().find(|r| r.id() == id).unwrap()
    }

    /// Check if all honest replicas agree on the same tip hash.
    pub fn check_divergence(&self) -> bool {
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

    /// Get the chain state from the first honest replica (for display).
    pub fn chain_state_display(&self) -> &ChainState {
        self.replicas.iter()
            .find(|r| self.is_honest(r.id()))
            .map(|r| r.chain_state())
            .unwrap_or_else(|| self.replicas[0].chain_state())
    }

    /// Run one view of the Simplex protocol as a pure message delivery loop.
    ///
    /// 1. Tell the leader replica to propose
    /// 2. Route all messages between replicas (with Byzantine filter)
    /// 3. Timeout any stuck replicas
    /// 4. Read replica states for display
    pub fn run_view(&mut self, view: View) -> ViewResult {
        let t0 = Instant::now();

        // ── Leader election (read from any honest replica) ──────────────
        let leader = self.replicas.iter()
            .find(|r| self.is_honest(r.id()))
            .map(|r| r.leader_for(view))
            .unwrap_or(1);
        let _leader_beh = self.behavior(leader);

        // Track what happened for display.
        let mut equivocation_attempted = false;
        let mut fake_proposal_attempted = false;
        // Track per-node actions: who voted, who rejected, etc.
        let mut action_map: HashMap<NodeId, NodeAction> = HashMap::new();
        for &nid in &self.node_ids {
            let beh = self.behavior(nid);
            let role = if nid == leader { NodeRole::Leader } else { NodeRole::Voter };
            action_map.insert(nid, NodeAction {
                id: nid, behavior: beh, role,
                voted: false, double_voted: false, rejected_proposal: false,
            });
        }

        // ── Message queue ───────────────────────────────────────────────
        let mut pending: VecDeque<Delivery> = VecDeque::new();

        // Step 1: Tell the leader to propose.
        pending.push_back(Delivery {
            recipient: leader,
            message: Message::ProposeRequest {
                view,
                payload: format!("block-v{}-by-{}", view, leader).into_bytes(),
            },
        });

        // Track which equivocation blocks exist (for double-vote forging).
        let mut known_block_hashes: Vec<BlockHash> = Vec::new();

        // Step 2: Message delivery loop.
        // Process messages until the queue is empty.
        let mut iterations = 0;
        let max_iterations = 10_000; // safety bound

        while let Some(delivery) = pending.pop_front() {
            iterations += 1;
            if iterations > max_iterations { break; }

            let recipient_id = delivery.recipient;
            let recipient_beh = self.behavior(recipient_id);

            // Deliver the message to the replica.
            let replica = self.replica_mut(recipient_id);
            let (transition, outgoing) = replica.apply_message(delivery.message);

            // Update display actions based on what happened.
            match &transition {
                StateTransition::Rejected { reason, .. } => {
                    if let Some(action) = action_map.get_mut(&recipient_id) {
                        // Only mark as rejected for BadParentHash (not AlreadyVoted/WrongView).
                        if matches!(reason, RejectReason::BadParentHash) {
                            action.rejected_proposal = true;
                        }
                    }
                }
                _ => {}
            }

            // Route outgoing messages through the Byzantine filter.
            let ctx = FilterContext {
                sender: recipient_id,
                sender_behavior: recipient_beh,
                view,
                all_node_ids: &self.node_ids,
                shares: &self.shares,
            };

            for out in &outgoing {
                // Track votes for display.
                match out {
                    Outgoing::Vote { .. } => {
                        if let Some(action) = action_map.get_mut(&recipient_id) {
                            action.voted = true;
                        }
                    }
                    Outgoing::NullifyVote { .. } => {
                        if let Some(action) = action_map.get_mut(&recipient_id) {
                            action.voted = true;
                        }
                    }
                    Outgoing::Proposal { block } => {
                        let bh = block_hash(block);
                        if !known_block_hashes.contains(&bh) {
                            known_block_hashes.push(bh);
                        }
                    }
                    _ => {}
                }

                // Pass through the naughty filter.
                let deliveries = naughty::filter_outgoing(out, &ctx);

                // Check for equivocation (filter produced proposals with different hashes).
                for d in &deliveries {
                    if let Message::Proposal { block } = &d.message {
                        let bh = block_hash(block);
                        if !known_block_hashes.contains(&bh) {
                            known_block_hashes.push(bh);
                            equivocation_attempted = true;
                        }
                    }
                }

                pending.extend(deliveries);
            }

            // For capitulators who produced a vote: also forge a vote for
            // the OTHER equivocation block (double-vote across partitions).
            if recipient_beh == ByzantineBehavior::Capitulator && known_block_hashes.len() >= 2 {
                for out in &outgoing {
                    if let Outgoing::Vote { view: v, block_hash: bh, .. } = out {
                        // Find block hashes this node hasn't voted for yet.
                        for &other_bh in &known_block_hashes {
                            if other_bh == *bh { continue; }
                            // Forge a vote for the other block.
                            let share = &self.shares[&recipient_id];
                            let forged = naughty::forge_vote(share, *v, &other_bh);
                            if let Some(action) = action_map.get_mut(&recipient_id) {
                                action.double_voted = true;
                            }
                            // Deliver to all peers.
                            for &peer in &self.node_ids {
                                if peer == recipient_id { continue; }
                                pending.push_back(Delivery {
                                    recipient: peer,
                                    message: Message::Vote {
                                        view: *v,
                                        block_hash: other_bh,
                                        signer: recipient_id,
                                        partial: forged.clone(),
                                    },
                                });
                            }
                        }
                    }
                }
            }

            // Check for fake leader proposals.
            if recipient_beh == ByzantineBehavior::FakeLeader && recipient_id != leader {
                for out in &outgoing {
                    if matches!(out, Outgoing::Proposal { .. }) {
                        fake_proposal_attempted = true;
                    }
                }
            }
        }

        // Step 3: Timeout any replicas still stuck in this view.
        // In the real protocol, timer T_h fires after 3*Delta.
        let stuck_ids: Vec<NodeId> = self.replicas.iter()
            .filter(|r| r.current_view() == view)
            .map(|r| r.id())
            .collect();

        if !stuck_ids.is_empty() {
            // First, send Timeout to each stuck replica and collect their nullify votes.
            let mut timeout_outgoing: Vec<(NodeId, Vec<Outgoing>)> = Vec::new();
            for &nid in &stuck_ids {
                let replica = self.replica_mut(nid);
                let (_, outs) = replica.apply_message(Message::Timeout { view });
                if !outs.is_empty() {
                    timeout_outgoing.push((nid, outs));
                }
            }

            // Also generate nullify votes for capitulators who haven't sent one yet.
            for &nid in &self.node_ids {
                if self.behavior(nid) == ByzantineBehavior::Capitulator {
                    let share = &self.shares[&nid];
                    let msg = crate::vrf::vrf_message(view);
                    let digest = threshold_crypto::beacon::digest_message(view, Some(&msg));
                    let msg_hash = threshold_crypto::beacon::hash_to_g2(&digest);
                    let sig = threshold_crypto::signing::partial_sign(&msg_hash, share);
                    timeout_outgoing.push((nid, vec![Outgoing::NullifyVote { view, partial: sig }]));
                }
            }

            // Route the nullify votes to all stuck replicas.
            for (sender, outs) in &timeout_outgoing {
                for out in outs {
                    if let Outgoing::NullifyVote { view: v, partial } = out {
                        for &nid in &stuck_ids {
                            if nid == *sender { continue; }
                            let replica = self.replica_mut(nid);
                            let _ = replica.apply_message(Message::NullifyVote {
                                view: *v, signer: *sender, partial: partial.clone(),
                            });
                        }
                    }
                }
            }
        }

        // Step 4: Read replica states for display.
        let diverged = self.check_divergence();
        let cs = self.chain_state_display();
        let vrf_seed = cs.vrf_seed;
        let tip = cs.tip_hash;

        // Determine display outcome from honest replica states.
        // If any honest replica finalized a block in this view, it's Finalized.
        // Otherwise, it's Nullified.
        let mut finalized_block: Option<Block> = None;
        for r in &self.replicas {
            if self.is_honest(r.id()) && r.current_view() > view {
                let new_tip = r.chain_state().tip_hash;
                if new_tip != [0u8; 32] {
                    // This replica has a non-genesis tip -- look for the block.
                    // We don't have the block stored in the engine anymore,
                    // so reconstruct from the known_block_hashes.
                    for &bh in &known_block_hashes {
                        if bh == new_tip {
                            finalized_block = Some(Block {
                                view,
                                parent_hash: [0u8; 32], // placeholder
                                payload: format!("view-{}", view).into_bytes(),
                                proposer: leader,
                            });
                            break;
                        }
                    }
                    break;
                }
            }
        }

        let outcome = if let Some(_block) = &finalized_block {
            ViewOutcome::Finalized {
                block: Block {
                    view,
                    parent_hash: tip,
                    payload: format!("view-{}", view).into_bytes(),
                    proposer: leader,
                },
                cert: Certificate { view, kind: CertKind::Finalization(tip), signature: ark_bls12_381::G2Affine::default() },
                vrf_seed,
            }
        } else {
            ViewOutcome::Nullified {
                cert: Certificate { view, kind: CertKind::Nullification, signature: ark_bls12_381::G2Affine::default() },
                vrf_seed,
            }
        };

        // Build node_actions in order.
        let node_actions: Vec<NodeAction> = self.node_ids.iter()
            .map(|&nid| action_map.remove(&nid).unwrap())
            .collect();

        let latency_ms = t0.elapsed().as_secs_f64() * 1000.0;

        ViewResult {
            outcome,
            latency_ms,
            leader,
            node_actions,
            fake_proposal_attempted,
            equivocation_attempted,
            diverged,
        }
    }
}
