//! Byzantine behavior presets for Simplex consensus simulation.
//!
//! All adversarial logic is isolated here. The engine's message router
//! passes outgoing messages through [`filter_outgoing`] before delivery.
//! Byzantine behavior is modeled as message manipulation in transit:
//! - Drop (silent leader, non-voter)
//! - Duplicate with modification (equivocation, double-vote)
//! - Inject (fake leader)

use golden_dkg::types::NodeId;
use std::collections::HashMap;
use std::fmt;

use crate::types::*;
use golden_dkg::threshold::types::KeyShare;

/// What kind of adversary a node is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ByzantineBehavior {
    /// Follows the protocol faithfully.
    Honest,
    /// When elected leader, proposes nothing (crash/silent).
    /// As voter, participates normally.
    SilentLeader,
    /// When elected leader, proposes different blocks to different subsets
    /// of nodes (equivocation). As voter, participates normally.
    EquivocatingLeader,
    /// Proposes a block even when NOT the elected leader.
    /// As voter, participates normally.
    FakeLeader,
    /// Never signs notarize/finalize messages (drops all votes).
    /// As leader, proposes normally.
    NonVoter,
    /// Signs both the real leader's block AND a fake block from a
    /// colluding fake-leader. Produces conflicting partial signatures.
    Colluding,
    /// Full attack: cycles through ALL attack vectors per view.
    /// As leader: alternates silent / equivocate.
    /// As voter: alternates non-vote / double-vote / fake-propose.
    FullAttack,
    /// Capitulation: always equivocates as leader, always double-votes.
    /// Used when f+1 nodes are corrupt to demonstrate BFT threshold violation.
    Capitulator,
}

impl fmt::Display for ByzantineBehavior {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Honest => write!(f, "honest"),
            Self::SilentLeader => write!(f, "SILENT"),
            Self::EquivocatingLeader => write!(f, "EQUIVOC"),
            Self::FakeLeader => write!(f, "FAKE"),
            Self::NonVoter => write!(f, "NO-VOTE"),
            Self::Colluding => write!(f, "COLLUDE"),
            Self::FullAttack => write!(f, "ATTACK"),
            Self::Capitulator => write!(f, "CAPIT"),
        }
    }
}

impl ByzantineBehavior {
    /// Whether this node is adversarial in any way.
    pub fn is_byzantine(self) -> bool {
        self != Self::Honest
    }
}

/// Named attack scenario presets.
#[derive(Clone, Copy, Debug, PartialEq, Eq, clap::ValueEnum)]
pub enum Scenario {
    /// All nodes honest.
    Happy,
    /// f nodes are silent when elected leader (crash-fault).
    SilentLeader,
    /// f nodes equivocate when elected leader (send conflicting blocks).
    Equivocation,
    /// 1 fake leader proposes out of turn + (f-1) colluding voters double-sign.
    FakeLeader,
    /// f nodes never vote (but propose normally when leader).
    NonVoter,
    /// Mix of all behaviors: 1 silent + 1 equivocating + 1 non-voter (for f>=3).
    FullAttack,
    /// Catastrophic failure: f+1 nodes in full-attack mode.
    /// Exceeds the BFT threshold -- the chain SHOULD halt or diverge.
    Capitulation,
}

impl fmt::Display for Scenario {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Happy => write!(f, "happy"),
            Self::SilentLeader => write!(f, "silent-leader"),
            Self::Equivocation => write!(f, "equivocation"),
            Self::FakeLeader => write!(f, "fake-leader"),
            Self::NonVoter => write!(f, "non-voter"),
            Self::FullAttack => write!(f, "full-attack"),
            Self::Capitulation => write!(f, "CAPITULATION"),
        }
    }
}

impl Scenario {
    /// How many Byzantine nodes this scenario uses.
    /// Most scenarios use `f`; Capitulation uses `f+1` to exceed the BFT bound.
    pub fn byzantine_count(self, f: u32) -> u32 {
        match self {
            Self::Capitulation => f + 1,
            _ => f,
        }
    }
}

/// Assign a behavior to each node based on the scenario.
///
/// Byzantine nodes are always the last node IDs. Most scenarios corrupt `f`
/// nodes; `Capitulation` corrupts `f+1` to demonstrate what happens when
/// the BFT threshold is exceeded.
pub fn assign_behaviors(scenario: Scenario, n: u32, f: u32) -> HashMap<NodeId, ByzantineBehavior> {
    let mut map = HashMap::new();

    // All honest by default
    for id in 1..=n {
        map.insert(id, ByzantineBehavior::Honest);
    }

    let byz_count = scenario.byzantine_count(f);
    if byz_count == 0 || scenario == Scenario::Happy {
        return map;
    }

    // Byzantine node IDs: the last `byz_count` nodes
    let byz_start = n.saturating_sub(byz_count) + 1;
    let byz_ids: Vec<NodeId> = (byz_start..=n).collect();

    match scenario {
        Scenario::Happy => {} // already all honest
        Scenario::SilentLeader => {
            for &id in &byz_ids {
                map.insert(id, ByzantineBehavior::SilentLeader);
            }
        }
        Scenario::Equivocation => {
            for &id in &byz_ids {
                map.insert(id, ByzantineBehavior::EquivocatingLeader);
            }
        }
        Scenario::FakeLeader => {
            // First byzantine node is the fake leader, rest are colluding voters
            map.insert(byz_ids[0], ByzantineBehavior::FakeLeader);
            for &id in &byz_ids[1..] {
                map.insert(id, ByzantineBehavior::Colluding);
            }
        }
        Scenario::NonVoter => {
            for &id in &byz_ids {
                map.insert(id, ByzantineBehavior::NonVoter);
            }
        }
        Scenario::FullAttack => {
            for &id in &byz_ids {
                map.insert(id, ByzantineBehavior::FullAttack);
            }
        }
        Scenario::Capitulation => {
            // f+1 nodes: always equivocate as leader, always double-vote
            for &id in &byz_ids {
                map.insert(id, ByzantineBehavior::Capitulator);
            }
        }
    }

    map
}

/// What a node does when it could propose a block.
#[derive(Debug)]
pub enum ProposalAction {
    /// Propose the normal block.
    Propose,
    /// Stay silent -- propose nothing.
    Skip,
    /// Propose two conflicting blocks (equivocation).
    Equivocate,
    /// Propose a block even though not the elected leader.
    FakePropose,
}

/// Decide what a node does at proposal time.
///
/// `view` is used by FullAttack to cycle through attack vectors.
pub fn should_propose(behavior: ByzantineBehavior, is_elected_leader: bool, view: u64) -> ProposalAction {
    match (behavior, is_elected_leader) {
        // Honest or non-voter: propose normally when leader, skip otherwise
        (ByzantineBehavior::Honest, true) => ProposalAction::Propose,
        (ByzantineBehavior::NonVoter, true) => ProposalAction::Propose,
        (ByzantineBehavior::Honest, false) => ProposalAction::Skip,
        (ByzantineBehavior::NonVoter, false) => ProposalAction::Skip,

        // Silent: never propose when leader
        (ByzantineBehavior::SilentLeader, true) => ProposalAction::Skip,
        (ByzantineBehavior::SilentLeader, false) => ProposalAction::Skip,

        // Equivocating: send conflicting blocks when leader
        (ByzantineBehavior::EquivocatingLeader, true) => ProposalAction::Equivocate,
        (ByzantineBehavior::EquivocatingLeader, false) => ProposalAction::Skip,

        // Fake leader: propose even when not the leader
        (ByzantineBehavior::FakeLeader, _) => ProposalAction::FakePropose,

        // Colluding voters don't propose
        (ByzantineBehavior::Colluding, _) => ProposalAction::Skip,

        // Capitulator: ALWAYS equivocate as leader, propose normally otherwise
        (ByzantineBehavior::Capitulator, true) => ProposalAction::Equivocate,
        (ByzantineBehavior::Capitulator, false) => ProposalAction::Skip,

        // Full attack: cycle through leader attacks per view
        (ByzantineBehavior::FullAttack, true) => {
            match view % 3 {
                0 => ProposalAction::Skip,       // silent
                1 => ProposalAction::Equivocate, // equivocate
                _ => ProposalAction::Propose,    // propose normally (attack as voter instead)
            }
        }
        (ByzantineBehavior::FullAttack, false) => {
            // As non-leader: sometimes fake-propose
            if view % 4 == 0 {
                ProposalAction::FakePropose
            } else {
                ProposalAction::Skip
            }
        }
    }
}

/// What a node does when it's time to vote.
#[derive(Debug)]
pub enum VoteAction {
    /// Cast a normal vote.
    Vote,
    /// Don't vote at all.
    Abstain,
    /// Cast two conflicting votes (for real block + fake block).
    DoubleVote,
}

/// Decide what a node does at voting time.
///
/// `view` is used by FullAttack to cycle through attack vectors.
pub fn should_vote(behavior: ByzantineBehavior, view: u64) -> VoteAction {
    match behavior {
        ByzantineBehavior::Honest => VoteAction::Vote,
        ByzantineBehavior::SilentLeader => VoteAction::Vote, // honest as voter
        ByzantineBehavior::EquivocatingLeader => VoteAction::Vote, // honest as voter
        ByzantineBehavior::FakeLeader => VoteAction::Vote, // votes normally
        ByzantineBehavior::NonVoter => VoteAction::Abstain,
        ByzantineBehavior::Colluding => VoteAction::DoubleVote,
        // Capitulator: ALWAYS double-vote (vote for both partitioned blocks)
        ByzantineBehavior::Capitulator => VoteAction::DoubleVote,
        // Full attack: cycle through voter attacks per view
        ByzantineBehavior::FullAttack => {
            match view % 3 {
                0 => VoteAction::Abstain,    // refuse to vote
                1 => VoteAction::DoubleVote, // double-vote
                _ => VoteAction::Vote,       // vote normally (attacked as leader)
            }
        }
    }
}

// ── Message filter (Byzantine manipulation in transit) ───────────────

/// A delivery action: who gets what message.
pub struct Delivery {
    pub recipient: NodeId,
    pub message: Message,
}

/// Context needed by the filter to forge signatures or modify blocks.
pub struct FilterContext<'a> {
    pub sender: NodeId,
    pub sender_behavior: ByzantineBehavior,
    pub view: View,
    pub all_node_ids: &'a [NodeId],
    pub shares: &'a HashMap<NodeId, KeyShare>,
}

/// Filter an outgoing message from a sender before delivery.
///
/// Returns the list of (recipient, message) pairs to deliver.
/// Honest nodes: the message is delivered to all peers unchanged.
/// Byzantine nodes: messages may be dropped, modified, or duplicated.
pub fn filter_outgoing(
    out: &Outgoing,
    ctx: &FilterContext,
) -> Vec<Delivery> {
    let beh = ctx.sender_behavior;

    // Honest nodes: broadcast to all peers.
    if !beh.is_byzantine() {
        return broadcast_to_all(out, ctx.sender, ctx.all_node_ids);
    }

    match out {
        Outgoing::Proposal { block } => filter_proposal(block, ctx),
        Outgoing::Vote { view, block_hash, partial } => {
            filter_vote(*view, *block_hash, partial, ctx)
        }
        Outgoing::NullifyVote { .. } => {
            // Byzantine: drop nullify votes for Abstain scenarios,
            // otherwise broadcast normally (capitulators want views to advance).
            let vote_action = should_vote(beh, ctx.view);
            if matches!(vote_action, VoteAction::Abstain) {
                vec![] // drop
            } else {
                broadcast_to_all(out, ctx.sender, ctx.all_node_ids)
            }
        }
        Outgoing::FinalizeVote { .. } | Outgoing::RelayNotarization { .. } => {
            // Broadcast normally (Byzantine nodes still want to advance).
            broadcast_to_all(out, ctx.sender, ctx.all_node_ids)
        }
    }
}

/// Filter a proposal from a Byzantine leader.
fn filter_proposal(block: &Block, ctx: &FilterContext) -> Vec<Delivery> {
    let beh = ctx.sender_behavior;
    let action = should_propose(beh, true, ctx.view);

    match action {
        ProposalAction::Skip => vec![], // silent leader: drop proposal
        ProposalAction::Propose => {
            // Normal proposal
            broadcast_to_all(
                &Outgoing::Proposal { block: block.clone() },
                ctx.sender, ctx.all_node_ids,
            )
        }
        ProposalAction::Equivocate => {
            // Send block A to even-indexed peers, block B to odd-indexed.
            // Block B has different payload but same parent/view/proposer.
            let block_b = Block {
                view: block.view,
                parent_hash: block.parent_hash,
                payload: format!("equivoc-B-v{}-by-{}", block.view, block.proposer).into_bytes(),
                proposer: block.proposer,
            };

            let mut deliveries = Vec::new();
            for (idx, &nid) in ctx.all_node_ids.iter().enumerate() {
                if nid == ctx.sender { continue; }
                let b = if idx % 2 == 0 { block.clone() } else { block_b.clone() };
                deliveries.push(Delivery {
                    recipient: nid,
                    message: Message::Proposal { block: b },
                });
            }
            deliveries
        }
        ProposalAction::FakePropose => {
            // Fake leader: inject proposal even though not the real leader.
            // Most replicas will reject (WrongLeader).
            broadcast_to_all(
                &Outgoing::Proposal { block: block.clone() },
                ctx.sender, ctx.all_node_ids,
            )
        }
    }
}

/// Filter a vote from a Byzantine voter.
fn filter_vote(
    view: View,
    bh: BlockHash,
    partial: &golden_dkg::threshold::types::PartialSignature,
    ctx: &FilterContext,
) -> Vec<Delivery> {
    let beh = ctx.sender_behavior;
    let vote_action = should_vote(beh, view);

    match vote_action {
        VoteAction::Abstain => vec![], // drop the vote
        VoteAction::Vote => {
            // Send the vote normally.
            broadcast_vote_to_all(view, bh, ctx.sender, partial, ctx.all_node_ids)
        }
        VoteAction::DoubleVote => {
            // Send the original vote to all peers.
            let deliveries = broadcast_vote_to_all(view, bh, ctx.sender, partial, ctx.all_node_ids);
            // For capitulators: also forge a vote for ANY other block hash
            // they might know about. In practice this is the other equivocation
            // block. The engine will inject the second block hash when it
            // detects equivocation.
            // (The actual double-vote injection is handled by the engine
            // because the filter doesn't know the other block hash.)
            deliveries
        }
    }
}

/// Broadcast an Outgoing message as a Message to all peers (except sender).
fn broadcast_to_all(out: &Outgoing, sender: NodeId, all_ids: &[NodeId]) -> Vec<Delivery> {
    let msg = outgoing_to_message(out, sender);
    all_ids.iter()
        .filter(|&&nid| nid != sender)
        .map(|&nid| Delivery { recipient: nid, message: msg.clone() })
        .collect()
}

/// Broadcast a vote to all peers.
fn broadcast_vote_to_all(
    view: View,
    bh: BlockHash,
    sender: NodeId,
    partial: &golden_dkg::threshold::types::PartialSignature,
    all_ids: &[NodeId],
) -> Vec<Delivery> {
    all_ids.iter()
        .filter(|&&nid| nid != sender)
        .map(|&nid| Delivery {
            recipient: nid,
            message: Message::Vote {
                view,
                block_hash: bh,
                signer: sender,
                partial: partial.clone(),
            },
        })
        .collect()
}

/// Convert an Outgoing to a Message for delivery.
pub fn outgoing_to_message(out: &Outgoing, sender: NodeId) -> Message {
    match out {
        Outgoing::Vote { view, block_hash, partial } => Message::Vote {
            view: *view, block_hash: *block_hash, signer: sender, partial: partial.clone(),
        },
        Outgoing::NullifyVote { view, partial } => Message::NullifyVote {
            view: *view, signer: sender, partial: partial.clone(),
        },
        Outgoing::FinalizeVote { view, partial } => Message::FinalizeVote {
            view: *view, signer: sender, partial: partial.clone(),
        },
        Outgoing::RelayNotarization { view, block, certificate } => Message::Notarization {
            view: *view, block: block.clone(), certificate: certificate.clone(),
        },
        Outgoing::Proposal { block } => Message::Proposal {
            block: block.clone(),
        },
    }
}

/// Forge a vote for a given block hash using a Byzantine node's key share.
pub fn forge_vote(
    share: &KeyShare,
    view: View,
    bh: &BlockHash,
) -> golden_dkg::threshold::types::PartialSignature {
    use golden_dkg::threshold::{beacon, signing};
    let mut msg = view.to_be_bytes().to_vec();
    msg.extend_from_slice(bh);
    let digest = beacon::digest_message(view, Some(&msg));
    let msg_hash = beacon::hash_to_g2(&digest);
    signing::partial_sign(&msg_hash, share)
}
