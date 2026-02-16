//! Byzantine behavior presets for Simplex consensus simulation.
//!
//! All adversarial logic is isolated here. The engine consults these
//! functions to decide what each node does each view.

use golden_dkg::types::NodeId;
use std::collections::HashMap;
use std::fmt;

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
