//! Simplex BFT Consensus -- binary demo.
//!
//! Runs a local simulation of the Simplex BFT consensus protocol using
//! BLS12-381 threshold signatures from `threshold-crypto`, displaying
//! per-view results in a live-updating terminal table.
//!
//! Usage:
//!   cargo run --release -p simplex                                      # all honest (default)
//!   cargo run --release -p simplex -- --byzantine silent-leader         # crash-fault leader
//!   cargo run --release -p simplex -- --byzantine equivocation          # equivocating leader
//!   cargo run --release -p simplex -- --byzantine fake-leader           # out-of-turn proposal
//!   cargo run --release -p simplex -- --byzantine non-voter             # nodes refuse to vote
//!   cargo run --release -p simplex -- --byzantine full-attack           # ALL attacks cycling
//!   cargo run --release -p simplex -- --byzantine capitulation          # f+1 naughty -- chain halts!
//!   cargo run --release -p simplex -- --rounds 10                       # 10 views only

use clap::Parser;
use comfy_table::presets::UTF8_FULL;
use comfy_table::{Attribute, Cell, Color, ContentArrangement, Table};
use crossterm::{cursor, execute, terminal};
use std::collections::VecDeque;
use std::io::{self, Write};

use golden_dkg::types::NodeId;
use threshold_crypto::cache::LagrangeCache;
use threshold_crypto::dkg;

use simplex_consensus::sim::engine::{ConsensusEngine, ViewOutcome};
use simplex_consensus::sim::naughty::{ByzantineBehavior, Scenario};

// ── CLI ─────────────────────────────────────────────────────────────────

/// Simplex BFT Consensus -- threshold signature demo
#[derive(Parser)]
#[command(name = "simplex", about = "Simplex BFT consensus with BLS12-381 threshold signatures")]
struct Cli {
    /// Byzantine failures to tolerate (n=3f+1, t=2f+1) [default: 3]
    #[arg(short, long, default_value_t = 3)]
    failures: u32,

    /// Number of views to run (omit for infinite)
    #[arg(short, long)]
    rounds: Option<u64>,

    /// Disable in-place table updates (scroll instead)
    #[arg(long)]
    no_overwrite: bool,

    /// Byzantine attack behavior (omit for all-honest)
    #[arg(short, long, value_enum)]
    byzantine: Option<Scenario>,

    /// Keep running after a safety violation (fork) instead of halting
    #[arg(long)]
    continue_after_fork: bool,
}

// ── Display helpers ─────────────────────────────────────────────────────

fn to_hex(bytes: &[u8], n: usize) -> String {
    bytes.iter().take(n).map(|b| format!("{:02x}", b)).collect()
}

fn vrf_color(b: u8) -> Color {
    match b % 6 {
        0 => Color::Red,
        1 => Color::Blue,
        2 => Color::Green,
        3 => Color::Magenta,
        4 => Color::Cyan,
        _ => Color::Yellow,
    }
}

// ── Block strip ─────────────────────────────────────────────────────────

/// Fixed-width visual chain of colored block indicators.
///
/// Models the Simplex two-phase pipeline:
///   Yellow `█` = notarized (got 2f+1 votes, not yet finalized)
///   Green  `█` = finalized (next block notarized on top, confirming this one)
///   Grey   `█` = nullified (timeout / no valid proposal)
///   Dim    `·` = empty (undecided)
///
/// When a new block is finalized, the previous notarized block is promoted
/// to green. The new block enters as yellow. The strip wraps when full.
const STRIP_LEN: usize = 40;

struct BlockStrip {
    /// Ring buffer of decided view outcomes.
    slots: Vec<Option<BlockSlot>>,
    /// Next write position (wraps at STRIP_LEN).
    cursor: usize,
    /// Total views recorded.
    total: usize,
    /// Position of the last notarized (yellow) block, if any.
    last_notarized: Option<usize>,
}

#[derive(Clone, Copy, PartialEq)]
enum BlockSlot {
    Notarized,
    Finalized,
    Nullified,
}

impl BlockStrip {
    fn new() -> Self {
        Self {
            slots: vec![None; STRIP_LEN],
            cursor: 0,
            total: 0,
            last_notarized: None,
        }
    }

    fn push(&mut self, slot: BlockSlot) {
        match slot {
            BlockSlot::Finalized => {
                // Promote the previous notarized block to finalized (green)
                if let Some(prev) = self.last_notarized {
                    self.slots[prev] = Some(BlockSlot::Finalized);
                }
                // This block enters as notarized (yellow) until the next one confirms it
                self.slots[self.cursor] = Some(BlockSlot::Notarized);
                self.last_notarized = Some(self.cursor);
            }
            BlockSlot::Nullified => {
                // Nullified blocks don't promote anything -- the notarized
                // block stays yellow (it's still waiting for confirmation)
                self.slots[self.cursor] = Some(BlockSlot::Nullified);
            }
            BlockSlot::Notarized => {
                self.slots[self.cursor] = Some(BlockSlot::Notarized);
                self.last_notarized = Some(self.cursor);
            }
        }
        self.cursor = (self.cursor + 1) % STRIP_LEN;
        self.total += 1;
    }

    /// Render the strip as a single fixed-width line of ANSI-colored blocks.
    fn render(&self) -> String {
        let mut parts = Vec::with_capacity(STRIP_LEN);
        for i in 0..STRIP_LEN {
            match self.slots[i] {
                Some(BlockSlot::Finalized) => {
                    // Bright green block
                    parts.push("\x1b[92m\u{2588}\x1b[0m".to_string());
                }
                Some(BlockSlot::Notarized) => {
                    // Yellow block (notarized, awaiting finalization)
                    parts.push("\x1b[93m\u{2588}\x1b[0m".to_string());
                }
                Some(BlockSlot::Nullified) => {
                    // Dark grey block
                    parts.push("\x1b[90m\u{2588}\x1b[0m".to_string());
                }
                None => {
                    // Dim dot for empty slot
                    parts.push("\x1b[90m\u{00b7}\x1b[0m".to_string());
                }
            }
        }

        // Cursor marker underneath the next write position
        let cursor_char = if self.total > 0 { "\u{25b2}" } else { " " };
        let mut indicator = " ".repeat(self.cursor);
        indicator.push_str(cursor_char);

        format!(
            " chain: [{}] {:>4}\n         {}",
            parts.join(""),
            self.total,
            indicator,
        )
    }
}

struct LatencyTracker {
    window: VecDeque<f64>,
    capacity: usize,
}

impl LatencyTracker {
    fn new(capacity: usize) -> Self {
        Self {
            window: VecDeque::with_capacity(capacity),
            capacity,
        }
    }

    fn push(&mut self, ms: f64) {
        if self.window.len() == self.capacity {
            self.window.pop_front();
        }
        self.window.push_back(ms);
    }

    fn avg(&self) -> f64 {
        if self.window.is_empty() { return 0.0; }
        self.window.iter().sum::<f64>() / self.window.len() as f64
    }

    fn last(&self) -> f64 { self.window.back().copied().unwrap_or(0.0) }
    fn min(&self) -> f64 { self.window.iter().cloned().fold(f64::MAX, f64::min) }
    fn max(&self) -> f64 { self.window.iter().cloned().fold(0.0_f64, f64::max) }
}

// ── Table builders ──────────────────────────────────────────────────────

fn build_pk_table(pk_hex: &str, n: u32, t: u32, f: u32, scenario: Scenario) -> Table {
    let mut table = Table::new();
    table
        .load_preset(UTF8_FULL)
        .set_content_arrangement(ContentArrangement::Dynamic);

    let header_text = if scenario == Scenario::Capitulation {
        "Simplex BFT Consensus -- CAPITULATION MODE"
    } else {
        "Simplex BFT Consensus"
    };
    let header_color = if scenario == Scenario::Capitulation {
        Color::Red
    } else {
        Color::Cyan
    };

    table.set_header(vec![Cell::new(header_text)
        .add_attribute(Attribute::Bold)
        .fg(header_color)]);

    let mid = pk_hex.len() / 2;
    table.add_row(vec![Cell::new(format!(
        "Group PK: {}\n          {}",
        &pk_hex[..mid],
        &pk_hex[mid..]
    ))
    .fg(Color::White)]);

    let byz_count = scenario.byzantine_count(f);
    let info_line = if scenario == Scenario::Capitulation {
        format!("n={n}  t={t}  f={f}  byzantine={byz_count} (f+1!)  scenario={scenario}")
    } else {
        format!("n={n}  t={t}  f={f}  scenario={scenario}")
    };
    let info_color = if scenario == Scenario::Capitulation {
        Color::Red
    } else {
        Color::DarkGrey
    };
    table.add_row(vec![Cell::new(info_line).fg(info_color)]);

    table
}

fn behavior_color(beh: ByzantineBehavior) -> Color {
    match beh {
        ByzantineBehavior::Honest => Color::Green,
        ByzantineBehavior::SilentLeader => Color::DarkGrey,
        ByzantineBehavior::EquivocatingLeader => Color::Red,
        ByzantineBehavior::FakeLeader => Color::Magenta,
        ByzantineBehavior::NonVoter => Color::Yellow,
        ByzantineBehavior::Colluding => Color::Red,
        ByzantineBehavior::FullAttack => Color::Red,
        ByzantineBehavior::Capitulator => Color::Red,
    }
}

fn build_view_table(
    view: u64,
    result: &simplex_consensus::sim::engine::ViewResult,
    latency: &LatencyTracker,
) -> Table {
    let mut table = Table::new();
    table
        .load_preset(UTF8_FULL)
        .set_content_arrangement(ContentArrangement::Dynamic);

    let vrf_seed = match &result.outcome {
        ViewOutcome::Finalized { vrf_seed, .. } => vrf_seed,
        ViewOutcome::Nullified { vrf_seed, .. } => vrf_seed,
    };

    // Fixed cell width for the top-right status cell (24 chars per line)
    const W: usize = 24;

    let (status_text, status_color, block_text) = match &result.outcome {
        ViewOutcome::Finalized { block, .. } => {
            let block_h = simplex_consensus::types::block_hash(block);
            ("FINALIZED", Color::Green, format!("#{} ({})", view, to_hex(&block_h, 6)))
        }
        ViewOutcome::Nullified { .. } => ("NULLIFIED", Color::Yellow, "dummy".to_string()),
    };

    let seed_hex = to_hex(vrf_seed, 8);
    let seed_color = vrf_color(vrf_seed[0]);

    // Annotations for special events
    let anno_text = if result.diverged {
        "!! DIVERGED !!"
    } else if result.fake_proposal_attempted && result.equivocation_attempted {
        "FAKE+EQUIVOC"
    } else if result.fake_proposal_attempted {
        "FAKE-REJECTED"
    } else if result.equivocation_attempted {
        "EQUIVOC-DETECT"
    } else {
        ""
    };

    // Header: fixed-width multiline status cell (4 lines, each W chars)
    let status_cell_text = format!(
        "{:<W$}\n{:<W$}\nVRF: {:<w2$}\n{:<W$}",
        status_text,
        block_text,
        seed_hex,
        anno_text,
        W = W,
        w2 = W - 5,
    );

    table.set_header(vec![
        Cell::new(format!("View {:06}", view))
            .add_attribute(Attribute::Bold)
            .fg(Color::Cyan),
        Cell::new("Role").add_attribute(Attribute::Bold),
        Cell::new("Vote").add_attribute(Attribute::Bold),
        Cell::new(status_cell_text)
            .add_attribute(Attribute::Bold)
            .fg(status_color),
    ]);

    // One row per node
    for action in &result.node_actions {
        let is_leader = matches!(action.role, simplex_consensus::sim::engine::NodeRole::Leader);
        let beh = action.behavior;

        // Node name cell
        let node_cell = if is_leader {
            Cell::new(format!("Node {:>2}", action.id))
                .fg(Color::Blue)
                .add_attribute(Attribute::Bold)
        } else {
            Cell::new(format!("Node {:>2}", action.id))
                .fg(behavior_color(beh))
        };

        // Role cell (fixed 15 chars: longest is "LEADER (ATTACK)")
        let role_text = if is_leader {
            if beh.is_byzantine() {
                format!("{:<15}", format!("LEADER ({})", beh))
            } else {
                format!("{:<15}", "LEADER")
            }
        } else if beh.is_byzantine() {
            format!("{:<15}", format!("{}", beh))
        } else {
            format!("{:<15}", "voter")
        };

        let role_cell = if is_leader {
            Cell::new(&role_text).fg(Color::Blue).add_attribute(Attribute::Bold)
        } else {
            Cell::new(&role_text).fg(behavior_color(beh))
        };

        // Vote cell (fixed 17 chars: longest is "notarize+finalize")
        let vote_cell = if action.rejected_proposal {
            Cell::new(format!("{:<17}", "REJECTED")).fg(Color::Red).add_attribute(Attribute::Bold)
        } else if !action.voted {
            Cell::new(format!("{:<17}", "---")).fg(Color::DarkGrey)
        } else if action.double_voted {
            Cell::new(format!("{:<17}", "DOUBLE-VOTE")).fg(Color::Red).add_attribute(Attribute::Bold)
        } else {
            match &result.outcome {
                ViewOutcome::Finalized { .. } => Cell::new(format!("{:<17}", "notarize+finalize")).fg(Color::Green),
                ViewOutcome::Nullified { .. } => Cell::new(format!("{:<17}", "nullify")).fg(Color::Yellow),
            }
        };

        // Status cell (fixed 7 chars)
        let status_cell = if action.rejected_proposal {
            Cell::new(format!("{:<7}", "REJECT")).fg(Color::Red).add_attribute(Attribute::Bold)
        } else if !action.voted && beh.is_byzantine() {
            Cell::new(format!("{:<7}", "offline")).fg(Color::Red)
        } else if action.double_voted {
            Cell::new(format!("{:<7}", "EQUIVOC")).fg(Color::Red)
        } else if action.voted {
            Cell::new(format!("{:<7}", "OK")).fg(Color::Green).add_attribute(Attribute::Bold)
        } else {
            Cell::new(format!("{:<7}", "---")).fg(Color::DarkGrey)
        };

        table.add_row(vec![node_cell, role_cell, vote_cell, status_cell]);
    }

    // Footer: fixed-width latency stats
    let latency_footer = format!(
        "avg  {:06.2}ms\nlast {:06.2}ms\nmin  {:06.2}ms\nmax  {:06.2}ms",
        latency.avg(), latency.last(), latency.min(), latency.max(),
    );
    table.add_row(vec![
        Cell::new(format!("{:<12}", status_text))
            .fg(status_color)
            .add_attribute(Attribute::Bold),
        Cell::new(format!("VRF: {}", seed_hex)).fg(seed_color),
        Cell::new(""),
        Cell::new(latency_footer).fg(Color::DarkGrey),
    ]);

    table
}

fn rendered_lines(s: &str) -> u16 {
    s.lines().count() as u16
}

// ── Main ────────────────────────────────────────────────────────────────

fn main() {
    let cli = Cli::parse();

    let f = cli.failures;
    let n = 3 * f + 1;
    let t = 2 * f + 1;
    let scenario = cli.byzantine.unwrap_or(Scenario::Happy);
    let max_rounds = cli.rounds;
    let overwrite = !cli.no_overwrite;

    let byz_count = scenario.byzantine_count(f);

    eprintln!("=== Simplex BFT Consensus ===");
    eprintln!("n={n}, t={t}, f={f}, scenario={scenario}");
    if scenario == Scenario::Capitulation {
        eprintln!(
            "*** CAPITULATION: {byz_count} Byzantine nodes (f+1 = {}) > BFT bound (f = {f}) ***",
            f + 1
        );
        eprintln!("*** Chain WILL halt or diverge -- this demonstrates BFT threshold violation ***");
    }
    eprintln!(
        "views={}",
        max_rounds.map_or("infinite".into(), |r| r.to_string())
    );
    eprintln!("Running DKG...");

    let (shares, group_info) = dkg::run_dkg(n, t);
    let pk = group_info.public_key;

    let mut pk_bytes = Vec::new();
    ark_serialize::CanonicalSerialize::serialize_compressed(&pk, &mut pk_bytes)
        .expect("serialize pk");
    let pk_hex: String = pk_bytes.iter().map(|b| format!("{:02x}", b)).collect();

    let node_ids: Vec<NodeId> = shares.iter().map(|s| s.id).collect();
    let cache = LagrangeCache::new(&node_ids, t, 1);

    let mut engine = ConsensusEngine::new(shares, group_info, cache, scenario, f);

    eprintln!("DKG complete. Consensus running.\n");

    let mut stdout = io::stdout();

    let pk_table = build_pk_table(&pk_hex, n, t, f, scenario);
    println!("{pk_table}");
    stdout.flush().ok();

    let mut prev_output_lines: u16 = 0;
    let mut latency = LatencyTracker::new(20);
    let mut strip = BlockStrip::new();

    let mut view: u64 = 1;
    let mut finalized_count: u64 = 0;
    let mut nullified_count: u64 = 0;
    loop {
        if let Some(max) = max_rounds {
            if view > max {
                break;
            }
        }

        let result = engine.run_view(view);
        latency.push(result.latency_ms);

        // Track finalized/nullified counts for display.
        match &result.outcome {
            ViewOutcome::Finalized { .. } => {
                finalized_count += 1;
                strip.push(BlockSlot::Finalized);
            }
            ViewOutcome::Nullified { .. } => {
                nullified_count += 1;
                strip.push(BlockSlot::Nullified);
            }
        }

        let strip_rendered = strip.render();
        let table = build_view_table(view, &result, &latency);
        let table_rendered = table.to_string();
        let full_output = format!("{}\n{}", strip_rendered, table_rendered);

        if overwrite && view > 1 {
            execute!(
                stdout,
                cursor::MoveUp(prev_output_lines),
                terminal::Clear(terminal::ClearType::FromCursorDown)
            )
            .ok();
        }

        println!("{full_output}");
        stdout.flush().ok();

        prev_output_lines = rendered_lines(&full_output);

        // Stop on divergence unless --continue-after-fork is set
        if result.diverged && !cli.continue_after_fork {
            eprintln!();
            eprintln!("*** SAFETY VIOLATION: honest nodes diverged at view {} ***", view);
            eprintln!("*** Chain is permanently forked. Halting. ***");
            eprintln!("*** (use --continue-after-fork to see post-fork behavior) ***");
            break;
        }

        view += 1;
    }

    eprintln!(
        "\n{} views complete. Finalized: {}, Nullified: {}",
        view,
        finalized_count,
        nullified_count,
    );
}
