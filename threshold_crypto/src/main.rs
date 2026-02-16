//! Threshold VRF Random Beacon -- binary demo.
//!
//! Runs a threshold BLS beacon using golden-dkg, displaying per-round
//! chained and unchained VRF outputs in a live-updating terminal table.
//!
//! Usage:
//!   cargo run --release -p golden-threshold-crypto                       # infinite rounds
//!   cargo run --release -p golden-threshold-crypto -- --rounds 50        # 50 rounds
//!   cargo run --release -p golden-threshold-crypto -- --no-overwrite     # scrolling output

use ark_bls12_381::{Fr, G2Affine, G2Projective};
use ark_ec::CurveGroup;
use ark_serialize::CanonicalSerialize;
use clap::Parser;
use comfy_table::presets::UTF8_FULL;
use comfy_table::{Attribute, Cell, Color, ContentArrangement, Table};
use crossterm::{cursor, execute, terminal};
use golden_dkg::types::NodeId;
use rayon::prelude::*;
use std::collections::{HashMap, VecDeque};
use std::io::{self, Write};
use std::time::Instant;

use threshold_demo::beacon;
use threshold_demo::cache::{combinations, LagrangeCache};
use threshold_demo::dkg;
use threshold_demo::signing;
use threshold_demo::types::KeyShare;

// ── CLI ─────────────────────────────────────────────────────────────────

/// Threshold VRF Random Beacon -- Golden DKG demo
#[derive(Parser)]
#[command(name = "threshold-vrf", about = "Threshold VRF random beacon using Golden DKG")]
struct Cli {
    /// Number of rounds to run (omit for infinite)
    #[arg(short, long)]
    rounds: Option<u64>,

    /// Disable in-place table updates (scroll instead)
    #[arg(long)]
    no_overwrite: bool,

    /// Byzantine failures to tolerate (n=3f+1, t=2f+1) [default: 3]
    #[arg(short, long, default_value_t = 3)]
    failures: u32,

    /// Number of random C(n,t) subsets to cross-check per round [default: 1]
    #[arg(short, long, default_value_t = 1)]
    check_subsets: usize,

    /// Run pairing verification every N rounds (omit to skip verification)
    #[arg(long)]
    verify_every: Option<u64>,
}

// ── Display types (binary-only) ─────────────────────────────────────────

struct RoundResult {
    round: u64,
    chained_hex: String,
    chained_color: Color,
    chained_valid: bool,
    chained_match: bool,
    chained_bytes: Vec<u8>,
    unchained_hex: String,
    unchained_color: Color,
    unchained_valid: bool,
    unchained_match: bool,
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

fn to_hex(bytes: &[u8], n: usize) -> String {
    bytes.iter().take(n).map(|b| format!("{:02x}", b)).collect()
}

/// Rolling window latency tracker.
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
        if self.window.is_empty() {
            return 0.0;
        }
        self.window.iter().sum::<f64>() / self.window.len() as f64
    }

    fn last(&self) -> f64 {
        self.window.back().copied().unwrap_or(0.0)
    }

    fn min(&self) -> f64 {
        self.window.iter().cloned().fold(f64::MAX, f64::min)
    }

    fn max(&self) -> f64 {
        self.window.iter().cloned().fold(0.0_f64, f64::max)
    }
}

// ── Table builders ──────────────────────────────────────────────────────

fn build_pk_table(pk_hex: &str) -> Table {
    let mut table = Table::new();
    table
        .load_preset(UTF8_FULL)
        .set_content_arrangement(ContentArrangement::Dynamic);
    let mid = pk_hex.len() / 2;
    table.set_header(vec![
        Cell::new("Network Public Key (BLS12-381 G1)")
            .add_attribute(Attribute::Bold)
            .fg(Color::Cyan),
    ]);
    table.add_row(vec![Cell::new(format!(
        "{}\n{}",
        &pk_hex[..mid],
        &pk_hex[mid..]
    ))
    .fg(Color::White)]);
    table
}

fn build_table(result: &RoundResult, n: u32, num_subsets: usize, latency: &LatencyTracker) -> Table {
    let mut table = Table::new();
    table
        .load_preset(UTF8_FULL)
        .set_content_arrangement(ContentArrangement::Dynamic);

    table.set_header(vec![
        Cell::new("Node").add_attribute(Attribute::Bold),
        Cell::new(format!("Round {:012}", result.round))
            .add_attribute(Attribute::Bold)
            .fg(Color::Cyan),
        Cell::new("Chained VRF").add_attribute(Attribute::Bold),
        Cell::new("Unchained Beacon").add_attribute(Attribute::Bold),
        Cell::new("Status").add_attribute(Attribute::Bold),
    ]);

    let node_colors = [Color::Green, Color::Yellow, Color::Magenta, Color::Cyan, Color::Red];

    for i in 0..n {
        let id = i + 1;
        let ok = result.chained_valid && result.unchained_valid;
        let status_cell = if ok {
            Cell::new(" OK ").fg(Color::Green).add_attribute(Attribute::Bold)
        } else {
            Cell::new(" !! ").fg(Color::Red).add_attribute(Attribute::Bold)
        };

        table.add_row(vec![
            Cell::new(format!("Node {}", id))
                .fg(node_colors[i as usize % node_colors.len()])
                .add_attribute(Attribute::Bold),
            Cell::new(format!("#{:012}", result.round)),
            Cell::new(&result.chained_hex).fg(result.chained_color),
            Cell::new(&result.unchained_hex).fg(result.unchained_color),
            status_cell,
        ]);
    }

    let both_match = result.chained_match && result.unchained_match;
    let (match_text, match_color) = if both_match {
        (format!("{} SUBSETS MATCH", num_subsets), Color::Green)
    } else {
        ("MISMATCH!".to_string(), Color::Red)
    };

    let latency_text = format!(
        "avg  {:06.2}ms\nlast {:06.2}ms\nmin  {:06.2}ms\nmax  {:06.2}ms",
        latency.avg(),
        latency.last(),
        latency.min(),
        latency.max(),
    );

    table.add_row(vec![
        Cell::new(match_text)
            .fg(match_color)
            .add_attribute(Attribute::Bold),
        Cell::new(&latency_text).fg(Color::DarkGrey),
        Cell::new("chained").fg(Color::DarkGrey),
        Cell::new("unchained").fg(Color::DarkGrey),
        Cell::new(""),
    ]);

    table
}

fn rendered_lines(s: &str) -> u16 {
    s.lines().count() as u16
}

// ── Per-round orchestration ─────────────────────────────────────────────

fn g2_to_bytes(point: &G2Affine) -> Vec<u8> {
    let mut buf = Vec::new();
    point.serialize_compressed(&mut buf).expect("serialize");
    buf
}

/// Combine a single subset and return the G2 point.
fn combine_one(subset_coeffs: &[(NodeId, Fr)], partials: &HashMap<NodeId, G2Affine>) -> G2Affine {
    let mut combined = G2Projective::default();
    for &(id, ref li) in subset_coeffs {
        let sig_i = partials[&id];
        combined += sig_i * li;
    }
    combined.into_affine()
}

/// Combine partials for one message hash, optionally cross-checking multiple subsets.
fn threshold_combine(
    msg_hash: &G2Affine,
    partials: &HashMap<NodeId, G2Affine>,
    pk: &ark_bls12_381::G1Affine,
    cache: &LagrangeCache,
    do_verify: bool,
) -> (Vec<u8>, bool, bool) {
    if cache.subsets.len() == 1 {
        let combined = combine_one(&cache.subsets[0], partials);
        let sig_bytes = g2_to_bytes(&combined);
        let valid = if do_verify {
            signing::verify(msg_hash, &threshold_demo::types::ThresholdSignature { signature: combined }, pk)
        } else {
            true
        };
        return (sig_bytes, valid, true);
    }

    let results: Vec<G2Affine> = cache
        .subsets
        .par_iter()
        .map(|subset_coeffs| combine_one(subset_coeffs, partials))
        .collect();

    let sig_bytes = g2_to_bytes(&results[0]);
    let all_match = results.windows(2).all(|w| {
        g2_to_bytes(&w[0]) == g2_to_bytes(&w[1])
    });
    let valid = if do_verify {
        signing::verify(msg_hash, &threshold_demo::types::ThresholdSignature { signature: results[0] }, pk)
    } else {
        true
    };

    (sig_bytes, valid, all_match)
}

fn run_round(
    round: u64,
    shares: &[KeyShare],
    prev_chained_bytes: &[u8],
    pk: &ark_bls12_381::G1Affine,
    cache: &LagrangeCache,
    do_verify: bool,
) -> RoundResult {
    let chained_msg = beacon::digest_message(round, Some(prev_chained_bytes));
    let unchained_msg = beacon::digest_message(round, None);

    let (chained_hash, unchained_hash) = rayon::join(
        || beacon::hash_to_g2(&chained_msg),
        || beacon::hash_to_g2(&unchained_msg),
    );

    let n = shares.len();
    let mut work: Vec<(NodeId, bool, ark_bls12_381::Fr)> = Vec::with_capacity(2 * n);
    for share in shares {
        work.push((share.id, true, share.secret));
        work.push((share.id, false, share.secret));
    }

    let results: Vec<(NodeId, bool, G2Affine)> = work
        .par_iter()
        .map(|&(id, is_chained, sk)| {
            let h = if is_chained { &chained_hash } else { &unchained_hash };
            let sig = (*h * sk).into_affine();
            (id, is_chained, sig)
        })
        .collect();

    let mut chained_partials = HashMap::with_capacity(n);
    let mut unchained_partials = HashMap::with_capacity(n);
    for &(id, is_chained, sig) in &results {
        if is_chained {
            chained_partials.insert(id, sig);
        } else {
            unchained_partials.insert(id, sig);
        }
    }

    let ((chained_bytes, chained_valid, chained_match), (unchained_bytes, unchained_valid, unchained_match)) =
        rayon::join(
            || threshold_combine(&chained_hash, &chained_partials, pk, cache, do_verify),
            || threshold_combine(&unchained_hash, &unchained_partials, pk, cache, do_verify),
        );

    RoundResult {
        round,
        chained_hex: to_hex(&chained_bytes, 10),
        chained_color: vrf_color(chained_bytes[0]),
        chained_valid,
        chained_match,
        chained_bytes,
        unchained_hex: to_hex(&unchained_bytes, 10),
        unchained_color: vrf_color(unchained_bytes[0]),
        unchained_valid,
        unchained_match,
    }
}

// ── Main ────────────────────────────────────────────────────────────────

fn main() {
    let cli = Cli::parse();
    let max_rounds: Option<u64> = cli.rounds;
    let overwrite = !cli.no_overwrite;
    let num_check = cli.check_subsets;
    let verify_every = cli.verify_every;

    let f = cli.failures;
    let n = 3 * f + 1;
    let t = 2 * f + 1;

    eprintln!("=== Threshold VRF Random Beacon ===");
    eprintln!("n={n}, t={t}, f={f} (BFT: n=3f+1, t=2f+1)");
    let total_subsets = combinations(&(1..=n).collect::<Vec<_>>(), t as usize).len();
    eprintln!(
        "rounds={}, checking {} of {} subsets per round",
        max_rounds.map_or("infinite".into(), |r| r.to_string()),
        num_check.min(total_subsets),
        total_subsets,
    );
    eprintln!("Running DKG...");

    let (shares, group_info) = dkg::run_dkg(n, t);
    let pk = group_info.public_key;

    let mut pk_bytes = Vec::new();
    pk.serialize_compressed(&mut pk_bytes).expect("serialize pk");
    let pk_hex: String = pk_bytes.iter().map(|b| format!("{:02x}", b)).collect();

    let node_ids: Vec<NodeId> = shares.iter().map(|s| s.id).collect();
    let cache = LagrangeCache::new(&node_ids, t, num_check);

    eprintln!(
        "DKG complete. Lagrange cache: {} subsets precomputed. Beacon running.\n",
        cache.subsets.len()
    );

    let mut stdout = io::stdout();

    let pk_table = build_pk_table(&pk_hex);
    println!("{pk_table}");
    stdout.flush().ok();

    let mut prev_chained_bytes: Vec<u8> = vec![0u8; 128];
    let mut prev_table_lines: u16 = 0;
    let mut latency = LatencyTracker::new(10);

    let mut round: u64 = 0;
    loop {
        if let Some(max) = max_rounds {
            if round >= max {
                break;
            }
        }

        let do_verify = match verify_every {
            Some(0) => true,
            Some(n) => round % n == 0,
            None => false,
        };

        let t0 = Instant::now();
        let result = run_round(round, &shares, &prev_chained_bytes, &pk, &cache, do_verify);
        let elapsed_ms = t0.elapsed().as_secs_f64() * 1000.0;
        latency.push(elapsed_ms);

        let table = build_table(&result, n, cache.subsets.len(), &latency);
        let rendered = table.to_string();

        if overwrite && round > 0 {
            execute!(
                stdout,
                cursor::MoveUp(prev_table_lines),
                terminal::Clear(terminal::ClearType::FromCursorDown)
            )
            .ok();
        }

        println!("{rendered}");
        stdout.flush().ok();

        prev_table_lines = rendered_lines(&rendered);
        prev_chained_bytes = result.chained_bytes;

        if !result.chained_match || !result.unchained_match {
            eprintln!("ERROR: subset mismatch at round {round}!");
            std::process::exit(1);
        }

        round += 1;
    }

    if !overwrite {
        eprintln!("\nAll {round} rounds complete. Every subset produced identical VRF output.");
    }
}
