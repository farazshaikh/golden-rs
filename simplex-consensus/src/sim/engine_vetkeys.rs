//! vetKeys IBE demo flow for the Simplex consensus simulation.
//!
//! This module runs a complete vetKeys Identity-Based Encryption cycle
//! using the consensus network's threshold key shares. It is designed
//! to be called periodically (e.g., every Nth view) from the main
//! simulation loop.
//!
//! # Protocol flow (DFINITY vetKeys reference)
//!
//! ```text
//! Step 0: IBE Encrypt -- anyone encrypts a message to an identity
//! Step 1: Transport keygen -- recipient generates ephemeral key pair
//! Step 2: Key share requests -- each node produces encrypted key share
//! Step 3: Verify shares -- verifier checks pairing equations
//! Step 4: Combine shares -- Lagrange interpolation in the exponent
//! Step 5: Decrypt vetKey -- recipient recovers BLS sig using transport key
//! Step 6: Decrypt message -- recipient decrypts IBE ciphertext with vetKey
//! ```
//!
//! # References
//!
//! - vetKeys paper (ePrint 2023/616), Section 2, Figure 1 (protocol flow)
//! - vetKeys paper, Section 5.3, pi_vetbls-agg2 (encrypted key shares)
//! - vetKeys paper, Section 6.2, pi_vetibe (Boneh-Franklin IBE)
//! - DFINITY docs: https://docs.internetcomputer.org/references/vetkeys-overview
//! - NCC audit: threshold_crypto/papers/ncc-vetkeys-audit-2025.pdf

use std::time::Instant;

use ark_bls12_381::G1Affine;
use ark_ec::AffineRepr;
use golden_dkg::threshold::ibe;

use crate::replica::Replica;

/// Result of a vetKeys IBE demo round.
#[derive(Clone, Debug)]
pub struct VetKeysDemoResult {
    /// The identity the message was encrypted to.
    pub identity: String,
    /// The original plaintext message.
    pub message: String,
    /// How many nodes produced encrypted key shares.
    pub num_shares: usize,
    /// How many shares passed pairing verification.
    pub num_verified: usize,
    /// Whether the combined encrypted vetKey passed verification.
    pub encrypted_vetkey_valid: bool,
    /// Whether the final IBE decryption succeeded and matched the original.
    pub decryption_success: bool,
    /// Total wall-clock time for the entire vetKeys round.
    pub latency_ms: f64,
}

/// Run one complete vetKeys IBE demo cycle using the consensus replicas.
///
/// This demonstrates the full protocol:
///
/// 1. **Encrypt** a message to `identity` using the network's group public key
///    (vetKeys paper, Section 6.2, pi_vetibe, Figure 11)
///
/// 2. **Transport keygen**: recipient generates ephemeral ElGamal key pair
///    (vetKeys paper, Section 2, TKG algorithm)
///
/// 3. **Key share requests**: each replica produces an encrypted key share
///    (DFINITY API: `vetkd_derive_key` per-node behavior)
///
/// 4. **Verify + combine**: verify shares via pairing, Lagrange-combine
///    (vetKeys paper, Section 5.3, pi_vetbls-agg2)
///
/// 5. **Decrypt vetKey**: recipient recovers BLS signature
///    (vetKeys paper, Section 5.3: "U decrypts sigma = C3 * C1^{-tsk}")
///
/// 6. **Decrypt message**: recipient uses vetKey to decrypt IBE ciphertext
///    (vetKeys paper, Section 6.2: "On (sid, decrypt, id, C), user U...")
pub fn run_vetkeys_demo(
    replicas: &[Replica],
    group_pk: &G1Affine,
    threshold: usize,
    view: u64,
) -> VetKeysDemoResult {
    let t0 = Instant::now();
    let mut rng = rand::thread_rng();

    // Identity and message for this demo round
    let identity = format!("simplex-view-{view}@demo");
    let message = format!("vetKeys demo at view {view}: threshold decryption works!");

    // ── Step 0: IBE Encrypt ──────────────────────────────────────────────
    // Anyone can do this with just the group public key -- no network needed.
    // (vetKeys paper, Section 6.2, pi_vetibe, Figure 11)
    let ciphertext = ibe::ibe_encrypt(
        group_pk,
        identity.as_bytes(),
        message.as_bytes(),
        &mut rng,
    );

    // ── Step 1: Transport keygen ─────────────────────────────────────────
    // Recipient generates ephemeral key pair for secure delivery.
    // (vetKeys paper, Section 2, p.6: TKG() -> (tpk, tsk))
    let (tpk, tsk) = ibe::transport_keygen(&mut rng);

    // ── Step 2: Key share requests ───────────────────────────────────────
    // Each replica computes encrypted key share using its threshold share.
    // (DFINITY API: vetkd_derive_key node-level behavior)
    // (vetKeys paper, Section 5.3, pi_vetbls-agg2, Figure 9)
    let encrypted_shares: Vec<_> = replicas
        .iter()
        .map(|r| r.vetkd_encrypted_key_share(identity.as_bytes(), &tpk))
        .collect();
    let num_shares = encrypted_shares.len();

    // ── Step 3: Verify shares ────────────────────────────────────────────
    // Verifier checks each share via pairing equations.
    // (vetKeys paper, Section 5.3, Figure 9: "combiner checks...")
    let mut num_verified = 0;
    for (i, eks) in encrypted_shares.iter().enumerate() {
        let pk_i = (G1Affine::generator() * replicas[i].key_share().secret).into();
        if ibe::verify_encrypted_key_share(eks, identity.as_bytes(), &tpk, &pk_i) {
            num_verified += 1;
        }
    }

    // ── Step 4: Combine shares ───────────────────────────────────────────
    // Lagrange interpolation in the exponent on the encrypted shares.
    // (vetKeys paper, Section 5.3, Figure 9: "prod C_{i,k}^{Lambda_i}")
    let evk = ibe::combine_encrypted_shares(&encrypted_shares, threshold);

    // Verify the combined encrypted vetKey.
    let encrypted_vetkey_valid = ibe::verify_encrypted_vetkey(
        &evk,
        identity.as_bytes(),
        &tpk,
        group_pk,
    );

    // ── Step 5: Decrypt vetKey ───────────────────────────────────────────
    // Recipient recovers the BLS signature using transport secret key.
    // (vetKeys paper, Section 5.3, Figure 9: "sigma = C3 * C1^{-tsk}")
    let vetkey = ibe::decrypt_vetkey(
        &evk,
        &tsk,
        identity.as_bytes(),
        group_pk,
    );

    // ── Step 6: Decrypt message ──────────────────────────────────────────
    // Recipient uses vetKey to decrypt the IBE ciphertext.
    // (vetKeys paper, Section 6.2, Figure 11: "On (sid, decrypt, id, C)...")
    let decryption_success = if let Some(ref vk) = vetkey {
        match ibe::ibe_decrypt(vk, &ciphertext) {
            Some(recovered) => recovered == message.as_bytes(),
            None => false,
        }
    } else {
        false
    };

    let latency_ms = t0.elapsed().as_secs_f64() * 1000.0;

    VetKeysDemoResult {
        identity,
        message,
        num_shares,
        num_verified,
        encrypted_vetkey_valid,
        decryption_success,
        latency_ms,
    }
}

/// Format a VetKeysDemoResult as a compact one-line display string.
pub fn format_vetkeys_result(r: &VetKeysDemoResult) -> String {
    let status = if r.decryption_success { "OK" } else { "FAIL" };
    format!(
        "vetKeys [{}]: shares={}/{} combined={} decrypt={} ({:.1}ms)",
        r.identity,
        r.num_verified,
        r.num_shares,
        if r.encrypted_vetkey_valid { "valid" } else { "INVALID" },
        status,
        r.latency_ms,
    )
}
