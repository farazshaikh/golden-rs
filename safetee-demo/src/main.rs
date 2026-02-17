//! SAFE-TEE Demo: vetKeys key delivery for GCP Confidential VMs.
//!
//! This binary implements the SAFE-TEE key delivery protocol:
//!
//! 1. `keygen`   -- Generate transport key pair (run inside TEE)
//! 2. `network`  -- Run DKG, encrypt a secret, produce encrypted vetKey (run locally)
//! 3. `decrypt`  -- Decrypt vetKey + IBE ciphertext using transport secret key (run inside TEE)
//!
//! The three subcommands are designed to run on different machines:
//!   - `keygen` and `decrypt` run inside the GCP Confidential VM (TEE)
//!   - `network` runs on the local machine (simulating the SAFE-TEE network)
//!
//! Data is exchanged as hex-encoded JSON files transferred via SCP.
//!
//! # Protocol Flow (SAFE-TEE Whitepaper, Section 7.3)
//!
//! ```text
//! TEE:     keygen -> tpk (transport public key)
//!                     |
//!                     v  (SCP to local)
//! Network: DKG -> group_pk
//!          ibe_encrypt(group_pk, tee_identity, secret) -> ciphertext
//!          encrypt_key_shares(shares, tee_identity, tpk) -> encrypted_shares
//!          combine + verify -> encrypted_vetkey
//!                     |
//!                     v  (SCP to TEE)
//! TEE:     decrypt_vetkey(tsk, encrypted_vetkey) -> vetkey
//!          ibe_decrypt(vetkey, ciphertext) -> secret
//! ```

use std::fs;
use std::path::PathBuf;

use ark_bls12_381::{G1Affine, G2Affine};
use ark_ec::AffineRepr;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use clap::{Parser, Subcommand};
use serde::{Deserialize, Serialize};

use golden_dkg::threshold::dkg;
use golden_dkg::threshold::ibe;

// ---------------------------------------------------------------------------
// CLI
// ---------------------------------------------------------------------------

#[derive(Parser)]
#[command(name = "safetee-demo")]
#[command(about = "SAFE-TEE: vetKeys key delivery for Confidential VMs")]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Generate transport key pair (run inside the TEE).
    /// Outputs tpk (public) to a file and keeps tsk (secret) in a separate file.
    Keygen {
        /// Output directory for key files
        #[arg(short, long, default_value = ".")]
        output: PathBuf,
    },

    /// Run the SAFE-TEE network side: DKG + encrypt secret + produce encrypted vetKey.
    /// Reads tpk from file, outputs encrypted_vetkey + ciphertext + group_pk.
    Network {
        /// Path to transport public key file (from keygen)
        #[arg(short, long)]
        tpk_file: PathBuf,

        /// TEE identity string (e.g., "tee://cc-h100-tdx-1@us-central1-a")
        #[arg(short, long, default_value = "tee://cc-h100-tdx-1@us-central1-a")]
        identity: String,

        /// Secret message to encrypt and deliver to the TEE
        #[arg(short, long, default_value = "SAFE-TEE: This secret was delivered via vetKeys IBE to a GCP Confidential VM with H100 CC-On.")]
        secret: String,

        /// Number of network nodes (n = 3f+1)
        #[arg(short, long, default_value = "10")]
        nodes: u32,

        /// Threshold (t = 2f+1)
        #[arg(long, default_value = "7")]
        threshold: u32,

        /// Output directory for network artifacts
        #[arg(short, long, default_value = ".")]
        output: PathBuf,
    },

    /// Decrypt the vetKey and IBE ciphertext using the transport secret key (run inside TEE).
    /// Reads tsk, encrypted_vetkey, ciphertext, and group_pk from files.
    Decrypt {
        /// Directory containing all artifact files
        #[arg(short, long, default_value = ".")]
        artifacts: PathBuf,
    },
}

// ---------------------------------------------------------------------------
// Serializable wire types (hex-encoded for easy SCP transfer)
// ---------------------------------------------------------------------------

#[derive(Serialize, Deserialize)]
struct TransportPublicKeyFile {
    tpk_hex: String,
}

#[derive(Serialize, Deserialize)]
struct TransportSecretKeyFile {
    tsk_hex: String,
}

#[derive(Serialize, Deserialize)]
struct NetworkArtifacts {
    group_pk_hex: String,
    identity: String,
    encrypted_vetkey_c1_hex: String,
    encrypted_vetkey_c2_hex: String,
    encrypted_vetkey_c3_hex: String,
    ciphertext_u_hex: String,
    ciphertext_v_hex: String,
    ciphertext_w_hex: String,
    num_nodes: u32,
    threshold: u32,
    num_shares_verified: usize,
    encrypted_vetkey_valid: bool,
}

#[derive(Serialize, Deserialize)]
struct DecryptionResult {
    identity: String,
    vetkey_valid: bool,
    decrypted_secret: Option<String>,
    success: bool,
}

// ---------------------------------------------------------------------------
// Serialization helpers
// ---------------------------------------------------------------------------

fn serialize_point<T: CanonicalSerialize>(p: &T) -> String {
    let mut buf = Vec::new();
    p.serialize_compressed(&mut buf).expect("serialize point");
    hex::encode(&buf)
}

fn deserialize_g1(hex_str: &str) -> G1Affine {
    let bytes = hex::decode(hex_str).expect("hex decode G1");
    G1Affine::deserialize_compressed(&bytes[..]).expect("deserialize G1")
}

fn deserialize_g2(hex_str: &str) -> G2Affine {
    let bytes = hex::decode(hex_str).expect("hex decode G2");
    G2Affine::deserialize_compressed(&bytes[..]).expect("deserialize G2")
}

// ---------------------------------------------------------------------------
// Subcommands
// ---------------------------------------------------------------------------

fn cmd_keygen(output: PathBuf) {
    println!("=== SAFE-TEE: Transport Key Generation (TEE side) ===");
    println!();

    let mut rng = rand::thread_rng();
    let (tpk, tsk) = ibe::transport_keygen(&mut rng);

    let tpk_hex = serialize_point(&tpk.0);
    let tsk_hex = serialize_point(&tsk.0);

    // Write tpk (public -- safe to transfer)
    let tpk_file = output.join("tpk.json");
    let tpk_data = TransportPublicKeyFile { tpk_hex: tpk_hex.clone() };
    fs::write(&tpk_file, serde_json::to_string_pretty(&tpk_data).unwrap())
        .expect("write tpk.json");

    // Write tsk (SECRET -- stays on TEE)
    let tsk_file = output.join("tsk.json");
    let tsk_data = TransportSecretKeyFile { tsk_hex };
    fs::write(&tsk_file, serde_json::to_string_pretty(&tsk_data).unwrap())
        .expect("write tsk.json");

    println!("  Transport public key (tpk): {}", &tpk_hex[..40]);
    println!("  tpk written to: {}", tpk_file.display());
    println!("  tsk written to: {} (SECRET -- do not transfer!)", tsk_file.display());
    println!();
    println!("Next: SCP tpk.json to the local machine and run `safetee-demo network`.");
}

fn cmd_network(tpk_file: PathBuf, identity: String, secret: String, nodes: u32, threshold: u32, output: PathBuf) {
    println!("=== SAFE-TEE: Network Side (DKG + vetKey Derivation) ===");
    println!();
    println!("  Nodes:     {nodes}");
    println!("  Threshold: {threshold}");
    println!("  Identity:  {identity}");
    println!("  Secret:    {} bytes", secret.len());
    println!();

    // Read transport public key
    println!("[1] Reading transport public key from {}...", tpk_file.display());
    let tpk_json: TransportPublicKeyFile =
        serde_json::from_str(&fs::read_to_string(&tpk_file).expect("read tpk.json"))
            .expect("parse tpk.json");
    let tpk = ibe::TransportPublicKey(deserialize_g2(&tpk_json.tpk_hex));
    println!("  tpk: {}...", &tpk_json.tpk_hex[..40]);

    // Run DKG
    println!();
    println!("[2] Running Distributed Key Generation (n={nodes}, t={threshold})...");
    let t0 = std::time::Instant::now();
    let (shares, group) = dkg::run_dkg(nodes, threshold);
    let dkg_ms = t0.elapsed().as_millis();
    println!("  DKG complete in {dkg_ms}ms");
    println!("  Group public key: {}...", &serialize_point(&group.public_key)[..40]);

    // IBE Encrypt the secret
    println!();
    println!("[3] IBE encrypting secret to identity '{identity}'...");
    let mut rng = rand::thread_rng();
    let ciphertext = ibe::ibe_encrypt(
        &group.public_key,
        identity.as_bytes(),
        secret.as_bytes(),
        &mut rng,
    );
    println!("  Ciphertext: u={}..., v={} bytes, w={} bytes",
        &serialize_point(&ciphertext.u)[..20],
        ciphertext.v.len(),
        ciphertext.w.len(),
    );

    // Produce encrypted key shares
    println!();
    println!("[4] Producing encrypted key shares from {nodes} nodes...");
    let t0 = std::time::Instant::now();
    let encrypted_shares: Vec<_> = shares
        .iter()
        .map(|s| ibe::encrypt_key_share(s, identity.as_bytes(), &tpk, &mut rng))
        .collect();

    // Verify each share
    let mut num_verified = 0;
    for (i, eks) in encrypted_shares.iter().enumerate() {
        let pk_i: G1Affine = (G1Affine::generator() * shares[i].secret).into();
        if ibe::verify_encrypted_key_share(eks, identity.as_bytes(), &tpk, &pk_i) {
            num_verified += 1;
        }
    }
    println!("  Verified: {num_verified}/{nodes} shares pass pairing checks");

    // Combine shares
    println!();
    println!("[5] Combining {threshold} shares via Lagrange interpolation...");
    let evk = ibe::combine_encrypted_shares(&encrypted_shares, threshold as usize);
    let evk_valid = ibe::verify_encrypted_vetkey(&evk, identity.as_bytes(), &tpk, &group.public_key);
    let derive_ms = t0.elapsed().as_millis();
    println!("  Encrypted vetKey valid: {evk_valid}");
    println!("  Key derivation took {derive_ms}ms");

    // Write artifacts
    let artifacts = NetworkArtifacts {
        group_pk_hex: serialize_point(&group.public_key),
        identity: identity.clone(),
        encrypted_vetkey_c1_hex: serialize_point(&evk.c1),
        encrypted_vetkey_c2_hex: serialize_point(&evk.c2),
        encrypted_vetkey_c3_hex: serialize_point(&evk.c3),
        ciphertext_u_hex: serialize_point(&ciphertext.u),
        ciphertext_v_hex: hex::encode(&ciphertext.v),
        ciphertext_w_hex: hex::encode(&ciphertext.w),
        num_nodes: nodes,
        threshold,
        num_shares_verified: num_verified,
        encrypted_vetkey_valid: evk_valid,
    };

    let artifacts_file = output.join("network_artifacts.json");
    fs::write(&artifacts_file, serde_json::to_string_pretty(&artifacts).unwrap())
        .expect("write network_artifacts.json");

    println!();
    println!("  Artifacts written to: {}", artifacts_file.display());
    println!();
    println!("=== Network side complete ===");
    println!();
    println!("Next: SCP network_artifacts.json to the TEE and run `safetee-demo decrypt`.");
}

fn cmd_decrypt(artifacts_dir: PathBuf) {
    println!("=== SAFE-TEE: Decryption (TEE side) ===");
    println!();

    // Read transport secret key
    let tsk_file = artifacts_dir.join("tsk.json");
    println!("[1] Reading transport secret key from {}...", tsk_file.display());
    let tsk_json: TransportSecretKeyFile =
        serde_json::from_str(&fs::read_to_string(&tsk_file).expect("read tsk.json"))
            .expect("parse tsk.json");
    let tsk_bytes = hex::decode(&tsk_json.tsk_hex).expect("hex decode tsk");
    let tsk_scalar = ark_bls12_381::Fr::deserialize_compressed(&tsk_bytes[..])
        .expect("deserialize tsk scalar");
    let tsk = ibe::TransportSecretKey(tsk_scalar);

    // Read network artifacts
    let artifacts_file = artifacts_dir.join("network_artifacts.json");
    println!("[2] Reading network artifacts from {}...", artifacts_file.display());
    let artifacts: NetworkArtifacts =
        serde_json::from_str(&fs::read_to_string(&artifacts_file).expect("read artifacts"))
            .expect("parse artifacts");

    let group_pk = deserialize_g1(&artifacts.group_pk_hex);
    let identity = &artifacts.identity;

    let evk = ibe::EncryptedVetKey {
        c1: deserialize_g1(&artifacts.encrypted_vetkey_c1_hex),
        c2: deserialize_g2(&artifacts.encrypted_vetkey_c2_hex),
        c3: deserialize_g2(&artifacts.encrypted_vetkey_c3_hex),
    };

    let ciphertext = ibe::IBECiphertext {
        u: deserialize_g1(&artifacts.ciphertext_u_hex),
        v: hex::decode(&artifacts.ciphertext_v_hex).expect("hex decode v"),
        w: hex::decode(&artifacts.ciphertext_w_hex).expect("hex decode w"),
    };

    println!("  Identity:  {identity}");
    println!("  Network:   n={}, t={}", artifacts.num_nodes, artifacts.threshold);
    println!("  Shares verified: {}", artifacts.num_shares_verified);
    println!("  Encrypted vetKey valid: {}", artifacts.encrypted_vetkey_valid);

    // Decrypt vetKey using transport secret key
    println!();
    println!("[3] Decrypting vetKey using transport secret key...");
    let t0 = std::time::Instant::now();
    let vetkey = ibe::decrypt_vetkey(&evk, &tsk, identity.as_bytes(), &group_pk);
    let vetkey_valid = vetkey.is_some();
    println!("  vetKey decryption: {}", if vetkey_valid { "SUCCESS" } else { "FAILED" });

    // Decrypt IBE ciphertext
    let (decrypted_secret, success) = if let Some(ref vk) = vetkey {
        println!();
        println!("[4] Decrypting IBE ciphertext with vetKey...");
        match ibe::ibe_decrypt(vk, &ciphertext) {
            Some(plaintext) => {
                let secret = String::from_utf8_lossy(&plaintext).to_string();
                println!("  IBE decryption: SUCCESS");
                println!();
                println!("  ┌─────────────────────────────────────────────────┐");
                println!("  │ DECRYPTED SECRET:                               │");
                println!("  │ {}│", format!("{:<48}", &secret[..std::cmp::min(secret.len(), 48)]));
                if secret.len() > 48 {
                    for chunk in secret[48..].as_bytes().chunks(48) {
                        let s = String::from_utf8_lossy(chunk);
                        println!("  │ {}│", format!("{:<48}", s));
                    }
                }
                println!("  └─────────────────────────────────────────────────┘");
                (Some(secret), true)
            }
            None => {
                println!("  IBE decryption: FAILED (CCA check or wrong identity)");
                (None, false)
            }
        }
    } else {
        (None, false)
    };

    let decrypt_ms = t0.elapsed().as_millis();

    // Write result
    let result = DecryptionResult {
        identity: identity.clone(),
        vetkey_valid,
        decrypted_secret,
        success,
    };

    let result_file = artifacts_dir.join("decryption_result.json");
    fs::write(&result_file, serde_json::to_string_pretty(&result).unwrap())
        .expect("write decryption_result.json");

    println!();
    println!("  Decryption took {decrypt_ms}ms");
    println!("  Result written to: {}", result_file.display());
    println!();

    if success {
        println!("=== SAFE-TEE Demo Complete: Secret successfully delivered to TEE via vetKeys! ===");
    } else {
        println!("=== SAFE-TEE Demo FAILED: Could not decrypt secret ===");
        std::process::exit(1);
    }
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

fn main() {
    let cli = Cli::parse();
    match cli.command {
        Commands::Keygen { output } => cmd_keygen(output),
        Commands::Network { tpk_file, identity, secret, nodes, threshold, output } => {
            cmd_network(tpk_file, identity, secret, nodes, threshold, output)
        }
        Commands::Decrypt { artifacts } => cmd_decrypt(artifacts),
    }
}
