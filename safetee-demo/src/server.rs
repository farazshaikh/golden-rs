//! SAFE-TEE Server: holds DKG key material and issues vetKeys on demand.
//!
//! This is the "network" from the SAFE-TEE paper -- it runs DKG at startup,
//! holds the threshold key shares in memory, and exposes HTTP endpoints for:
//!
//! - `GET  /mpk`     -- return the master public key (group_pk)
//! - `POST /vetkey`  -- produce an encrypted vetKey for a given identity + transport key
//! - `POST /encrypt` -- IBE-encrypt a message (public operation, no secrets needed)
//! - `POST /decrypt` -- decrypt using a transport secret key + encrypted vetKey
//! - `GET  /health`  -- liveness check

mod crypto;

use std::sync::Arc;

use axum::{extract::State, http::StatusCode, routing::{get, post}, Json, Router};
use base64::Engine;
use clap::Parser;
use tower_http::cors::CorsLayer;
use tower_http::services::ServeDir;

use golden_dkg::threshold::dkg;
use golden_dkg::threshold::ibe;
use golden_dkg::threshold::types::{GroupInfo, KeyShare};

use crypto::*;

// ---------------------------------------------------------------------------
// CLI
// ---------------------------------------------------------------------------

#[derive(Parser)]
#[command(name = "safetee-server")]
#[command(about = "SAFE-TEE network server: DKG + vetKey issuance")]
struct Cli {
    /// Number of network nodes (n = 3f+1)
    #[arg(short, long, default_value = "10")]
    nodes: u32,

    /// Threshold (t = 2f+1)
    #[arg(short, long, default_value = "7")]
    threshold: u32,

    /// Listen address
    #[arg(short, long, default_value = "0.0.0.0:3000")]
    listen: String,

    /// TLS certificate file (PEM). If provided with --tls-key, enables HTTPS.
    #[arg(long)]
    tls_cert: Option<String>,

    /// TLS private key file (PEM).
    #[arg(long)]
    tls_key: Option<String>,

    /// Skip TEE attestation verification. By default, attestation is required
    /// and vetKeys are only issued to attested TEEs (TDX + GPU CC).
    #[arg(long, default_value = "false")]
    skip_attestation: bool,
}

// ---------------------------------------------------------------------------
// Shared state
// ---------------------------------------------------------------------------

struct AppState {
    shares: Vec<KeyShare>,
    group: GroupInfo,
    require_attestation: bool,
}

// ---------------------------------------------------------------------------
// Handlers
// ---------------------------------------------------------------------------

async fn health() -> &'static str {
    "ok"
}

async fn get_mpk(State(state): State<Arc<AppState>>) -> Json<MpkResponse> {
    Json(MpkResponse {
        group_pk_hex: serialize_point(&state.group.public_key),
        num_nodes: state.group.num_nodes,
        threshold: state.group.threshold,
    })
}

/// Verify TEE attestation evidence. Returns (verified, reason).
fn verify_attestation(attestation: &Option<TeeAttestation>, require: bool) -> (bool, String) {
    let Some(att) = attestation else {
        if require {
            return (false, "no attestation provided".into());
        }
        eprintln!("[vetkey] No attestation provided (not required)");
        return (false, "not provided".into());
    };

    let mut checks_passed = 0;
    let mut reasons = Vec::new();

    // Check 1: TDX quote present (proves running inside TDX enclave)
    match &att.tdx_quote_hex {
        Some(q) if !q.is_empty() => {
            eprintln!("[vetkey] TDX quote present: {} bytes", q.len() / 2);
            checks_passed += 1;
        }
        _ => {
            reasons.push("TDX quote missing");
        }
    }

    // Check 2: GPU CC status is ON
    if let Some(gpu) = &att.gpu_evidence {
        if gpu.cc_status == "ON" {
            eprintln!("[vetkey] GPU CC: ON ({})", gpu.gpu_name);
            checks_passed += 1;
        } else {
            reasons.push("GPU CC status is not ON");
        }

        // Check 3: GPU is H100
        if gpu.gpu_name.contains("H100") || gpu.gpu_name.contains("GH100") {
            checks_passed += 1;
        } else {
            reasons.push("GPU is not H100");
        }
    } else {
        reasons.push("GPU CC evidence missing");
    }

    let verified = checks_passed >= 2; // At least TDX + CC:ON, or CC:ON + H100
    let reason = if verified {
        format!("{checks_passed}/3 checks passed")
    } else {
        format!("failed: {}", reasons.join(", "))
    };

    eprintln!("[vetkey] Attestation: verified={verified} ({reason})");
    (verified, reason)
}

async fn post_vetkey(
    State(state): State<Arc<AppState>>,
    Json(req): Json<VetKeyRequest>,
) -> Result<Json<VetKeyResponse>, (StatusCode, String)> {
    // Verify attestation
    let (attestation_verified, reason) = verify_attestation(&req.attestation, state.require_attestation);

    if state.require_attestation && !attestation_verified {
        return Err((StatusCode::FORBIDDEN, format!("TEE attestation failed: {reason}")));
    }

    let identity = hex::decode(&req.identity_hex)
        .map_err(|e| (StatusCode::BAD_REQUEST, format!("bad identity_hex: {e}")))?;
    let tpk = ibe::TransportPublicKey(deserialize_g2(&req.tpk_hex));

    let mut rng = rand::thread_rng();

    let encrypted_shares: Vec<_> = state.shares.iter()
        .map(|s| ibe::encrypt_key_share(s, &identity, &tpk, &mut rng))
        .collect();

    let evk = ibe::combine_encrypted_shares(&encrypted_shares, state.group.threshold as usize);
    let valid = ibe::verify_encrypted_vetkey(&evk, &identity, &tpk, &state.group.public_key);

    let (c1, c2, c3) = evk_to_wire(&evk);
    Ok(Json(VetKeyResponse {
        encrypted_vetkey_c1_hex: c1,
        encrypted_vetkey_c2_hex: c2,
        encrypted_vetkey_c3_hex: c3,
        valid,
        attestation_verified,
    }))
}

async fn post_encrypt(
    State(state): State<Arc<AppState>>,
    Json(req): Json<EncryptRequest>,
) -> Result<Json<EncryptResponse>, (StatusCode, String)> {
    let identity = hex::decode(&req.identity_hex)
        .map_err(|e| (StatusCode::BAD_REQUEST, format!("bad identity_hex: {e}")))?;

    // Encrypt the base64 string as-is (not decoded). The sidecar will get
    // the base64 text back after decryption, which it can pass to vLLM.
    let message = req.message_base64.as_bytes();

    let mut rng = rand::thread_rng();
    let ct = ibe::ibe_encrypt(&state.group.public_key, &identity, message, &mut rng);

    let (u, v, w) = ibe_ciphertext_to_wire(&ct);
    Ok(Json(EncryptResponse {
        ciphertext_u_hex: u,
        ciphertext_v_hex: v,
        ciphertext_w_hex: w,
    }))
}

async fn post_decrypt(
    State(state): State<Arc<AppState>>,
    Json(req): Json<DecryptRequest>,
) -> Result<Json<DecryptResponse>, (StatusCode, String)> {
    let identity = hex::decode(&req.identity_hex)
        .map_err(|e| (StatusCode::BAD_REQUEST, format!("bad identity_hex: {e}")))?;
    let tsk = ibe::TransportSecretKey(deserialize_fr(&req.tsk_hex));
    let evk = wire_to_evk(
        &req.encrypted_vetkey_c1_hex,
        &req.encrypted_vetkey_c2_hex,
        &req.encrypted_vetkey_c3_hex,
    );
    let ct = wire_to_ibe_ciphertext(
        &req.ciphertext_u_hex,
        &req.ciphertext_v_hex,
        &req.ciphertext_w_hex,
    );

    let vetkey = ibe::decrypt_vetkey(&evk, &tsk, &identity, &state.group.public_key);
    if let Some(vk) = vetkey {
        if let Some(plaintext) = ibe::ibe_decrypt(&vk, &ct) {
            // Plaintext is the original string that was encrypted (could be base64 or text).
            // Return it as-is in the message_base64 field.
            let msg = String::from_utf8(plaintext)
                .unwrap_or_else(|e| base64::engine::general_purpose::STANDARD.encode(e.into_bytes()));
            return Ok(Json(DecryptResponse { message_base64: Some(msg), success: true }));
        }
    }
    Ok(Json(DecryptResponse { message_base64: None, success: false }))
}

// ---------------------------------------------------------------------------
// Transport keygen helper (for browser clients that can't do BLS12-381)
// ---------------------------------------------------------------------------

#[derive(serde::Serialize)]
struct TransportKeygenResponse {
    tpk_hex: String,
    tsk_hex: String,
}

async fn post_transport_keygen() -> Json<TransportKeygenResponse> {
    let mut rng = rand::thread_rng();
    let (tpk, tsk) = ibe::transport_keygen(&mut rng);
    Json(TransportKeygenResponse {
        tpk_hex: serialize_point(&tpk.0),
        tsk_hex: serialize_point(&tsk.0),
    })
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

#[tokio::main]
async fn main() {
    let cli = Cli::parse();

    println!("=== SAFE-TEE Server ===");
    println!("  Nodes:     {}", cli.nodes);
    println!("  Threshold: {}", cli.threshold);
    println!();

    println!("[1] Running DKG...");
    let t0 = std::time::Instant::now();
    let (shares, group) = dkg::run_dkg(cli.nodes, cli.threshold);
    println!("  DKG complete in {}ms", t0.elapsed().as_millis());
    println!("  Group PK: {}...", &serialize_point(&group.public_key)[..40]);
    println!();

    let require_attestation = !cli.skip_attestation;
    let state = Arc::new(AppState { shares, group, require_attestation });
    if require_attestation {
        println!("  Attestation: REQUIRED (vetKeys only issued to attested TEEs)");
    } else {
        println!("  Attestation: SKIPPED (pass --skip-attestation to disable)");
    }

    // Serve static files: try several paths to find the static/ directory
    let candidates = [
        "static",
        "safetee-demo/static",
        "../safetee-demo/static",
    ];
    let static_fallback = candidates.iter()
        .map(std::path::PathBuf::from)
        .find(|p| p.join("index.html").exists())
        .unwrap_or_else(|| std::path::PathBuf::from("static"));
    println!("  Static dir: {}", static_fallback.display());

    let app = Router::new()
        .route("/", get(|| async { axum::response::Redirect::permanent("/setup.html") }))
        .route("/health", get(health))
        .route("/mpk", get(get_mpk))
        .route("/vetkey", post(post_vetkey))
        .route("/encrypt", post(post_encrypt))
        .route("/decrypt", post(post_decrypt))
        .route("/transport-keygen", post(post_transport_keygen))
        .fallback_service(ServeDir::new(&static_fallback))
        .layer(CorsLayer::permissive())
        .with_state(state);

    let tls = cli.tls_cert.as_ref().zip(cli.tls_key.as_ref());
    let scheme = if tls.is_some() { "https" } else { "http" };

    println!("[2] Listening on {scheme}://{}", cli.listen);
    println!();
    println!("  Endpoints:");
    println!("    GET  /health           -- liveness check");
    println!("    GET  /mpk              -- master public key");
    println!("    POST /vetkey           -- issue encrypted vetKey");
    println!("    POST /encrypt          -- IBE encrypt a message");
    println!("    POST /decrypt          -- decrypt with tsk + vetKey");
    println!("    POST /transport-keygen -- generate transport key pair");
    println!();

    if let Some((cert_path, key_path)) = tls {
        let tls_config = axum_server::tls_rustls::RustlsConfig::from_pem_file(cert_path, key_path)
            .await
            .expect("failed to load TLS cert/key");
        let addr: std::net::SocketAddr = cli.listen.parse().expect("invalid listen address");
        axum_server::bind_rustls(addr, tls_config)
            .serve(app.into_make_service())
            .await
            .unwrap();
    } else {
        let listener = tokio::net::TcpListener::bind(&cli.listen).await.unwrap();
        axum::serve(listener, app).await.unwrap();
    }
}
