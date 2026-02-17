//! SAFE-TEE Inference Sidecar: runs on the TDX VM next to vLLM.
//!
//! Collects Intel TDX + NVIDIA H100 CC attestation evidence on startup
//! and attaches it to every vetKey request. Caches vetKeys by nonce.

mod crypto;

use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;

use axum::extract::State;
use axum::routing::{get, post};
use axum::Router;
use clap::Parser;
use tower_http::cors::CorsLayer;

use golden_dkg::threshold::ibe;

use crypto::*;

#[derive(Parser)]
#[command(name = "safetee-sidecar")]
#[command(about = "SAFE-TEE inference sidecar: encrypted VLM proxy on TDX VM")]
struct Cli {
    #[arg(short, long, default_value = "http://localhost:8000")]
    vllm_url: String,
    #[arg(short, long, default_value = "Qwen/Qwen3-VL-30B-A3B-Instruct")]
    model: String,
    #[arg(short, long, default_value = "0.0.0.0:3001")]
    listen: String,
    #[arg(long)]
    tls_cert: Option<String>,
    #[arg(long)]
    tls_key: Option<String>,
}

// ---------------------------------------------------------------------------
// TEE attestation evidence collection
// ---------------------------------------------------------------------------

/// Collect Intel TDX quote from the configfs-tsm interface.
/// Returns hex-encoded quote bytes, or None if not available.
fn collect_tdx_quote() -> Option<String> {
    // Try configfs-tsm (Linux 6.7+): /sys/kernel/config/tsm/report/
    let tsm_path = std::path::Path::new("/sys/kernel/config/tsm/report");
    if tsm_path.exists() {
        // Create a report entry with a nonce
        let entry = tsm_path.join("safetee-attest");
        let _ = std::fs::create_dir_all(&entry);
        // Write 64-byte nonce (all zeros for demo -- production would use random)
        let _ = std::fs::write(entry.join("inblob"), vec![0u8; 64]);
        // Read the generated quote
        if let Ok(quote_bytes) = std::fs::read(entry.join("outblob")) {
            if !quote_bytes.is_empty() {
                eprintln!("[attest] TDX quote collected via configfs-tsm: {} bytes", quote_bytes.len());
                return Some(hex::encode(&quote_bytes));
            }
        }
    }

    // Fallback: try /dev/tdx_guest (older kernels)
    if std::path::Path::new("/dev/tdx_guest").exists() {
        // The device exists -- we can't easily do the ioctl from pure Rust without
        // a dedicated crate, but its presence proves we're in a TDX VM.
        eprintln!("[attest] TDX device /dev/tdx_guest detected (quote collection requires configfs-tsm)");
        return Some("tdx_guest_device_present".to_string());
    }

    // Check dmesg for TDX evidence
    if let Ok(output) = std::process::Command::new("dmesg")
        .output()
    {
        let dmesg = String::from_utf8_lossy(&output.stdout);
        if dmesg.contains("tdx") || dmesg.contains("TDX") {
            eprintln!("[attest] TDX evidence found in dmesg");
            return Some("tdx_dmesg_evidence".to_string());
        }
    }

    eprintln!("[attest] No TDX attestation available (not a TDX VM?)");
    None
}

/// Collect NVIDIA GPU CC evidence by parsing nvidia-smi output.
fn collect_gpu_cc_evidence() -> Option<GpuCcEvidence> {
    let cc_output = std::process::Command::new("sudo")
        .args(["nvidia-smi", "conf-compute", "-f"])
        .output()
        .ok()?;
    let cc_text = String::from_utf8_lossy(&cc_output.stdout);
    let cc_status = if cc_text.contains("ON") { "ON" } else if cc_text.contains("OFF") { "OFF" } else { return None; }.to_string();

    // Query full GPU details: name, driver, uuid, vbios, serial
    let query_output = std::process::Command::new("nvidia-smi")
        .args(["--query-gpu=name,driver_version,uuid,vbios_version,serial", "--format=csv,noheader,nounits"])
        .output()
        .ok()?;
    let query_text = String::from_utf8_lossy(&query_output.stdout);
    let parts: Vec<&str> = query_text.trim().splitn(5, ", ").collect();

    let (gpu_name, driver_version, gpu_uuid, vbios_version, serial) = if parts.len() >= 5 {
        (parts[0].to_string(), parts[1].to_string(), parts[2].to_string(), parts[3].to_string(), parts[4].to_string())
    } else {
        // Fallback for CC mode where nvidia-smi query may fail
        let driver = std::fs::read_to_string("/proc/driver/nvidia/version")
            .ok()
            .and_then(|s| s.split_whitespace().find(|w| w.chars().next().map_or(false, |c| c.is_ascii_digit())).map(|s| s.to_string()))
            .unwrap_or_else(|| "unknown".to_string());
        let lspci = std::process::Command::new("lspci").output().ok()
            .map(|o| String::from_utf8_lossy(&o.stdout).to_string()).unwrap_or_default();
        let gpu = lspci.lines().find(|l| l.contains("NVIDIA"))
            .map(|l| l.split(": ").last().unwrap_or("NVIDIA GPU").to_string())
            .unwrap_or_else(|| "NVIDIA GPU".to_string());
        (gpu, driver, "unknown".to_string(), "unknown".to_string(), "unknown".to_string())
    };

    // GSP firmware version
    let gsp_firmware = std::fs::read_dir("/lib/firmware/nvidia/")
        .ok()
        .and_then(|mut d| d.next())
        .and_then(|e| e.ok())
        .map(|e| e.file_name().to_string_lossy().to_string())
        .unwrap_or_else(|| "unknown".to_string());

    eprintln!("[attest] GPU: {gpu_name} | CC:{cc_status} | driver:{driver_version} | UUID:{gpu_uuid} | vBIOS:{vbios_version} | GSP:{gsp_firmware}");

    Some(GpuCcEvidence { cc_status, gpu_name, driver_version, gpu_uuid, vbios_version, serial, gsp_firmware })
}

/// Collect Intel TDX evidence: Secure Boot certs and TDX device info.
fn collect_tdx_evidence() -> Option<TdxEvidence> {
    let tdx_device = if std::path::Path::new("/dev/tdx_guest").exists() {
        "/dev/tdx_guest".to_string()
    } else {
        String::new()
    };

    // Check dmesg for TDX activation
    let dmesg = std::process::Command::new("sudo").args(["dmesg"]).output().ok()
        .map(|o| String::from_utf8_lossy(&o.stdout).to_string())
        .unwrap_or_default();
    let tdx_active = dmesg.contains("Intel TDX") || dmesg.contains("confidential virtualization tdx");

    // Extract Secure Boot X.509 cert names
    let secure_boot_certs: Vec<String> = dmesg.lines()
        .filter(|l| l.contains("Loaded X.509 cert"))
        .filter_map(|l| l.split('\'').nth(1).map(|s| s.to_string()))
        .collect();

    if !tdx_active && tdx_device.is_empty() {
        return None;
    }

    eprintln!("[attest] TDX: active={tdx_active} | device={tdx_device} | secure_boot_certs={}", secure_boot_certs.len());

    Some(TdxEvidence { tdx_active, tdx_device, secure_boot_certs })
}

/// Collect GCP instance metadata from the metadata server.
fn collect_gcp_info() -> Option<GcpInfo> {
    fn gcp_meta(path: &str) -> Option<String> {
        std::process::Command::new("curl")
            .args(["-sf", "-H", "Metadata-Flavor: Google", &format!("http://metadata.google.internal/computeMetadata/v1/{path}")])
            .output()
            .ok()
            .filter(|o| o.status.success())
            .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
    }

    let project = gcp_meta("project/project-id")?;
    let zone_full = gcp_meta("instance/zone").unwrap_or_default();
    let zone = zone_full.rsplit('/').next().unwrap_or(&zone_full).to_string();
    let instance = gcp_meta("instance/name").unwrap_or_else(|| "unknown".to_string());
    let machine_type_full = gcp_meta("instance/machine-type").unwrap_or_default();
    let machine_type = machine_type_full.rsplit('/').next().unwrap_or(&machine_type_full).to_string();

    eprintln!("[attest] GCP: project={project} | zone={zone} | instance={instance} | machine={machine_type}");

    Some(GcpInfo { project, zone, instance, machine_type })
}

/// Collect all TEE attestation evidence. Called once on startup.
fn collect_attestation() -> TeeAttestation {
    eprintln!("[attest] Collecting TEE attestation evidence...");
    let tdx_quote = collect_tdx_quote();
    let tdx_evidence = collect_tdx_evidence();
    let gpu = collect_gpu_cc_evidence();
    let gcp = collect_gcp_info();
    eprintln!("[attest] TDX: {}, GPU CC: {}, GCP: {}",
        if tdx_evidence.is_some() { "available" } else { "not available" },
        gpu.as_ref().map(|g| g.cc_status.as_str()).unwrap_or("not available"),
        gcp.as_ref().map(|g| g.instance.as_str()).unwrap_or("not available"),
    );
    TeeAttestation {
        tdx_quote_hex: tdx_quote,
        tdx_evidence,
        gpu_evidence: gpu,
        gcp_info: gcp,
    }
}

// ---------------------------------------------------------------------------
// State and handlers
// ---------------------------------------------------------------------------

#[derive(Clone)]
struct CachedVetKey {
    tsk_hex: String,
    evk_c1_hex: String,
    evk_c2_hex: String,
    evk_c3_hex: String,
    mpk_hex: String,
    attestation_verified: bool,
}

#[derive(Clone)]
struct AppState {
    vllm_url: String,
    model: String,
    http: reqwest::Client,
    vetkey_cache: Arc<RwLock<HashMap<String, CachedVetKey>>>,
    attestation: TeeAttestation,
}

async fn health() -> &'static str { "ok" }

async fn post_infer(
    State(state): State<AppState>,
    body: String,
) -> axum::Json<InferResponse> {
    let req: InferRequest = match serde_json::from_str(&body) {
        Ok(r) => r,
        Err(e) => return axum::Json(err_resp(format!("bad JSON: {e}"))),
    };
    match do_infer(state, req).await {
        Ok(r) => axum::Json(r),
        Err(e) => axum::Json(err_resp(e)),
    }
}

fn err_resp(e: String) -> InferResponse {
    InferResponse {
        sidecar_pubkey_hex: String::new(),
        encrypted_response_hex: String::new(),
        success: false,
        error: Some(e),
        cached: false,
        attestation_verified: false,
        tee_attestation: None,
    }
}

async fn get_vetkey_material(
    state: &AppState,
    nonce_hex: &str,
    safetee_url: &str,
) -> Result<(CachedVetKey, bool), String> {
    {
        let cache = state.vetkey_cache.read().await;
        if let Some(cached) = cache.get(nonce_hex) {
            eprintln!("[sidecar] vetKey cache HIT for nonce {}...", &nonce_hex[..16.min(nonce_hex.len())]);
            return Ok((cached.clone(), true));
        }
    }

    let keys = tokio::task::spawn_blocking(|| {
        let mut rng = rand::thread_rng();
        let (tpk, tsk) = ibe::transport_keygen(&mut rng);
        (serialize_point(&tpk.0), serialize_point(&tsk.0))
    }).await.map_err(|e| format!("keygen: {e}"))?;

    // Attach attestation evidence to the vetKey request
    let vetkey_resp: VetKeyResponse = state.http
        .post(format!("{}/vetkey", safetee_url))
        .json(&VetKeyRequest {
            identity_hex: nonce_hex.to_string(),
            tpk_hex: keys.0.clone(),
            attestation: Some(state.attestation.clone()),
        })
        .send().await.map_err(|e| format!("SAFE-TEE: {e}"))?
        .json().await.map_err(|e| format!("SAFE-TEE parse: {e}"))?;

    if !vetkey_resp.valid {
        return Err("invalid vetKey".into());
    }

    eprintln!("[sidecar] vetKey issued (attestation_verified: {})", vetkey_resp.attestation_verified);

    let mpk: MpkResponse = state.http
        .get(format!("{}/mpk", safetee_url))
        .send().await.map_err(|e| format!("MPK: {e}"))?
        .json().await.map_err(|e| format!("MPK parse: {e}"))?;

    let cached = CachedVetKey {
        tsk_hex: keys.1,
        evk_c1_hex: vetkey_resp.encrypted_vetkey_c1_hex,
        evk_c2_hex: vetkey_resp.encrypted_vetkey_c2_hex,
        evk_c3_hex: vetkey_resp.encrypted_vetkey_c3_hex,
        mpk_hex: mpk.group_pk_hex,
        attestation_verified: vetkey_resp.attestation_verified,
    };

    {
        let mut cache = state.vetkey_cache.write().await;
        cache.insert(nonce_hex.to_string(), cached.clone());
    }

    Ok((cached, false))
}

async fn do_infer(state: AppState, req: InferRequest) -> Result<InferResponse, String> {
    let t0 = std::time::Instant::now();
    let nonce_hex = req.nonce_hex.clone();

    let (vk_material, key_was_cached) = get_vetkey_material(&state, &nonce_hex, &req.safetee_url).await?;

    let ct_u = req.ciphertext_u_hex.clone();
    let ct_v = req.ciphertext_v_hex.clone();
    let ct_w = req.ciphertext_w_hex.clone();
    let nh = nonce_hex.clone();
    let vk = vk_material.clone();

    let frame_b64: String = tokio::task::spawn_blocking(move || -> Result<String, String> {
        let evk = wire_to_evk(&vk.evk_c1_hex, &vk.evk_c2_hex, &vk.evk_c3_hex);
        let group_pk = deserialize_g1(&vk.mpk_hex);
        let ct = wire_to_ibe_ciphertext(&ct_u, &ct_v, &ct_w);
        let identity = hex::decode(&nh).map_err(|e| format!("nonce: {e}"))?;
        let tsk = ibe::TransportSecretKey(deserialize_fr(&vk.tsk_hex));
        let vetkey = ibe::decrypt_vetkey(&evk, &tsk, &identity, &group_pk)
            .ok_or("vetKey decryption failed")?;
        let plaintext = ibe::ibe_decrypt(&vetkey, &ct)
            .ok_or("IBE decryption failed")?;
        String::from_utf8(plaintext).map_err(|e| format!("not UTF-8: {e}"))
    }).await.map_err(|e| format!("decrypt: {e}"))??;

    eprintln!("[sidecar] Decrypted in {}ms (key cached: {key_was_cached}), calling vLLM...", t0.elapsed().as_millis());

    let vllm_body = serde_json::json!({
        "model": state.model,
        "messages": [{
            "role": "user",
            "content": [
                { "type": "image_url", "image_url": { "url": format!("data:image/jpeg;base64,{frame_b64}") } },
                { "type": "text", "text": "Describe what you see in this image in 2-3 sentences." }
            ]
        }],
        "max_tokens": 200
    });

    let vllm_resp = state.http
        .post(format!("{}/v1/chat/completions", state.vllm_url))
        .json(&vllm_body)
        .send().await.map_err(|e| format!("vLLM: {e}"))?;

    let vllm_json: serde_json::Value = vllm_resp.json().await
        .map_err(|e| format!("vLLM parse: {e}"))?;

    let response_text = vllm_json["choices"][0]["message"]["content"]
        .as_str().unwrap_or("(no response)").to_string();

    eprintln!("[sidecar] vLLM responded in {}ms", t0.elapsed().as_millis());

    // Step 4: Encrypt response with X25519 + AES-256-GCM (fast, client decrypts locally)
    let client_return_pk_hex = req.client_return_pubkey_hex.clone();
    let resp_text = response_text.clone();

    let (sidecar_pk_hex, encrypted_resp_hex) = tokio::task::spawn_blocking(move || -> Result<(String, String), String> {
        use aes_gcm::{Aes256Gcm, KeyInit, aead::Aead};
        use x25519_dalek::{EphemeralSecret, PublicKey};
        use sha2::{Sha256, Digest};

        // Parse client's X25519 public key
        let client_pk_bytes: [u8; 32] = hex::decode(&client_return_pk_hex)
            .map_err(|e| format!("bad client pubkey: {e}"))?
            .try_into()
            .map_err(|_| "client pubkey must be 32 bytes")?;
        let client_pk = PublicKey::from(client_pk_bytes);

        // Generate ephemeral X25519 keypair for this response
        let sidecar_secret = EphemeralSecret::random_from_rng(rand::thread_rng());
        let sidecar_pk = PublicKey::from(&sidecar_secret);

        // ECDH shared secret -> AES-256 key via SHA-256
        let shared_secret = sidecar_secret.diffie_hellman(&client_pk);
        let aes_key = Sha256::digest(shared_secret.as_bytes());

        // AES-256-GCM encrypt
        let cipher = Aes256Gcm::new_from_slice(&aes_key)
            .map_err(|e| format!("AES init: {e}"))?;
        let mut nonce_bytes = [0u8; 12];
        rand::Rng::fill(&mut rand::thread_rng(), &mut nonce_bytes);
        let nonce = aes_gcm::Nonce::from_slice(&nonce_bytes);

        let ciphertext = cipher.encrypt(nonce, resp_text.as_bytes())
            .map_err(|e| format!("AES encrypt: {e}"))?;

        // Pack: nonce (12) || ciphertext+tag
        let mut packed = Vec::with_capacity(12 + ciphertext.len());
        packed.extend_from_slice(&nonce_bytes);
        packed.extend_from_slice(&ciphertext);

        Ok((hex::encode(sidecar_pk.as_bytes()), hex::encode(&packed)))
    }).await.map_err(|e| format!("encrypt: {e}"))??;

    eprintln!("[sidecar] Total: {}ms", t0.elapsed().as_millis());

    Ok(InferResponse {
        sidecar_pubkey_hex: sidecar_pk_hex,
        encrypted_response_hex: encrypted_resp_hex,
        success: true,
        error: None,
        cached: key_was_cached,
        attestation_verified: vk_material.attestation_verified,
        tee_attestation: Some(state.attestation.clone()),
    })
}

#[tokio::main]
async fn main() {
    let cli = Cli::parse();

    println!("=== SAFE-TEE Inference Sidecar ===");
    println!("  vLLM:   {}", cli.vllm_url);
    println!("  Model:  {}", cli.model);
    println!("  Listen: {}", cli.listen);
    println!();

    // Collect TEE attestation evidence on startup
    let attestation = collect_attestation();
    println!("  TDX:    {}", if attestation.tdx_quote_hex.is_some() { "available" } else { "not available" });
    println!("  GPU CC: {}", attestation.gpu_evidence.as_ref()
        .map(|g| format!("{} ({})", g.cc_status, g.gpu_name))
        .unwrap_or_else(|| "not available".to_string()));
    println!();

    let state = AppState {
        vllm_url: cli.vllm_url,
        model: cli.model,
        http: reqwest::Client::builder()
            .danger_accept_invalid_certs(true)
            .build()
            .unwrap(),
        vetkey_cache: Arc::new(RwLock::new(HashMap::new())),
        attestation,
    };

    let app = Router::new()
        .route("/health", get(health))
        .route("/infer", post(post_infer))
        .layer(CorsLayer::permissive())
        .with_state(state);

    let tls = cli.tls_cert.as_ref().zip(cli.tls_key.as_ref());
    let scheme = if tls.is_some() { "https" } else { "http" };
    println!("  {scheme}://{}", cli.listen);

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
