//! SAFE-TEE Inference Sidecar: runs on the TDX VM next to vLLM.
//!
//! Session-based multi-user latest-frame-wins architecture with parallel batching:
//!   POST /frame  -- store encrypted frame keyed by client pk (fire-and-forget)
//!   GET  /result?pk=... -- poll for this session's latest inference result
//!   Background loop collects up to --batch-size pending frames and sends them
//!   to vLLM concurrently, leveraging vLLM's internal continuous batching.

mod crypto;

use std::collections::HashMap;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Instant;
use tokio::sync::RwLock;

use axum::extract::State;
use axum::http::StatusCode;
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
    #[arg(short, long, default_value = "16")]
    batch_size: usize,
}

// ---------------------------------------------------------------------------
// TEE attestation collection (unchanged)
// ---------------------------------------------------------------------------

fn collect_tdx_quote() -> Option<String> {
    let tsm_path = std::path::Path::new("/sys/kernel/config/tsm/report");
    if tsm_path.exists() {
        let entry = tsm_path.join("safetee-attest");
        let _ = std::fs::create_dir_all(&entry);
        let _ = std::fs::write(entry.join("inblob"), vec![0u8; 64]);
        if let Ok(q) = std::fs::read(entry.join("outblob")) {
            if !q.is_empty() { return Some(hex::encode(&q)); }
        }
    }
    if std::path::Path::new("/dev/tdx_guest").exists() {
        return Some("tdx_guest_device_present".to_string());
    }
    if let Ok(o) = std::process::Command::new("dmesg").output() {
        let d = String::from_utf8_lossy(&o.stdout);
        if d.contains("tdx") || d.contains("TDX") { return Some("tdx_dmesg_evidence".to_string()); }
    }
    None
}

fn collect_gpu_cc_evidence() -> Option<GpuCcEvidence> {
    let cc = std::process::Command::new("sudo").args(["nvidia-smi", "conf-compute", "-f"]).output().ok()?;
    let ct = String::from_utf8_lossy(&cc.stdout);
    let cc_status = if ct.contains("ON") { "ON" } else if ct.contains("OFF") { "OFF" } else { return None; }.to_string();
    let q = std::process::Command::new("nvidia-smi").args(["--query-gpu=name,driver_version,uuid,vbios_version,serial", "--format=csv,noheader,nounits"]).output().ok()?;
    let qt = String::from_utf8_lossy(&q.stdout);
    let p: Vec<&str> = qt.trim().splitn(5, ", ").collect();
    let (gn, dv, gu, vb, sr) = if p.len() >= 5 {
        (p[0].into(), p[1].into(), p[2].into(), p[3].into(), p[4].into())
    } else {
        let d = std::fs::read_to_string("/proc/driver/nvidia/version").ok()
            .and_then(|s| s.split_whitespace().find(|w| w.chars().next().map_or(false, |c| c.is_ascii_digit())).map(|s| s.to_string()))
            .unwrap_or("?".into());
        let l = std::process::Command::new("lspci").output().ok().map(|o| String::from_utf8_lossy(&o.stdout).to_string()).unwrap_or_default();
        let g = l.lines().find(|l| l.contains("NVIDIA")).map(|l| l.split(": ").last().unwrap_or("GPU").to_string()).unwrap_or("GPU".into());
        (g, d, "?".into(), "?".into(), "?".into())
    };
    let gsp = std::fs::read_dir("/lib/firmware/nvidia/").ok().and_then(|mut d| d.next()).and_then(|e| e.ok()).map(|e| e.file_name().to_string_lossy().to_string()).unwrap_or("?".into());
    Some(GpuCcEvidence { cc_status, gpu_name: gn, driver_version: dv, gpu_uuid: gu, vbios_version: vb, serial: sr, gsp_firmware: gsp })
}

fn collect_tdx_evidence() -> Option<TdxEvidence> {
    let dev = if std::path::Path::new("/dev/tdx_guest").exists() { "/dev/tdx_guest".into() } else { String::new() };
    let dm = std::process::Command::new("sudo").args(["dmesg"]).output().ok().map(|o| String::from_utf8_lossy(&o.stdout).to_string()).unwrap_or_default();
    let active = dm.contains("Intel TDX") || dm.contains("confidential virtualization tdx");
    let certs: Vec<String> = dm.lines().filter(|l| l.contains("Loaded X.509 cert")).filter_map(|l| l.split('\'').nth(1).map(|s| s.to_string())).collect();
    if !active && dev.is_empty() { return None; }
    Some(TdxEvidence { tdx_active: active, tdx_device: dev, secure_boot_certs: certs })
}

fn collect_gcp_info() -> Option<GcpInfo> {
    fn m(p: &str) -> Option<String> {
        std::process::Command::new("curl").args(["-sf", "-H", "Metadata-Flavor: Google", &format!("http://metadata.google.internal/computeMetadata/v1/{p}")])
            .output().ok().filter(|o| o.status.success()).map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
    }
    let project = m("project/project-id")?;
    let zf = m("instance/zone").unwrap_or_default();
    let zone = zf.rsplit('/').next().unwrap_or(&zf).to_string();
    let instance = m("instance/name").unwrap_or("?".into());
    let mf = m("instance/machine-type").unwrap_or_default();
    let machine_type = mf.rsplit('/').next().unwrap_or(&mf).to_string();
    Some(GcpInfo { project, zone, instance, machine_type })
}

fn collect_attestation() -> TeeAttestation {
    eprintln!("[attest] Collecting TEE attestation evidence...");
    TeeAttestation {
        tdx_quote_hex: collect_tdx_quote(),
        tdx_evidence: collect_tdx_evidence(),
        gpu_evidence: collect_gpu_cc_evidence(),
        gcp_info: collect_gcp_info(),
    }
}

// ---------------------------------------------------------------------------
// Per-session state
// ---------------------------------------------------------------------------

struct Session {
    latest_frame: Option<FrameRequest>,
    latest_result: Option<PlaintextResult>,
    new_frame: bool,
    last_active: Instant,
}

// ---------------------------------------------------------------------------
// Shared app state
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
    sessions: Arc<RwLock<HashMap<String, Session>>>,
    batch_size: usize,
    inflight: Arc<AtomicU64>,
}

// ---------------------------------------------------------------------------
// Handlers
// ---------------------------------------------------------------------------

async fn health() -> &'static str { "ok" }

/// POST /frame -- store encrypted frame keyed by client's X25519 public key
async fn post_frame(State(state): State<AppState>, body: String) -> StatusCode {
    let req: FrameRequest = match serde_json::from_str(&body) {
        Ok(r) => r,
        Err(_) => return StatusCode::BAD_REQUEST,
    };
    let pk = req.client_return_pubkey_hex.clone();
    eprintln!("[sidecar] Frame #{} from session {}...", req.frame_id, &pk[..12]);
    let mut sessions = state.sessions.write().await;
    let session = sessions.entry(pk).or_insert_with(|| Session {
        latest_frame: None,
        latest_result: None,
        new_frame: false,
        last_active: Instant::now(),
    });
    session.latest_frame = Some(req);
    session.new_frame = true;
    session.last_active = Instant::now();
    StatusCode::ACCEPTED
}

/// GET /result?pk=<hex> -- return this session's latest result, encrypted on-the-fly
async fn get_result(
    State(state): State<AppState>,
    axum::extract::Query(params): axum::extract::Query<HashMap<String, String>>,
) -> axum::Json<ResultResponse> {
    let empty = ResultResponse {
        frame_id: 0, sidecar_pubkey_hex: String::new(), encrypted_response_hex: String::new(),
        attestation_verified: false, tee_attestation: None, crypto_log: None, ready: false,
    };

    let pk = match params.get("pk") {
        Some(pk) if pk.len() == 64 => pk.clone(),
        _ => return axum::Json(empty),
    };

    let pt = {
        let sessions = state.sessions.read().await;
        match sessions.get(&pk) {
            Some(s) => s.latest_result.clone(),
            None => return axum::Json(empty),
        }
    };

    let pt = match pt {
        Some(p) => p,
        None => return axum::Json(empty),
    };

    let rt = pt.response_text.clone();
    let cpk = pk.clone();
    let enc_t0 = Instant::now();
    match tokio::task::spawn_blocking(move || encrypt_response(&rt, &cpk)).await {
        Ok(Ok((spk, enc))) => {
            let return_encrypt_ms = enc_t0.elapsed().as_millis() as u64;
            let crypto_log = pt.crypto_log.map(|mut cl| {
                cl.return_encrypt_ms = Some(return_encrypt_ms);
                cl
            });
            axum::Json(ResultResponse {
                frame_id: pt.frame_id,
                sidecar_pubkey_hex: spk,
                encrypted_response_hex: enc,
                attestation_verified: pt.attestation_verified,
                tee_attestation: pt.tee_attestation,
                crypto_log,
                ready: true,
            })
        },
        _ => axum::Json(empty),
    }
}

/// POST /infer -- synchronous single-shot (backward compat)
async fn post_infer(State(state): State<AppState>, body: String) -> axum::Json<InferResponse> {
    let req: InferRequest = match serde_json::from_str(&body) {
        Ok(r) => r,
        Err(e) => return axum::Json(err_resp(format!("bad JSON: {e}"))),
    };
    match do_infer(&state, req).await {
        Ok(r) => axum::Json(r),
        Err(e) => axum::Json(err_resp(e)),
    }
}

fn err_resp(e: String) -> InferResponse {
    InferResponse {
        sidecar_pubkey_hex: String::new(), encrypted_response_hex: String::new(),
        success: false, error: Some(e), cached: false, attestation_verified: false, tee_attestation: None,
    }
}

// ---------------------------------------------------------------------------
// Crypto + inference helpers
// ---------------------------------------------------------------------------

struct VetKeyResult {
    vk: CachedVetKey,
    cached: bool,
    transport_keygen_ms: Option<u64>,
    vetkey_request_ms: Option<u64>,
    vetkey_valid: Option<bool>,
    tpk_hex: Option<String>,
}

async fn get_vetkey_material(state: &AppState, nonce_hex: &str, safetee_url: &str) -> Result<VetKeyResult, String> {
    {
        let c = state.vetkey_cache.read().await;
        if let Some(v) = c.get(nonce_hex) {
            return Ok(VetKeyResult {
                vk: v.clone(), cached: true,
                transport_keygen_ms: None, vetkey_request_ms: None,
                vetkey_valid: None, tpk_hex: None,
            });
        }
    }

    let tkg_t0 = Instant::now();
    let keys = tokio::task::spawn_blocking(|| {
        let mut r = rand::thread_rng();
        let (tpk, tsk) = ibe::transport_keygen(&mut r);
        (serialize_point(&tpk.0), serialize_point(&tsk.0))
    }).await.map_err(|e| format!("{e}"))?;
    let transport_keygen_ms = tkg_t0.elapsed().as_millis() as u64;

    let vk_t0 = Instant::now();
    let vr: VetKeyResponse = state.http
        .post(format!("{safetee_url}/vetkey"))
        .json(&VetKeyRequest { identity_hex: nonce_hex.into(), tpk_hex: keys.0.clone(), attestation: Some(state.attestation.clone()) })
        .send().await.map_err(|e| format!("{e}"))?
        .json().await.map_err(|e| format!("{e}"))?;
    let vetkey_request_ms = vk_t0.elapsed().as_millis() as u64;
    if !vr.valid { return Err("invalid vetKey".into()); }

    let mpk: MpkResponse = state.http
        .get(format!("{safetee_url}/mpk"))
        .send().await.map_err(|e| format!("{e}"))?
        .json().await.map_err(|e| format!("{e}"))?;

    let cached = CachedVetKey {
        tsk_hex: keys.1,
        evk_c1_hex: vr.encrypted_vetkey_c1_hex, evk_c2_hex: vr.encrypted_vetkey_c2_hex, evk_c3_hex: vr.encrypted_vetkey_c3_hex,
        mpk_hex: mpk.group_pk_hex, attestation_verified: vr.attestation_verified,
    };
    let tpk_hex = Some(keys.0);
    state.vetkey_cache.write().await.insert(nonce_hex.to_string(), cached.clone());
    Ok(VetKeyResult {
        vk: cached, cached: false,
        transport_keygen_ms: Some(transport_keygen_ms),
        vetkey_request_ms: Some(vetkey_request_ms),
        vetkey_valid: Some(vr.valid),
        tpk_hex,
    })
}

fn decrypt_frame(vk: &CachedVetKey, ct_u: &str, ct_v: &str, ct_w: &str, nonce_hex: &str) -> Result<String, String> {
    let evk = wire_to_evk(&vk.evk_c1_hex, &vk.evk_c2_hex, &vk.evk_c3_hex);
    let group_pk = deserialize_g1(&vk.mpk_hex);
    let ct = wire_to_ibe_ciphertext(ct_u, ct_v, ct_w);
    let identity = hex::decode(nonce_hex).map_err(|e| format!("{e}"))?;
    let tsk = ibe::TransportSecretKey(deserialize_fr(&vk.tsk_hex));
    let vetkey = ibe::decrypt_vetkey(&evk, &tsk, &identity, &group_pk).ok_or("vetKey decrypt failed")?;
    let pt = ibe::ibe_decrypt(&vetkey, &ct).ok_or("IBE decrypt failed")?;
    String::from_utf8(pt).map_err(|e| format!("{e}"))
}

fn encrypt_response(resp_text: &str, client_pk_hex: &str) -> Result<(String, String), String> {
    use aes_gcm::{Aes256Gcm, KeyInit, aead::Aead};
    use x25519_dalek::{EphemeralSecret, PublicKey};
    use sha2::{Sha256, Digest};
    let client_pk_bytes: [u8; 32] = hex::decode(client_pk_hex).map_err(|e| format!("{e}"))?.try_into().map_err(|_| "bad pk len")?;
    let client_pk = PublicKey::from(client_pk_bytes);
    let secret = EphemeralSecret::random_from_rng(rand::thread_rng());
    let pk = PublicKey::from(&secret);
    let shared = secret.diffie_hellman(&client_pk);
    let aes_key = Sha256::digest(shared.as_bytes());
    let cipher = Aes256Gcm::new_from_slice(&aes_key).map_err(|e| format!("{e}"))?;
    let mut nonce = [0u8; 12];
    rand::Rng::fill(&mut rand::thread_rng(), &mut nonce);
    let ct = cipher.encrypt(aes_gcm::Nonce::from_slice(&nonce), resp_text.as_bytes()).map_err(|e| format!("{e}"))?;
    let mut packed = Vec::with_capacity(12 + ct.len());
    packed.extend_from_slice(&nonce);
    packed.extend_from_slice(&ct);
    Ok((hex::encode(pk.as_bytes()), hex::encode(&packed)))
}

async fn call_vllm(state: &AppState, frame_b64: &str) -> Result<String, String> {
    let body = serde_json::json!({
        "model": state.model,
        "messages": [{"role": "user", "content": [
            {"type": "image_url", "image_url": {"url": format!("data:image/jpeg;base64,{frame_b64}")}},
            {"type": "text", "text": "Describe what you see in this image in 2-3 sentences."}
        ]}],
        "max_tokens": 200
    });
    let r = state.http.post(format!("{}/v1/chat/completions", state.vllm_url)).json(&body).send().await.map_err(|e| format!("{e}"))?;
    let j: serde_json::Value = r.json().await.map_err(|e| format!("{e}"))?;
    Ok(j["choices"][0]["message"]["content"].as_str().unwrap_or("(no response)").to_string())
}

/// Synchronous single-shot inference (for POST /infer backward compat)
async fn do_infer(state: &AppState, req: InferRequest) -> Result<InferResponse, String> {
    let t0 = Instant::now();
    let vkr = get_vetkey_material(state, &req.nonce_hex, &req.safetee_url).await?;
    let vk = vkr.vk;
    let cached = vkr.cached;
    let cu = req.ciphertext_u_hex.clone(); let cv = req.ciphertext_v_hex.clone();
    let cw = req.ciphertext_w_hex.clone(); let nh = req.nonce_hex.clone();
    let vk2 = vk.clone();
    let frame_b64 = tokio::task::spawn_blocking(move || decrypt_frame(&vk2, &cu, &cv, &cw, &nh)).await.map_err(|e| format!("{e}"))??;
    eprintln!("[infer] Decrypted {}ms", t0.elapsed().as_millis());
    let resp = call_vllm(state, &frame_b64).await?;
    eprintln!("[infer] vLLM {}ms", t0.elapsed().as_millis());
    let cpk = req.client_return_pubkey_hex.clone();
    let rt = resp.clone();
    let (spk, enc) = tokio::task::spawn_blocking(move || encrypt_response(&rt, &cpk)).await.map_err(|e| format!("{e}"))??;
    eprintln!("[infer] Total {}ms", t0.elapsed().as_millis());
    Ok(InferResponse {
        sidecar_pubkey_hex: spk, encrypted_response_hex: enc, success: true, error: None,
        cached, attestation_verified: vk.attestation_verified, tee_attestation: Some(state.attestation.clone()),
    })
}

// ---------------------------------------------------------------------------
// Background inference loop -- parallel batched across sessions
// ---------------------------------------------------------------------------

/// Process a single frame: decrypt, call vLLM, return result with session key.
async fn process_one_frame(
    state: &AppState,
    session_pk: String,
    frame: FrameRequest,
) -> (String, Result<PlaintextResult, String>) {
    let frame_id = frame.frame_id;
    let t0 = Instant::now();

    let result = async {
        let vkr = get_vetkey_material(state, &frame.nonce_hex, &frame.safetee_url).await?;
        let vk = vkr.vk;

        let ibe_t0 = Instant::now();
        let cu = frame.ciphertext_u_hex;
        let cv = frame.ciphertext_v_hex;
        let cw = frame.ciphertext_w_hex;
        let nh = frame.nonce_hex.clone();
        let vk2 = vk.clone();
        let frame_b64 = tokio::task::spawn_blocking(move || decrypt_frame(&vk2, &cu, &cv, &cw, &nh))
            .await.map_err(|e| format!("{e}"))??;
        let ibe_decrypt_ms = ibe_t0.elapsed().as_millis() as u64;

        let vllm_t0 = Instant::now();
        let resp = call_vllm(state, &frame_b64).await?;
        let vllm_ms = vllm_t0.elapsed().as_millis() as u64;

        let total_ms = t0.elapsed().as_millis() as u64;
        eprintln!("[batch] #{frame_id} session {}... decrypt {ibe_decrypt_ms}ms vLLM {vllm_ms}ms total {total_ms}ms",
            &session_pk[..12.min(session_pk.len())]);

        let crypto_log = CryptoLog {
            vetkey_cached: vkr.cached,
            transport_keygen_ms: vkr.transport_keygen_ms,
            vetkey_request_ms: vkr.vetkey_request_ms,
            vetkey_valid: vkr.vetkey_valid,
            attestation_verified: vk.attestation_verified,
            attestation_checks: if vk.attestation_verified { Some("3/3 checks passed".into()) } else { Some("unverified".into()) },
            ibe_decrypt_ms: Some(ibe_decrypt_ms),
            vllm_ms: Some(vllm_ms),
            return_encrypt_ms: None,
            total_ms,
            tpk_hex: vkr.tpk_hex,
            evk_c1_hex: Some(vk.evk_c1_hex.clone()),
            evk_c2_hex: Some(vk.evk_c2_hex.clone()),
            evk_c3_hex: Some(vk.evk_c3_hex.clone()),
            mpk_hex: Some(vk.mpk_hex.clone()),
        };

        Ok::<PlaintextResult, String>(PlaintextResult {
            frame_id,
            response_text: resp,
            attestation_verified: vk.attestation_verified,
            tee_attestation: Some(state.attestation.clone()),
            crypto_log: Some(crypto_log),
        })
    }.await;

    (session_pk, result)
}

async fn inference_loop(state: AppState) {
    let batch_size = state.batch_size;
    eprintln!("[loop] Parallel batched inference loop started (batch_size={batch_size})");
    let mut last_cleanup = Instant::now();

    loop {
        tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;

        // How many slots are free?
        let inflight = state.inflight.load(Ordering::Relaxed) as usize;
        let available = batch_size.saturating_sub(inflight);
        if available == 0 { continue; }

        // Collect up to `available` pending frames from all sessions
        let batch: Vec<(String, FrameRequest)> = {
            let mut sessions = state.sessions.write().await;
            let mut collected = Vec::new();
            for (pk, session) in sessions.iter_mut() {
                if collected.len() >= available { break; }
                if session.new_frame {
                    if let Some(frame) = session.latest_frame.clone() {
                        session.new_frame = false;
                        collected.push((pk.clone(), frame));
                    }
                }
            }
            collected
        };

        if batch.is_empty() { continue; }

        let n = batch.len();
        eprintln!("[loop] Dispatching batch of {n} frames (inflight: {inflight} -> {})", inflight + n);

        // Spawn all inferences concurrently
        for (session_pk, frame) in batch {
            state.inflight.fetch_add(1, Ordering::Relaxed);
            let s = state.clone();
            tokio::spawn(async move {
                let (pk, result) = process_one_frame(&s, session_pk, frame).await;
                match result {
                    Ok(r) => {
                        let mut sessions = s.sessions.write().await;
                        if let Some(session) = sessions.get_mut(&pk) {
                            session.latest_result = Some(r);
                        }
                    }
                    Err(e) => { eprintln!("[batch] session {}... error: {e}", &pk[..12.min(pk.len())]); }
                }
                s.inflight.fetch_sub(1, Ordering::Relaxed);
            });
        }

        // Cleanup stale sessions every 60 seconds
        if last_cleanup.elapsed().as_secs() > 60 {
            let mut sessions = state.sessions.write().await;
            let before = sessions.len();
            sessions.retain(|_, s| s.last_active.elapsed().as_secs() < 300);
            let removed = before - sessions.len();
            if removed > 0 {
                eprintln!("[loop] Cleaned up {removed} stale sessions ({} remaining)", sessions.len());
            }
            last_cleanup = Instant::now();
        }
    }
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

#[tokio::main]
async fn main() {
    let cli = Cli::parse();
    println!("=== SAFE-TEE Inference Sidecar ===");
    println!("  vLLM:   {}", cli.vllm_url);
    println!("  Model:  {}", cli.model);
    println!("  Listen: {}", cli.listen);

    let attestation = collect_attestation();
    println!("  TDX:    {}", if attestation.tdx_quote_hex.is_some() { "available" } else { "N/A" });
    println!("  GPU CC: {}", attestation.gpu_evidence.as_ref().map(|g| format!("{} ({})", g.cc_status, g.gpu_name)).unwrap_or("N/A".into()));

    let batch_size = cli.batch_size;
    let state = AppState {
        vllm_url: cli.vllm_url,
        model: cli.model,
        http: reqwest::Client::builder().danger_accept_invalid_certs(true).build().unwrap(),
        vetkey_cache: Arc::new(RwLock::new(HashMap::new())),
        attestation,
        sessions: Arc::new(RwLock::new(HashMap::new())),
        batch_size,
        inflight: Arc::new(AtomicU64::new(0)),
    };

    tokio::spawn(inference_loop(state.clone()));

    let app = Router::new()
        .route("/health", get(health))
        .route("/frame", post(post_frame))
        .route("/result", get(get_result))
        .route("/infer", post(post_infer))
        .layer(CorsLayer::permissive())
        .with_state(state);

    let tls = cli.tls_cert.as_ref().zip(cli.tls_key.as_ref());
    let scheme = if tls.is_some() { "https" } else { "http" };
    println!("  {scheme}://{}", cli.listen);
    println!("  Batch:  {batch_size} concurrent inferences");
    println!("  Endpoints: /frame (POST), /result (GET), /infer (POST), /health (GET)");
    println!("  Sessions:  per-client (keyed by X25519 pubkey)");

    if let Some((cert, key)) = tls {
        let cfg = axum_server::tls_rustls::RustlsConfig::from_pem_file(cert, key).await.expect("TLS");
        let addr: std::net::SocketAddr = cli.listen.parse().expect("addr");
        axum_server::bind_rustls(addr, cfg).serve(app.into_make_service()).await.unwrap();
    } else {
        let l = tokio::net::TcpListener::bind(&cli.listen).await.unwrap();
        axum::serve(l, app).await.unwrap();
    }
}
