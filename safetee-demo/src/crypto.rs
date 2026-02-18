//! Shared serialization helpers for SAFE-TEE crypto types.
//!
//! Converts BLS12-381 curve points and IBE types to/from hex strings
//! for JSON wire transport between the browser, SAFE-TEE server, and sidecar.

#![allow(dead_code)]

use ark_bls12_381::{Fr, G1Affine, G2Affine};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use golden_dkg::threshold::ibe;
use serde::{Deserialize, Serialize};

// ---------------------------------------------------------------------------
// Serialization helpers
// ---------------------------------------------------------------------------

pub fn serialize_point<T: CanonicalSerialize>(p: &T) -> String {
    let mut buf = Vec::new();
    p.serialize_compressed(&mut buf).expect("serialize point");
    hex::encode(&buf)
}

pub fn deserialize_g1(hex_str: &str) -> G1Affine {
    let bytes = hex::decode(hex_str).expect("hex decode G1");
    G1Affine::deserialize_compressed(&bytes[..]).expect("deserialize G1")
}

pub fn deserialize_g2(hex_str: &str) -> G2Affine {
    let bytes = hex::decode(hex_str).expect("hex decode G2");
    G2Affine::deserialize_compressed(&bytes[..]).expect("deserialize G2")
}

pub fn deserialize_fr(hex_str: &str) -> Fr {
    let bytes = hex::decode(hex_str).expect("hex decode Fr");
    Fr::deserialize_compressed(&bytes[..]).expect("deserialize Fr")
}

// ---------------------------------------------------------------------------
// JSON wire types shared between server, sidecar, and browser
// ---------------------------------------------------------------------------

/// Master public key response from GET /mpk.
#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct MpkResponse {
    pub group_pk_hex: String,
    pub num_nodes: u32,
    pub threshold: u32,
}

/// GPU Confidential Computing attestation evidence.
#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct GpuCcEvidence {
    /// CC mode status: "ON" or "OFF"
    pub cc_status: String,
    /// GPU model name, e.g. "NVIDIA H100 80GB HBM3"
    pub gpu_name: String,
    /// Driver version, e.g. "580.126.09"
    pub driver_version: String,
    /// Unique GPU identifier, e.g. "GPU-17ce47a6-..."
    pub gpu_uuid: String,
    /// vBIOS version, e.g. "96.00.CF.00.01"
    #[serde(default)]
    pub vbios_version: String,
    /// GPU serial number
    #[serde(default)]
    pub serial: String,
    /// GSP firmware version
    #[serde(default)]
    pub gsp_firmware: String,
}

/// Intel TDX attestation evidence.
#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct TdxEvidence {
    /// Whether TDX memory encryption is active
    pub tdx_active: bool,
    /// TDX device path (e.g. "/dev/tdx_guest")
    #[serde(default)]
    pub tdx_device: String,
    /// Secure Boot X.509 certificate names loaded at boot
    #[serde(default)]
    pub secure_boot_certs: Vec<String>,
}

/// GCP instance metadata.
#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct GcpInfo {
    pub project: String,
    pub zone: String,
    pub instance: String,
    pub machine_type: String,
}

/// Combined TEE attestation evidence from the sidecar.
#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct TeeAttestation {
    /// Intel TDX quote (hex-encoded raw bytes from configfs-tsm or /dev/tdx_guest)
    #[serde(default)]
    pub tdx_quote_hex: Option<String>,
    /// Intel TDX evidence (device, Secure Boot certs)
    #[serde(default)]
    pub tdx_evidence: Option<TdxEvidence>,
    /// NVIDIA GPU CC evidence
    #[serde(default)]
    pub gpu_evidence: Option<GpuCcEvidence>,
    /// GCP instance metadata
    #[serde(default)]
    pub gcp_info: Option<GcpInfo>,
}

/// Request to POST /vetkey -- ask the network for an encrypted vetKey.
#[derive(Serialize, Deserialize, Debug)]
pub struct VetKeyRequest {
    pub identity_hex: String,
    pub tpk_hex: String,
    /// TEE attestation evidence (optional for backward compat)
    #[serde(default)]
    pub attestation: Option<TeeAttestation>,
}

/// Response from POST /vetkey -- the encrypted vetKey.
#[derive(Serialize, Deserialize, Debug)]
pub struct VetKeyResponse {
    pub encrypted_vetkey_c1_hex: String,
    pub encrypted_vetkey_c2_hex: String,
    pub encrypted_vetkey_c3_hex: String,
    pub valid: bool,
    /// Whether TEE attestation was verified before issuing the key.
    #[serde(default)]
    pub attestation_verified: bool,
}

/// Request to POST /encrypt -- IBE encrypt a message.
#[derive(Serialize, Deserialize, Debug)]
pub struct EncryptRequest {
    pub identity_hex: String,
    pub message_base64: String,
}

/// Response from POST /encrypt -- the IBE ciphertext.
#[derive(Serialize, Deserialize, Debug)]
pub struct EncryptResponse {
    pub ciphertext_u_hex: String,
    pub ciphertext_v_hex: String,
    pub ciphertext_w_hex: String,
}

/// Request to POST /decrypt -- decrypt using transport secret key + encrypted vetkey.
#[derive(Serialize, Deserialize, Debug)]
pub struct DecryptRequest {
    pub tsk_hex: String,
    pub identity_hex: String,
    pub encrypted_vetkey_c1_hex: String,
    pub encrypted_vetkey_c2_hex: String,
    pub encrypted_vetkey_c3_hex: String,
    pub ciphertext_u_hex: String,
    pub ciphertext_v_hex: String,
    pub ciphertext_w_hex: String,
}

/// Response from POST /decrypt.
#[derive(Serialize, Deserialize, Debug)]
pub struct DecryptResponse {
    pub message_base64: Option<String>,
    pub success: bool,
}

/// Request to POST /infer on the sidecar (synchronous, kept for backward compat).
#[derive(Serialize, Deserialize, Debug)]
pub struct InferRequest {
    pub ciphertext_u_hex: String,
    pub ciphertext_v_hex: String,
    pub ciphertext_w_hex: String,
    pub nonce_hex: String,
    pub safetee_url: String,
    pub client_return_pubkey_hex: String,
}

/// Response from POST /infer on the sidecar.
#[derive(Serialize, Deserialize, Debug)]
pub struct InferResponse {
    pub sidecar_pubkey_hex: String,
    pub encrypted_response_hex: String,
    pub success: bool,
    pub error: Option<String>,
    #[serde(default)]
    pub cached: bool,
    #[serde(default)]
    pub attestation_verified: bool,
    #[serde(default)]
    pub tee_attestation: Option<TeeAttestation>,
}

/// Request to POST /frame (fire-and-forget, latest-frame-wins).
#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct FrameRequest {
    pub ciphertext_u_hex: String,
    pub ciphertext_v_hex: String,
    pub ciphertext_w_hex: String,
    pub nonce_hex: String,
    pub safetee_url: String,
    pub client_return_pubkey_hex: String,
    pub frame_id: u64,
}

/// Response from GET /result (poll for latest inference result).
/// Encrypted on-the-fly for each polling client's X25519 public key.
#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct ResultResponse {
    pub frame_id: u64,
    pub sidecar_pubkey_hex: String,
    pub encrypted_response_hex: String,
    pub attestation_verified: bool,
    #[serde(default)]
    pub tee_attestation: Option<TeeAttestation>,
    pub ready: bool,
}

/// Internal: plaintext result stored by the background loop (never serialized to clients).
#[derive(Clone, Debug)]
pub struct PlaintextResult {
    pub frame_id: u64,
    pub response_text: String,
    pub attestation_verified: bool,
    pub tee_attestation: Option<TeeAttestation>,
}

// ---------------------------------------------------------------------------
// Conversion helpers
// ---------------------------------------------------------------------------

pub fn ibe_ciphertext_to_wire(ct: &ibe::IBECiphertext) -> (String, String, String) {
    (
        serialize_point(&ct.u),
        hex::encode(&ct.v),
        hex::encode(&ct.w),
    )
}

pub fn wire_to_ibe_ciphertext(u_hex: &str, v_hex: &str, w_hex: &str) -> ibe::IBECiphertext {
    ibe::IBECiphertext {
        u: deserialize_g1(u_hex),
        v: hex::decode(v_hex).expect("hex decode v"),
        w: hex::decode(w_hex).expect("hex decode w"),
    }
}

pub fn evk_to_wire(evk: &ibe::EncryptedVetKey) -> (String, String, String) {
    (
        serialize_point(&evk.c1),
        serialize_point(&evk.c2),
        serialize_point(&evk.c3),
    )
}

pub fn wire_to_evk(c1_hex: &str, c2_hex: &str, c3_hex: &str) -> ibe::EncryptedVetKey {
    ibe::EncryptedVetKey {
        c1: deserialize_g1(c1_hex),
        c2: deserialize_g2(c2_hex),
        c3: deserialize_g2(c3_hex),
    }
}
