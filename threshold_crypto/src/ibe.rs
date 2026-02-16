//! vetKeys: Identity-Based Encryption with verifiably encrypted threshold key derivation.
//!
//! Implements the Boneh-Franklin IBE scheme with threshold BLS key derivation,
//! following the [vetKeys paper](https://eprint.iacr.org/2023/616.pdf) (ePrint 2023/616)
//! by Cerulli, Connolly, Neven, Preiss, and Shoup (DFINITY).
//!
//! # Paper Reference Map
//!
//! | Code construct | Paper section | Page | Description |
//! |---|---|---|---|
//! | `TransportPublicKey` / `TransportSecretKey` | Sec 2, TKG() | p.6 | "TKG() -> (tpk, tsk): transport key generation" |
//! | `EncryptedKeyShare` | Sec 5.3, pi_vetbls-agg2 | p.27, Fig 9 | "S_i computes (C1,C2,C3) = (g1^r, g2^r, tpk^r * sigma_i)" |
//! | `verify_encrypted_key_share` | Sec 5.3, pi_vetbls-agg2 | p.27, Fig 9 | "combiner checks e(C1,g2)=e(g1,C2) and pairing eq" |
//! | `combine_encrypted_shares` | Sec 5.3, pi_vetbls-agg2 | p.27, Fig 9 | "interpolation in the exponent" |
//! | `decrypt_vetkey` | Sec 5.3, pi_vetbls-agg2 | p.27, Fig 9 | "U decrypts sigma = C3 * C1^{-tsk}" |
//! | `VetKey` | Sec 2, Recover() | p.6 | "Recover(mpk, id, tsk, ek) -> K" |
//! | `ibe_encrypt` | Sec 6.2, pi_vetibe | p.31, Fig 11 | "On (sid, encrypt, mpk', id, m), P computes..." |
//! | `ibe_decrypt` | Sec 6.2, pi_vetibe | p.31, Fig 11 | "On (sid, decrypt, id, C), user U checks..." |
//! | `hash_identity_to_g2` | Sec 3, H: {0,1}* -> G1 | p.7 | Hash function modeled as random oracle (we use G2) |
//! | `hash_h2` | Sec 6.2, H2 | p.31 | "H2: G_T -> {0,1}^n" seed mask |
//! | `hash_h3` | Sec 6.2, H3 | p.31 | "H3: {0,1}^n x {0,1}^l -> Z_q" FO derandomization |
//! | `hash_h4` | Sec 6.2, H4 | p.31 | "H4: {0,1}^n -> {0,1}^l" message mask |
//!
//! # Architecture (Paper Section 2, Figure 1, p.6)
//!
//! Two layers compose to deliver encrypted secrets:
//!
//! 1. **IBE (Boneh-Franklin FullIdent)** [BF01, Sec 6.2 p.29-34]:
//!    Encrypt to an identity string using only the group public key.
//!    Decryption key for identity `id` = BLS signature `sigma = H(id)^sk`.
//!    Uses Fujisaki-Okamoto transform for CCA security (H3, H4 hash functions).
//!
//! 2. **Transport encryption (vetKD)** [Sec 2 p.5-7, Sec 5.3 p.25-28]:
//!    Threshold nodes each produce an encrypted key share under the recipient's
//!    transport public key. Shares are publicly verifiable via pairing equations.
//!    Only the transport secret key holder can decrypt the combined result.
//!
//! # Pairing Configuration (adapted from Paper Section 3, p.7)
//!
//! The paper uses: signatures in G1, public keys in G2 (Type-3 pairing).
//! Our threshold-crypto convention SWAPS this: `pk = g1^sk` (G1), `sigma = H(m)^sk` (G2).
//!
//! Consequently, for IBE we adapt:
//! - Identity hash: `H(id)` maps to **G2** (paper has G1)
//! - VetKey (decryption key): `sigma = H(id)^sk` in **G2** (paper has G1)
//! - Transport key: `tpk = g2^tsk` in **G2** (paper has G1)
//! - Encrypted key share: `(C1, C2, C3) = (g1^r, g2^r, tpk^r * sigma_i)` in **(G1, G2, G2)**
//!
//! All pairing checks are adjusted for this swap. The security properties are
//! identical because BLS12-381 is a Type-3 pairing where G1 and G2 are
//! symmetric in the security reduction (co-CDH, co-BDH hardness).
//!
//! # Security Theorems (Paper references)
//!
//! - **Theorem 5** (p.24): BLS signatures remain uf-cma secure under co-ElGamal leakage
//! - **Theorem 6** (p.25): pi_vetbls-agg2 realizes F_vetbls^{cEG2} under co-CDH hardness
//!   -- meaning: at least one honest node must participate for a valid encrypted key
//! - **Theorem 7** (p.32): pi_vetibe realizes F_vetibe under co-BDH hardness
//!   -- meaning: IBE ciphertexts are semantically secure
//! - **Theorem 11** (p.42): Single-key composition is secure
//!   -- meaning: safe to use one master key for IBE + signatures + VRF + PRF simultaneously
//! - **Corollary 1** (p.46): All four primitives compose securely with domain separation

use ark_bls12_381::{Bls12_381, Fr, G1Affine, G1Projective, G2Affine, G2Projective};
use ark_ec::pairing::Pairing;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::UniformRand;
use ark_serialize::CanonicalSerialize;
use ark_std::rand::Rng;
use golden_dkg::types::NodeId;
use sha2::{Digest, Sha256};

use crate::signing::lagrange_coeff;
use crate::types::KeyShare;

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

/// Transport public key for encrypted key delivery.
///
/// `tpk = g2^tsk` (in our convention; paper Section 2, p.6 has tpk in G1).
///
/// **Paper**: Section 2, p.6: "TKG() -> (tpk, tsk): A transport key generation
/// algorithm that a user can use to generate a transport public key tpk and
/// corresponding secret key tsk."
///
/// **NCC Audit Finding XPJ**: TransportSecretKey must be zeroized on drop
/// (see NCC Group VetKeys report, Section 4, p.16-17).
#[derive(Clone, Debug)]
pub struct TransportPublicKey(pub G2Affine);

/// Transport secret key: scalar `tsk` such that `tpk = g2^tsk`.
///
/// **Zeroization**: Overwritten with zero on drop to prevent secret leakage
/// through memory inspection (NCC Audit Finding XPJ, p.16-17).
///
/// **Paper**: Section 2, p.6: part of TKG() output.
#[derive(Clone)]
pub struct TransportSecretKey(pub Fr);

impl Drop for TransportSecretKey {
    fn drop(&mut self) {
        // NCC Audit Finding XPJ (p.16): sensitive values must be cleared from memory
        self.0 = Fr::from(0u64);
    }
}

/// Encrypted key share from one node.
///
/// **Paper**: Section 5.3, protocol pi_vetbls-agg2, Figure 9 (p.27):
/// "On (sid, encsign, m, tpk), S_i computes sigma_i = H(m)^{sk_i},
///  encrypts sigma_i as (C1, C2, C3) = (g1^t, g2^t, tpk^t * sigma_i)"
///
/// In our G1-pk/G2-sig convention, C3 is in G2 (paper has it in G1).
/// The pairing verification equations are adapted accordingly.
#[derive(Clone, Debug)]
pub struct EncryptedKeyShare {
    /// `g1^r` -- ElGamal randomness (G1). Paper: C_{i,1} in Figure 9.
    pub c1: G1Affine,
    /// `g2^r` -- ElGamal randomness (G2). Paper: C_{i,2} in Figure 9 (our addition for pairing).
    pub c2: G2Affine,
    /// `tpk^r * sigma_i` -- encrypted partial BLS sig (G2). Paper: C_{i,2} in Figure 9.
    pub c3: G2Affine,
    /// Which node produced this share (maps to Shamir evaluation point).
    pub signer: NodeId,
}

/// Combined encrypted vetKey after Lagrange interpolation of shares.
///
/// **Paper**: Section 5.3, Figure 9 (p.27): "When it received t valid such
/// es_i = (C_{i,1}, C_{i,2}, C_{i,3}) from different servers S_i, i in S,
/// it computes es = (C1, C2, C3) = (prod C_{i,1}^{lambda_i}, ...)"
///
/// Verifiable via pairing: `e(group_pk, H(id)) + e(C1, tpk) = e(g1, C3)`
/// (adapted from paper's `e(C2, g2) = e(C1, tpk_2) * e(H(m), pk)`)
#[derive(Clone, Debug)]
pub struct EncryptedVetKey {
    /// Aggregated randomness (G1)
    pub c1: G1Affine,
    /// Aggregated randomness (G2)
    pub c2: G2Affine,
    /// Aggregated encrypted signature (G2)
    pub c3: G2Affine,
}

/// A vetKey: the BLS signature on an identity, used as IBE decryption key.
///
/// **Paper**: Section 2, p.6: "Recover(mpk, id, tsk, ek) -> K: A recovery
/// algorithm that enables the user to recover the derived key K for identity
/// id from the verified encrypted key ek using the transport secret key tsk."
///
/// In our convention: `vetkey = H(id)^sk` is a **G2** point (paper has G1).
/// This is both a valid BLS signature (verifiable via pairing) and the
/// decryption key for Boneh-Franklin IBE ciphertexts encrypted to `id`.
///
/// **Paper Section 3, p.7**: "A signature on a message m is sigma = H(m)^{sk}"
/// -- the vetKey IS the BLS signature on the identity string.
#[derive(Clone, Debug)]
pub struct VetKey(pub G2Affine);

/// Boneh-Franklin IBE ciphertext with Fujisaki-Okamoto CCA transform.
///
/// **Paper**: Section 6.2, protocol pi_vetibe, Figure 11 (p.31):
/// "On (sid, encrypt, mpk', id, m), P checks that m in {0,1}^l.
///  It calls H(id) to obtain h. It then chooses s <- {0,1}^kappa,
///  sets t = H3(s, m), and computes C = (g2^t, s XOR H2(e(h, mpk')^t), m XOR H4(s))"
///
/// In our convention, `u` is in G1 (paper has G2) because mpk is in G1 and
/// the pairing `e(mpk, H(id))` requires first arg in G1.
///
/// **Security**: Theorem 7 (p.32): "If the co-BDH problem is hard in (G1, G2)
/// and H2, H3, H4 are modeled as random oracles, then pi_vetibe securely
/// realizes F_vetibe"
#[derive(Clone, Debug)]
pub struct IBECiphertext {
    /// `g1^t` -- FO randomness point. Paper (p.31): "g2^t" (swapped for our convention).
    pub u: G1Affine,
    /// `s XOR H2(e(mpk, H(id))^t)` -- encrypted random seed (32 bytes).
    /// Paper (p.31): second component of ciphertext C.
    pub v: Vec<u8>,
    /// `m XOR H4(s)` -- encrypted message (variable length).
    /// Paper (p.31): third component of ciphertext C.
    pub w: Vec<u8>,
}

// ---------------------------------------------------------------------------
// Hash functions
// ---------------------------------------------------------------------------

/// Hash identity to G2 for IBE. Domain-separated from beacon hashing.
///
/// **Paper**: Section 3, p.7: "Let H: {0,1}* -> G1 be a hash function,
/// modeled as a random oracle." In our convention we hash to G2 instead.
///
/// **Paper**: Section 4.1, p.9: Used as the message space for BLS signatures
/// that serve as IBE decryption keys.
///
/// Domain separation prefix "vetkeys-ibe-identity:" ensures this hash is
/// independent from the beacon's `hash_to_g2` (which uses no prefix).
/// This separation is required by Theorem 11 / Corollary 1 (p.42-46)
/// for safe single-key composition of IBE with signatures and VRF.
///
/// Uses SHA-256 -> ChaCha8Rng -> G2Projective::rand for deterministic
/// hash-to-curve.
pub fn hash_identity_to_g2(identity: &[u8]) -> G2Affine {
    use ark_std::rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;

    let mut hasher = Sha256::new();
    hasher.update(b"vetkeys-ibe-identity:");
    hasher.update(identity);
    let hash = hasher.finalize();
    let mut seed = [0u8; 32];
    seed.copy_from_slice(&hash);
    let mut rng = ChaCha8Rng::from_seed(seed);
    G2Projective::rand(&mut rng).into_affine()
}

/// H2: Hash pairing target element to 32-byte mask for seed encryption.
///
/// **Paper**: Section 6.2, Figure 11 (p.31): "H2" is one of the random
/// oracles in the Boneh-Franklin FullIdent scheme. Maps G_T -> {0,1}^n
/// where n = 256 bits (our seed length).
///
/// Domain separation: "vetkeys-ibe-h2:" (Corollary 1, p.46).
fn hash_h2(gt: &<Bls12_381 as Pairing>::TargetField) -> [u8; 32] {
    let mut buf = Vec::new();
    gt.serialize_compressed(&mut buf).expect("GT serialize");
    let mut hasher = Sha256::new();
    hasher.update(b"vetkeys-ibe-h2:");
    hasher.update(&buf);
    let mut out = [0u8; 32];
    out.copy_from_slice(&hasher.finalize());
    out
}

/// H3: Hash (seed, message) to scalar for Fujisaki-Okamoto CCA transform.
///
/// **Paper**: Section 6.2, Figure 11 (p.31): "sets t = H3(s, m)".
/// This derandomization step converts the CPA-secure BasicIdent into the
/// CCA-secure FullIdent scheme [BF01]. The CCA check in `ibe_decrypt`
/// recomputes t and verifies u == g1^t.
///
/// Maps: {0,1}^256 x {0,1}^* -> Z_q (scalar field).
/// Domain separation: "vetkeys-ibe-h3:".
fn hash_h3(seed: &[u8; 32], message: &[u8]) -> Fr {
    use ark_std::rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;

    let mut hasher = Sha256::new();
    hasher.update(b"vetkeys-ibe-h3:");
    hasher.update(seed);
    hasher.update(message);
    let mut s = [0u8; 32];
    s.copy_from_slice(&hasher.finalize());
    let mut rng = ChaCha8Rng::from_seed(s);
    Fr::rand(&mut rng)
}

/// H4: Hash seed to variable-length byte mask for message encryption.
///
/// **Paper**: Section 6.2, Figure 11 (p.31): "m XOR H4(s)".
/// Maps: {0,1}^256 -> {0,1}^l where l = message length.
///
/// Implemented as chained SHA-256 blocks (counter mode) to support
/// arbitrary-length messages. The NCC audit (Finding RVN, p.9-11)
/// notes that very large messages cause proportional heap allocation;
/// for large payloads, prefer hybrid encryption (IBE for key, AES-GCM for data).
///
/// Domain separation: "vetkeys-ibe-h4:".
fn hash_h4(seed: &[u8; 32], len: usize) -> Vec<u8> {
    let mut result = Vec::with_capacity(len);
    let mut counter = 0u32;
    while result.len() < len {
        let mut hasher = Sha256::new();
        hasher.update(b"vetkeys-ibe-h4:");
        hasher.update(seed);
        hasher.update(counter.to_le_bytes());
        let block = hasher.finalize();
        let take = std::cmp::min(32, len - result.len());
        result.extend_from_slice(&block[..take]);
        counter += 1;
    }
    result
}

fn xor_bytes(a: &[u8], b: &[u8]) -> Vec<u8> {
    assert_eq!(a.len(), b.len());
    a.iter().zip(b.iter()).map(|(x, y)| x ^ y).collect()
}

// ---------------------------------------------------------------------------
// Transport key generation
// ---------------------------------------------------------------------------

/// Generate transport key pair: `tpk = g2^tsk`.
///
/// **Paper**: Section 2, p.6: "TKG() -> (tpk, tsk): A transport key generation
/// algorithm that a user can use to generate a transport public key tpk and
/// corresponding secret key tsk."
///
/// **Paper**: Section 5.3, pi_vetbls-agg2, Figure 9 (p.27): "On (sid,
/// transport-keygen), U chooses tsk <- Z_q, computes tpk <- g1^{tsk}"
/// (we use g2 instead of g1 for our G1-pk/G2-sig convention).
///
/// The transport key is ephemeral -- it only needs to be held for the
/// duration of one vetKD evaluation (Paper Section 2, p.7).
pub fn transport_keygen<R: Rng>(rng: &mut R) -> (TransportPublicKey, TransportSecretKey) {
    let tsk = Fr::rand(rng);
    let tpk = (G2Affine::generator() * tsk).into_affine();
    (TransportPublicKey(tpk), TransportSecretKey(tsk))
}

// ---------------------------------------------------------------------------
// Encrypted key share operations
// ---------------------------------------------------------------------------

/// Produce encrypted key share for given identity and transport key.
///
/// **Paper**: Section 5.3, protocol pi_vetbls-agg2, Figure 9 (p.27):
/// "On (sid, encsign, m, tpk), S_i computes sigma_i = H(m)^{sk_i},
///  encrypts sigma_i as (C1, C2, C3) = (g1^t, g2^t, tpk_1^t * sigma_i),
///  and sends es_i = (C1, C2, C3) to a combiner."
///
/// Steps (adapted to our G2-sig convention):
///   1. `sigma_i = H(id)^{sk_i}` -- partial BLS signature (G2)
///   2. Choose random `r <- Z_q`
///   3. `C1 = g1^r` -- ElGamal randomness (G1)
///   4. `C2 = g2^r` -- ElGamal randomness (G2, for pairing verification)
///   5. `C3 = tpk^r * sigma_i` -- encrypted partial sig (G2)
///
/// **Security**: Theorem 6 (p.25) proves this realizes F_vetbls^{cEG2}
/// under co-CDH hardness. The leakage (co-ElGamal encryption of sigma_i)
/// is shown harmless for IBE by Theorem 7 (p.32).
pub fn encrypt_key_share<R: Rng>(
    share: &KeyShare,
    identity: &[u8],
    tpk: &TransportPublicKey,
    rng: &mut R,
) -> EncryptedKeyShare {
    let h = hash_identity_to_g2(identity);
    let sigma_i = (h * share.secret).into_affine();

    let r = Fr::rand(rng);
    let c1 = (G1Affine::generator() * r).into_affine();
    let c2 = (G2Affine::generator() * r).into_affine();
    let c3 = (tpk.0 * r + G2Projective::from(sigma_i)).into_affine();

    EncryptedKeyShare { c1, c2, c3, signer: share.id }
}

/// Verify encrypted key share via pairing equations.
///
/// **Paper**: Section 5.3, pi_vetbls-agg2, Figure 9 (p.27):
/// "When a combiner receives this message, it checks that
///  e(C1, g2) = e(g1, C2) and that
///  e(C3, g2) = e(tpk, C2) * e(H(m), pk_i)"
///
/// Adapted to our convention (pk in G1, sig in G2):
///   Check 1: `e(C1, g2) = e(g1, C2)` -- G1/G2 randomness components are consistent
///   Check 2: `e(pk_i, H(id)) + e(C1, tpk) = e(g1, C3)` -- encryption is correct
///
/// This verification reveals NOTHING about sigma_i to the verifier.
/// The verifier only sees the encrypted form. (Paper Section 5.1, p.23:
/// "the encrypted signature shares actually do leak some information about
/// the signature share, namely, a verifiable ElGamal encryption of it.")
///
/// **NCC Audit**: Finding D7X (p.14) notes that identity checks on curve
/// points are important. Our pairing checks implicitly reject identity elements.
pub fn verify_encrypted_key_share(
    eks: &EncryptedKeyShare,
    identity: &[u8],
    tpk: &TransportPublicKey,
    pk_share: &G1Affine,
) -> bool {
    let g1 = G1Affine::generator();
    let g2 = G2Affine::generator();
    let h = hash_identity_to_g2(identity);

    // Check 1: e(C1, g2) = e(g1, C2)
    if Bls12_381::pairing(eks.c1, g2) != Bls12_381::pairing(g1, eks.c2) {
        return false;
    }

    // Check 2: e(pk_i, H(id)) + e(C1, tpk) = e(g1, C3)
    let lhs = Bls12_381::pairing(*pk_share, h) + Bls12_381::pairing(eks.c1, tpk.0);
    let rhs = Bls12_381::pairing(g1, eks.c3);
    lhs == rhs
}

/// Combine encrypted key shares via Lagrange interpolation in the exponent.
///
/// **Paper**: Section 5.3, pi_vetbls-agg2, Figure 9 (p.27):
/// "When it received t valid such es_i = (C_{i,1}, C_{i,2}, C_{i,3})
///  from different servers S_i, i in S, it computes
///  es = (C1, C2, C3) = (prod_{i in S} C_{i,1}^{Lambda_{i,S}(0)}, ...)"
///
/// Uses standard Lagrange basis polynomial evaluation at 0:
///   Lambda_{i,S}(0) = prod_{j in S, j != i} (x_j / (x_j - x_i))
/// where x_i are the Shamir evaluation points (node IDs).
///
/// **Paper**: Section 4.1, p.10: "sk = sum_{i in S} Lambda_{i,S}(0) * sk_i"
/// The same interpolation applies in the exponent to the encrypted shares.
///
/// **NCC Audit**: Finding XD6 (p.6-8) warns about duplicate share handling.
/// We take the first `threshold` shares, assuming distinct signers.
pub fn combine_encrypted_shares(
    shares: &[EncryptedKeyShare],
    threshold: usize,
) -> EncryptedVetKey {
    let shares = if shares.len() > threshold { &shares[..threshold] } else { shares };
    let ids: Vec<NodeId> = shares.iter().map(|s| s.signer).collect();

    let mut c1 = G1Projective::default();
    let mut c2 = G2Projective::default();
    let mut c3 = G2Projective::default();

    for s in shares {
        let li = lagrange_coeff(s.signer, &ids);
        c1 += s.c1 * li;
        c2 += s.c2 * li;
        c3 += s.c3 * li;
    }

    EncryptedVetKey {
        c1: c1.into_affine(),
        c2: c2.into_affine(),
        c3: c3.into_affine(),
    }
}

/// Verify combined encrypted vetKey via pairing equation.
///
/// **Paper**: Section 5.3, pi_vetbls-agg2, Figure 9 (p.27):
/// "When S_i receives es, it verifies that
///  e(C2, g2) = e(C1, tpk_2) * e(H(m), pk)"
///
/// Adapted to our convention:
///   `e(group_pk, H(id)) + e(C1, tpk) = e(g1, C3)`
///
/// This is the aggregated version of the per-share check. If this passes,
/// the encrypted vetKey is guaranteed to decrypt to a valid BLS signature.
pub fn verify_encrypted_vetkey(
    evk: &EncryptedVetKey,
    identity: &[u8],
    tpk: &TransportPublicKey,
    group_pk: &G1Affine,
) -> bool {
    let g1 = G1Affine::generator();
    let h = hash_identity_to_g2(identity);
    let lhs = Bls12_381::pairing(*group_pk, h) + Bls12_381::pairing(evk.c1, tpk.0);
    let rhs = Bls12_381::pairing(g1, evk.c3);
    lhs == rhs
}

/// Decrypt encrypted vetKey using transport secret key.
///
/// **Paper**: Section 5.3, pi_vetbls-agg2, Figure 9 (p.27):
/// "On (sid, decrypt, pk', m, tpk, es), U parses es as (C1, C2, C3)
///  and looks up tsk from its local state. It decrypts
///  sigma = C3 * C1^{-tsk} and checks whether e(sigma, g2) = e(H(m), pk')."
///
/// Adapted to our convention (C2 in G2, C3 in G2):
///   sigma = C3 - C2 * tsk
///         = (tpk^r * H(id)^sk) - (g2^r * tsk)
///         = (g2^{tsk*r} * H(id)^sk) - (g2^{r*tsk})
///         = H(id)^sk    -- the vetKey!
///
/// Verification: `e(group_pk, H(id)) = e(g1, sigma)`
/// This is the standard BLS verification equation applied to the identity.
///
/// Returns `None` if decrypted value fails BLS verification (tampered ciphertext
/// or wrong transport key).
pub fn decrypt_vetkey(
    evk: &EncryptedVetKey,
    tsk: &TransportSecretKey,
    identity: &[u8],
    group_pk: &G1Affine,
) -> Option<VetKey> {
    // sigma = C3 - C2 * tsk = (tpk^r * sigma) - g2^r * tsk = sigma
    let sigma = (G2Projective::from(evk.c3) - evk.c2 * tsk.0).into_affine();

    // Verify: e(group_pk, H(id)) = e(g1, sigma)
    let g1 = G1Affine::generator();
    let h = hash_identity_to_g2(identity);
    if Bls12_381::pairing(*group_pk, h) == Bls12_381::pairing(g1, sigma) {
        Some(VetKey(sigma))
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// Boneh-Franklin IBE
// ---------------------------------------------------------------------------

/// Encrypt a message to an identity using Boneh-Franklin IBE.
///
/// **Paper**: Section 6.2, protocol pi_vetibe, Figure 11 (p.31):
/// "On (sid, encrypt, mpk', id, m), P checks that m in {0,1}^l.
///  It calls (sid_vetbls, hash, id) on F_vetbls to obtain response h.
///  It then chooses s <- {0,1}^kappa, sets t = H3(s, m), and computes
///  C = (g2^t, s XOR H2(e(h, mpk')^t), m XOR H4(s))"
///
/// **Key property**: Anyone can encrypt using ONLY the group public key and
/// the recipient's identity. No interaction with the network is needed.
/// The recipient can be offline. This is the defining feature of IBE.
///
/// **Original paper**: Boneh & Franklin [BF01], "Identity-Based Encryption
/// from the Weil Pairing", CRYPTO 2001. The FullIdent scheme uses the
/// Fujisaki-Okamoto transform (H3, H4) to achieve CCA security from
/// a CPA-secure BasicIdent scheme.
///
/// **Security**: Theorem 7 (p.32): pi_vetibe realizes F_vetibe under
/// co-BDH hardness in the random oracle model for H2, H3, H4.
///
/// Steps (adapted to our G1-pk convention):
///   1. Choose random seed `s <- {0,1}^256`
///   2. `t = H3(s, message)` -- FO derandomization
///   3. `u = g1^t` -- randomness point (G1; paper has g2^t)
///   4. `v = s XOR H2(e(mpk * t, H(id)))` -- encrypted seed
///   5. `w = message XOR H4(s)` -- encrypted message
pub fn ibe_encrypt<R: Rng>(
    group_pk: &G1Affine,
    identity: &[u8],
    message: &[u8],
    rng: &mut R,
) -> IBECiphertext {
    let h = hash_identity_to_g2(identity);

    let mut seed = [0u8; 32];
    rng.fill_bytes(&mut seed);

    let t = hash_h3(&seed, message);

    // u = g1^t (G1 -- first pairing argument)
    let u = (G1Affine::generator() * t).into_affine();

    // e(mpk, H(id))^t = e(mpk * t, H(id)) -- single pairing
    let mpk_t = (*group_pk * t).into_affine();
    let pairing_val = Bls12_381::pairing(mpk_t, h);

    let h2_mask = hash_h2(&pairing_val.0);
    let v = xor_bytes(&seed, &h2_mask);

    let h4_mask = hash_h4(&seed, message.len());
    let w = xor_bytes(message, &h4_mask);

    IBECiphertext { u, v, w }
}

/// Decrypt IBE ciphertext using vetKey (BLS signature on the identity).
///
/// **Paper**: Section 6.2, protocol pi_vetibe, Figure 11 (p.31):
/// "On (sid, decrypt, id, C), user U checks whether it has a record (id, K)
///  in its state. If not, it ignores this input. Otherwise, it parses
///  C = (C1, C2, C3), computes s = C2 XOR H2(e(K, C1)), and recovers
///  m = C3 XOR H4(s). It also computes t = H3(s, m) and checks whether
///  C1 = g2^t."
///
/// Steps (adapted to our convention where u is in G1 and vetkey is in G2):
///   1. Compute `e(u, vetkey) = e(g1^t, H(id)^sk) = e(g1, H(id))^{t*sk}`
///   2. Recover seed: `s = v XOR H2(pairing_value)`
///   3. Recover message: `m = w XOR H4(s)`
///   4. **CCA check**: recompute `t = H3(s, m)` and verify `u == g1^t`
///
/// The CCA check (step 4) is the Fujisaki-Okamoto verification that rejects
/// maliciously modified ciphertexts. Without it, the scheme would only be
/// CPA-secure (BasicIdent). With it, the scheme is CCA-secure (FullIdent).
///
/// Returns `None` if:
///   - Seed length mismatch (v is not 32 bytes)
///   - CCA check fails (ciphertext was tampered with)
///   - Wrong vetKey (identity mismatch -- pairing produces wrong mask)
pub fn ibe_decrypt(vetkey: &VetKey, ct: &IBECiphertext) -> Option<Vec<u8>> {
    // e(u, vetkey) = e(g1^t, H(id)^sk) = e(g1, H(id))^{t*sk}
    let pairing_val = Bls12_381::pairing(ct.u, vetkey.0);

    // Recover seed: s = v XOR H2(pairing_value)
    let h2_mask = hash_h2(&pairing_val.0);
    if ct.v.len() != 32 {
        return None;
    }
    let seed_vec = xor_bytes(&ct.v, &h2_mask);
    let mut seed = [0u8; 32];
    seed.copy_from_slice(&seed_vec);

    // Recover message: m = w XOR H4(s)
    let h4_mask = hash_h4(&seed, ct.w.len());
    let message = xor_bytes(&ct.w, &h4_mask);

    // CCA check (Fujisaki-Okamoto): t = H3(s, m), verify u == g1^t
    // Paper (p.31): "computes t = H3(s, m) and checks whether C1 = g2^t"
    let t = hash_h3(&seed, &message);
    let expected_u = (G1Affine::generator() * t).into_affine();
    if expected_u != ct.u {
        return None; // Ciphertext tampered or wrong identity
    }

    Some(message)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dkg;

    fn setup(n: u32, t: u32) -> (Vec<KeyShare>, crate::types::GroupInfo) {
        dkg::run_dkg(n, t)
    }

    #[test]
    fn hash_identity_deterministic() {
        let a = hash_identity_to_g2(b"alice");
        let b = hash_identity_to_g2(b"alice");
        assert_eq!(a, b);
    }

    #[test]
    fn hash_identity_distinct() {
        assert_ne!(hash_identity_to_g2(b"alice"), hash_identity_to_g2(b"bob"));
    }

    #[test]
    fn transport_keygen_consistent() {
        let mut rng = ark_std::test_rng();
        let (tpk, tsk) = transport_keygen(&mut rng);
        assert_eq!(tpk.0, (G2Affine::generator() * tsk.0).into_affine());
    }

    #[test]
    fn encrypted_share_verifies() {
        let mut rng = ark_std::test_rng();
        let (shares, _group) = setup(4, 3);
        let (tpk, _tsk) = transport_keygen(&mut rng);
        let id = b"test";

        let eks = encrypt_key_share(&shares[0], id, &tpk, &mut rng);
        let pk_share = (G1Affine::generator() * shares[0].secret).into_affine();

        assert!(verify_encrypted_key_share(&eks, id, &tpk, &pk_share));
        assert!(!verify_encrypted_key_share(&eks, b"wrong", &tpk, &pk_share));
    }

    #[test]
    fn vetkey_roundtrip() {
        let mut rng = ark_std::test_rng();
        let (shares, group) = setup(4, 3);
        let (tpk, tsk) = transport_keygen(&mut rng);
        let id = b"alice@example.com";

        let enc_shares: Vec<_> = shares.iter()
            .map(|s| encrypt_key_share(s, id, &tpk, &mut rng))
            .collect();

        // Verify each share
        for (i, eks) in enc_shares.iter().enumerate() {
            let pk_i = (G1Affine::generator() * shares[i].secret).into_affine();
            assert!(verify_encrypted_key_share(eks, id, &tpk, &pk_i), "share {i}");
        }

        let evk = combine_encrypted_shares(&enc_shares, group.threshold as usize);
        assert!(verify_encrypted_vetkey(&evk, id, &tpk, &group.public_key));

        let vk = decrypt_vetkey(&evk, &tsk, id, &group.public_key).expect("decrypt");

        // Verify vetkey is valid BLS sig on identity
        let g1 = G1Affine::generator();
        let h = hash_identity_to_g2(id);
        assert_eq!(Bls12_381::pairing(group.public_key, h), Bls12_381::pairing(g1, vk.0));
    }

    #[test]
    fn ibe_roundtrip() {
        let mut rng = ark_std::test_rng();
        let (shares, group) = setup(4, 3);
        let id = b"alice@example.com";
        let msg = b"Hello, Alice! This is secret.";

        let ct = ibe_encrypt(&group.public_key, id, msg, &mut rng);

        let (tpk, tsk) = transport_keygen(&mut rng);
        let enc_shares: Vec<_> = shares.iter()
            .map(|s| encrypt_key_share(s, id, &tpk, &mut rng))
            .collect();
        let evk = combine_encrypted_shares(&enc_shares, group.threshold as usize);
        let vk = decrypt_vetkey(&evk, &tsk, id, &group.public_key).unwrap();

        let recovered = ibe_decrypt(&vk, &ct).expect("IBE decrypt");
        assert_eq!(recovered, msg);
    }

    #[test]
    fn ibe_wrong_identity_fails() {
        let mut rng = ark_std::test_rng();
        let (shares, group) = setup(4, 3);

        let ct = ibe_encrypt(&group.public_key, b"alice", b"secret", &mut rng);

        let (tpk, tsk) = transport_keygen(&mut rng);
        let enc_shares: Vec<_> = shares.iter()
            .map(|s| encrypt_key_share(s, b"bob", &tpk, &mut rng))
            .collect();
        let evk = combine_encrypted_shares(&enc_shares, group.threshold as usize);
        let vk_bob = decrypt_vetkey(&evk, &tsk, b"bob", &group.public_key).unwrap();

        assert!(ibe_decrypt(&vk_bob, &ct).is_none(), "wrong identity must fail");
    }

    #[test]
    fn threshold_subset_sufficient() {
        let mut rng = ark_std::test_rng();
        let (shares, group) = setup(7, 5);
        let (tpk, tsk) = transport_keygen(&mut rng);
        let id = b"threshold-test";

        let enc_shares: Vec<_> = shares[..5].iter()
            .map(|s| encrypt_key_share(s, id, &tpk, &mut rng))
            .collect();
        let evk = combine_encrypted_shares(&enc_shares, group.threshold as usize);
        assert!(decrypt_vetkey(&evk, &tsk, id, &group.public_key).is_some());
    }

    #[test]
    fn ibe_empty_message() {
        let mut rng = ark_std::test_rng();
        let (shares, group) = setup(4, 3);
        let id = b"empty";

        let ct = ibe_encrypt(&group.public_key, id, b"", &mut rng);

        let (tpk, tsk) = transport_keygen(&mut rng);
        let enc_shares: Vec<_> = shares.iter()
            .map(|s| encrypt_key_share(s, id, &tpk, &mut rng))
            .collect();
        let evk = combine_encrypted_shares(&enc_shares, group.threshold as usize);
        let vk = decrypt_vetkey(&evk, &tsk, id, &group.public_key).unwrap();

        assert_eq!(ibe_decrypt(&vk, &ct).unwrap(), b"");
    }

    #[test]
    fn ibe_large_message() {
        let mut rng = ark_std::test_rng();
        let (shares, group) = setup(4, 3);
        let id = b"large";
        let msg = vec![0x42u8; 10_000];

        let ct = ibe_encrypt(&group.public_key, id, &msg, &mut rng);

        let (tpk, tsk) = transport_keygen(&mut rng);
        let enc_shares: Vec<_> = shares.iter()
            .map(|s| encrypt_key_share(s, id, &tpk, &mut rng))
            .collect();
        let evk = combine_encrypted_shares(&enc_shares, group.threshold as usize);
        let vk = decrypt_vetkey(&evk, &tsk, id, &group.public_key).unwrap();

        assert_eq!(ibe_decrypt(&vk, &ct).unwrap(), msg);
    }
}
