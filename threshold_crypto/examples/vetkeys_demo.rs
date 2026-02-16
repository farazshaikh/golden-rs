//! vetKeys IBE Demo
//!
//! Demonstrates the full vetKeys Identity-Based Encryption flow:
//!
//! 1. DKG: Threshold group generates shared BLS key
//! 2. Encrypt: Anyone encrypts a message to an identity string
//! 3. Derive: Threshold nodes produce encrypted key shares for the recipient
//! 4. Decrypt: Recipient recovers the vetKey and decrypts the IBE ciphertext
//!
//! Usage:
//!   cargo run --example vetkeys_demo
//!   cargo run --example vetkeys_demo -- --identity "bob@example.com" --message "Top secret"
//!   cargo run --example vetkeys_demo -- --nodes 10 --threshold 7

use std::time::Instant;

use ark_ec::AffineRepr;
use threshold_demo::{dkg, ibe};

fn main() {
    let args: Vec<String> = std::env::args().collect();

    let n: u32 = find_arg(&args, "--nodes").unwrap_or(7);
    let t: u32 = find_arg(&args, "--threshold").unwrap_or(5);
    let identity = find_str_arg(&args, "--identity")
        .unwrap_or_else(|| "alice@example.com".to_string());
    let message = find_str_arg(&args, "--message")
        .unwrap_or_else(|| "Hello from vetKeys! This message is encrypted to an identity.".to_string());

    println!("=== vetKeys IBE Demo ===");
    println!();
    println!("Network: n={n}, threshold={t}");
    println!("Identity: {identity}");
    println!("Message:  {} ({} bytes)", truncate(&message, 60), message.len());
    println!();

    // Step 1: DKG
    print!("Step 1: Running DKG...");
    let t0 = Instant::now();
    let (shares, group) = dkg::run_dkg(n, t);
    println!(" done ({:.0?})", t0.elapsed());
    println!("  Group public key: {}", hex_short(&pk_bytes(&group.public_key)));
    println!();

    // Step 2: IBE Encrypt (anyone can do this, no network needed)
    print!("Step 2: Encrypting message to identity \"{identity}\"...");
    let mut rng = ark_std::test_rng();
    let t0 = Instant::now();
    let ciphertext = ibe::ibe_encrypt(&group.public_key, identity.as_bytes(), message.as_bytes(), &mut rng);
    println!(" done ({:.0?})", t0.elapsed());
    println!("  Ciphertext: u={}, v={}, w={}",
        hex_short(&g1_bytes(&ciphertext.u)),
        hex_short(&ciphertext.v),
        hex_short(&ciphertext.w));
    println!();

    // Step 3: Recipient generates transport key pair
    print!("Step 3: Recipient generates transport key pair...");
    let t0 = Instant::now();
    let (tpk, tsk) = ibe::transport_keygen(&mut rng);
    println!(" done ({:.0?})", t0.elapsed());
    println!("  Transport PK: {}", hex_short(&g2_bytes(&tpk.0)));
    println!();

    // Step 4: Each node produces an encrypted key share
    println!("Step 4: Nodes produce encrypted key shares...");
    let t0 = Instant::now();
    let encrypted_shares: Vec<_> = shares.iter()
        .map(|s| ibe::encrypt_key_share(s, identity.as_bytes(), &tpk, &mut rng))
        .collect();
    let share_time = t0.elapsed();

    // Verify each share
    let t0 = Instant::now();
    let mut verified = 0;
    for (i, eks) in encrypted_shares.iter().enumerate() {
        let pk_i = (ark_bls12_381::G1Affine::generator() * shares[i].secret).into();
        if ibe::verify_encrypted_key_share(eks, identity.as_bytes(), &tpk, &pk_i) {
            verified += 1;
        }
    }
    let verify_time = t0.elapsed();
    println!("  {n} shares produced ({:.0?}), {verified}/{n} verified ({:.0?})", share_time, verify_time);
    println!();

    // Step 5: Combine encrypted shares
    print!("Step 5: Combining {t} encrypted shares...");
    let t0 = Instant::now();
    let evk = ibe::combine_encrypted_shares(&encrypted_shares, t as usize);
    println!(" done ({:.0?})", t0.elapsed());

    // Verify combined
    let valid = ibe::verify_encrypted_vetkey(&evk, identity.as_bytes(), &tpk, &group.public_key);
    println!("  Combined encrypted vetKey valid: {valid}");
    println!();

    // Step 6: Recipient decrypts the vetKey
    print!("Step 6: Decrypting vetKey with transport secret key...");
    let t0 = Instant::now();
    let vetkey = ibe::decrypt_vetkey(&evk, &tsk, identity.as_bytes(), &group.public_key)
        .expect("vetKey decryption failed");
    println!(" done ({:.0?})", t0.elapsed());
    println!("  vetKey (BLS sig on identity): {}", hex_short(&g2_bytes(&vetkey.0)));
    println!();

    // Step 7: Decrypt the IBE ciphertext
    print!("Step 7: Decrypting IBE ciphertext with vetKey...");
    let t0 = Instant::now();
    let recovered = ibe::ibe_decrypt(&vetkey, &ciphertext)
        .expect("IBE decryption failed");
    println!(" done ({:.0?})", t0.elapsed());
    println!("  Recovered: {}", String::from_utf8_lossy(&recovered));
    println!();

    assert_eq!(recovered, message.as_bytes(), "Message mismatch!");
    println!("SUCCESS: Message encrypted to identity, threshold-derived, and decrypted.");

    // Negative test: wrong identity
    println!();
    println!("--- Negative test: wrong identity ---");
    let wrong_shares: Vec<_> = shares.iter()
        .map(|s| ibe::encrypt_key_share(s, b"eve@evil.com", &tpk, &mut rng))
        .collect();
    let wrong_evk = ibe::combine_encrypted_shares(&wrong_shares, t as usize);
    let wrong_vk = ibe::decrypt_vetkey(&wrong_evk, &tsk, b"eve@evil.com", &group.public_key)
        .expect("eve's vetkey");
    match ibe::ibe_decrypt(&wrong_vk, &ciphertext) {
        None => println!("  CORRECT: Eve's vetKey cannot decrypt Alice's ciphertext."),
        Some(_) => println!("  BUG: Eve decrypted Alice's message!"),
    }
}

fn find_arg<T: std::str::FromStr>(args: &[String], flag: &str) -> Option<T> {
    args.windows(2).find(|w| w[0] == flag).and_then(|w| w[1].parse().ok())
}

fn find_str_arg(args: &[String], flag: &str) -> Option<String> {
    args.windows(2).find(|w| w[0] == flag).map(|w| w[1].clone())
}

fn hex_short(bytes: &[u8]) -> String {
    let hex: String = bytes.iter().take(12).map(|b| format!("{b:02x}")).collect();
    if bytes.len() > 12 { format!("{hex}...") } else { hex }
}

fn truncate(s: &str, max: usize) -> String {
    if s.len() > max { format!("{}...", &s[..max]) } else { s.to_string() }
}

fn pk_bytes(pk: &ark_bls12_381::G1Affine) -> Vec<u8> {
    use ark_serialize::CanonicalSerialize;
    let mut buf = Vec::new();
    pk.serialize_compressed(&mut buf).unwrap();
    buf
}

fn g1_bytes(p: &ark_bls12_381::G1Affine) -> Vec<u8> {
    use ark_serialize::CanonicalSerialize;
    let mut buf = Vec::new();
    p.serialize_compressed(&mut buf).unwrap();
    buf
}

fn g2_bytes(p: &ark_bls12_381::G2Affine) -> Vec<u8> {
    use ark_serialize::CanonicalSerialize;
    let mut buf = Vec::new();
    p.serialize_compressed(&mut buf).unwrap();
    buf
}
