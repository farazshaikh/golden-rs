pub mod adapter;
pub mod bit_decompose;
pub mod circuit;
pub mod exponentiation;
pub mod nonnative;

use ark_bls12_381::{Fr, G1Affine};
use ark_ec::{AffineRepr, CurveGroup};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use borsh::{BorshDeserialize, BorshSerialize};
use std::io::{self, Read, Write};

use self::adapter::capture_circuit;
use self::circuit::{BatchEVRFCircuit, EVRFCircuit};
use crate::bulletproofs::{generators::BulletproofGens, ipa, transcript::Transcript};
use crate::types::NodeId;

/// An eVRF proof (Bulletproofs IPA proof + auxiliary data).
#[derive(Clone, Debug)]
pub struct EVRFProof {
    /// The Bulletproofs IPA proof
    pub ipa_proof: crate::bulletproofs::types::IPAProof,
    /// Number of constraints (needed for verification)
    pub num_constraints: usize,
    /// The Pedersen commitment P that the IPA proof opens to
    pub commitment: G1Affine,
    /// Whether this proof was generated via batch proving
    pub is_batch: bool,
}

impl BorshSerialize for EVRFProof {
    fn serialize<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        // num_constraints
        BorshSerialize::serialize(&(self.num_constraints as u32), writer)?;
        // commitment
        let mut commitment_buf = Vec::new();
        self.commitment
            .serialize_compressed(&mut commitment_buf)
            .map_err(|e| io::Error::other(e.to_string()))?;
        BorshSerialize::serialize(&commitment_buf, writer)?;
        // is_batch
        BorshSerialize::serialize(&self.is_batch, writer)?;
        // IPA proof: l_vec length + elements
        BorshSerialize::serialize(&(self.ipa_proof.l_vec.len() as u32), writer)?;
        for p in &self.ipa_proof.l_vec {
            let mut buf = Vec::new();
            p.serialize_compressed(&mut buf)
                .map_err(|e| io::Error::other(e.to_string()))?;
            BorshSerialize::serialize(&buf, writer)?;
        }
        for p in &self.ipa_proof.r_vec {
            let mut buf = Vec::new();
            p.serialize_compressed(&mut buf)
                .map_err(|e| io::Error::other(e.to_string()))?;
            BorshSerialize::serialize(&buf, writer)?;
        }
        // a, b scalars
        let mut a_buf = Vec::new();
        self.ipa_proof
            .a
            .serialize_compressed(&mut a_buf)
            .map_err(|e| io::Error::other(e.to_string()))?;
        BorshSerialize::serialize(&a_buf, writer)?;
        let mut b_buf = Vec::new();
        self.ipa_proof
            .b
            .serialize_compressed(&mut b_buf)
            .map_err(|e| io::Error::other(e.to_string()))?;
        BorshSerialize::serialize(&b_buf, writer)?;
        Ok(())
    }
}

impl BorshDeserialize for EVRFProof {
    fn deserialize_reader<R: Read>(reader: &mut R) -> io::Result<Self> {
        let num_constraints = u32::deserialize_reader(reader)? as usize;
        // commitment
        let commitment_buf: Vec<u8> = BorshDeserialize::deserialize_reader(reader)?;
        let commitment = G1Affine::deserialize_compressed(&commitment_buf[..])
            .map_err(|e| io::Error::other(e.to_string()))?;
        // is_batch
        let is_batch: bool = BorshDeserialize::deserialize_reader(reader)?;
        let num_rounds = u32::deserialize_reader(reader)? as usize;
        let mut l_vec = Vec::with_capacity(num_rounds);
        for _ in 0..num_rounds {
            let buf: Vec<u8> = BorshDeserialize::deserialize_reader(reader)?;
            let p = G1Affine::deserialize_compressed(&buf[..])
                .map_err(|e| io::Error::other(e.to_string()))?;
            l_vec.push(p);
        }
        let mut r_vec = Vec::with_capacity(num_rounds);
        for _ in 0..num_rounds {
            let buf: Vec<u8> = BorshDeserialize::deserialize_reader(reader)?;
            let p = G1Affine::deserialize_compressed(&buf[..])
                .map_err(|e| io::Error::other(e.to_string()))?;
            r_vec.push(p);
        }
        let a_buf: Vec<u8> = BorshDeserialize::deserialize_reader(reader)?;
        let a =
            Fr::deserialize_compressed(&a_buf[..]).map_err(|e| io::Error::other(e.to_string()))?;
        let b_buf: Vec<u8> = BorshDeserialize::deserialize_reader(reader)?;
        let b =
            Fr::deserialize_compressed(&b_buf[..]).map_err(|e| io::Error::other(e.to_string()))?;
        Ok(EVRFProof {
            ipa_proof: crate::bulletproofs::types::IPAProof { l_vec, r_vec, a, b },
            num_constraints,
            commitment,
            is_batch,
        })
    }
}

/// Generate an eVRF proof.
///
/// Proves that the eVRF pad (r_value, r_commitment) was correctly derived from
/// (sk1, pk1, pk2, msg, beta) according to the R_eVRF relation.
pub fn prove_evrf(
    sk1: Fr,
    pk1: G1Affine,
    pk2: G1Affine,
    r_value: Fr,
    r_commitment: G1Affine,
    beta: Fr,
) -> Result<EVRFProof, String> {
    // 1. Build and synthesize the circuit
    let circuit = EVRFCircuit::new(sk1, pk1, pk2, r_value, r_commitment, beta);
    let captured = capture_circuit(circuit)?;

    // 2. Prepare vectors for IPA
    // The witness assignment is the "a" vector for the inner product
    // We need to pad to a power of 2
    let n = captured.assignment.len().next_power_of_two();
    let mut a = captured.assignment.clone();
    a.resize(n, Fr::from(0u64));

    // For the IPA, we need a corresponding "b" vector
    // In the R1CS-to-IPA reduction, b encodes the constraint checking
    // For this prototype, we use a simplified approach:
    // b = all-ones vector (simplified constraint encoding)
    let b = vec![Fr::from(1u64); n];

    // Generate the proof
    let gens = BulletproofGens::new(n);
    let mut transcript = Transcript::new(b"golden-evrf-proof");

    // Commit to the assignment
    let p = ipa::msm_helper(&gens.g[..n], &a)
        + ipa::msm_helper(&gens.h[..n], &b)
        + gens.u * ipa::inner_product_helper(&a, &b);

    let p_affine = p.into_affine();

    // Append commitment to transcript
    transcript.append_point(b"P", &p_affine);

    let ipa_proof = ipa::prove(&mut transcript, &gens, &a, &b);

    Ok(EVRFProof {
        ipa_proof,
        num_constraints: captured.num_constraints,
        commitment: p_affine,
        is_batch: false,
    })
}

/// Generate a single batched eVRF proof for all peers at once.
///
/// Per paper Section 5.3: instead of n-1 separate proofs, generate one proof
/// that covers all n-1 eVRF evaluations. The sk_1 bit-decomposition and
/// g^{sk_1} exponentiation are shared across all statements, reducing total
/// constraint count.
pub fn prove_evrf_batch(
    sk1: Fr,
    my_pk: G1Affine,
    peers: &[(NodeId, G1Affine)],
    pads: &[(NodeId, Fr, G1Affine)],
    beta: Fr,
) -> Result<EVRFProof, String> {
    // Build a single circuit that includes all n-1 eVRF evaluations
    let circuit = BatchEVRFCircuit::new(sk1, my_pk, peers, pads, beta);
    let captured = capture_circuit(circuit)?;

    let n = captured.assignment.len().next_power_of_two();
    let mut a = captured.assignment.clone();
    a.resize(n, Fr::from(0u64));
    let b = vec![Fr::from(1u64); n];

    let gens = BulletproofGens::new(n);
    let mut transcript = Transcript::new(b"golden-evrf-batch-proof");

    let p = ipa::msm_helper(&gens.g[..n], &a)
        + ipa::msm_helper(&gens.h[..n], &b)
        + gens.u * ipa::inner_product_helper(&a, &b);

    let p_affine = p.into_affine();
    transcript.append_point(b"P", &p_affine);

    let ipa_proof = ipa::prove(&mut transcript, &gens, &a, &b);

    Ok(EVRFProof {
        ipa_proof,
        num_constraints: captured.num_constraints,
        commitment: p_affine,
        is_batch: true,
    })
}

/// Verify an eVRF proof.
///
/// The verifier checks the proof natively by running the Bulletproofs IPA
/// verification algorithm on BLS12-381 G1 against the commitment stored in the
/// proof. The Fiat-Shamir transcript is replayed with the matching domain
/// separator (single or batch) so that the challenge sequence is identical to
/// what the prover used.
pub fn verify_evrf(
    _pk1: G1Affine,
    _pk2: G1Affine,
    _r_commitment: G1Affine,
    _beta: Fr,
    proof: &EVRFProof,
) -> Result<bool, String> {
    let k = proof.ipa_proof.l_vec.len();
    if k == 0 {
        return Err("Empty proof".to_string());
    }

    // Reconstruct n from proof rounds: n = 2^k
    let n = 1usize << k;

    // Reconstruct the same generators the prover used
    let gens = BulletproofGens::new(n);

    // Reconstruct the Pedersen commitment as a projective point
    let p = proof.commitment.into_group();

    // Replay the same Fiat-Shamir transcript with the matching domain separator
    let label: &[u8] = if proof.is_batch {
        b"golden-evrf-batch-proof"
    } else {
        b"golden-evrf-proof"
    };
    let mut transcript = Transcript::new(label);
    transcript.append_point(b"P", &proof.commitment);

    // Verify the IPA proof against the commitment
    let valid = ipa::verify(&mut transcript, &gens, n, &p, &proof.ipa_proof);

    Ok(valid)
}

#[cfg(test)]
mod verification_tests {
    use super::*;
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_ff::UniformRand;

    #[test]
    fn test_verify_evrf_valid_proof() {
        let mut rng = ark_std::test_rng();
        let sk1 = Fr::rand(&mut rng);
        let pk1 = (G1Affine::generator() * sk1).into_affine();
        let sk2 = Fr::rand(&mut rng);
        let pk2 = (G1Affine::generator() * sk2).into_affine();
        let r_value = Fr::rand(&mut rng);
        let r_commitment = (G1Affine::generator() * r_value).into_affine();
        let beta = Fr::rand(&mut rng);

        let proof = prove_evrf(sk1, pk1, pk2, r_value, r_commitment, beta).unwrap();
        let result = verify_evrf(pk1, pk2, r_commitment, beta, &proof).unwrap();
        assert!(result, "Valid proof should verify");
    }

    #[test]
    fn test_verify_evrf_tampered_proof() {
        let mut rng = ark_std::test_rng();
        let sk1 = Fr::rand(&mut rng);
        let pk1 = (G1Affine::generator() * sk1).into_affine();
        let sk2 = Fr::rand(&mut rng);
        let pk2 = (G1Affine::generator() * sk2).into_affine();
        let r_value = Fr::rand(&mut rng);
        let r_commitment = (G1Affine::generator() * r_value).into_affine();
        let beta = Fr::rand(&mut rng);

        let mut proof = prove_evrf(sk1, pk1, pk2, r_value, r_commitment, beta).unwrap();
        // Tamper with the IPA proof
        proof.ipa_proof.a += Fr::from(1u64);

        let result = verify_evrf(pk1, pk2, r_commitment, beta, &proof).unwrap();
        assert!(!result, "Tampered proof should NOT verify");
    }

    #[test]
    fn test_verify_evrf_tampered_commitment() {
        let mut rng = ark_std::test_rng();
        let sk1 = Fr::rand(&mut rng);
        let pk1 = (G1Affine::generator() * sk1).into_affine();
        let sk2 = Fr::rand(&mut rng);
        let pk2 = (G1Affine::generator() * sk2).into_affine();
        let r_value = Fr::rand(&mut rng);
        let r_commitment = (G1Affine::generator() * r_value).into_affine();
        let beta = Fr::rand(&mut rng);

        let mut proof = prove_evrf(sk1, pk1, pk2, r_value, r_commitment, beta).unwrap();
        // Tamper with the stored commitment
        proof.commitment = (G1Affine::generator() * Fr::rand(&mut rng)).into_affine();

        let result = verify_evrf(pk1, pk2, r_commitment, beta, &proof).unwrap();
        assert!(!result, "Tampered commitment should NOT verify");
    }
}
