use ark_bls12_381::{Fr, G1Affine, G1Projective};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use borsh::{BorshDeserialize, BorshSerialize};
use std::collections::HashMap;
use std::io::{self, Read, Write};

pub type NodeId = u32;
pub type Scalar = Fr;
pub type G1 = G1Projective;

/// Helper: serialize an arkworks type to bytes via CanonicalSerialize (compressed).
fn ark_to_bytes<T: CanonicalSerialize>(val: &T) -> Vec<u8> {
    let mut buf = Vec::new();
    val.serialize_compressed(&mut buf)
        .expect("ark serialization failed");
    buf
}

/// Helper: deserialize an arkworks type from bytes via CanonicalDeserialize (compressed).
fn ark_from_bytes<T: CanonicalDeserialize>(bytes: &[u8]) -> T {
    T::deserialize_compressed(bytes).expect("ark deserialization failed")
}

/// A single encrypted share from node i to node j
#[derive(Clone, Debug)]
pub struct Ciphertext {
    /// R_{i,j} = g^{r_{i,j}} -- commitment to the eVRF pad
    pub r_commitment: G1Affine,
    /// z_{i,j} = r_{i,j} + share_{i,j} -- encrypted Shamir share
    pub encrypted_share: Scalar,
}

impl BorshSerialize for Ciphertext {
    fn serialize<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        let r_bytes = ark_to_bytes(&self.r_commitment);
        let s_bytes = ark_to_bytes(&self.encrypted_share);
        BorshSerialize::serialize(&r_bytes, writer)?;
        BorshSerialize::serialize(&s_bytes, writer)?;
        Ok(())
    }
}

impl BorshDeserialize for Ciphertext {
    fn deserialize_reader<R: Read>(reader: &mut R) -> io::Result<Self> {
        let r_bytes: Vec<u8> = BorshDeserialize::deserialize_reader(reader)?;
        let s_bytes: Vec<u8> = BorshDeserialize::deserialize_reader(reader)?;
        Ok(Ciphertext {
            r_commitment: ark_from_bytes(&r_bytes),
            encrypted_share: ark_from_bytes(&s_bytes),
        })
    }
}

/// Round 0 broadcast message from a single node
#[derive(Clone, Debug)]
pub struct Round0Msg {
    /// Sender node ID
    pub from: NodeId,
    /// Random message used for eVRF evaluation
    pub random_msg: [u8; 32],
    /// Feldman VSS commitment: (A_{i,0}, ..., A_{i,t-1}) where A_{i,k} = g^{a_k}
    pub vss_commitment: Vec<G1Affine>,
    /// Encrypted shares: one Ciphertext per peer (keyed by recipient NodeId)
    pub ciphertexts: HashMap<NodeId, Ciphertext>,
}

impl BorshSerialize for Round0Msg {
    fn serialize<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        BorshSerialize::serialize(&self.from, writer)?;
        BorshSerialize::serialize(&self.random_msg, writer)?;
        // vss_commitment: Vec<G1Affine> -- serialize each element as bytes
        let commitment_bytes: Vec<Vec<u8>> = self.vss_commitment.iter().map(ark_to_bytes).collect();
        BorshSerialize::serialize(&commitment_bytes, writer)?;
        // ciphertexts: HashMap<NodeId, Ciphertext> -- serialize as length + entries
        let ct_entries: Vec<(NodeId, &Ciphertext)> =
            self.ciphertexts.iter().map(|(&k, v)| (k, v)).collect();
        let len = ct_entries.len() as u32;
        BorshSerialize::serialize(&len, writer)?;
        for (node_id, ct) in ct_entries {
            BorshSerialize::serialize(&node_id, writer)?;
            BorshSerialize::serialize(ct, writer)?;
        }
        Ok(())
    }
}

impl BorshDeserialize for Round0Msg {
    fn deserialize_reader<R: Read>(reader: &mut R) -> io::Result<Self> {
        let from: NodeId = BorshDeserialize::deserialize_reader(reader)?;
        let random_msg: [u8; 32] = BorshDeserialize::deserialize_reader(reader)?;
        let commitment_bytes: Vec<Vec<u8>> = BorshDeserialize::deserialize_reader(reader)?;
        let vss_commitment: Vec<G1Affine> =
            commitment_bytes.iter().map(|b| ark_from_bytes(b)).collect();
        let len: u32 = BorshDeserialize::deserialize_reader(reader)?;
        let mut ciphertexts = HashMap::new();
        for _ in 0..len {
            let node_id: NodeId = BorshDeserialize::deserialize_reader(reader)?;
            let ct: Ciphertext = BorshDeserialize::deserialize_reader(reader)?;
            ciphertexts.insert(node_id, ct);
        }
        Ok(Round0Msg {
            from,
            random_msg,
            vss_commitment,
            ciphertexts,
        })
    }
}

/// Reshare broadcast message (same structure as Round0Msg).
#[derive(Clone, Debug)]
pub struct ReshareMsg {
    pub from: NodeId,
    pub random_msg: [u8; 32],
    pub vss_commitment: Vec<G1Affine>,
    pub ciphertexts: HashMap<NodeId, Ciphertext>,
}

/// Output of the DKG protocol for a single node
#[derive(Clone, Debug)]
pub struct DkgOutput {
    /// The shared public key PK = g^{sk}
    pub public_key: G1Affine,
    /// Public key share for each participant: PK_j = g^{sk_j}
    pub public_key_shares: HashMap<NodeId, G1Affine>,
    /// This node's secret key share sk_i
    pub secret_share: Scalar,
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_ff::UniformRand;

    #[test]
    fn test_ciphertext_borsh_roundtrip() {
        let mut rng = ark_std::test_rng();
        let sk = Scalar::rand(&mut rng);
        let ct = Ciphertext {
            r_commitment: (G1Affine::generator() * sk).into_affine(),
            encrypted_share: Scalar::rand(&mut rng),
        };
        let bytes = borsh::to_vec(&ct).unwrap();
        let ct2: Ciphertext = borsh::from_slice(&bytes).unwrap();
        assert_eq!(ct.r_commitment, ct2.r_commitment);
        assert_eq!(ct.encrypted_share, ct2.encrypted_share);
    }

    #[test]
    fn test_round0msg_borsh_roundtrip() {
        let mut rng = ark_std::test_rng();

        let sk1 = Scalar::rand(&mut rng);
        let sk2 = Scalar::rand(&mut rng);

        let mut ciphertexts = HashMap::new();
        ciphertexts.insert(
            2u32,
            Ciphertext {
                r_commitment: (G1Affine::generator() * Scalar::rand(&mut rng)).into_affine(),
                encrypted_share: Scalar::rand(&mut rng),
            },
        );
        ciphertexts.insert(
            3u32,
            Ciphertext {
                r_commitment: (G1Affine::generator() * Scalar::rand(&mut rng)).into_affine(),
                encrypted_share: Scalar::rand(&mut rng),
            },
        );

        let msg = Round0Msg {
            from: 1,
            random_msg: [42u8; 32],
            vss_commitment: vec![
                (G1Affine::generator() * sk1).into_affine(),
                (G1Affine::generator() * sk2).into_affine(),
            ],
            ciphertexts,
        };

        let bytes = borsh::to_vec(&msg).unwrap();
        let msg2: Round0Msg = borsh::from_slice(&bytes).unwrap();

        assert_eq!(msg.from, msg2.from);
        assert_eq!(msg.random_msg, msg2.random_msg);
        assert_eq!(msg.vss_commitment.len(), msg2.vss_commitment.len());
        for (a, b) in msg.vss_commitment.iter().zip(msg2.vss_commitment.iter()) {
            assert_eq!(a, b);
        }
        assert_eq!(msg.ciphertexts.len(), msg2.ciphertexts.len());
        for (k, v) in &msg.ciphertexts {
            let v2 = &msg2.ciphertexts[k];
            assert_eq!(v.r_commitment, v2.r_commitment);
            assert_eq!(v.encrypted_share, v2.encrypted_share);
        }
    }
}
