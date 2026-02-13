//! DKG participant abstraction.
//!
//! Per Section 5.1 of the Golden paper (IACR 2025/1924):
//! > "Each party i maintains (sk_i^I, PK_i^I)"
//!
//! The [`Node`] struct encapsulates a single DKG participant, managing its
//! identity keypair, network handle, and protocol execution. It provides
//! high-level methods for running the full DKG and key refresh protocols.

use std::collections::HashMap;

use ark_bls12_381::G1Affine;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::UniformRand;
use rand::rngs::OsRng;
use tokio::sync::broadcast;

use crate::network::Network;
use crate::protocol;
use crate::schnorr_pok;
use crate::types::{DkgOutput, NodeId, Round0Msg, Scalar};

/// A participant in the Golden DKG protocol.
///
/// Holds the node's identity keypair `(sk_i^I, PK_i^I)`, protocol parameters
/// `(n, t, beta)`, and the network handle for broadcast communication.
pub struct Node {
    /// This node's unique identifier (1-indexed).
    pub id: NodeId,
    /// Total number of participants `n`.
    pub n: u32,
    /// Threshold parameter `t` (minimum shares needed to reconstruct).
    pub t: u32,
    /// Identity secret key `sk_i^I` per Section 5.1.
    sk: Scalar,
    /// Identity public key `PK_i^I = g^{sk_i^I}` per Section 5.1.
    pub pk: G1Affine,
    /// Public `beta` parameter for the leftover hash lemma (Appendix C).
    beta: Scalar,
    /// Network handle for broadcast and peer discovery.
    network: Network,
    /// Broadcast receiver for incoming Round 0 messages.
    receiver: broadcast::Receiver<Round0Msg>,
}

impl Node {
    /// Create a new node and register it with the network.
    ///
    /// Per Section 5.1 of the Golden paper (IACR 2025/1924), generates an
    /// identity keypair `(sk_i^I, PK_i^I)` and registers the public key with
    /// the PKI via a Schnorr proof of knowledge (Appendix F).
    pub async fn new(id: NodeId, n: u32, t: u32, beta: Scalar, network: Network) -> Self {
        let mut rng = OsRng;
        let sk = Scalar::rand(&mut rng);
        let pk = (G1Affine::generator() * sk).into_affine();
        let pok = schnorr_pok::prove(sk, pk, &mut rng);

        let receiver = network
            .register(id, pk, &pok)
            .await
            .expect("PKI registration failed: invalid proof of knowledge");

        Self {
            id,
            n,
            t,
            sk,
            pk,
            beta,
            network,
            receiver,
        }
    }

    /// Run the full DKG protocol (Round 0 + Round 1 per Figure 4).
    ///
    /// 1. Wait for all nodes to register
    /// 2. Execute Round 0: generate and broadcast
    /// 3. Collect `n-1` Round 0 messages from peers
    /// 4. Execute Round 1: verify, decrypt, aggregate
    /// 5. Return [`DkgOutput`] containing `(PK, {PK_j}, sk_i)`
    pub async fn run(mut self) -> DkgOutput {
        // Wait for all peers to register
        self.network.wait_ready().await;

        // Get peer public keys
        let peers = self.network.get_peers().await;
        assert_eq!(
            peers.len(),
            self.n as usize,
            "Expected {} peers, got {}",
            self.n,
            peers.len()
        );

        // Round 0: generate VSS shares, encrypt, and broadcast
        let mut rng = OsRng;
        let (my_msg, own_share) = protocol::round0(
            self.id, self.n, self.t, self.sk, &peers, self.beta, &mut rng,
        );

        // Save our VSS commitment before broadcasting
        let own_vss_commitment = my_msg.vss_commitment.clone();

        // Broadcast our Round 0 message
        self.network.broadcast(my_msg);

        // Collect n-1 messages from other nodes
        let mut received: HashMap<NodeId, Round0Msg> = HashMap::new();
        while received.len() < (self.n - 1) as usize {
            match self.receiver.recv().await {
                Ok(msg) => {
                    if msg.from != self.id {
                        received.insert(msg.from, msg);
                    }
                }
                Err(e) => {
                    panic!("Node {} failed to receive broadcast: {}", self.id, e);
                }
            }
        }

        // Round 1: verify, decrypt, aggregate
        protocol::round1(
            self.id,
            self.sk,
            &peers,
            own_share,
            own_vss_commitment,
            &received,
            self.beta,
        )
        .unwrap_or_else(|e| panic!("Node {} Round 1 failed: {}", self.id, e))
    }

    /// Run the key refresh protocol (zero secret sharing).
    ///
    /// Per Section 5.2 of the Golden paper (IACR 2025/1924): rotates secret
    /// shares while keeping `sk` and `PK` unchanged. Each node uses `omega = 0`
    /// and the zero-sharing deltas update existing shares.
    pub async fn run_refresh(mut self, existing_output: DkgOutput) -> DkgOutput {
        // Wait for all peers to register
        self.network.wait_ready().await;

        // Get peer public keys
        let peers = self.network.get_peers().await;
        assert_eq!(
            peers.len(),
            self.n as usize,
            "Expected {} peers, got {}",
            self.n,
            peers.len()
        );

        // Round 0 refresh: zero secret sharing
        let mut rng = OsRng;
        let (my_msg, own_refresh_delta) = protocol::round0_refresh(
            self.id, self.n, self.t, self.sk, &peers, self.beta, &mut rng,
        );

        let own_vss_commitment = my_msg.vss_commitment.clone();

        // Broadcast
        self.network.broadcast(my_msg);

        // Collect n-1 messages
        let mut received: HashMap<NodeId, Round0Msg> = HashMap::new();
        while received.len() < (self.n - 1) as usize {
            match self.receiver.recv().await {
                Ok(msg) => {
                    if msg.from != self.id {
                        received.insert(msg.from, msg);
                    }
                }
                Err(e) => {
                    panic!("Node {} failed to receive broadcast: {}", self.id, e);
                }
            }
        }

        // Round 1 refresh: verify zero-secret, decrypt deltas, update shares
        protocol::round1_refresh(
            self.id,
            self.sk,
            &peers,
            own_refresh_delta,
            own_vss_commitment,
            &received,
            self.beta,
            existing_output.secret_share,
            existing_output.public_key,
            &existing_output.public_key_shares,
        )
        .unwrap_or_else(|e| panic!("Node {} refresh Round 1 failed: {}", self.id, e))
    }
}
