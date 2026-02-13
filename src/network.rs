//! Simulated broadcast network for the Golden DKG protocol.
//!
//! Per Section 5.1 of the Golden paper (IACR 2025/1924), the protocol requires
//! a PKI and a broadcast channel. This module simulates both:
//! - A peer registry where nodes register their identity public keys with
//!   proof of knowledge (preventing rogue-key attacks per Appendix F)
//! - A broadcast channel for disseminating Round 0 messages to all participants

use std::collections::HashMap;
use std::sync::Arc;

use ark_bls12_381::G1Affine;
use tokio::sync::{broadcast, Barrier, RwLock};

use crate::schnorr_pok::{self, SchnorrPoK};
use crate::types::{NodeId, Round0Msg};

/// Simulated broadcast channel with peer discovery.
///
/// Per Section 5.1 of the Golden paper (IACR 2025/1924):
/// > "Each party i maintains (sk_i^I, PK_i^I) where PK_i^I = g^{sk_i^I} in G_in."
///
/// All nodes register their identity public key, then use a shared broadcast
/// channel to send Round 0 messages to every other participant.
#[derive(Clone)]
pub struct Network {
    /// Broadcast channel sender -- all nodes send Round0 messages here.
    sender: broadcast::Sender<Round0Msg>,
    /// Peer identity public keys: `NodeId -> PK_i`.
    peers: Arc<RwLock<HashMap<NodeId, G1Affine>>>,
    /// Barrier to synchronize: all nodes must register before Round 0 starts.
    barrier: Arc<Barrier>,
}

impl Network {
    /// Create a new network for `n` participants.
    ///
    /// The broadcast channel capacity is `n * 2` to avoid dropped messages.
    pub fn new(n: u32) -> Self {
        let (sender, _) = broadcast::channel((n * 2) as usize);
        Self {
            sender,
            peers: Arc::new(RwLock::new(HashMap::new())),
            barrier: Arc::new(Barrier::new(n as usize)),
        }
    }

    /// Register a node's identity public key with proof of knowledge.
    ///
    /// Per Appendix F of the Golden paper (IACR 2025/1924), registration
    /// requires proving knowledge of the secret key to prevent rogue-key attacks.
    /// Returns a broadcast receiver on success, or an error if the Schnorr PoK
    /// is invalid.
    pub async fn register(
        &self,
        id: NodeId,
        pk: G1Affine,
        pok: &SchnorrPoK,
    ) -> Result<broadcast::Receiver<Round0Msg>, String> {
        // Verify proof of knowledge before accepting
        if !schnorr_pok::verify(pk, pok) {
            return Err(format!(
                "Node {} failed proof of knowledge for PK registration",
                id
            ));
        }

        let mut peers = self.peers.write().await;
        peers.insert(id, pk);
        Ok(self.sender.subscribe())
    }

    /// Wait for all nodes to finish registration.
    ///
    /// Blocks until all `n` participants have registered, ensuring the peer
    /// directory is complete before Round 0 begins.
    pub async fn wait_ready(&self) {
        self.barrier.wait().await;
    }

    /// Broadcast a Round 0 message to all participants.
    ///
    /// Sends the message on the shared broadcast channel. All registered
    /// receivers will obtain a copy.
    pub fn broadcast(&self, msg: Round0Msg) {
        // Ignore the error (only fails if no receivers, shouldn't happen)
        let _ = self.sender.send(msg);
    }

    /// Get a snapshot of all registered peer public keys.
    ///
    /// Returns a clone of the current peer directory mapping `NodeId` to
    /// identity public key.
    pub async fn get_peers(&self) -> HashMap<NodeId, G1Affine> {
        self.peers.read().await.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Fr;
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_ff::UniformRand;

    /// Helper: generate a keypair and PoK proof for test registration.
    fn gen_keypair_with_pok(rng: &mut impl ark_std::rand::Rng) -> (Fr, G1Affine, SchnorrPoK) {
        let sk = Fr::rand(rng);
        let pk = (G1Affine::generator() * sk).into_affine();
        let pok = schnorr_pok::prove(sk, pk, rng);
        (sk, pk, pok)
    }

    #[tokio::test]
    async fn test_register_and_discover_peers() {
        let network = Network::new(3);

        let mut rng = ark_std::test_rng();
        let (_, pk1, pok1) = gen_keypair_with_pok(&mut rng);
        let (_, pk2, pok2) = gen_keypair_with_pok(&mut rng);
        let (_, pk3, pok3) = gen_keypair_with_pok(&mut rng);

        let _rx1 = network.register(1, pk1, &pok1).await.unwrap();
        let _rx2 = network.register(2, pk2, &pok2).await.unwrap();
        let _rx3 = network.register(3, pk3, &pok3).await.unwrap();

        let peers = network.get_peers().await;
        assert_eq!(peers.len(), 3);
        assert_eq!(peers[&1], pk1);
        assert_eq!(peers[&2], pk2);
        assert_eq!(peers[&3], pk3);
    }

    #[tokio::test]
    async fn test_register_rejects_bad_pok() {
        let network = Network::new(2);
        let mut rng = ark_std::test_rng();

        let sk = Fr::rand(&mut rng);
        let pk = (G1Affine::generator() * sk).into_affine();

        // Prove with a wrong secret key
        let wrong_sk = Fr::rand(&mut rng);
        let bad_pok = schnorr_pok::prove(wrong_sk, pk, &mut rng);

        let result = network.register(1, pk, &bad_pok).await;
        assert!(result.is_err(), "Registration with bad PoK should fail");
    }

    #[tokio::test]
    async fn test_broadcast_delivery() {
        let network = Network::new(3);
        let mut rng = ark_std::test_rng();

        let (_, pk1, pok1) = gen_keypair_with_pok(&mut rng);
        let (_, pk2, pok2) = gen_keypair_with_pok(&mut rng);

        let mut rx1 = network.register(1, pk1, &pok1).await.unwrap();
        let mut rx2 = network.register(2, pk2, &pok2).await.unwrap();

        let msg = Round0Msg {
            from: 1,
            random_msg: [42u8; 32],
            vss_commitment: vec![],
            ciphertexts: HashMap::new(),
            evrf_proofs: HashMap::new(),
            batch_evrf_proof: None,
        };

        network.broadcast(msg.clone());

        let received1 = rx1.recv().await.unwrap();
        let received2 = rx2.recv().await.unwrap();

        assert_eq!(received1.from, 1);
        assert_eq!(received2.from, 1);
        assert_eq!(received1.random_msg, [42u8; 32]);
    }

    #[tokio::test]
    async fn test_barrier_synchronization() {
        let network = Network::new(2);
        let mut rng = ark_std::test_rng();

        let (_, pk1, pok1) = gen_keypair_with_pok(&mut rng);
        let (_, pk2, pok2) = gen_keypair_with_pok(&mut rng);

        let net1 = network.clone();
        let net2 = network.clone();

        let h1 = tokio::spawn(async move {
            let _rx = net1.register(1, pk1, &pok1).await.unwrap();
            net1.wait_ready().await;
            true
        });

        let h2 = tokio::spawn(async move {
            let _rx = net2.register(2, pk2, &pok2).await.unwrap();
            net2.wait_ready().await;
            true
        });

        let (r1, r2) = tokio::join!(h1, h2);
        assert!(r1.unwrap());
        assert!(r2.unwrap());
    }
}
