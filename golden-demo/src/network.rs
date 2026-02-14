//! Simulated broadcast network for the Golden DKG protocol.

use std::collections::HashMap;
use std::sync::Arc;

use ark_bls12_381::G1Affine;
use rand::rngs::OsRng;
use tokio::sync::{broadcast, Barrier, RwLock};

use golden_dkg::schnorr_pok::{self, SchnorrPoK};
use golden_dkg::types::{MessageHeader, NodeId, Round0Msg, SessionId};

/// Simulated broadcast channel with peer discovery.
#[derive(Clone)]
pub struct Network {
    sender: broadcast::Sender<Round0Msg>,
    peers: Arc<RwLock<HashMap<NodeId, G1Affine>>>,
    barrier: Arc<Barrier>,
    session_id: Arc<SessionId>,
}

impl Network {
    /// Create a new network for `n` participants.
    pub fn new(n: u32) -> Self {
        let (sender, _) = broadcast::channel((n * 2) as usize);
        let session_id = SessionId::random(&mut OsRng);
        Self {
            sender,
            peers: Arc::new(RwLock::new(HashMap::new())),
            barrier: Arc::new(Barrier::new(n as usize)),
            session_id: Arc::new(session_id),
        }
    }

    /// Get the session ID for this network session.
    pub fn session_id(&self) -> SessionId {
        *self.session_id
    }

    /// Register a node's identity public key with proof of knowledge.
    pub async fn register(
        &self,
        id: NodeId,
        pk: G1Affine,
        pok: &SchnorrPoK,
    ) -> Result<broadcast::Receiver<Round0Msg>, String> {
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
    pub async fn wait_ready(&self) {
        self.barrier.wait().await;
    }

    /// Broadcast a Round 0 message to all participants.
    pub fn broadcast(&self, msg: Round0Msg) {
        let _ = self.sender.send(msg);
    }

    /// Get a snapshot of all registered peer public keys.
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
            dkg_header: MessageHeader {
                session_id: SessionId([0u8; 32]),
                from: 1,
                random_msg: [42u8; 32],
                vss_commitment: vec![],
                ciphertexts: HashMap::new(),
            },
            evrf_proofs: HashMap::new(),
            batch_evrf_proof: None,
        };

        network.broadcast(msg.clone());

        let received1 = rx1.recv().await.unwrap();
        let received2 = rx2.recv().await.unwrap();

        assert_eq!(received1.dkg_header.from, 1);
        assert_eq!(received2.dkg_header.from, 1);
        assert_eq!(received1.dkg_header.random_msg, [42u8; 32]);
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
