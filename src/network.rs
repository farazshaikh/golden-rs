use std::collections::HashMap;
use std::sync::Arc;

use ark_bls12_381::G1Affine;
use tokio::sync::{broadcast, Barrier, RwLock};

use crate::types::{NodeId, Round0Msg};

/// Simulated broadcast channel with peer discovery.
///
/// All nodes register their identity public key, then use a shared broadcast
/// channel to send Round0 messages to every other participant.
#[derive(Clone)]
pub struct Network {
    /// Broadcast channel sender -- all nodes send Round0 messages here
    sender: broadcast::Sender<Round0Msg>,
    /// Peer identity public keys: NodeId -> PK_i
    peers: Arc<RwLock<HashMap<NodeId, G1Affine>>>,
    /// Barrier to synchronize: all nodes must register before Round 0 starts
    barrier: Arc<Barrier>,
}

impl Network {
    /// Create a new network for `n` participants.
    /// The broadcast channel capacity is `n * 2` to avoid dropped messages.
    pub fn new(n: u32) -> Self {
        let (sender, _) = broadcast::channel((n * 2) as usize);
        Self {
            sender,
            peers: Arc::new(RwLock::new(HashMap::new())),
            barrier: Arc::new(Barrier::new(n as usize)),
        }
    }

    /// Register a node's identity public key and get a broadcast receiver.
    /// Called once per node during initialization.
    pub async fn register(&self, id: NodeId, pk: G1Affine) -> broadcast::Receiver<Round0Msg> {
        let mut peers = self.peers.write().await;
        peers.insert(id, pk);
        self.sender.subscribe()
    }

    /// Wait for all nodes to finish registration.
    pub async fn wait_ready(&self) {
        self.barrier.wait().await;
    }

    /// Broadcast a Round0 message to all participants.
    pub fn broadcast(&self, msg: Round0Msg) {
        // Ignore the error (only fails if no receivers, shouldn't happen)
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
    use ark_ec::AffineRepr;
    use ark_ff::UniformRand;

    #[tokio::test]
    async fn test_register_and_discover_peers() {
        let network = Network::new(3);

        let mut rng = ark_std::test_rng();
        let pk1: G1Affine = (G1Affine::generator() * Fr::rand(&mut rng)).into();
        let pk2: G1Affine = (G1Affine::generator() * Fr::rand(&mut rng)).into();
        let pk3: G1Affine = (G1Affine::generator() * Fr::rand(&mut rng)).into();

        let _rx1 = network.register(1, pk1).await;
        let _rx2 = network.register(2, pk2).await;
        let _rx3 = network.register(3, pk3).await;

        let peers = network.get_peers().await;
        assert_eq!(peers.len(), 3);
        assert_eq!(peers[&1], pk1);
        assert_eq!(peers[&2], pk2);
        assert_eq!(peers[&3], pk3);
    }

    #[tokio::test]
    async fn test_broadcast_delivery() {
        let network = Network::new(3);
        let mut rng = ark_std::test_rng();

        let pk1: G1Affine = (G1Affine::generator() * Fr::rand(&mut rng)).into();
        let pk2: G1Affine = (G1Affine::generator() * Fr::rand(&mut rng)).into();

        let mut rx1 = network.register(1, pk1).await;
        let mut rx2 = network.register(2, pk2).await;

        let msg = Round0Msg {
            from: 1,
            random_msg: [42u8; 32],
            vss_commitment: vec![],
            ciphertexts: HashMap::new(),
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

        let pk1: G1Affine = (G1Affine::generator() * Fr::rand(&mut rng)).into();
        let pk2: G1Affine = (G1Affine::generator() * Fr::rand(&mut rng)).into();

        let net1 = network.clone();
        let net2 = network.clone();

        let h1 = tokio::spawn(async move {
            let _rx = net1.register(1, pk1).await;
            net1.wait_ready().await;
            true
        });

        let h2 = tokio::spawn(async move {
            let _rx = net2.register(2, pk2).await;
            net2.wait_ready().await;
            true
        });

        let (r1, r2) = tokio::join!(h1, h2);
        assert!(r1.unwrap());
        assert!(r2.unwrap());
    }
}
