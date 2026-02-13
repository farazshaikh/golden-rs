use std::collections::HashMap;
use std::sync::Arc;

use ark_bls12_381::G1Affine;
use tokio::sync::{broadcast, Barrier, RwLock};

use crate::types::{NodeId, ReshareMsg};

/// Network for resharing protocol with two groups: old members broadcast, new members receive.
#[derive(Clone)]
pub struct ReshareNetwork {
    /// Broadcast channel for ReshareMsg (old -> new)
    sender: broadcast::Sender<ReshareMsg>,
    /// Old group member identity keys: NodeId -> PK
    old_members: Arc<RwLock<HashMap<NodeId, G1Affine>>>,
    /// New group member identity keys: NodeId -> PK
    new_members: Arc<RwLock<HashMap<NodeId, G1Affine>>>,
    /// Barrier: waits for all participants (old + new) to register
    barrier: Arc<Barrier>,
}

impl ReshareNetwork {
    /// Create a new reshare network.
    /// `total_participants` = n_old + n_new (or less if groups overlap -- caller decides).
    pub fn new(total_participants: u32) -> Self {
        let (sender, _) = broadcast::channel((total_participants * 2) as usize);
        Self {
            sender,
            old_members: Arc::new(RwLock::new(HashMap::new())),
            new_members: Arc::new(RwLock::new(HashMap::new())),
            barrier: Arc::new(Barrier::new(total_participants as usize)),
        }
    }

    /// Register an old group member and get a broadcast receiver.
    pub async fn register_old(&self, id: NodeId, pk: G1Affine) -> broadcast::Receiver<ReshareMsg> {
        let mut old = self.old_members.write().await;
        old.insert(id, pk);
        self.sender.subscribe()
    }

    /// Register a new group member and get a broadcast receiver.
    pub async fn register_new(&self, id: NodeId, pk: G1Affine) -> broadcast::Receiver<ReshareMsg> {
        let mut new_m = self.new_members.write().await;
        new_m.insert(id, pk);
        self.sender.subscribe()
    }

    /// Wait for all participants to register.
    pub async fn wait_ready(&self) {
        self.barrier.wait().await;
    }

    /// Broadcast a reshare message (called by old nodes).
    pub fn broadcast(&self, msg: ReshareMsg) {
        let _ = self.sender.send(msg);
    }

    /// Get old group member identity keys.
    pub async fn get_old_members(&self) -> HashMap<NodeId, G1Affine> {
        self.old_members.read().await.clone()
    }

    /// Get new group member identity keys.
    pub async fn get_new_members(&self) -> HashMap<NodeId, G1Affine> {
        self.new_members.read().await.clone()
    }
}
