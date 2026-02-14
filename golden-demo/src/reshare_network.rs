//! Network layer for the membership-change resharing protocol.

use std::collections::HashMap;
use std::sync::Arc;

use ark_bls12_381::G1Affine;
use rand::rngs::OsRng;
use tokio::sync::{broadcast, Barrier, RwLock};

use golden_dkg::schnorr_pok::{self, SchnorrPoK};
use golden_dkg::types::{NodeId, ReshareMsg, SessionId};

/// Network for the resharing protocol with two groups.
#[derive(Clone)]
pub struct ReshareNetwork {
    sender: broadcast::Sender<ReshareMsg>,
    old_members: Arc<RwLock<HashMap<NodeId, G1Affine>>>,
    new_members: Arc<RwLock<HashMap<NodeId, G1Affine>>>,
    barrier: Arc<Barrier>,
    session_id: Arc<SessionId>,
}

impl ReshareNetwork {
    /// Create a new reshare network.
    pub fn new(total_participants: u32) -> Self {
        let (sender, _) = broadcast::channel((total_participants * 2) as usize);
        let session_id = SessionId::random(&mut OsRng);
        Self {
            sender,
            old_members: Arc::new(RwLock::new(HashMap::new())),
            new_members: Arc::new(RwLock::new(HashMap::new())),
            barrier: Arc::new(Barrier::new(total_participants as usize)),
            session_id: Arc::new(session_id),
        }
    }

    /// Get the session ID for this reshare session.
    pub fn session_id(&self) -> SessionId {
        *self.session_id
    }

    /// Register an old group member with proof of knowledge.
    pub async fn register_old(
        &self,
        id: NodeId,
        pk: G1Affine,
        pok: &SchnorrPoK,
    ) -> Result<broadcast::Receiver<ReshareMsg>, String> {
        if !schnorr_pok::verify(pk, pok) {
            return Err(format!("Old node {} failed PoK", id));
        }
        let mut old = self.old_members.write().await;
        old.insert(id, pk);
        Ok(self.sender.subscribe())
    }

    /// Register a new group member with proof of knowledge.
    pub async fn register_new(
        &self,
        id: NodeId,
        pk: G1Affine,
        pok: &SchnorrPoK,
    ) -> Result<broadcast::Receiver<ReshareMsg>, String> {
        if !schnorr_pok::verify(pk, pok) {
            return Err(format!("New node {} failed PoK", id));
        }
        let mut new_m = self.new_members.write().await;
        new_m.insert(id, pk);
        Ok(self.sender.subscribe())
    }

    /// Wait for all participants (old + new) to register.
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
