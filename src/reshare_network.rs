//! Network layer for the membership-change resharing protocol.
//!
//! Provides a two-group broadcast network where old-group members deal
//! encrypted shares to new-group members. Both groups register their
//! identity public keys with proof of knowledge, and old members broadcast
//! [`ReshareMsg`](crate::types::ReshareMsg) messages that new members receive.

use std::collections::HashMap;
use std::sync::Arc;

use ark_bls12_381::G1Affine;
use tokio::sync::{broadcast, Barrier, RwLock};

use crate::schnorr_pok::{self, SchnorrPoK};
use crate::types::{NodeId, ReshareMsg};

/// Network for the resharing protocol with two groups: old members broadcast,
/// new members receive.
///
/// Maintains separate registries for old-group and new-group identity keys,
/// and a shared broadcast channel for reshare messages.
#[derive(Clone)]
pub struct ReshareNetwork {
    /// Broadcast channel for `ReshareMsg` (old -> new).
    sender: broadcast::Sender<ReshareMsg>,
    /// Old group member identity keys: `NodeId -> PK`.
    old_members: Arc<RwLock<HashMap<NodeId, G1Affine>>>,
    /// New group member identity keys: `NodeId -> PK`.
    new_members: Arc<RwLock<HashMap<NodeId, G1Affine>>>,
    /// Barrier: waits for all participants (old + new) to register.
    barrier: Arc<Barrier>,
}

impl ReshareNetwork {
    /// Create a new reshare network.
    ///
    /// `total_participants` is `n_old + n_new` (or fewer if groups overlap).
    pub fn new(total_participants: u32) -> Self {
        let (sender, _) = broadcast::channel((total_participants * 2) as usize);
        Self {
            sender,
            old_members: Arc::new(RwLock::new(HashMap::new())),
            new_members: Arc::new(RwLock::new(HashMap::new())),
            barrier: Arc::new(Barrier::new(total_participants as usize)),
        }
    }

    /// Register an old group member with proof of knowledge.
    ///
    /// Rejects registration if the Schnorr PoK is invalid (prevents rogue-key attacks).
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
    ///
    /// Rejects registration if the Schnorr PoK is invalid (prevents rogue-key attacks).
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
