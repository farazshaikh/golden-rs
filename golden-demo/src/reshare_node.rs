//! Resharing participant abstractions using the high-level golden-dkg API.

use std::collections::HashMap;

use ark_bls12_381::G1Affine;
use rand::rngs::OsRng;
use tokio::sync::broadcast;

use crate::reshare_network::ReshareNetwork;
use golden_dkg::error::ReshareError;
use golden_dkg::reshare;
use golden_dkg::types::{DkgOutput, NodeId, Participant, ReshareMsg, Scalar};

/// An old group member participating in resharing.
pub struct OldReshareNode {
    participant: Participant,
    old_share: Scalar,
    t_new: u32,
    beta: Scalar,
    network: ReshareNetwork,
    _receiver: broadcast::Receiver<ReshareMsg>,
}

impl OldReshareNode {
    /// Create a new old-group reshare node and register with the network.
    pub async fn new(
        id: NodeId,
        old_share: Scalar,
        t_new: u32,
        beta: Scalar,
        _n_old: u32,
        network: ReshareNetwork,
    ) -> Result<Self, ReshareError> {
        let mut rng = OsRng;
        let participant = Participant::new(id, &mut rng);
        let receiver = network
            .register_old(id, participant.pk, &participant.pok)
            .await
            .map_err(|reason| ReshareError::RegistrationFailed { node: id, reason })?;
        Ok(Self {
            participant,
            old_share,
            t_new,
            beta,
            network,
            _receiver: receiver,
        })
    }

    /// Deal old share to new group and return.
    pub async fn run(self) {
        self.network.wait_ready().await;
        let new_members = self.network.get_new_members().await;
        let session_id = self.network.session_id();

        let mut rng = OsRng;
        let msg = reshare::create_dealing(
            &self.participant,
            self.old_share,
            &new_members,
            self.t_new,
            self.beta,
            session_id,
            &mut rng,
        )
        .unwrap();

        self.network.broadcast(msg);
    }
}

/// A new group member participating in resharing.
pub struct NewReshareNode {
    participant: Participant,
    beta: Scalar,
    original_pk: G1Affine,
    old_pk_shares: HashMap<NodeId, G1Affine>,
    t_old: u32,
    n_old: u32,
    network: ReshareNetwork,
    receiver: broadcast::Receiver<ReshareMsg>,
}

impl NewReshareNode {
    /// Create a new new-group reshare node and register with the network.
    pub async fn new(
        id: NodeId,
        beta: Scalar,
        original_pk: G1Affine,
        old_pk_shares: HashMap<NodeId, G1Affine>,
        t_old: u32,
        n_old: u32,
        network: ReshareNetwork,
    ) -> Result<Self, ReshareError> {
        let mut rng = OsRng;
        let participant = Participant::new(id, &mut rng);
        let receiver = network
            .register_new(id, participant.pk, &participant.pok)
            .await
            .map_err(|reason| ReshareError::RegistrationFailed { node: id, reason })?;
        Ok(Self {
            participant,
            beta,
            original_pk,
            old_pk_shares,
            t_old,
            n_old,
            network,
            receiver,
        })
    }

    /// Collect reshare messages from old nodes and compute new share.
    pub async fn run(mut self) -> Result<DkgOutput, ReshareError> {
        self.network.wait_ready().await;
        let old_members = self.network.get_old_members().await;
        let session_id = self.network.session_id();

        let mut received: HashMap<NodeId, ReshareMsg> = HashMap::new();
        while received.len() < self.n_old as usize {
            match self.receiver.recv().await {
                Ok(msg) => {
                    received.insert(msg.reshare_header.from, msg);
                }
                Err(e) => {
                    return Err(ReshareError::BroadcastReceiveFailed {
                        node: self.participant.id,
                        reason: e.to_string(),
                    });
                }
            }
        }

        reshare::complete(
            &self.participant,
            &received,
            &old_members,
            self.original_pk,
            &self.old_pk_shares,
            self.t_old,
            self.beta,
            session_id,
        )
    }
}
