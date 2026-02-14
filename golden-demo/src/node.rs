//! DKG participant abstraction using the high-level golden-dkg API.

use std::collections::HashMap;

use rand::rngs::OsRng;
use tokio::sync::broadcast;

use crate::network::Network;
use golden_dkg::dkg;
use golden_dkg::error::DkgError;
use golden_dkg::refresh;
use golden_dkg::types::{DkgConfig, DkgOutput, NodeId, Participant, Round0Msg, Scalar};

/// A participant in the Golden DKG protocol.
pub struct Node {
    /// The participant's identity (keypair + PoK).
    participant: Participant,
    /// Total number of participants.
    n: u32,
    /// Threshold parameter.
    t: u32,
    /// Beta parameter for leftover hash lemma.
    beta: Scalar,
    /// Network handle.
    network: Network,
    /// Broadcast receiver.
    receiver: broadcast::Receiver<Round0Msg>,
}

impl Node {
    /// Create a new node and register it with the network.
    pub async fn new(
        id: NodeId,
        n: u32,
        t: u32,
        beta: Scalar,
        network: Network,
    ) -> Result<Self, DkgError> {
        let mut rng = OsRng;
        let participant = Participant::new(id, &mut rng);

        let receiver = network
            .register(id, participant.pk, &participant.pok)
            .await
            .map_err(|reason| DkgError::RegistrationFailed { node: id, reason })?;

        Ok(Self {
            participant,
            n,
            t,
            beta,
            network,
            receiver,
        })
    }

    /// Run the full DKG protocol.
    pub async fn run(mut self) -> Result<DkgOutput, DkgError> {
        self.network.wait_ready().await;

        let peers = self.network.get_peers().await;
        if peers.len() != self.n as usize {
            return Err(DkgError::PeerCountMismatch {
                expected: self.n,
                got: peers.len(),
            });
        }

        let session_id = self.network.session_id();
        let config = DkgConfig {
            n: self.n,
            t: self.t,
            beta: self.beta,
            session_id,
        };

        let mut rng = OsRng;
        let dealing = dkg::create_dealing(&self.participant, &config, &peers, &mut rng)?;

        self.network.broadcast(dealing.message.clone());

        let mut received: HashMap<NodeId, Round0Msg> = HashMap::new();
        while received.len() < (self.n - 1) as usize {
            match self.receiver.recv().await {
                Ok(msg) => {
                    if msg.from != self.participant.id {
                        received.insert(msg.from, msg);
                    }
                }
                Err(e) => {
                    return Err(DkgError::BroadcastReceiveFailed {
                        node: self.participant.id,
                        reason: e.to_string(),
                    });
                }
            }
        }

        dkg::complete(&self.participant, &dealing, &received, &peers, &config)
    }

    /// Run the key refresh protocol.
    pub async fn run_refresh(mut self, existing_output: DkgOutput) -> Result<DkgOutput, DkgError> {
        self.network.wait_ready().await;

        let peers = self.network.get_peers().await;
        if peers.len() != self.n as usize {
            return Err(DkgError::PeerCountMismatch {
                expected: self.n,
                got: peers.len(),
            });
        }

        let session_id = self.network.session_id();
        let config = DkgConfig {
            n: self.n,
            t: self.t,
            beta: self.beta,
            session_id,
        };

        let mut rng = OsRng;
        let dealing = refresh::create_dealing(&self.participant, &config, &peers, &mut rng)?;

        self.network.broadcast(dealing.message.clone());

        let mut received: HashMap<NodeId, Round0Msg> = HashMap::new();
        while received.len() < (self.n - 1) as usize {
            match self.receiver.recv().await {
                Ok(msg) => {
                    if msg.from != self.participant.id {
                        received.insert(msg.from, msg);
                    }
                }
                Err(e) => {
                    return Err(DkgError::BroadcastReceiveFailed {
                        node: self.participant.id,
                        reason: e.to_string(),
                    });
                }
            }
        }

        refresh::complete(
            &self.participant,
            &dealing,
            &received,
            &peers,
            &config,
            &existing_output,
        )
    }
}
