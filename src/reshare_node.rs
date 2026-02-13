use std::collections::HashMap;

use ark_bls12_381::G1Affine;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::UniformRand;
use rand::rngs::OsRng;
use tokio::sync::broadcast;

use crate::reshare;
use crate::reshare_network::ReshareNetwork;
use crate::schnorr_pok;
use crate::types::{DkgOutput, NodeId, ReshareMsg, Scalar};

/// An old group member participating in resharing.
/// Deals its existing share to the new group via eVRF-encrypted broadcast.
pub struct OldReshareNode {
    pub id: NodeId,
    sk_identity: Scalar,
    _pk_identity: G1Affine,
    old_share: Scalar,
    t_new: u32,
    beta: Scalar,
    network: ReshareNetwork,
    _n_old: u32,
    _receiver: broadcast::Receiver<ReshareMsg>,
}

impl OldReshareNode {
    pub async fn new(
        id: NodeId,
        old_share: Scalar,
        t_new: u32,
        beta: Scalar,
        n_old: u32,
        network: ReshareNetwork,
    ) -> Self {
        let mut rng = OsRng;
        let sk = Scalar::rand(&mut rng);
        let pk = (G1Affine::generator() * sk).into_affine();
        let pok = schnorr_pok::prove(sk, pk, &mut rng);
        let receiver = network
            .register_old(id, pk, &pok)
            .await
            .expect("Old node PKI registration failed: invalid proof of knowledge");
        Self {
            id,
            sk_identity: sk,
            _pk_identity: pk,
            old_share,
            t_new,
            beta,
            network,
            _n_old: n_old,
            _receiver: receiver,
        }
    }

    /// Deal old share to new group and return.
    /// Old nodes don't produce a DkgOutput -- they just broadcast.
    pub async fn run(self) {
        self.network.wait_ready().await;
        let new_members = self.network.get_new_members().await;

        let mut rng = OsRng;
        let msg = reshare::reshare_deal(
            self.id,
            self.old_share,
            self.sk_identity,
            &new_members,
            self.t_new,
            self.beta,
            &mut rng,
        );

        self.network.broadcast(msg);
    }
}

/// A new group member participating in resharing.
/// Receives deals from old members and computes new share.
pub struct NewReshareNode {
    pub id: NodeId,
    sk_identity: Scalar,
    _pk_identity: G1Affine,
    beta: Scalar,
    original_pk: G1Affine,
    old_pk_shares: HashMap<NodeId, G1Affine>,
    t_old: u32,
    n_old: u32,
    network: ReshareNetwork,
    receiver: broadcast::Receiver<ReshareMsg>,
}

impl NewReshareNode {
    pub async fn new(
        id: NodeId,
        beta: Scalar,
        original_pk: G1Affine,
        old_pk_shares: HashMap<NodeId, G1Affine>,
        t_old: u32,
        n_old: u32,
        network: ReshareNetwork,
    ) -> Self {
        let mut rng = OsRng;
        let sk = Scalar::rand(&mut rng);
        let pk = (G1Affine::generator() * sk).into_affine();
        let pok = schnorr_pok::prove(sk, pk, &mut rng);
        let receiver = network
            .register_new(id, pk, &pok)
            .await
            .expect("New node PKI registration failed: invalid proof of knowledge");
        Self {
            id,
            sk_identity: sk,
            _pk_identity: pk,
            beta,
            original_pk,
            old_pk_shares,
            t_old,
            n_old,
            network,
            receiver,
        }
    }

    /// Collect reshare messages from old nodes and compute new share.
    pub async fn run(mut self) -> DkgOutput {
        self.network.wait_ready().await;
        let old_members = self.network.get_old_members().await;

        // Collect n_old messages from old nodes
        let mut received: HashMap<NodeId, ReshareMsg> = HashMap::new();
        while received.len() < self.n_old as usize {
            match self.receiver.recv().await {
                Ok(msg) => {
                    received.insert(msg.from, msg);
                }
                Err(e) => {
                    panic!("NewReshareNode {} failed to receive: {}", self.id, e);
                }
            }
        }

        reshare::reshare_receive(
            self.id,
            self.sk_identity,
            &old_members,
            &received,
            self.beta,
            self.original_pk,
            &self.old_pk_shares,
            self.t_old,
        )
        .unwrap_or_else(|e| panic!("NewReshareNode {} reshare failed: {}", self.id, e))
    }
}
