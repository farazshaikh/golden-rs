//! Resharing participant abstractions for old-group and new-group members.
//!
//! Provides [`OldReshareNode`] (deals existing shares to the new group) and
//! [`NewReshareNode`] (receives deals and computes new shares). Both register
//! identity keypairs with proof of knowledge and communicate via the
//! [`ReshareNetwork`](crate::reshare_network::ReshareNetwork).

use std::collections::HashMap;

use ark_bls12_381::G1Affine;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::UniformRand;
use rand::rngs::OsRng;
use tokio::sync::broadcast;

use crate::reshare::{self, ReshareError};
use crate::reshare_network::ReshareNetwork;
use crate::schnorr_pok;
use crate::types::{DkgOutput, NodeId, ReshareMsg, Scalar, SecretScalar};

/// An old group member participating in resharing.
///
/// Deals its existing share to the new group via eVRF-encrypted broadcast.
/// After dealing, the old node's role is complete -- it does not produce
/// a [`DkgOutput`].
pub struct OldReshareNode {
    /// Old-group node identifier.
    pub id: NodeId,
    /// Identity secret key for eVRF pad derivation.
    sk_identity: SecretScalar,
    /// Identity public key (registered with PKI).
    _pk_identity: G1Affine,
    /// This node's existing secret key share `sk_i`.
    old_share: SecretScalar,
    /// New group's threshold parameter.
    t_new: u32,
    /// Public `beta` for leftover hash lemma.
    beta: Scalar,
    /// Reshare network handle.
    network: ReshareNetwork,
    /// Size of old group (unused but stored for completeness).
    _n_old: u32,
    /// Broadcast receiver (unused by old nodes, but required for registration).
    _receiver: broadcast::Receiver<ReshareMsg>,
}

impl OldReshareNode {
    /// Create a new old-group reshare node and register with the network.
    ///
    /// Generates an identity keypair and registers with proof of knowledge.
    pub async fn new(
        id: NodeId,
        old_share: Scalar,
        t_new: u32,
        beta: Scalar,
        n_old: u32,
        network: ReshareNetwork,
    ) -> Result<Self, ReshareError> {
        let mut rng = OsRng;
        let sk = SecretScalar::new(Scalar::rand(&mut rng));
        let pk = (G1Affine::generator() * sk.inner()).into_affine();
        let pok = schnorr_pok::prove(sk.inner(), pk, &mut rng);
        let receiver = network
            .register_old(id, pk, &pok)
            .await
            .map_err(|reason| ReshareError::RegistrationFailed { node: id, reason })?;
        Ok(Self {
            id,
            sk_identity: sk,
            _pk_identity: pk,
            old_share: SecretScalar::new(old_share),
            t_new,
            beta,
            network,
            _n_old: n_old,
            _receiver: receiver,
        })
    }

    /// Deal old share to new group and return.
    ///
    /// Waits for all participants to register, then creates a dealing polynomial
    /// `g_i(0) = old_share` and broadcasts encrypted evaluations to the new group.
    pub async fn run(self) {
        self.network.wait_ready().await;
        let new_members = self.network.get_new_members().await;
        let session_id = self.network.session_id();

        let mut rng = OsRng;
        let msg = reshare::reshare_deal(
            self.id,
            self.old_share.inner(),
            self.sk_identity.inner(),
            &new_members,
            self.t_new,
            self.beta,
            &mut rng,
            session_id,
        );

        self.network.broadcast(msg);
    }
}

/// A new group member participating in resharing.
///
/// Receives deals from old members and computes a new secret key share.
/// The output preserves the original public key `PK` and produces shares
/// under the new group's `(n_new, t_new)` parameters.
pub struct NewReshareNode {
    /// New-group node identifier.
    pub id: NodeId,
    /// Identity secret key for eVRF pad derivation.
    sk_identity: SecretScalar,
    /// Identity public key (registered with PKI).
    _pk_identity: G1Affine,
    /// Public `beta` for leftover hash lemma.
    beta: Scalar,
    /// Original shared public key `PK` (must be preserved).
    original_pk: G1Affine,
    /// Old-group public key shares: `old_id -> g^{sk_i}` (for verification).
    old_pk_shares: HashMap<NodeId, G1Affine>,
    /// Old group's threshold parameter `t_old`.
    t_old: u32,
    /// Number of old-group members.
    n_old: u32,
    /// Reshare network handle.
    network: ReshareNetwork,
    /// Broadcast receiver for incoming reshare messages.
    receiver: broadcast::Receiver<ReshareMsg>,
}

impl NewReshareNode {
    /// Create a new new-group reshare node and register with the network.
    ///
    /// Generates an identity keypair and registers with proof of knowledge.
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
        let sk = SecretScalar::new(Scalar::rand(&mut rng));
        let pk = (G1Affine::generator() * sk.inner()).into_affine();
        let pok = schnorr_pok::prove(sk.inner(), pk, &mut rng);
        let receiver = network
            .register_new(id, pk, &pok)
            .await
            .map_err(|reason| ReshareError::RegistrationFailed { node: id, reason })?;
        Ok(Self {
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
        })
    }

    /// Collect reshare messages from old nodes and compute new share.
    ///
    /// Waits for `n_old` messages, then runs [`reshare::reshare_receive`] to
    /// verify, decrypt, and aggregate into a new [`DkgOutput`].
    pub async fn run(mut self) -> Result<DkgOutput, ReshareError> {
        self.network.wait_ready().await;
        let old_members = self.network.get_old_members().await;
        let session_id = self.network.session_id();

        // Collect n_old messages from old nodes
        let mut received: HashMap<NodeId, ReshareMsg> = HashMap::new();
        while received.len() < self.n_old as usize {
            match self.receiver.recv().await {
                Ok(msg) => {
                    received.insert(msg.from, msg);
                }
                Err(e) => {
                    return Err(ReshareError::BroadcastReceiveFailed {
                        node: self.id,
                        reason: e.to_string(),
                    });
                }
            }
        }

        reshare::reshare_receive(
            self.id,
            self.sk_identity.inner(),
            &old_members,
            &received,
            self.beta,
            self.original_pk,
            &self.old_pk_shares,
            self.t_old,
            session_id,
        )
    }
}
