//! BLS12-381 threshold signing operations.
//!
//! Provides partial signing, verification, Lagrange interpolation, and
//! threshold combination. All operations use the BLS12-381 curve with
//! signatures on G2 and public keys on G1.

use ark_bls12_381::{Bls12_381, Fr, G1Affine, G2Affine, G2Projective};
use ark_ec::pairing::Pairing;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::Field;
use golden_dkg::types::NodeId;

use crate::cache::LagrangeCache;
use crate::types::{KeyShare, PartialSignature, ThresholdSignature};

/// Compute a partial BLS signature: `sigma_i = H(m)^{sk_i}`.
///
/// The caller must hash the message to a G2 point first (see
/// [`crate::beacon::hash_to_g2`]).
pub fn partial_sign(msg_hash: &G2Affine, share: &KeyShare) -> PartialSignature {
    let sig = (*msg_hash * share.secret).into_affine();
    PartialSignature {
        signer: share.id,
        signature: sig,
    }
}

/// Verify a single partial signature against the signer's public key share.
///
/// Checks `e(pk_i, H(m)) == e(g1, sigma_i)` via a pairing comparison.
pub fn verify_partial(msg_hash: &G2Affine, partial: &PartialSignature, pk_share: &G1Affine) -> bool {
    let g1 = G1Affine::generator();
    Bls12_381::pairing(*pk_share, *msg_hash) == Bls12_381::pairing(g1, partial.signature)
}

/// Combine `>= threshold` partial signatures into a threshold signature.
///
/// Uses precomputed Lagrange coefficients from the cache. Only the first
/// subset in the cache is used for combination (use
/// [`combine_and_check`] to cross-check multiple subsets).
///
/// # Panics
///
/// Panics if the cache has no subsets or if a required partial is missing.
pub fn combine(
    partials: &[PartialSignature],
    _signer_ids: &[NodeId],
    cache: &LagrangeCache,
) -> ThresholdSignature {
    let partial_map: std::collections::HashMap<NodeId, G2Affine> =
        partials.iter().map(|p| (p.signer, p.signature)).collect();

    let combined = combine_one(&cache.subsets[0], &partial_map);
    ThresholdSignature { signature: combined }
}

/// Verify a threshold signature against the group public key.
///
/// Checks `e(PK, H(m)) == e(g1, sigma)` via a pairing comparison.
pub fn verify(msg_hash: &G2Affine, sig: &ThresholdSignature, group_pk: &G1Affine) -> bool {
    let g1 = G1Affine::generator();
    Bls12_381::pairing(*group_pk, *msg_hash) == Bls12_381::pairing(g1, sig.signature)
}

/// Compute the Lagrange coefficient for `node_id` given the set of signer IDs.
///
/// Returns `l_i(0) = prod_{j != i} (x_j / (x_j - x_i))` where evaluation
/// points are the node IDs cast to field elements.
pub fn lagrange_coeff(node_id: NodeId, all_ids: &[NodeId]) -> Fr {
    let xi = Fr::from(node_id as u64);
    let mut li = Fr::from(1u64);
    for &id in all_ids {
        if id == node_id {
            continue;
        }
        let xj = Fr::from(id as u64);
        li *= xj * (xj - xi).inverse().expect("duplicate node IDs");
    }
    li
}

/// Combine a single subset of partial signatures using precomputed Lagrange coefficients.
///
/// This is the inner workhorse used by [`combine`] and the multi-subset checker.
pub fn combine_one(
    subset_coeffs: &[(NodeId, Fr)],
    partials: &std::collections::HashMap<NodeId, G2Affine>,
) -> G2Affine {
    let mut combined = G2Projective::default();
    for &(id, ref li) in subset_coeffs {
        let sig_i = partials[&id];
        combined += sig_i * li;
    }
    combined.into_affine()
}

/// Combine partial signatures by computing Lagrange coefficients on the fly.
///
/// Unlike [`combine`], this does not require a precomputed cache. It takes the
/// first `threshold` partials, computes their Lagrange coefficients, and
/// interpolates. Useful when the signer set is dynamic (e.g., Byzantine
/// double-voting creates non-standard signer subsets).
pub fn combine_dynamic(
    partials: &[PartialSignature],
    threshold: usize,
) -> ThresholdSignature {
    let partials = if partials.len() > threshold {
        &partials[..threshold]
    } else {
        partials
    };
    let signer_ids: Vec<NodeId> = partials.iter().map(|p| p.signer).collect();
    let mut combined = G2Projective::default();
    for p in partials {
        let li = lagrange_coeff(p.signer, &signer_ids);
        combined += p.signature * li;
    }
    ThresholdSignature {
        signature: combined.into_affine(),
    }
}
