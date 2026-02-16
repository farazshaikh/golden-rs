//! Precomputed Lagrange coefficient cache.
//!
//! Computes and stores Lagrange interpolation coefficients for selected
//! `C(n, t)` subsets so they can be reused across beacon rounds without
//! repeated field inversions.

use ark_bls12_381::Fr;
use golden_dkg::types::NodeId;

use crate::signing::lagrange_coeff;

/// Precomputed Lagrange coefficients for each selected subset.
///
/// After construction, each entry in `subsets` contains the `(node_id, coeff)`
/// pairs for one threshold-sized subset. The first subset is always used for
/// combination; additional subsets are used for cross-checking.
pub struct LagrangeCache {
    /// For each check-subset, the `(node_id, lagrange_coeff)` pairs.
    pub subsets: Vec<Vec<(NodeId, Fr)>>,
}

impl LagrangeCache {
    /// Build a cache by selecting `num_check` evenly-spaced subsets from all
    /// `C(n, t)` combinations of `node_ids`.
    ///
    /// If `num_check` is 1, only the first subset is stored (fast path).
    /// If `num_check >= C(n,t)`, all subsets are stored.
    pub fn new(node_ids: &[NodeId], t: u32, num_check: usize) -> Self {
        let all_subsets = combinations(node_ids, t as usize);
        let total = all_subsets.len();

        let mut indices: Vec<usize> = Vec::new();
        if total <= num_check || num_check <= 1 {
            indices.extend(0..total.min(num_check.max(1)));
        } else {
            for i in 0..num_check {
                indices.push(i * (total - 1) / (num_check - 1));
            }
        }
        indices.sort();
        indices.dedup();

        let subsets = indices
            .into_iter()
            .map(|idx| {
                let subset = &all_subsets[idx];
                subset
                    .iter()
                    .map(|&id| (id, lagrange_coeff(id, subset)))
                    .collect()
            })
            .collect();

        Self { subsets }
    }
}

/// Enumerate all `k`-element combinations of `items`.
///
/// Returns a `Vec` of sorted sub-slices. Used to enumerate all possible
/// threshold-signing subsets for cross-checking.
pub fn combinations(items: &[NodeId], k: usize) -> Vec<Vec<NodeId>> {
    if k == 0 {
        return vec![vec![]];
    }
    if items.len() < k {
        return vec![];
    }
    let mut result = Vec::new();
    let first = items[0];
    let rest = &items[1..];
    for mut combo in combinations(rest, k - 1) {
        combo.insert(0, first);
        result.push(combo);
    }
    result.extend(combinations(rest, k));
    result
}
