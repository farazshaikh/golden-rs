use std::collections::HashMap;
use std::time::Instant;

use ark_bls12_381::G1Affine;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::UniformRand;
use rand::rngs::OsRng;

use goldenkeysharing::network::Network;
use goldenkeysharing::node::Node;
use goldenkeysharing::reshare_network::ReshareNetwork;
use goldenkeysharing::reshare_node::{NewReshareNode, OldReshareNode};
use goldenkeysharing::shamir::lagrange_interpolate_at_zero;
use goldenkeysharing::types::{DkgOutput, NodeId, Scalar};

/// Generate all C(n, k) combinations of indices.
fn generate_combinations(
    items: &[usize],
    k: usize,
    current: &mut Vec<usize>,
    start: usize,
    results: &mut Vec<Vec<usize>>,
) {
    if current.len() == k {
        results.push(current.clone());
        return;
    }
    for i in start..items.len() {
        current.push(items[i]);
        generate_combinations(items, k, current, i + 1, results);
        current.pop();
    }
}

#[tokio::main]
async fn main() {
    tracing_subscriber::fmt::init();

    let n = 5u32;
    let t = 3u32;

    println!("=== Golden DKG Prototype ===");
    println!("Participants: {}, Threshold: {}", n, t);
    println!();

    // Shared public parameter beta (same for all nodes)
    let mut rng = OsRng;
    let beta = Scalar::rand(&mut rng);

    // Create network
    let network = Network::new(n);

    // Spawn n nodes as tokio tasks
    let start = Instant::now();

    let mut handles = Vec::new();
    for i in 1..=n {
        let net = network.clone();
        let b = beta;
        handles.push(tokio::spawn(async move {
            let node = Node::new(i, n, t, b, net).await;
            node.run().await
        }));
    }

    // Collect results
    let mut outputs: Vec<(NodeId, DkgOutput)> = Vec::new();
    for (i, handle) in handles.into_iter().enumerate() {
        let output = handle.await.expect("Task panicked");
        outputs.push(((i + 1) as NodeId, output));
    }

    let elapsed = start.elapsed();

    println!("DKG completed in {:.2?}", elapsed);
    println!();

    // === VERIFICATION ===

    // 1. All nodes agree on the same public key
    let pk = outputs[0].1.public_key;
    for (id, output) in &outputs {
        assert_eq!(output.public_key, pk, "Node {} has different PK!", id);
    }
    println!("[PASS] All {} nodes agree on public key PK", n);

    // 2. All nodes agree on the same public key shares
    for k in 1..=n {
        let pk_k = outputs[0].1.public_key_shares[&k];
        for (id, output) in &outputs {
            assert_eq!(
                output.public_key_shares[&k], pk_k,
                "Node {} has different PK_{} share!",
                id, k
            );
        }
    }
    println!("[PASS] All nodes agree on all {} public key shares", n);

    // 3. Exhaustive threshold reconstruction: ALL C(n,t) combinations must reconstruct the same sk
    let all_shares: Vec<(NodeId, Scalar)> = outputs
        .iter()
        .map(|(id, o)| (*id, o.secret_share))
        .collect();

    // Generate all C(5,3) = 10 combinations
    let mut combinations = Vec::new();
    let indices: Vec<usize> = (0..n as usize).collect();
    generate_combinations(&indices, t as usize, &mut vec![], 0, &mut combinations);

    let mut reference_sk: Option<Scalar> = None;
    let mut combo_count = 0;

    for combo in &combinations {
        let subset: Vec<(NodeId, Scalar)> = combo.iter().map(|&idx| all_shares[idx]).collect();

        let reconstructed = lagrange_interpolate_at_zero(&subset);
        let reconstructed_pk = (G1Affine::generator() * reconstructed).into_affine();

        // Every combination must produce g^sk == PK
        assert_eq!(
            reconstructed_pk,
            pk,
            "Combination {:?} reconstructed wrong PK!",
            combo.iter().map(|&i| all_shares[i].0).collect::<Vec<_>>()
        );

        // Every combination must produce the same sk
        match reference_sk {
            None => reference_sk = Some(reconstructed),
            Some(ref_sk) => {
                assert_eq!(
                    reconstructed,
                    ref_sk,
                    "Combination {:?} reconstructed different sk!",
                    combo.iter().map(|&i| all_shares[i].0).collect::<Vec<_>>()
                );
            }
        }

        combo_count += 1;
    }

    println!(
        "[PASS] All {} of C({},{}) combinations reconstruct the same sk (g^sk == PK)",
        combo_count, n, t
    );

    // 5. Verify public key shares match secret shares
    for (id, output) in &outputs {
        let expected_pk_share = (G1Affine::generator() * output.secret_share).into_affine();
        assert_eq!(
            output.public_key_shares[id], expected_pk_share,
            "Node {}'s PK share doesn't match g^{{sk_i}}!",
            id
        );
    }
    println!("[PASS] All public key shares match g^{{sk_i}} for each node");

    println!();
    println!("=== All checks passed! Golden DKG working correctly. ===");
    println!("  n={}, t={}, time={:.2?}", n, t, elapsed);

    // ================================================================
    // === KEY REFRESH PHASE ===
    // ================================================================
    println!();
    println!("=== Key Refresh (Zero Secret Sharing) ===");
    println!();

    // Save original shares and PK for comparison
    let original_pk = pk;
    let original_sk = reference_sk.unwrap();
    let original_shares: Vec<(NodeId, Scalar)> = outputs
        .iter()
        .map(|(id, o)| (*id, o.secret_share))
        .collect();

    // Create fresh network for refresh round
    let refresh_network = Network::new(n);
    let refresh_start = Instant::now();

    // Spawn n nodes for refresh -- each carries its existing DkgOutput
    let mut refresh_handles = Vec::new();
    for (id, output) in outputs {
        let net = refresh_network.clone();
        let b = beta;
        refresh_handles.push(tokio::spawn(async move {
            let node = Node::new(id, n, t, b, net).await;
            node.run_refresh(output).await
        }));
    }

    // Collect refresh results
    let mut refresh_outputs: Vec<(NodeId, DkgOutput)> = Vec::new();
    for (i, handle) in refresh_handles.into_iter().enumerate() {
        let output = handle.await.expect("Refresh task panicked");
        refresh_outputs.push(((i + 1) as NodeId, output));
    }

    let refresh_elapsed = refresh_start.elapsed();
    println!("Refresh completed in {:.2?}", refresh_elapsed);
    println!();

    // === REFRESH VERIFICATION ===

    // 1. PK is unchanged
    let refresh_pk = refresh_outputs[0].1.public_key;
    assert_eq!(refresh_pk, original_pk, "PK changed after refresh!");
    for (id, output) in &refresh_outputs {
        assert_eq!(
            output.public_key, original_pk,
            "Node {} has different PK after refresh!",
            id
        );
    }
    println!("[PASS] Public key PK unchanged after refresh");

    // 2. Shares are DIFFERENT from original (rotation happened)
    let new_shares: Vec<(NodeId, Scalar)> = refresh_outputs
        .iter()
        .map(|(id, o)| (*id, o.secret_share))
        .collect();
    let shares_changed = original_shares
        .iter()
        .zip(new_shares.iter())
        .any(|((_, old), (_, new))| old != new);
    assert!(shares_changed, "Shares did not change after refresh!");
    println!("[PASS] Secret shares rotated (different from original)");

    // 3. Exhaustive C(n,t) reconstruction with new shares
    let mut refresh_combinations = Vec::new();
    generate_combinations(
        &indices,
        t as usize,
        &mut vec![],
        0,
        &mut refresh_combinations,
    );

    let mut refresh_ref_sk: Option<Scalar> = None;
    let mut refresh_combo_count = 0;

    for combo in &refresh_combinations {
        let subset: Vec<(NodeId, Scalar)> = combo.iter().map(|&idx| new_shares[idx]).collect();
        let reconstructed = lagrange_interpolate_at_zero(&subset);
        let reconstructed_pk = (G1Affine::generator() * reconstructed).into_affine();

        // Must reconstruct the SAME sk as original DKG
        assert_eq!(
            reconstructed_pk,
            original_pk,
            "Refreshed combination {:?} reconstructed wrong PK!",
            combo.iter().map(|&i| new_shares[i].0).collect::<Vec<_>>()
        );

        // All combinations must agree on same sk
        match refresh_ref_sk {
            None => refresh_ref_sk = Some(reconstructed),
            Some(ref_sk) => {
                assert_eq!(
                    reconstructed,
                    ref_sk,
                    "Refreshed combination {:?} reconstructed different sk!",
                    combo.iter().map(|&i| new_shares[i].0).collect::<Vec<_>>()
                );
            }
        }

        refresh_combo_count += 1;
    }

    // Verify the reconstructed sk matches the original
    assert_eq!(
        refresh_ref_sk.unwrap(),
        original_sk,
        "Refreshed sk differs from original sk!"
    );

    println!(
        "[PASS] All {} of C({},{}) combinations of NEW shares reconstruct the SAME original sk",
        refresh_combo_count, n, t
    );

    // 4. New PK shares match g^{new_sk_i}
    for (id, output) in &refresh_outputs {
        let expected_pk_share = (G1Affine::generator() * output.secret_share).into_affine();
        assert_eq!(
            output.public_key_shares[id], expected_pk_share,
            "Node {}'s refreshed PK share doesn't match g^{{new_sk_i}}!",
            id
        );
    }
    println!("[PASS] All refreshed public key shares match g^{{new_sk_i}}");

    println!();
    println!("=== All refresh checks passed! ===");
    println!(
        "  n={}, t={}, refresh_time={:.2?}, total_time={:.2?}",
        n,
        t,
        refresh_elapsed,
        start.elapsed()
    );

    // ================================================================
    // === RESHARING PHASE 1: SHRINK (n=5,t=3) -> (n=4,t=2) ===
    // ================================================================
    println!();
    println!("=== Resharing: (n=5,t=3) -> (n=4,t=2) -- drop 1 member, lower threshold ===");
    println!();

    let reshare1_original_pk = original_pk;
    let reshare1_original_sk = original_sk;

    // Old group: all 5 nodes from refresh phase
    let n_old_1 = 5u32;
    let t_old_1 = 3u32;
    // New group: nodes 1-4, threshold 2
    let n_new_1 = 4u32;
    let t_new_1 = 2u32;

    // Collect old PK shares for verification
    let old_pk_shares_1: HashMap<NodeId, G1Affine> = refresh_outputs
        .iter()
        .map(|(id, o)| (*id, o.public_key_shares[id]))
        .collect();

    // Create reshare network: 5 old + 4 new = 9 total participants
    let reshare_net_1 = ReshareNetwork::new(n_old_1 + n_new_1);
    let reshare1_start = Instant::now();

    // Spawn old nodes (dealers)
    let mut old_handles_1 = Vec::new();
    for (id, output) in &refresh_outputs {
        let net = reshare_net_1.clone();
        let b = beta;
        let share = output.secret_share;
        let old_id = *id;
        old_handles_1.push(tokio::spawn(async move {
            let node = OldReshareNode::new(old_id, share, t_new_1, b, n_old_1, net).await;
            node.run().await;
        }));
    }

    // Spawn new nodes (receivers)
    let mut new_handles_1 = Vec::new();
    for new_id in 1..=n_new_1 {
        let net = reshare_net_1.clone();
        let b = beta;
        let pk = reshare1_original_pk;
        let old_pks = old_pk_shares_1.clone();
        new_handles_1.push(tokio::spawn(async move {
            let node = NewReshareNode::new(new_id, b, pk, old_pks, t_old_1, n_old_1, net).await;
            node.run().await
        }));
    }

    // Wait for old nodes to finish dealing
    for handle in old_handles_1 {
        handle.await.expect("Old reshare node panicked");
    }

    // Collect new node outputs
    let mut reshare1_outputs: Vec<(NodeId, DkgOutput)> = Vec::new();
    for (i, handle) in new_handles_1.into_iter().enumerate() {
        let output = handle.await.expect("New reshare node panicked");
        reshare1_outputs.push(((i + 1) as NodeId, output));
    }

    let reshare1_elapsed = reshare1_start.elapsed();
    println!("Resharing completed in {:.2?}", reshare1_elapsed);
    println!();

    // Verify PK unchanged
    for (id, output) in &reshare1_outputs {
        assert_eq!(
            output.public_key, reshare1_original_pk,
            "Node {} has different PK after resharing!",
            id
        );
    }
    println!(
        "[PASS] PK unchanged after resharing to (n={},t={})",
        n_new_1, t_new_1
    );

    // Verify all C(4,2) = 6 combinations reconstruct same sk
    let reshare1_shares: Vec<(NodeId, Scalar)> = reshare1_outputs
        .iter()
        .map(|(id, o)| (*id, o.secret_share))
        .collect();

    let reshare1_indices: Vec<usize> = (0..n_new_1 as usize).collect();
    let mut reshare1_combos = Vec::new();
    generate_combinations(
        &reshare1_indices,
        t_new_1 as usize,
        &mut vec![],
        0,
        &mut reshare1_combos,
    );

    let mut reshare1_ref_sk: Option<Scalar> = None;
    let mut reshare1_count = 0;

    for combo in &reshare1_combos {
        let subset: Vec<(NodeId, Scalar)> = combo.iter().map(|&idx| reshare1_shares[idx]).collect();
        let reconstructed = lagrange_interpolate_at_zero(&subset);
        let reconstructed_pk = (G1Affine::generator() * reconstructed).into_affine();

        assert_eq!(
            reconstructed_pk,
            reshare1_original_pk,
            "Reshare1 combo {:?} wrong PK!",
            combo
                .iter()
                .map(|&i| reshare1_shares[i].0)
                .collect::<Vec<_>>()
        );

        match reshare1_ref_sk {
            None => reshare1_ref_sk = Some(reconstructed),
            Some(ref_sk) => assert_eq!(
                reconstructed, ref_sk,
                "Reshare1 combo {:?} different sk!",
                combo
            ),
        }
        reshare1_count += 1;
    }

    assert_eq!(
        reshare1_ref_sk.unwrap(),
        reshare1_original_sk,
        "Reshared sk differs from original!"
    );

    println!(
        "[PASS] All {} of C({},{}) combinations reconstruct the SAME original sk",
        reshare1_count, n_new_1, t_new_1
    );

    // Verify PK shares match g^{sk_i}
    for (id, output) in &reshare1_outputs {
        let expected = (G1Affine::generator() * output.secret_share).into_affine();
        assert_eq!(
            output.public_key_shares[id], expected,
            "Reshare1 node {} PK share mismatch!",
            id
        );
    }
    println!("[PASS] All reshared PK shares match g^{{sk_i}}");

    println!();
    println!("=== Resharing phase 1 passed! (n=5,t=3) -> (n=4,t=2) ===");

    // ================================================================
    // === RESHARING PHASE 2: GROW (n=4,t=2) -> (n=7,t=4) ===
    // ================================================================
    println!();
    println!("=== Resharing: (n=4,t=2) -> (n=7,t=4) -- add 3 members, raise threshold ===");
    println!();

    // Old group: 4 nodes from reshare phase 1
    let n_old_2 = n_new_1; // 4
    let t_old_2 = t_new_1; // 2
                           // New group: 7 nodes, threshold 4
    let n_new_2 = 7u32;
    let t_new_2 = 4u32;

    // Old PK shares from reshare phase 1
    let old_pk_shares_2: HashMap<NodeId, G1Affine> = reshare1_outputs
        .iter()
        .map(|(id, o)| (*id, o.public_key_shares[id]))
        .collect();

    let reshare_net_2 = ReshareNetwork::new(n_old_2 + n_new_2);
    let reshare2_start = Instant::now();

    // Spawn old nodes (the 4 from phase 1)
    let mut old_handles_2 = Vec::new();
    for (id, output) in &reshare1_outputs {
        let net = reshare_net_2.clone();
        let b = beta;
        let share = output.secret_share;
        let old_id = *id;
        old_handles_2.push(tokio::spawn(async move {
            let node = OldReshareNode::new(old_id, share, t_new_2, b, n_old_2, net).await;
            node.run().await;
        }));
    }

    // Spawn 7 new nodes
    let mut new_handles_2 = Vec::new();
    for new_id in 1..=n_new_2 {
        let net = reshare_net_2.clone();
        let b = beta;
        let pk = reshare1_original_pk;
        let old_pks = old_pk_shares_2.clone();
        new_handles_2.push(tokio::spawn(async move {
            let node = NewReshareNode::new(new_id, b, pk, old_pks, t_old_2, n_old_2, net).await;
            node.run().await
        }));
    }

    for handle in old_handles_2 {
        handle.await.expect("Old reshare node 2 panicked");
    }

    let mut reshare2_outputs: Vec<(NodeId, DkgOutput)> = Vec::new();
    for (i, handle) in new_handles_2.into_iter().enumerate() {
        let output = handle.await.expect("New reshare node 2 panicked");
        reshare2_outputs.push(((i + 1) as NodeId, output));
    }

    let reshare2_elapsed = reshare2_start.elapsed();
    println!("Resharing completed in {:.2?}", reshare2_elapsed);
    println!();

    // Verify PK unchanged
    for (id, output) in &reshare2_outputs {
        assert_eq!(
            output.public_key, reshare1_original_pk,
            "Node {} has different PK after resharing phase 2!",
            id
        );
    }
    println!(
        "[PASS] PK unchanged after resharing to (n={},t={})",
        n_new_2, t_new_2
    );

    // Verify all C(7,4) = 35 combinations
    let reshare2_shares: Vec<(NodeId, Scalar)> = reshare2_outputs
        .iter()
        .map(|(id, o)| (*id, o.secret_share))
        .collect();

    let reshare2_indices: Vec<usize> = (0..n_new_2 as usize).collect();
    let mut reshare2_combos = Vec::new();
    generate_combinations(
        &reshare2_indices,
        t_new_2 as usize,
        &mut vec![],
        0,
        &mut reshare2_combos,
    );

    let mut reshare2_ref_sk: Option<Scalar> = None;
    let mut reshare2_count = 0;

    for combo in &reshare2_combos {
        let subset: Vec<(NodeId, Scalar)> = combo.iter().map(|&idx| reshare2_shares[idx]).collect();
        let reconstructed = lagrange_interpolate_at_zero(&subset);
        let reconstructed_pk = (G1Affine::generator() * reconstructed).into_affine();

        assert_eq!(
            reconstructed_pk,
            reshare1_original_pk,
            "Reshare2 combo {:?} wrong PK!",
            combo
                .iter()
                .map(|&i| reshare2_shares[i].0)
                .collect::<Vec<_>>()
        );

        match reshare2_ref_sk {
            None => reshare2_ref_sk = Some(reconstructed),
            Some(ref_sk) => assert_eq!(
                reconstructed, ref_sk,
                "Reshare2 combo {:?} different sk!",
                combo
            ),
        }
        reshare2_count += 1;
    }

    assert_eq!(
        reshare2_ref_sk.unwrap(),
        reshare1_original_sk,
        "Reshare2 sk differs from original!"
    );

    println!(
        "[PASS] All {} of C({},{}) combinations reconstruct the SAME original sk",
        reshare2_count, n_new_2, t_new_2
    );

    for (id, output) in &reshare2_outputs {
        let expected = (G1Affine::generator() * output.secret_share).into_affine();
        assert_eq!(
            output.public_key_shares[id], expected,
            "Reshare2 node {} PK share mismatch!",
            id
        );
    }
    println!("[PASS] All reshared PK shares match g^{{sk_i}}");

    println!();
    println!("=== Resharing phase 2 passed! (n=4,t=2) -> (n=7,t=4) ===");
    println!();
    println!("=== ALL PROTOCOL PHASES COMPLETE ===");
    println!(
        "  DKG: n=5,t=3 ({:.2?}) -> Refresh ({:.2?}) -> Reshare to n=4,t=2 ({:.2?}) -> Reshare to n=7,t=4 ({:.2?})",
        elapsed, refresh_elapsed, reshare1_elapsed, reshare2_elapsed
    );
    println!("  Total time: {:.2?}", start.elapsed());
}
