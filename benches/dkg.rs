use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};

use ark_bls12_381::G1Affine;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::UniformRand;
use std::collections::HashMap;
use std::time::Duration;

use golden_rs::types::{NodeId, Scalar};

fn bench_evrf_prove(c: &mut Criterion) {
    let mut rng = ark_std::test_rng();
    let sk1 = Scalar::rand(&mut rng);
    let pk1 = (G1Affine::generator() * sk1).into_affine();
    let sk2 = Scalar::rand(&mut rng);
    let pk2 = (G1Affine::generator() * sk2).into_affine();
    let r_value = Scalar::rand(&mut rng);
    let r_commitment = (G1Affine::generator() * r_value).into_affine();
    let beta = Scalar::rand(&mut rng);

    c.bench_function("evrf_prove_single", |b| {
        b.iter(|| {
            golden_rs::zk_evrf::prove_evrf(sk1, pk1, pk2, r_value, r_commitment, beta).unwrap()
        })
    });
}

fn bench_evrf_verify(c: &mut Criterion) {
    let mut rng = ark_std::test_rng();
    let sk1 = Scalar::rand(&mut rng);
    let pk1 = (G1Affine::generator() * sk1).into_affine();
    let sk2 = Scalar::rand(&mut rng);
    let pk2 = (G1Affine::generator() * sk2).into_affine();
    let r_value = Scalar::rand(&mut rng);
    let r_commitment = (G1Affine::generator() * r_value).into_affine();
    let beta = Scalar::rand(&mut rng);

    let proof =
        golden_rs::zk_evrf::prove_evrf(sk1, pk1, pk2, r_value, r_commitment, beta).unwrap();

    c.bench_function("evrf_verify_single", |b| {
        b.iter(|| golden_rs::zk_evrf::verify_evrf(pk1, pk2, r_commitment, beta, &proof).unwrap())
    });
}

fn bench_dkg_e2e(c: &mut Criterion) {
    let rt = tokio::runtime::Runtime::new().unwrap();

    let mut group = c.benchmark_group("dkg_e2e");
    group.sample_size(10);
    group.measurement_time(Duration::from_secs(60));

    for &(n, t) in &[(2u32, 2u32), (5, 3), (10, 6)] {
        group.bench_with_input(
            BenchmarkId::new("dkg", format!("n={}_t={}", n, t)),
            &(n, t),
            |b, &(n, t)| {
                b.iter(|| rt.block_on(async { run_dkg(n, t).await }));
            },
        );
    }
    group.finish();
}

async fn run_dkg(n: u32, t: u32) -> Vec<golden_rs::types::DkgOutput> {
    use rand::rngs::OsRng;

    let mut rng = OsRng;
    let beta = Scalar::rand(&mut rng);
    let network = golden_rs::network::Network::new(n);

    let mut handles = Vec::new();
    for i in 1..=n {
        let net = network.clone();
        let b = beta;
        handles.push(tokio::spawn(async move {
            let node = golden_rs::node::Node::new(i, n, t, b, net)
                .await
                .unwrap();
            node.run().await.unwrap()
        }));
    }

    let mut outputs = Vec::new();
    for handle in handles {
        outputs.push(handle.await.unwrap());
    }
    outputs
}

fn bench_message_size(c: &mut Criterion) {
    let rt = tokio::runtime::Runtime::new().unwrap();

    c.bench_function("message_size_n5_t3", |b| {
        b.iter(|| {
            rt.block_on(async {
                use golden_rs::protocol;
                use rand::rngs::OsRng;

                let n = 5u32;
                let t = 3u32;
                let mut rng = OsRng;
                let beta = Scalar::rand(&mut rng);

                // Generate identity keys
                let mut sks = HashMap::new();
                let mut peers: HashMap<NodeId, G1Affine> = HashMap::new();
                for i in 1..=n {
                    let sk = Scalar::rand(&mut rng);
                    let pk = (G1Affine::generator() * sk).into_affine();
                    sks.insert(i, sk);
                    peers.insert(i, pk);
                }

                let session_id = [42u8; 32];
                let (msg, _) =
                    protocol::round0(1, n, t, sks[&1], &peers, beta, &mut rng, session_id);

                // Measure Borsh serialized size
                let bytes = borsh::to_vec(&msg).unwrap();
                bytes.len()
            })
        })
    });
}

criterion_group!(
    benches,
    bench_evrf_prove,
    bench_evrf_verify,
    bench_dkg_e2e,
    bench_message_size,
);
criterion_main!(benches);
