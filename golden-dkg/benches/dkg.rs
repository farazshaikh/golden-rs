use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};

use ark_bls12_381::G1Affine;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::UniformRand;
use std::collections::HashMap;

use golden_dkg::dkg;
use golden_dkg::types::{DkgConfig, NodeId, Participant, Scalar, SessionId};

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
            golden_dkg::zk_evrf::prove_evrf(sk1, pk1, pk2, r_value, r_commitment, beta).unwrap()
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
        golden_dkg::zk_evrf::prove_evrf(sk1, pk1, pk2, r_value, r_commitment, beta).unwrap();

    c.bench_function("evrf_verify_single", |b| {
        b.iter(|| golden_dkg::zk_evrf::verify_evrf(pk1, pk2, r_commitment, beta, &proof).unwrap())
    });
}

fn bench_dkg_e2e(c: &mut Criterion) {
    let mut group = c.benchmark_group("dkg_e2e");
    group.sample_size(10);

    for &(n, t) in &[(2u32, 2u32), (5, 3)] {
        group.bench_with_input(
            BenchmarkId::new("dkg", format!("n={}_t={}", n, t)),
            &(n, t),
            |b, &(n, t)| {
                b.iter(|| {
                    let mut rng = ark_std::test_rng();
                    let beta = Scalar::rand(&mut rng);

                    let mut participants = Vec::new();
                    let mut peers = HashMap::new();
                    for i in 1..=n {
                        let p = Participant::new(i, &mut rng);
                        peers.insert(i, p.pk);
                        participants.push(p);
                    }

                    let session_id = SessionId([0u8; 32]);
                    let config = DkgConfig {
                        n,
                        t,
                        beta,
                        session_id,
                    };

                    // Round 0: all participants create dealings
                    let mut dealings = Vec::new();
                    let mut all_msgs: HashMap<NodeId, _> = HashMap::new();
                    for p in &participants {
                        let dealing = dkg::create_dealing(p, &config, &peers, &mut rng).unwrap();
                        all_msgs.insert(p.id, dealing.message.clone());
                        dealings.push(dealing);
                    }

                    // Round 1: all participants complete
                    for (i, p) in participants.iter().enumerate() {
                        let peer_msgs: HashMap<NodeId, _> = all_msgs
                            .iter()
                            .filter(|(&id, _)| id != p.id)
                            .map(|(&id, msg)| (id, msg.clone()))
                            .collect();
                        let _output =
                            dkg::complete(p, &dealings[i], &peer_msgs, &peers, &config).unwrap();
                    }
                });
            },
        );
    }
    group.finish();
}

#[cfg(feature = "borsh")]
fn bench_message_size(c: &mut Criterion) {
    c.bench_function("message_size_n5_t3", |b| {
        b.iter(|| {
            let n = 5u32;
            let t = 3u32;
            let mut rng = ark_std::test_rng();
            let beta = Scalar::rand(&mut rng);

            let mut participants = Vec::new();
            let mut peers = HashMap::new();
            for i in 1..=n {
                let p = Participant::new(i, &mut rng);
                peers.insert(i, p.pk);
                participants.push(p);
            }

            let config = DkgConfig {
                n,
                t,
                beta,
                session_id: SessionId([42u8; 32]),
            };

            let dealing = dkg::create_dealing(&participants[0], &config, &peers, &mut rng).unwrap();
            let bytes = borsh::to_vec(&dealing.message).unwrap();
            bytes.len()
        })
    });
}

#[cfg(feature = "borsh")]
criterion_group!(
    benches,
    bench_evrf_prove,
    bench_evrf_verify,
    bench_dkg_e2e,
    bench_message_size,
);

#[cfg(not(feature = "borsh"))]
criterion_group!(benches, bench_evrf_prove, bench_evrf_verify, bench_dkg_e2e,);
criterion_main!(benches);
