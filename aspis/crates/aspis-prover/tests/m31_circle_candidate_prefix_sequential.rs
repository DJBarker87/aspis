use aspis_core::circle_candidate_verify::{
    verify_candidate_relation, verify_fresh_kappa_candidate, CandidateRelationVerifyError,
};
use aspis_core::circle_prefix::{
    CandidateOneLaneBatchingMode, CandidatePrefix, CANDIDATE_PREFIX_OFFSETS, CANDIDATE_QUERY_COUNT,
    CANDIDATE_STATEMENT_POINT_COORDINATES,
};
use aspis_core::field::{CM31, M31, P, QM31};
use aspis_prover::circle_candidate::{C1_COLUMNS, C2_COLUMNS, TRACE_LEN};
use aspis_prover::circle_candidate_prefix::{
    build_candidate_prefix_sequential, build_fresh_kappa_candidate_proof,
};
use aspis_prover::HOST_HASH;
use sha2::{Digest as _, Sha256};

#[derive(Clone, Copy)]
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0 = self.0.wrapping_mul(0x2545_f491_4f6c_dd1d);
        self.0
    }

    fn m31(&mut self) -> M31 {
        M31((self.next() as u32) % P)
    }

    fn qm31(&mut self) -> QM31 {
        QM31 {
            c0: CM31::new(self.m31(), self.m31()),
            c1: CM31::new(self.m31(), self.m31()),
        }
    }
}

fn fixture() -> (
    Vec<Vec<M31>>,
    Vec<Vec<QM31>>,
    [QM31; CANDIDATE_STATEMENT_POINT_COORDINATES],
) {
    let mut rng = Rng(0x5052_4546_4958_4341);
    let c1 = (0..C1_COLUMNS)
        .map(|column| {
            (0..TRACE_LEN)
                .map(|row| rng.m31().add(M31((column * 65_537 + row * 257 + 1) as u32)))
                .collect()
        })
        .collect();
    let c2 = (0..C2_COLUMNS)
        .map(|helper| {
            (0..TRACE_LEN)
                .map(|row| {
                    let mut value = rng.qm31();
                    value.c0.a = value.c0.a.add(M31((helper * 4_099 + row + 1) as u32));
                    value
                })
                .collect()
        })
        .collect();
    let z = core::array::from_fn(|coordinate| {
        let mut value = rng.qm31();
        value.c1.b = value.c1.b.add(M31((coordinate * 313 + 17) as u32));
        value
    });
    (c1, c2, z)
}

fn sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

#[test]
fn sequential_builder_pins_both_unselected_shapes_and_stale_statement_teeth() {
    let (c1, c2, z) = fixture();
    let statement_digest = Sha256::digest(b"aspis/m31-circle/sequential-candidate/v1").into();

    let selected =
        build_fresh_kappa_candidate_proof(&c1, &c2, z, statement_digest, HOST_HASH).unwrap();
    let proof = selected.bytes;
    let fresh = selected.prefix;
    let disjoint = build_candidate_prefix_sequential(
        &c1,
        &c2,
        z,
        statement_digest,
        HOST_HASH,
        CandidateOneLaneBatchingMode::DisjointGamma51,
    )
    .unwrap();

    CandidatePrefix::parse_exact(&fresh.bytes).unwrap();
    CandidatePrefix::parse_exact(&disjoint.bytes).unwrap();
    assert_eq!(
        fresh.batching_mode,
        CandidateOneLaneBatchingMode::FreshKappa
    );
    assert_eq!(
        disjoint.batching_mode,
        CandidateOneLaneBatchingMode::DisjointGamma51
    );
    assert_eq!(fresh.schedule.batching_mode, fresh.batching_mode);
    assert_eq!(disjoint.schedule.batching_mode, disjoint.batching_mode);
    assert_eq!(
        fresh.schedule.kappa,
        Some(fresh.schedule.second_point_scale)
    );
    assert_eq!(disjoint.schedule.kappa, None);
    assert_eq!(
        disjoint.schedule.second_point_scale,
        disjoint.schedule.prefix.gamma.pow(51)
    );
    assert_eq!(fresh.material.ood_values, fresh.relation.ood_values);
    assert_eq!(fresh.material.sumchecks, fresh.relation.sumchecks);
    assert_eq!(
        fresh.material.final_coefficients,
        fresh.relation.final_coefficients
    );
    assert_eq!(disjoint.material.ood_values, disjoint.relation.ood_values);
    assert_eq!(disjoint.material.sumchecks, disjoint.relation.sumchecks);
    assert_eq!(
        disjoint.material.final_coefficients,
        disjoint.relation.final_coefficients
    );
    assert_eq!(fresh.schedule.queries.len(), CANDIDATE_QUERY_COUNT as usize);
    assert!(fresh.schedule.queries.iter().all(|&query| query < 1_024));
    assert!(disjoint.schedule.queries.iter().all(|&query| query < 1_024));
    assert_ne!(fresh.bytes, disjoint.bytes);
    assert_ne!(
        fresh.schedule.state_after_queries,
        disjoint.schedule.state_after_queries
    );

    let mut stale_statement_digest = statement_digest;
    stale_statement_digest[0] ^= 1;
    let stale = build_candidate_prefix_sequential(
        &c1,
        &c2,
        z,
        stale_statement_digest,
        HOST_HASH,
        CandidateOneLaneBatchingMode::FreshKappa,
    )
    .unwrap();
    assert_ne!(fresh.bytes, stale.bytes);
    assert_ne!(fresh.schedule.prefix.gamma, stale.schedule.prefix.gamma);
    assert_ne!(
        fresh.schedule.state_after_queries,
        stale.schedule.state_after_queries
    );

    assert_eq!(
        sha256(&fresh.bytes),
        "8df40160314199a667225dcffd23ef8b04929e050e74235bc9aeabbbe5152b8e"
    );
    assert_eq!(
        sha256(&disjoint.bytes),
        "8b17d07daf9e259c7c7787e949e12215d13eda13fb80a9e49045ba2200327296"
    );
    assert_eq!(
        sha256(&stale.bytes),
        "2596c4ccd5873a14c490acb3521aaf0aab2fa6f91646d2440d0819a1a6f7ee5f"
    );
    assert_eq!(fresh.material.nonce, 20_677);
    assert_eq!(disjoint.material.nonce, 54_739);
    assert_eq!(stale.material.nonce, 65_871);

    let verified = verify_fresh_kappa_candidate(&proof, &statement_digest, &z, HOST_HASH).unwrap();
    assert_eq!(verified.schedule, fresh.schedule);
    assert!(!verified.openings.later.indices.layer0.is_empty());
    assert!(verified.openings.later.indices.layer0.len() <= 36);
    assert_eq!(
        sha256(&proof),
        "68a536081d60264494206895bb99f18c0633174583000fb7398d86dff50505ca"
    );

    let mut bad_relation = fresh.bytes.clone();
    let sumcheck_offset = CANDIDATE_PREFIX_OFFSETS.rounds[0].sumcheck_start;
    let changed = QM31::from_le_bytes(&bad_relation[sumcheck_offset..sumcheck_offset + 16])
        .unwrap()
        .add(QM31::ONE);
    changed.write_le_bytes(&mut bad_relation[sumcheck_offset..sumcheck_offset + 16]);
    let parsed_bad_relation = CandidatePrefix::parse_exact(&bad_relation).unwrap();
    assert_eq!(
        verify_candidate_relation(&parsed_bad_relation, &z, &fresh.schedule),
        Err(CandidateRelationVerifyError::BoundaryMismatch { round: 0 })
    );

    let mut bad_opening = proof.clone();
    bad_opening[CANDIDATE_PREFIX_OFFSETS.openings_start + 2] ^= 1;
    assert!(verify_fresh_kappa_candidate(&bad_opening, &statement_digest, &z, HOST_HASH).is_err());
    assert!(verify_fresh_kappa_candidate(&proof, &stale_statement_digest, &z, HOST_HASH).is_err());
    assert!(
        verify_fresh_kappa_candidate(&disjoint.bytes, &statement_digest, &z, HOST_HASH).is_err()
    );

    eprintln!(
        "fresh_prefix_sha256={} disjoint_prefix_sha256={} stale_prefix_sha256={} selected_proof_sha256={} selected_proof_bytes={} fresh_nonce={} disjoint_nonce={} stale_nonce={}",
        sha256(&fresh.bytes),
        sha256(&disjoint.bytes),
        sha256(&stale.bytes),
        sha256(&proof),
        proof.len(),
        fresh.material.nonce,
        disjoint.material.nonce,
        stale.material.nonce,
    );
}
