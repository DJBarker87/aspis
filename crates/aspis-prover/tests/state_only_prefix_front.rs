use aspis_core::field::{CM31, M31, P, QM31};
use aspis_core::state_only_prefix::STATE_ONLY_RATE16_SHAPE;
use aspis_prover::state_only_candidate_prefix::{build_state_only_prefix_front, StateOnlyPowMode};
use aspis_prover::HOST_HASH;
use aspis_statement::{
    build_spend_trace_v4, derive_nullifier, derive_owner_key, merkle_root, note_commitment,
    output_commitment, project_state_only_trace_v4, Digest, MerklePath, SpendPublic, SpendWitness,
};

fn digest(seed: u32) -> Digest {
    core::array::from_fn(|index| M31(seed + index as u32 * 17))
}

fn fixture() -> (SpendPublic, SpendWitness) {
    let nullifier_key = digest(101);
    let input_salt = digest(301);
    let output_salt = digest(501);
    let output_owner_key = digest(701);
    let asset_id = M31(17);
    let value = 1_000_000;
    let value_out = 999_999;
    let owner_key = derive_owner_key(&nullifier_key);
    let note = note_commitment(&owner_key, value, asset_id, &input_salt);
    let merkle_path = MerklePath {
        siblings: (0..20).map(|level| digest(1_000 + level * 29)).collect(),
        index: 0x5_4321,
    };
    let public = SpendPublic {
        anchor: merkle_root(note, &merkle_path).unwrap(),
        nullifier: derive_nullifier(&nullifier_key, &input_salt),
        output_commitment: output_commitment(&output_owner_key, value_out, asset_id, &output_salt),
        asset_id,
        fee: 1,
    };
    let witness = SpendWitness {
        nullifier_key,
        input_salt,
        output_salt,
        output_owner_key,
        input_asset_id: asset_id,
        value,
        value_out,
        merkle_path,
    };
    (public, witness)
}

fn g_mask() -> Vec<QM31> {
    let mut state = 0x474d_4153_4b31_3032u64;
    (0..1024)
        .map(|_| {
            let mut next = || {
                state = state
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1_442_695_040_888_963_407);
                M31((state % u64::from(P)) as u32)
            };
            QM31 {
                c0: CM31::new(next(), next()),
                c1: CM31::new(next(), next()),
            }
        })
        .collect()
}

#[test]
fn honest_state_only_prefix_front_replays_byte_exact() {
    let (public, witness) = fixture();
    let old = build_spend_trace_v4(&public, &witness).unwrap();
    let trace = project_state_only_trace_v4(&old).unwrap();
    let front = build_state_only_prefix_front(
        &public,
        &trace,
        &g_mask(),
        [0x51; 32],
        [0xa7; 32],
        STATE_ONLY_RATE16_SHAPE,
        HOST_HASH,
        StateOnlyPowMode::UnminedZero,
    )
    .unwrap();
    // Repinned 2026-07-15 for the spend epoch: the pre-strip pin predated
    // the current front layout while this suite was outside the per-suite CI
    // filters.
    assert_eq!(front.bytes.len(), 6_736);
    assert_eq!(front.schedule.z, front.zerocheck.challenges);
    assert_eq!(
        front.schedule.masked_terminal_claim,
        front.zerocheck.terminal_claim
    );
    assert!(!front.batch_pow_valid);
}
