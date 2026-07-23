//! Read-only deployment audit for the provisional v5 inactive claim.
//!
//! This test does not construct two witnesses for one statement and makes no
//! same-statement privacy claim. It checks two narrower code facts:
//!
//! 1. every currently encoded structured-B lane has atomic-v3 copy-inactive
//!    functional equal to its caller-supplied row-993 pivot pad; and
//! 2. the semantic inactive aggregate is not a protocol-wide constant across
//!    several independently valid atomic-v3 fixture pairs.

#![cfg(feature = "v5-mask")]

use aspis_core::field::{qm31_power_table, CM31, M31, P, QM31};
use aspis_prover::v5_mask::spend_messages::{V5StructuredBLane, V5_B_INACTIVE_PIVOT_ROW};
use aspis_prover::v5_mask::Qm31WordSource;
use aspis_prover::v5_sumcheck_mask::V5SumcheckMask;
use aspis_statement::atomic_state_only_terminal::atomic_state_only_copy_inactive_row_masks_v3;
use aspis_statement::atomic_state_only_trace::{
    atomic_merkle_root_v3, build_atomic_state_only_trace_v3,
};
use aspis_statement::{
    derive_nullifier, derive_owner_key, note_commitment, output_commitment,
    AtomicPaymentStatementV4, Digest, MerklePath, SpendPublic, SpendWitness,
};

const SEMANTIC_LANES: usize = 16;
const TOTAL_LANES: usize = 19;

struct XorShift(u64);

impl Qm31WordSource for XorShift {
    fn next_word(&mut self) -> u32 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        (x >> 21) as u32 % P
    }
}

fn digest(seed: u32) -> Digest {
    core::array::from_fn(|index| M31(seed + 17 * index as u32))
}

fn q(seed: u32) -> QM31 {
    QM31 {
        c0: CM31::new(M31(seed * 1_003 + 1), M31(seed * 1_009 + 3)),
        c1: CM31::new(M31(seed * 1_021 + 5), M31(seed * 1_031 + 7)),
    }
}

fn valid_fixture(variant: u32) -> (AtomicPaymentStatementV4, SpendWitness) {
    let nullifier_key = digest(101 + 10_000 * variant);
    let input_salt = digest(301 + 10_000 * variant);
    let output_salt = digest(501 + 10_000 * variant);
    let output_owner_key = digest(701 + 10_000 * variant);
    let asset_id = M31(17);
    let value = 1_000_000u32 + variant * 1_000;
    let value_out = value - 1;
    let merkle_path = MerklePath {
        siblings: (0..20)
            .map(|level| digest(1_000 + 31 * level + 10_000 * variant))
            .collect(),
        index: (0x5_a5a5u32.wrapping_add(0x1_1111 * variant)) & ((1 << 20) - 1),
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
    let input = note_commitment(
        &derive_owner_key(&nullifier_key),
        value,
        asset_id,
        &input_salt,
    );
    let output = output_commitment(&output_owner_key, value_out, asset_id, &output_salt);
    let statement = AtomicPaymentStatementV4 {
        pool: [0x5a; 32],
        sequence: 73,
        spend: SpendPublic {
            anchor: atomic_merkle_root_v3(input, &witness.merkle_path).unwrap(),
            nullifier: derive_nullifier(&nullifier_key, &input_salt),
            output_commitment: output,
            asset_id,
            fee: 1,
        },
        output_anchor: atomic_merkle_root_v3(output, &witness.merkle_path).unwrap(),
        deployment_domain: [0x5d; 32],
    };
    (statement, witness)
}

fn inactive(row: usize, masks: &[u16; 64]) -> bool {
    masks[row >> 4] & (1 << (row & 15)) != 0
}

fn b_inactive_sum(values: &[QM31; 1024], masks: &[u16; 64]) -> QM31 {
    values
        .iter()
        .copied()
        .enumerate()
        .filter(|(row, _)| inactive(*row, masks))
        .fold(QM31::ZERO, |sum, (_, value)| sum.add(value))
}

fn semantic_inactive_claim(
    statement: &AtomicPaymentStatementV4,
    witness: &SpendWitness,
    gamma: QM31,
) -> QM31 {
    let atomic = build_atomic_state_only_trace_v3(statement, witness).unwrap();
    let masks = atomic_state_only_copy_inactive_row_masks_v3();
    let powers = qm31_power_table::<TOTAL_LANES>(gamma);
    (0..SEMANTIC_LANES).fold(QM31::ZERO, |claim, lane| {
        let lane_sum = atomic.trace.c1[lane]
            .iter()
            .copied()
            .enumerate()
            .filter(|(row, _)| inactive(*row, &masks))
            .fold(M31::ZERO, |sum, (_, value)| sum.add(value));
        claim.add(powers[lane].mul_m31(lane_sum))
    })
}

#[test]
fn deployed_b_has_exact_affine_inactive_pad_while_semantic_claim_is_not_constant() {
    let masks = atomic_state_only_copy_inactive_row_masks_v3();
    assert!(inactive(V5_B_INACTIVE_PIVOT_ROW, &masks));

    for variant in 0..8u64 {
        let mask = V5SumcheckMask::sample(&mut XorShift(
            0xb517_1a90_5eed_0001 ^ variant.wrapping_mul(0x9e37_79b9),
        ))
        .unwrap();
        let pads = core::array::from_fn(|index| q(20_000 + 1_000 * variant as u32 + index as u32));
        let pivot_pad = q(30_000 + variant as u32);
        let lane = V5StructuredBLane::encode(&mask, &pads, pivot_pad).unwrap();
        let values = lane.values();
        assert_eq!(lane.pivot_pad(), pivot_pad);
        assert_eq!(b_inactive_sum(values, &masks), pivot_pad);

        let without_pivot = values
            .iter()
            .copied()
            .enumerate()
            .filter(|(row, _)| *row != V5_B_INACTIVE_PIVOT_ROW && inactive(*row, &masks))
            .fold(QM31::ZERO, |sum, (_, value)| sum.add(value));
        assert_eq!(
            values[V5_B_INACTIVE_PIVOT_ROW],
            pivot_pad.add(without_pivot.neg())
        );
    }

    let gamma = q(77_777);
    let claims: [QM31; 4] = core::array::from_fn(|variant| {
        let (statement, witness) = valid_fixture(variant as u32);
        semantic_inactive_claim(&statement, &witness, gamma)
    });
    eprintln!("valid-fixture semantic inactive claims: {claims:?}");
    for left in 0..claims.len() {
        for right in left + 1..claims.len() {
            assert_ne!(claims[left], claims[right]);
        }
    }
}
