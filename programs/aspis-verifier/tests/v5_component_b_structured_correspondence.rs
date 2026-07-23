//! Executable correspondence tests for the V5 Component-B structured compact
//! terminal path and its mode lock.
//!
//! Every test drives the
//! deployed code (`probe_sink`, the tag-66 entrypoint, the tag-67 verifier
//! callback, `verify_v5_relation_stress_with_additive`, and the production
//! `WeightAccumulator`) against literal references spelled out in this file
//! from the documented structured layout. The source-authentic Lean proofs
//! provide the corresponding universal result.
//!
//! The mode lock verified here:
//!   * mode 9 / tag 67 constructs its
//!     Component-B terminal only through the structured compact evaluator
//!     (`RelationVariant::FourClaimsCompact` + `CompactBTerminalWeights`);
//!   * the free-coordinate dense covector (`derive_v5_b_terminal_covector`)
//!     is reachable only from the rejected control modes 6 and 7, and those
//!     control fixtures cannot enter the mode-9/tag-67 production path.
//!
//! `CompactBTerminalWeights` itself is module-private, so its intermediate
//! per-fold states are compared indirectly: the literal dense mirror is
//! checked against an independent arity-4 fold reference after each of the
//! four folds, and the deployed compact object is checked end-to-end through
//! the sink and entrypoint equalities.  See the run report for the minimal
//! visibility patch that would allow direct intermediate-state comparison.
//!
//! Run with:
//! `cargo test -p aspis-verifier --locked --features v5-cu-probe,no-entrypoint \
//!      --test v5_component_b_structured_correspondence`

#![cfg(feature = "v5-cu-probe")]

use std::cell::RefCell;
use std::rc::Rc;

use aspis_core::field::{qm31_power_table, CM31, M31, P, QM31};
use aspis_core::sumcheck::WeightAccumulator;
use aspis_statement::atomic_state_only_terminal::atomic_state_only_copy_inactive_row_masks_v3;
use aspis_statement::{atomic_payment_statement_digest_v4, AtomicPaymentStatementV4, SpendPublic};
use aspis_verifier::v5_cu_probe::{
    probe_sink, process_v5_cu_probe_instruction, verify_uploaded_v5_mode9_cu_fixture,
    V5_CU_PROBE_ACCOUNT_BYTES, V5_CU_PROBE_ACCOUNT_MAGIC, V5_CU_PROBE_B_BLOCK_ROWS,
    V5_CU_PROBE_B_BLOCK_SELECTORS, V5_CU_PROBE_B_COMPACT_DYNAMIC_HEAP_BYTES,
    V5_CU_PROBE_B_COMPACT_STATE_BYTES, V5_CU_PROBE_B_DEPENDENT_PIVOT_ROW,
    V5_CU_PROBE_B_INITIAL_STATE_ROW, V5_CU_PROBE_B_MASK_COORDINATES, V5_CU_PROBE_B_PAD_COORDINATES,
    V5_CU_PROBE_B_STRUCTURED_BLOCKS, V5_CU_PROBE_COMPOSITE_MODE, V5_CU_PROBE_GAMMA_OFFSET,
    V5_CU_PROBE_RELATION3_MODE, V5_CU_PROBE_RELATION4_COMPACT_MODE,
    V5_CU_PROBE_RELATION4_DENSE_MODE, V5_CU_PROBE_RELATION4_STANDALONE_DOT_MODE,
    V5_CU_PROBE_RELATION_ALPHAS_OFFSET, V5_CU_PROBE_RELATION_CLAIMS_OFFSET,
    V5_CU_PROBE_RELATION_CLAIMS_PER_LANE, V5_CU_PROBE_RELATION_DENSE_VALUES,
    V5_CU_PROBE_RELATION_FINAL_OFFSET, V5_CU_PROBE_RELATION_FINAL_VALUES,
    V5_CU_PROBE_RELATION_FOLDS, V5_CU_PROBE_RELATION_LANES, V5_CU_PROBE_RELATION_LOG_ROWS,
    V5_CU_PROBE_RELATION_POINTS, V5_CU_PROBE_RELATION_POINTS_OFFSET,
    V5_CU_PROBE_RELATION_SCALES_OFFSET, V5_CU_PROBE_TAG, V5_CU_PROBE_WIRE_BYTES,
};
use aspis_verifier::v5_full_transaction::{
    parse_v5_full_cu_public_inputs, V5_FULL_CU_TRANSACTION_TAG, V5_FULL_CU_TRANSACTION_WIRE_BYTES,
};
use aspis_verifier::v5_relation_stress::{
    build_v5_relation_stress_tail_for_initial_claim, verify_v5_relation_stress_with_additive,
    V5RelationStressAdditive, V5_RELATION_STRESS_ROUNDS,
};
use aspis_verifier::PROOF_ACCOUNT_HEADER_LEN;
use solana_program::{
    account_info::AccountInfo, clock::Epoch, hash::hashv, program_error::ProgramError,
    pubkey::Pubkey,
};

const QM31_BYTES: usize = 16;
const LOG_ROWS: usize = V5_CU_PROBE_RELATION_LOG_ROWS as usize;
const ROWS: usize = V5_CU_PROBE_RELATION_DENSE_VALUES;
const LIVE_DEGREES_PER_BLOCK: usize = 28;

/// Pin of the deployed sink domain separator (`SINK_DOMAIN` in
/// `v5_cu_probe.rs`).  The sink for a relation mode is
/// `sha256(domain || [mode] || value_le16)`; if the deployed domain drifts,
/// every sink equality below fails loudly.
const SINK_DOMAIN: &[u8] = b"aspis-v5-cu-probe-v3";

fn host_hashv(inputs: &[&[u8]]) -> [u8; 32] {
    // Byte-identical to the crate-private `verify::sbf_hashv` host path:
    // both delegate to solana_program's SHA-256 `hashv`.
    hashv(inputs).to_bytes()
}

fn next_m31(state: &mut u64) -> M31 {
    *state = state
        .wrapping_mul(6_364_136_223_846_793_005)
        .wrapping_add(1_442_695_040_888_963_407);
    M31((*state % u64::from(P)) as u32)
}

fn next_qm31(state: &mut u64) -> QM31 {
    QM31 {
        c0: CM31::new(next_m31(state), next_m31(state)),
        c1: CM31::new(next_m31(state), next_m31(state)),
    }
}

fn next_nonzero_qm31(state: &mut u64) -> QM31 {
    loop {
        let value = next_qm31(state);
        if !value.is_zero() {
            return value;
        }
    }
}

fn write_qm31(data: &mut [u8], offset: usize, index: usize, value: QM31) {
    let start = offset + index * QM31_BYTES;
    value.write_le_bytes(&mut data[start..start + QM31_BYTES]);
}

fn read_qm31(data: &[u8], offset: usize, index: usize) -> QM31 {
    let start = offset + index * QM31_BYTES;
    QM31::from_le_bytes(&data[start..start + QM31_BYTES]).expect("canonical test field element")
}

fn limbs(value: QM31) -> [u32; 4] {
    [value.c0.a.0, value.c0.b.0, value.c1.a.0, value.c1.b.0]
}

fn hex32(bytes: &[u8; 32]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

/// Build a synthetic isolated-relation account: magic, canonical gamma,
/// kappa in scales slot zero, three ten-coordinate points, four claims per
/// lane, four nonzero fold challenges, and four nonzero final values.  The
/// v5 wire-prefix region stays zeroed, so the deployed decoder takes the
/// synthetic (non-real-prefix) path, exactly as the isolated controls do.
fn synthetic_relation_account(seed: u64) -> Vec<u8> {
    let mut state = seed;
    let mut data = vec![0u8; V5_CU_PROBE_ACCOUNT_BYTES];
    data[..V5_CU_PROBE_ACCOUNT_MAGIC.len()].copy_from_slice(&V5_CU_PROBE_ACCOUNT_MAGIC);
    write_qm31(
        &mut data,
        V5_CU_PROBE_GAMMA_OFFSET,
        0,
        next_nonzero_qm31(&mut state),
    );
    let kappa = next_nonzero_qm31(&mut state);
    write_qm31(&mut data, V5_CU_PROBE_RELATION_SCALES_OFFSET, 0, kappa);
    write_qm31(
        &mut data,
        V5_CU_PROBE_RELATION_SCALES_OFFSET,
        1,
        kappa.square(),
    );
    write_qm31(
        &mut data,
        V5_CU_PROBE_RELATION_SCALES_OFFSET,
        2,
        kappa.square().mul(kappa),
    );
    for index in 0..V5_CU_PROBE_RELATION_POINTS * LOG_ROWS {
        write_qm31(
            &mut data,
            V5_CU_PROBE_RELATION_POINTS_OFFSET,
            index,
            next_qm31(&mut state),
        );
    }
    for index in 0..V5_CU_PROBE_RELATION_CLAIMS_PER_LANE * V5_CU_PROBE_RELATION_LANES {
        write_qm31(
            &mut data,
            V5_CU_PROBE_RELATION_CLAIMS_OFFSET,
            index,
            next_qm31(&mut state),
        );
    }
    for index in 0..V5_CU_PROBE_RELATION_FOLDS {
        write_qm31(
            &mut data,
            V5_CU_PROBE_RELATION_ALPHAS_OFFSET,
            index,
            next_nonzero_qm31(&mut state),
        );
    }
    for index in 0..V5_CU_PROBE_RELATION_FINAL_VALUES {
        write_qm31(
            &mut data,
            V5_CU_PROBE_RELATION_FINAL_OFFSET,
            index,
            next_nonzero_qm31(&mut state),
        );
    }
    data
}

struct RelationInputs {
    gamma: QM31,
    kappa: QM31,
    points: [[QM31; LOG_ROWS]; V5_CU_PROBE_RELATION_POINTS],
    claims: [[QM31; V5_CU_PROBE_RELATION_LANES]; V5_CU_PROBE_RELATION_CLAIMS_PER_LANE],
    alphas: [QM31; V5_CU_PROBE_RELATION_FOLDS],
    finals: [QM31; V5_CU_PROBE_RELATION_FINAL_VALUES],
}

/// Decode the relation inputs from the exact account bytes, through the same
/// public offsets the deployed parser uses.
fn relation_inputs(data: &[u8]) -> RelationInputs {
    RelationInputs {
        gamma: read_qm31(data, V5_CU_PROBE_GAMMA_OFFSET, 0),
        kappa: read_qm31(data, V5_CU_PROBE_RELATION_SCALES_OFFSET, 0),
        points: core::array::from_fn(|point| {
            core::array::from_fn(|coordinate| {
                read_qm31(
                    data,
                    V5_CU_PROBE_RELATION_POINTS_OFFSET,
                    point * LOG_ROWS + coordinate,
                )
            })
        }),
        claims: core::array::from_fn(|point| {
            core::array::from_fn(|lane| {
                read_qm31(
                    data,
                    V5_CU_PROBE_RELATION_CLAIMS_OFFSET,
                    point * V5_CU_PROBE_RELATION_LANES + lane,
                )
            })
        }),
        alphas: core::array::from_fn(|index| {
            read_qm31(data, V5_CU_PROBE_RELATION_ALPHAS_OFFSET, index)
        }),
        finals: core::array::from_fn(|index| {
            read_qm31(data, V5_CU_PROBE_RELATION_FINAL_OFFSET, index)
        }),
    }
}

/// Literal spelling of the shared relation base used by every relation mode:
/// three gamma-batched multilinear claims scaled `[1, kappa, kappa^2]`, the
/// copy-inactive grouped masks, and (for four-claim variants) the fourth
/// gamma-batched claim scaled `kappa^3`, which is also the Component-B
/// covector scale.  Built from the production `WeightAccumulator` API.
fn base_accumulator_and_value(
    inputs: &RelationInputs,
    four_claims: bool,
) -> (WeightAccumulator, QM31, QM31) {
    let lane_powers = qm31_power_table::<V5_CU_PROBE_RELATION_LANES>(inputs.gamma);
    let mut weights = WeightAccumulator::empty(V5_CU_PROBE_RELATION_LOG_ROWS);
    let mut relation_value = QM31::ZERO;
    let kappa2 = inputs.kappa.square();
    let point_scales = [QM31::ONE, inputs.kappa, kappa2];
    for point in 0..V5_CU_PROBE_RELATION_POINTS {
        weights
            .add_multilinear(point_scales[point], inputs.points[point].to_vec())
            .expect("ten-coordinate point matches the log-1024 accumulator");
        let mut claim = QM31::ZERO;
        for lane in 0..V5_CU_PROBE_RELATION_LANES {
            claim = claim.add(lane_powers[lane].mul(inputs.claims[point][lane]));
        }
        relation_value = relation_value.add(point_scales[point].mul(claim));
    }
    let dense_scale = if four_claims {
        let kappa3 = kappa2.mul(inputs.kappa);
        let mut claim = QM31::ZERO;
        for lane in 0..V5_CU_PROBE_RELATION_LANES {
            claim = claim.add(lane_powers[lane].mul(inputs.claims[3][lane]));
        }
        relation_value = relation_value.add(kappa3.mul(claim));
        kappa3
    } else {
        QM31::ZERO
    };
    weights
        .add_grouped_64x16_binary_masks_deferred(atomic_state_only_copy_inactive_row_masks_v3())
        .expect("copy-inactive masks fit the log-1024 accumulator");
    (weights, relation_value, dense_scale)
}

/// The literal dense 1024-row STRUCTURED Component-B terminal covector,
/// derived from the documented compact layout: ten aligned 32-row blocks at
/// selectors `[0,1,2,3,4,5,6,28,29,30]`, 28 live degree weights
/// `scale * half^(9-round) * z_round^degree` per block with offsets 28..31
/// fixed zero, plus the initial-value singleton `scale * half^10` at row 992.
/// Row 993 (the copy-inactive dependent pivot) carries no terminal weight.
fn literal_structured_covector(point: &[QM31; LOG_ROWS], scale: QM31) -> Vec<QM31> {
    let half = QM31::ONE.half();
    let mut values = vec![QM31::ZERO; ROWS];
    for (round, (&selector, &z)) in V5_CU_PROBE_B_BLOCK_SELECTORS
        .iter()
        .zip(point.iter())
        .enumerate()
    {
        let block_scale = scale.mul(half.pow((V5_CU_PROBE_B_STRUCTURED_BLOCKS - 1 - round) as u64));
        let start = usize::from(selector) * V5_CU_PROBE_B_BLOCK_ROWS;
        let mut power = QM31::ONE;
        for degree in 0..LIVE_DEGREES_PER_BLOCK {
            values[start + degree] = block_scale.mul(power);
            power = power.mul(z);
        }
    }
    values[V5_CU_PROBE_B_INITIAL_STATE_ROW] = values[V5_CU_PROBE_B_INITIAL_STATE_ROW]
        .add(scale.mul(half.pow(V5_CU_PROBE_B_STRUCTURED_BLOCKS as u64)));
    values
}

fn first_copy_inactive_row() -> usize {
    let masks = atomic_state_only_copy_inactive_row_masks_v3();
    (0..ROWS)
        .find(|row| masks[row >> 4] & (1 << (row & 15)) != 0)
        .expect("the pinned copy-inactive functional is nonzero")
}

/// Literal spelling of the REJECTED free-coordinate control covector used
/// only by modes 6 and 7: 271 packed coordinate weights
/// (`half^10`, then `half^(9-round) * (z_round^degree - half)` for degrees
/// 1..=27) written to consecutive rows that skip the copy-inactive pivot.
/// This is the differential reference for the controls, not the candidate.
fn literal_free_coordinate_covector(point: &[QM31; LOG_ROWS], scale: QM31) -> (Vec<QM31>, usize) {
    const DEGREE: usize = 27;
    let pivot = first_copy_inactive_row();
    let half = QM31::ONE.half();
    let mut coordinate_weights = vec![QM31::ZERO; V5_CU_PROBE_B_MASK_COORDINATES];
    coordinate_weights[0] = half.pow(LOG_ROWS as u64);
    for (round, challenge) in point.iter().copied().enumerate() {
        let later_round_scale = half.pow((LOG_ROWS - 1 - round) as u64);
        let mut challenge_power = challenge;
        for degree in 1..=DEGREE {
            let coordinate = 1 + round * DEGREE + degree - 1;
            coordinate_weights[coordinate] = later_round_scale.mul(challenge_power.sub(half));
            challenge_power = challenge_power.mul(challenge);
        }
    }
    let mut covector = vec![QM31::ZERO; ROWS];
    for (coordinate, weight) in coordinate_weights.into_iter().enumerate() {
        let row = if coordinate < pivot {
            coordinate
        } else {
            coordinate + 1
        };
        covector[row] = scale.mul(weight);
    }
    (covector, pivot)
}

/// Independent arity-4 dual fold reference:
/// `out[i] = (in[4i] + a^3*in[4i+1] + a^2*in[4i+2] + a*in[4i+3]) / 4`,
/// with `/4` the true field inverse of four.
fn reference_fold(values: &[QM31], alpha: QM31) -> Vec<QM31> {
    let alpha2 = alpha.square();
    let alpha3 = alpha2.mul(alpha);
    let quarter = QM31::ONE.half().half();
    values
        .chunks_exact(4)
        .map(|chunk| {
            chunk[0]
                .add(alpha3.mul(chunk[1]))
                .add(alpha2.mul(chunk[2]))
                .add(alpha.mul(chunk[3]))
                .mul(quarter)
        })
        .collect()
}

fn folded_dot(
    mut accumulator: WeightAccumulator,
    alphas: &[QM31; V5_CU_PROBE_RELATION_FOLDS],
    finals: &[QM31; V5_CU_PROBE_RELATION_FINAL_VALUES],
) -> QM31 {
    for alpha in alphas {
        accumulator.fold(*alpha);
    }
    accumulator.dot(finals)
}

fn dense_only_accumulator(covector: Vec<QM31>) -> WeightAccumulator {
    let mut accumulator = WeightAccumulator::empty(V5_CU_PROBE_RELATION_LOG_ROWS);
    accumulator
        .add_dense(covector)
        .expect("1024-row covector matches the log-1024 accumulator");
    accumulator
}

fn relation_sink(mode: u8, value: QM31) -> [u8; 32] {
    let mut bytes = [0u8; QM31_BYTES];
    value.write_le_bytes(&mut bytes);
    hashv(&[SINK_DOMAIN, &[mode], &bytes]).to_bytes()
}

struct ExpectedRelationValues {
    mode5: QM31,
    mode6: QM31,
    mode7: QM31,
    mode8: QM31,
    /// Mode 8's arithmetic with the free-coordinate control swapped in;
    /// must NOT match the deployed mode-8 sink.
    mode8_free_swap: QM31,
    /// Mode 6's arithmetic with the structured covector swapped in;
    /// must NOT match the deployed mode-6 sink.
    mode6_structured_swap: QM31,
}

fn expected_relation_values(data: &[u8]) -> ExpectedRelationValues {
    let inputs = relation_inputs(data);
    let point0 = &inputs.points[0];

    let (base3, value3, _) = base_accumulator_and_value(&inputs, false);
    let mode5 = folded_dot(base3, &inputs.alphas, &inputs.finals).add(value3);

    let (_, value4, dense_scale) = base_accumulator_and_value(&inputs, true);
    let structured = literal_structured_covector(point0, dense_scale);
    let (free, pivot) = literal_free_coordinate_covector(point0, dense_scale);

    // Mode 6: the free-coordinate covector joins the shared accumulator and
    // is dual-folded with everything else.
    let (mut shared6, _, _) = base_accumulator_and_value(&inputs, true);
    shared6.add_dense(free.clone()).expect("dense fits");
    let mode6 = folded_dot(shared6, &inputs.alphas, &inputs.finals).add(value4);

    // Mode 7: rejected standalone unfolded row dot against the first final
    // value, excluding the pivot row.
    let (base7, _, _) = base_accumulator_and_value(&inputs, true);
    let standalone = free
        .iter()
        .copied()
        .enumerate()
        .filter(|(row, _)| *row != pivot)
        .fold(QM31::ZERO, |sum, (_, weight)| {
            sum.add(inputs.finals[0].mul(weight))
        });
    let mode7 = folded_dot(base7, &inputs.alphas, &inputs.finals)
        .add(value4)
        .add(standalone);

    // Mode 8: the structured covector is carried separately through the same
    // four folds and dotted with the same final values.  The deployed side
    // performs this with the compact evaluator; the literal dense mirror is
    // the correspondence reference.
    let (base8, _, _) = base_accumulator_and_value(&inputs, true);
    let structured_term = folded_dot(
        dense_only_accumulator(structured.clone()),
        &inputs.alphas,
        &inputs.finals,
    );
    let mode8 = folded_dot(base8, &inputs.alphas, &inputs.finals)
        .add(value4)
        .add(structured_term);

    let (base8_swap, _, _) = base_accumulator_and_value(&inputs, true);
    let free_term = folded_dot(dense_only_accumulator(free), &inputs.alphas, &inputs.finals);
    let mode8_free_swap = folded_dot(base8_swap, &inputs.alphas, &inputs.finals)
        .add(value4)
        .add(free_term);

    let (mut shared6_swap, _, _) = base_accumulator_and_value(&inputs, true);
    shared6_swap.add_dense(structured).expect("dense fits");
    let mode6_structured_swap =
        folded_dot(shared6_swap, &inputs.alphas, &inputs.finals).add(value4);

    ExpectedRelationValues {
        mode5,
        mode6,
        mode7,
        mode8,
        mode8_free_swap,
        mode6_structured_swap,
    }
}

fn make_account<'a>(
    key: &'a Pubkey,
    owner: &'a Pubkey,
    lamports: &'a mut u64,
    data: &'a mut [u8],
) -> AccountInfo<'a> {
    AccountInfo::new(
        key,
        false,
        false,
        lamports,
        data,
        owner,
        false,
        Epoch::default(),
    )
}

fn tiny_statement() -> AtomicPaymentStatementV4 {
    AtomicPaymentStatementV4 {
        pool: [7u8; 32],
        sequence: 3,
        spend: SpendPublic {
            anchor: [M31(1); 8],
            nullifier: [M31(2); 8],
            output_commitment: [M31(3); 8],
            asset_id: M31(5),
            fee: 1,
        },
        output_anchor: [M31(4); 8],
        deployment_domain: [9u8; 32],
    }
}

/// Wrap raw probe bytes in a sealed (finalized) lifecycle proof account:
/// `"ASPU" || proof_len || zeroed upload authority || proof bytes`.
fn sealed_proof_account_bytes(proof: &[u8]) -> Vec<u8> {
    let mut data = vec![0u8; PROOF_ACCOUNT_HEADER_LEN + proof.len()];
    data[..4].copy_from_slice(b"ASPU");
    data[4..8].copy_from_slice(&(proof.len() as u32).to_le_bytes());
    // Bytes 8..40 (upload authority) stay zero: finalized.
    data[PROOF_ACCOUNT_HEADER_LEN..].copy_from_slice(proof);
    data
}

// ---------------------------------------------------------------------------
// 1. Layout and mode-number pins.
// ---------------------------------------------------------------------------

#[test]
fn structured_layout_and_mode_constants_are_pinned() {
    assert_eq!(
        V5_CU_PROBE_B_BLOCK_SELECTORS,
        [0, 1, 2, 3, 4, 5, 6, 28, 29, 30],
        "structured block selectors"
    );
    assert_eq!(V5_CU_PROBE_B_STRUCTURED_BLOCKS, 10);
    assert_eq!(V5_CU_PROBE_B_BLOCK_ROWS, 32);
    assert_eq!(V5_CU_PROBE_B_INITIAL_STATE_ROW, 992);
    assert_eq!(V5_CU_PROBE_B_DEPENDENT_PIVOT_ROW, 993);
    assert_eq!(ROWS, 1024);
    assert_eq!(
        V5_CU_PROBE_B_MASK_COORDINATES,
        1 + V5_CU_PROBE_B_STRUCTURED_BLOCKS * 27,
        "271 = one initial value + ten rounds of 27 free degree coefficients"
    );
    assert_eq!(
        V5_CU_PROBE_B_MASK_COORDINATES + V5_CU_PROBE_B_PAD_COORDINATES,
        ROWS - 1
    );

    // Pivot facts derived from the production copy-inactive masks: the
    // structured design pins row 993 as its dependent pivot, and that row is
    // indeed copy-inactive; the free-coordinate CONTROL instead pivots on
    // the FIRST copy-inactive row, which is row 0.  The two pivots are
    // different rows in different layouts.
    let masks = atomic_state_only_copy_inactive_row_masks_v3();
    let copy_inactive = |row: usize| masks[row >> 4] & (1 << (row & 15)) != 0;
    assert!(
        copy_inactive(V5_CU_PROBE_B_DEPENDENT_PIVOT_ROW),
        "row 993 is a copy-inactive row"
    );
    assert_eq!(
        first_copy_inactive_row(),
        0,
        "the free-coordinate control pivots on the first copy-inactive row"
    );
    assert_ne!(
        V5_CU_PROBE_B_INITIAL_STATE_ROW,
        V5_CU_PROBE_B_DEPENDENT_PIVOT_ROW
    );

    // No structured block overlaps the initial-state or pivot rows.
    for selector in V5_CU_PROBE_B_BLOCK_SELECTORS {
        let start = usize::from(selector) * V5_CU_PROBE_B_BLOCK_ROWS;
        let end = start + V5_CU_PROBE_B_BLOCK_ROWS;
        assert!(
            end <= V5_CU_PROBE_B_INITIAL_STATE_ROW,
            "block at selector {selector} stays below row 992"
        );
    }

    // Mode and tag numbering the lock is stated against.
    assert_eq!(V5_CU_PROBE_RELATION3_MODE, 5);
    assert_eq!(V5_CU_PROBE_RELATION4_DENSE_MODE, 6);
    assert_eq!(V5_CU_PROBE_RELATION4_STANDALONE_DOT_MODE, 7);
    assert_eq!(V5_CU_PROBE_RELATION4_COMPACT_MODE, 8);
    assert_eq!(V5_CU_PROBE_COMPOSITE_MODE, 9);
    assert_eq!(V5_CU_PROBE_TAG, 66);
    assert_eq!(V5_FULL_CU_TRANSACTION_TAG, 67);

    // The compact state is a fixed small struct, not a 1024-value vector.
    assert_eq!(V5_CU_PROBE_B_COMPACT_DYNAMIC_HEAP_BYTES, 0);
    assert!(
        V5_CU_PROBE_B_COMPACT_STATE_BYTES < ROWS * QM31_BYTES / 16,
        "compact state ({V5_CU_PROBE_B_COMPACT_STATE_BYTES} bytes) must be far \
         below the 16384-byte dense materialisation"
    );
}

// ---------------------------------------------------------------------------
// 2. Literal structured covector layout properties.
// ---------------------------------------------------------------------------

#[test]
fn literal_structured_covector_matches_documented_block_layout() {
    let mut state = 0x51ab_11ce_0000_0002u64;
    for case in 0..8 {
        let point: [QM31; LOG_ROWS] = core::array::from_fn(|_| next_nonzero_qm31(&mut state));
        let scale = next_nonzero_qm31(&mut state);
        let covector = literal_structured_covector(&point, scale);
        let half = QM31::ONE.half();

        let mut live_rows = 0usize;
        for (round, &selector) in V5_CU_PROBE_B_BLOCK_SELECTORS.iter().enumerate() {
            let start = usize::from(selector) * V5_CU_PROBE_B_BLOCK_ROWS;
            let block_scale = scale.mul(half.pow((9 - round) as u64));
            let mut power = QM31::ONE;
            for degree in 0..LIVE_DEGREES_PER_BLOCK {
                assert_eq!(
                    covector[start + degree],
                    block_scale.mul(power),
                    "case {case}: block {selector} degree {degree}"
                );
                assert!(!covector[start + degree].is_zero());
                live_rows += 1;
                power = power.mul(point[round]);
            }
            // Offsets 28..31 of every selected block are fixed zero.
            for offset in LIVE_DEGREES_PER_BLOCK..V5_CU_PROBE_B_BLOCK_ROWS {
                assert_eq!(
                    covector[start + offset],
                    QM31::ZERO,
                    "case {case}: block {selector} fixed-zero offset {offset}"
                );
            }
        }

        // Row 992 carries the initial-value role: scale * half^10.
        assert_eq!(
            covector[V5_CU_PROBE_B_INITIAL_STATE_ROW],
            scale.mul(half.pow(10)),
            "case {case}: initial-state row 992"
        );
        live_rows += 1;
        // Row 993, the copy-inactive dependent pivot, is EXCLUDED from the
        // Component-B terminal contribution.
        assert_eq!(
            covector[V5_CU_PROBE_B_DEPENDENT_PIVOT_ROW],
            QM31::ZERO,
            "case {case}: dependent pivot row 993 carries no terminal weight"
        );

        let nonzero = covector.iter().filter(|value| !value.is_zero()).count();
        assert_eq!(nonzero, live_rows, "case {case}");
        assert_eq!(
            nonzero,
            V5_CU_PROBE_B_STRUCTURED_BLOCKS * LIVE_DEGREES_PER_BLOCK + 1
        );
    }
}

// ---------------------------------------------------------------------------
// 3. Deployed fold coefficient order and true-inverse normalization.
// ---------------------------------------------------------------------------

#[test]
fn deployed_fold_uses_alpha3_alpha2_alpha_order_and_true_quarter_normalization() {
    // `half` and `quarter` are the true field inverses of two and four, not
    // bit shifts: 2 * half = 1 and 4 * quarter = 1 in QM31.
    let half = QM31::ONE.half();
    let quarter = half.half();
    let two = QM31::ONE.add(QM31::ONE);
    let four = two.add(two);
    assert_eq!(two.mul(half), QM31::ONE);
    assert_eq!(four.mul(quarter), QM31::ONE);
    // In M31, 1/2 is (P+1)/2 = 2^30 — pinned as the embedded limb value.
    let expected_half = QM31 {
        c0: CM31::new(M31(1 << 30), M31(0)),
        c1: CM31::new(M31(0), M31(0)),
    };
    assert_eq!(half, expected_half);
    assert_eq!((1u64 << 30) * 2 % u64::from(P), 1);

    let mut state = 0x0f01_dfe0_0000_0003u64;
    let alpha = next_nonzero_qm31(&mut state);
    let alpha2 = alpha.square();
    let alpha3 = alpha2.mul(alpha);

    // Basis probes: a single unit weight in slot j of an arity-4 chunk folds
    // to coefficient [1, a^3, a^2, a][j] / 4 under the deployed dual fold.
    let expected_coefficients = [QM31::ONE, alpha3, alpha2, alpha];
    for block in [0usize, 5, 255] {
        for slot in 0..4 {
            let mut values = vec![QM31::ZERO; ROWS];
            values[4 * block + slot] = QM31::ONE;
            let mut accumulator = dense_only_accumulator(values);
            accumulator.fold(alpha);
            assert_eq!(
                accumulator.weight_at(block as u32),
                expected_coefficients[slot].mul(quarter),
                "block {block} slot {slot}"
            );
        }
    }

    // Whole-vector agreement with the independent reference fold.
    let dense: Vec<QM31> = (0..ROWS).map(|_| next_qm31(&mut state)).collect();
    let mut accumulator = dense_only_accumulator(dense.clone());
    accumulator.fold(alpha);
    let reference = reference_fold(&dense, alpha);
    for (index, expected) in reference.iter().enumerate() {
        assert_eq!(
            accumulator.weight_at(index as u32),
            *expected,
            "index {index}"
        );
    }
}

// ---------------------------------------------------------------------------
// 4. Many-input differential correspondence, with intermediate fold states.
// ---------------------------------------------------------------------------

#[test]
fn compact_structured_path_matches_literal_dense_reference_for_many_inputs() {
    for case in 0u64..24 {
        let seed = 0xb10c_ab1e_0000_0100 ^ (case.wrapping_mul(0x9e37_79b9_7f4a_7c15));
        let data = synthetic_relation_account(seed);
        let inputs = relation_inputs(&data);
        let expected = expected_relation_values(&data);

        // Boundary control: without the fourth claim no Component-B covector
        // enters at all.
        assert_eq!(
            probe_sink(V5_CU_PROBE_RELATION3_MODE, &data).unwrap(),
            relation_sink(V5_CU_PROBE_RELATION3_MODE, expected.mode5),
            "case {case}: mode 5 three-claim baseline"
        );
        // Rejected controls: the free-coordinate covector arithmetic.
        assert_eq!(
            probe_sink(V5_CU_PROBE_RELATION4_DENSE_MODE, &data).unwrap(),
            relation_sink(V5_CU_PROBE_RELATION4_DENSE_MODE, expected.mode6),
            "case {case}: mode 6 free-coordinate shared-fold control"
        );
        assert_eq!(
            probe_sink(V5_CU_PROBE_RELATION4_STANDALONE_DOT_MODE, &data).unwrap(),
            relation_sink(V5_CU_PROBE_RELATION4_STANDALONE_DOT_MODE, expected.mode7),
            "case {case}: mode 7 free-coordinate standalone-dot control"
        );
        // Candidate: the STRUCTURED compact path equals the literal dense
        // structured covector carried through the same four folds and the
        // same four final values.
        assert_eq!(
            probe_sink(V5_CU_PROBE_RELATION4_COMPACT_MODE, &data).unwrap(),
            relation_sink(V5_CU_PROBE_RELATION4_COMPACT_MODE, expected.mode8),
            "case {case}: mode 8 structured compact candidate"
        );

        // Mode-lock differentials: swapping the covectors changes the value,
        // so the sink equalities above genuinely distinguish the two layouts.
        assert_ne!(
            expected.mode8, expected.mode8_free_swap,
            "case {case}: structured and free-coordinate layouts must differ"
        );
        assert_ne!(
            probe_sink(V5_CU_PROBE_RELATION4_COMPACT_MODE, &data).unwrap(),
            relation_sink(V5_CU_PROBE_RELATION4_COMPACT_MODE, expected.mode8_free_swap),
            "case {case}: mode 8 does NOT run the free-coordinate control"
        );
        assert_ne!(
            expected.mode6, expected.mode6_structured_swap,
            "case {case}: control and candidate layouts must differ"
        );
        assert_ne!(
            probe_sink(V5_CU_PROBE_RELATION4_DENSE_MODE, &data).unwrap(),
            relation_sink(
                V5_CU_PROBE_RELATION4_DENSE_MODE,
                expected.mode6_structured_swap
            ),
            "case {case}: mode 6 does NOT run the structured candidate"
        );

        // Intermediate states after EACH of the four folds: the literal
        // structured covector, folded by the production accumulator, matches
        // the independent arity-4 reference at every surviving position.
        let (_, _, dense_scale) = base_accumulator_and_value(&inputs, true);
        let structured = literal_structured_covector(&inputs.points[0], dense_scale);
        let mut accumulator = dense_only_accumulator(structured.clone());
        let mut reference = structured;
        for (fold, alpha) in inputs.alphas.iter().enumerate() {
            accumulator.fold(*alpha);
            reference = reference_fold(&reference, *alpha);
            assert_eq!(reference.len(), ROWS >> (2 * (fold + 1)));
            for (index, expected_weight) in reference.iter().enumerate() {
                assert_eq!(
                    accumulator.weight_at(index as u32),
                    *expected_weight,
                    "case {case}: fold {fold} weight {index}"
                );
            }
        }
        // Final-level check: the four folded weights dot the final values to
        // the same additive term used in the expected mode-8 value.
        let final_term = (0..V5_CU_PROBE_RELATION_FINAL_VALUES).fold(QM31::ZERO, |sum, index| {
            sum.add(reference[index].mul(inputs.finals[index]))
        });
        assert_eq!(final_term, accumulator.dot(&inputs.finals), "case {case}");
    }

    // Isolated modes read kappa from scales slot zero only: perturbing the
    // unused slot one leaves the deployed mode-8 sink unchanged.
    let data = synthetic_relation_account(0xb10c_ab1e_0000_0100);
    let baseline = probe_sink(V5_CU_PROBE_RELATION4_COMPACT_MODE, &data).unwrap();
    let mut perturbed = data.clone();
    write_qm31(
        &mut perturbed,
        V5_CU_PROBE_RELATION_SCALES_OFFSET,
        1,
        QM31::ONE,
    );
    assert_eq!(
        probe_sink(V5_CU_PROBE_RELATION4_COMPACT_MODE, &perturbed).unwrap(),
        baseline
    );
}

// ---------------------------------------------------------------------------
// 5. The deployed additive seam folds the Component-B carrier in lockstep.
// ---------------------------------------------------------------------------

struct RecordingInner {
    accumulator: WeightAccumulator,
    alphas_seen: Vec<QM31>,
    snapshots: Vec<Vec<QM31>>,
}

/// Records every fold applied through `V5RelationStressAdditive`, the exact
/// seam `verify_v5_relation_stress_with_additive` uses to carry the private
/// `CompactBTerminalWeights` in the mode-9 composite.  The literal dense
/// structured covector stands in for the compact object here because the
/// compact type is not visible outside its module.
#[derive(Clone)]
struct RecordingAdditive(Rc<RefCell<RecordingInner>>);

impl V5RelationStressAdditive for RecordingAdditive {
    fn fold(&mut self, alpha: QM31) {
        let mut inner = self.0.borrow_mut();
        inner.accumulator.fold(alpha);
        inner.alphas_seen.push(alpha);
        let level = inner.alphas_seen.len();
        let survivors = ROWS >> (2 * level);
        let snapshot = (0..survivors)
            .map(|index| inner.accumulator.weight_at(index as u32))
            .collect();
        inner.snapshots.push(snapshot);
    }

    fn dot(&self, finals: &[QM31; V5_CU_PROBE_RELATION_FINAL_VALUES]) -> QM31 {
        let inner = self.0.borrow();
        (0..V5_CU_PROBE_RELATION_FINAL_VALUES).fold(QM31::ZERO, |sum, index| {
            sum.add(inner.accumulator.weight_at(index as u32).mul(finals[index]))
        })
    }
}

#[test]
fn deployed_additive_seam_applies_exactly_four_ordered_folds() {
    assert_eq!(V5_RELATION_STRESS_ROUNDS, V5_CU_PROBE_RELATION_FOLDS);
    let data = synthetic_relation_account(0x5ea1_ab1e_0000_0005);
    let inputs = relation_inputs(&data);
    let (_, _, dense_scale) = base_accumulator_and_value(&inputs, true);
    let structured = literal_structured_covector(&inputs.points[0], dense_scale);

    let recorder = RecordingAdditive(Rc::new(RefCell::new(RecordingInner {
        accumulator: dense_only_accumulator(structured.clone()),
        alphas_seen: Vec::new(),
        snapshots: Vec::new(),
    })));
    let initial_claim = next_nonzero_qm31(&mut 0x5ea1_ab1e_0000_0006u64.clone());
    let tail = build_v5_relation_stress_tail_for_initial_claim(initial_claim, inputs.alphas);
    verify_v5_relation_stress_with_additive(
        WeightAccumulator::empty(V5_CU_PROBE_RELATION_LOG_ROWS),
        initial_claim,
        inputs.alphas,
        &tail,
        recorder.clone(),
    )
    .expect("the crafted stress tail accepts and drives the additive seam");

    let inner = recorder.0.borrow();
    assert_eq!(
        inner.alphas_seen,
        inputs.alphas.to_vec(),
        "the additive receives exactly the four round challenges in order"
    );
    let mut reference = structured;
    for (fold, alpha) in inputs.alphas.iter().enumerate() {
        reference = reference_fold(&reference, *alpha);
        assert_eq!(
            inner.snapshots[fold], reference,
            "additive state after fold {fold} matches the reference chain"
        );
    }
}

// ---------------------------------------------------------------------------
// 6. The mode lock, observed through every reachable public boundary.
// ---------------------------------------------------------------------------

#[test]
fn mode_lock_mode9_and_tag67_reject_control_fixtures() {
    let mut data = synthetic_relation_account(0x10c4_0000_0000_0009);

    // Mode 9 refuses the isolated-control account outright: the composite
    // candidate path demands the full verified artifact and cannot be
    // entered with a mode-6/7-shaped fixture.
    assert_eq!(
        probe_sink(V5_CU_PROBE_COMPOSITE_MODE, &data),
        Err(ProgramError::InvalidAccountData)
    );
    // The tag-66 mode surface is closed above mode 9.
    for mode in [10u8, 42, 66, 67, 255] {
        assert_eq!(
            probe_sink(mode, &data),
            Err(ProgramError::InvalidInstructionData),
            "mode {mode}"
        );
    }

    // Through the real entrypoint: modes 6/7 (controls) and 8 (candidate)
    // accept exactly the sinks computed from this file's literal references,
    // and mode 9 rejects the same account.
    let expected = expected_relation_values(&data);
    let owner = aspis_verifier::id();
    let key = Pubkey::new_unique();
    let mut lamports = 10_000_000u64;
    let account = make_account(&key, &owner, &mut lamports, &mut data);
    for (mode, value) in [
        (V5_CU_PROBE_RELATION3_MODE, expected.mode5),
        (V5_CU_PROBE_RELATION4_DENSE_MODE, expected.mode6),
        (V5_CU_PROBE_RELATION4_STANDALONE_DOT_MODE, expected.mode7),
        (V5_CU_PROBE_RELATION4_COMPACT_MODE, expected.mode8),
    ] {
        let mut wire = vec![V5_CU_PROBE_TAG, mode];
        wire.extend_from_slice(&relation_sink(mode, value));
        assert_eq!(wire.len(), V5_CU_PROBE_WIRE_BYTES);
        assert_eq!(
            process_v5_cu_probe_instruction(&owner, &[account.clone()], &wire),
            Ok(()),
            "mode {mode} accepts the literal-reference sink"
        );
        wire[2] ^= 1;
        assert_eq!(
            process_v5_cu_probe_instruction(&owner, &[account.clone()], &wire),
            Err(ProgramError::InvalidInstructionData),
            "mode {mode} rejects a corrupted sink"
        );
    }
    // Mode 8 must not accept the free-coordinate swap through the entrypoint.
    let mut swapped_wire = vec![V5_CU_PROBE_TAG, V5_CU_PROBE_RELATION4_COMPACT_MODE];
    swapped_wire.extend_from_slice(&relation_sink(
        V5_CU_PROBE_RELATION4_COMPACT_MODE,
        expected.mode8_free_swap,
    ));
    assert_eq!(
        process_v5_cu_probe_instruction(&owner, &[account.clone()], &swapped_wire),
        Err(ProgramError::InvalidInstructionData)
    );
    // Mode 9 through the entrypoint on the control fixture: rejected.
    let mut composite_wire = vec![V5_CU_PROBE_TAG, V5_CU_PROBE_COMPOSITE_MODE];
    composite_wire.extend_from_slice(&[0u8; 32]);
    assert_eq!(
        process_v5_cu_probe_instruction(&owner, &[account.clone()], &composite_wire),
        Err(ProgramError::InvalidAccountData)
    );
}

#[test]
fn tag67_wire_carries_no_mode_selector_and_seam_demands_the_composite() {
    // The tag-67 wire is exactly tag + the atomic public tuple.  There is no
    // mode byte, so no wire form of tag 67 can select probe modes 6 or 7.
    assert_eq!(V5_FULL_CU_TRANSACTION_WIRE_BYTES, 1 + 4 * 32 + 2 * 4 + 32);
    let mut wire = Vec::with_capacity(V5_FULL_CU_TRANSACTION_WIRE_BYTES);
    wire.push(V5_FULL_CU_TRANSACTION_TAG);
    wire.extend_from_slice(&[1u8; 32]);
    wire.extend_from_slice(&[2u8; 32]);
    wire.extend_from_slice(&[3u8; 32]);
    wire.extend_from_slice(&[4u8; 32]);
    wire.extend_from_slice(&17u32.to_le_bytes());
    wire.extend_from_slice(&1u32.to_le_bytes());
    wire.extend_from_slice(&[5u8; 32]);
    assert_eq!(wire.len(), V5_FULL_CU_TRANSACTION_WIRE_BYTES);
    let public = parse_v5_full_cu_public_inputs(&wire).unwrap();
    assert_eq!(public.asset_id, 17);
    // The probe tag (66) is not a valid tag-67 wire, and any extra byte —
    // the only place a mode selector could hide — is rejected.
    let mut probe_tagged = wire.clone();
    probe_tagged[0] = V5_CU_PROBE_TAG;
    assert_eq!(
        parse_v5_full_cu_public_inputs(&probe_tagged),
        Err(ProgramError::InvalidInstructionData)
    );
    let mut extended = wire.clone();
    extended.push(V5_CU_PROBE_RELATION4_DENSE_MODE);
    assert_eq!(
        parse_v5_full_cu_public_inputs(&extended),
        Err(ProgramError::InvalidInstructionData)
    );

    // The verifier callback bound to tag 67 accepts only the full mode-9
    // composite artifact.  Every reachable negative gate is exercised:
    let statement = tiny_statement();
    let digest = atomic_payment_statement_digest_v4(&statement, host_hashv)
        .expect("canonical tiny statement digests");
    let owner = aspis_verifier::id();
    let key = Pubkey::new_unique();

    // (a) statement-digest mismatch fails closed before account access;
    let probe_bytes = synthetic_relation_account(0x10c4_0000_0000_000a);
    let mut sealed = sealed_proof_account_bytes(&probe_bytes);
    let mut lamports = 10_000_000u64;
    let account = make_account(&key, &owner, &mut lamports, &mut sealed);
    assert_eq!(
        verify_uploaded_v5_mode9_cu_fixture(&account, &statement, &[0u8; 32]),
        Err(ProgramError::InvalidAccountData)
    );
    // (b) an unsealed proof account (nonzero upload authority) is rejected;
    let mut unsealed = sealed_proof_account_bytes(&probe_bytes);
    unsealed[8] = 1;
    let mut lamports_unsealed = 10_000_000u64;
    let unsealed_account = make_account(&key, &owner, &mut lamports_unsealed, &mut unsealed);
    assert_eq!(
        verify_uploaded_v5_mode9_cu_fixture(&unsealed_account, &statement, &digest),
        Err(ProgramError::InvalidAccountData)
    );
    // (c) a SEALED account whose body is the mode-6/7-capable control fixture
    // still fails: the tag-67 seam parses only the composite artifact, so
    // the rejected-control format cannot enter the candidate path.
    let mut sealed_again = sealed_proof_account_bytes(&probe_bytes);
    let mut lamports_sealed = 10_000_000u64;
    let sealed_account = make_account(&key, &owner, &mut lamports_sealed, &mut sealed_again);
    assert_eq!(
        verify_uploaded_v5_mode9_cu_fixture(&sealed_account, &statement, &digest),
        Err(ProgramError::InvalidAccountData)
    );
}

// ---------------------------------------------------------------------------
// 7. Source tripwire: the dispatch spelling of the lock, pinned.
// ---------------------------------------------------------------------------

/// Baked at compile time from the deployed source.  These are textual pins
/// of the lock as spelled today; if the dispatch is reshaped this test asks
/// to be re-audited rather than silently keeping stale expectations.
const DEPLOYED_SOURCE: &str = include_str!("../src/v5_cu_probe.rs");

fn try_top_level_item<'a>(source: &'a str, name: &str) -> Option<&'a str> {
    let patterns = [format!("\nfn {name}("), format!("\npub fn {name}(")];
    let start = patterns
        .iter()
        .find_map(|pattern| source.find(pattern.as_str()))?;
    let body = &source[start..];
    let end = body
        .find("\n}")
        .unwrap_or_else(|| panic!("`{name}` closes at column zero"));
    Some(&body[..end + 2])
}

fn top_level_item<'a>(source: &'a str, name: &str) -> &'a str {
    try_top_level_item(source, name).unwrap_or_else(|| panic!("deployed source defines `{name}`"))
}

#[test]
fn dispatch_source_pins_the_mode_lock_spelling() {
    // The free-coordinate control is guarded to modes 6 and 7 only, and
    // fails closed with InvalidInstructionData for every other mode.
    let derive = top_level_item(DEPLOYED_SOURCE, "derive_v5_b_terminal_covector");
    assert!(derive
        .contains("V5_CU_PROBE_RELATION4_DENSE_MODE | V5_CU_PROBE_RELATION4_STANDALONE_DOT_MODE"));
    assert!(derive.contains("InvalidInstructionData"));
    assert!(!derive.contains("V5_CU_PROBE_RELATION4_COMPACT_MODE"));
    assert!(!derive.contains("V5_CU_PROBE_COMPOSITE_MODE"));

    // Mode 9 is not a relation-variant mode: it cannot reach the mode->
    // variant dispatch that hands modes 6/7 the free-coordinate covector.
    let variant = top_level_item(DEPLOYED_SOURCE, "relation_variant");
    assert!(variant.contains(
        "V5_CU_PROBE_RELATION4_COMPACT_MODE => Some(RelationVariant::FourClaimsCompact)"
    ));
    assert!(variant.contains("_ => None"));
    assert!(!variant.contains("V5_CU_PROBE_COMPOSITE_MODE"));

    // The isolated dispatch pairs SharedFold/StandaloneDot with the derive
    // control and FourClaimsCompact with the compact evaluator.
    let prepare = top_level_item(DEPLOYED_SOURCE, "prepare_relation");
    assert!(prepare.contains("derive_v5_b_terminal_covector(mode"));
    assert!(prepare.contains("CompactBTerminalWeights::new"));
    assert!(prepare.contains(
        "RelationVariant::FourClaimsSharedFold | RelationVariant::FourClaimsStandaloneDot"
    ));

    // The composite (mode 9) verifier builds Component B exclusively through
    // the structured compact evaluator; the control derive never appears in
    // its call graph.  The relation phase may live in the composite function
    // itself or in the extracted `verify_mode9_relation_phase` helper.
    let composite = top_level_item(
        DEPLOYED_SOURCE,
        "verify_mode9_composite_with_live_statement",
    );
    let relation_phase = try_top_level_item(DEPLOYED_SOURCE, "verify_mode9_relation_phase");
    let mut composite_graph = String::from(composite);
    if let Some(phase) = relation_phase {
        assert!(
            composite.contains("verify_mode9_relation_phase("),
            "the composite delegates its relation phase to the extracted helper"
        );
        composite_graph.push_str(phase);
    }
    assert!(composite_graph.contains("RelationVariant::FourClaimsCompact"));
    assert!(composite_graph.contains("CompactBTerminalWeights::new"));
    assert!(!composite_graph.contains("derive_v5_b_terminal_covector"));

    let sink = top_level_item(DEPLOYED_SOURCE, "probe_sink");
    assert!(sink.contains("RelationVariant::FourClaimsCompact"));
    assert!(!sink.contains("derive_v5_b_terminal_covector"));

    // Tag 67 routes to the mode-9 composite verifier callback and nothing
    // else; the tag-66 entrypoint carries the routing.
    let entry = top_level_item(DEPLOYED_SOURCE, "process_v5_cu_probe_instruction");
    assert!(entry.contains("V5_FULL_CU_TRANSACTION_TAG"));
    assert!(entry.contains("verify_uploaded_v5_mode9_cu_fixture"));
    let fixture = top_level_item(DEPLOYED_SOURCE, "verify_uploaded_v5_mode9_cu_fixture");
    assert!(fixture.contains("exact_uploaded_v5_proof_body"));
    assert!(fixture.contains("verify_mode9_composite_with_live_statement"));
    let exact_body = top_level_item(DEPLOYED_SOURCE, "exact_uploaded_v5_proof_body");
    assert!(exact_body.contains("proof_account_finalized"));
    assert!(exact_body.contains("uploaded_proof_bounds"));
    assert!(exact_body.contains("proof_end != data.len()"));
}

// ---------------------------------------------------------------------------
// 8. Known-answer test: fixed inputs, intermediate states, pinned outputs.
// ---------------------------------------------------------------------------

const KAT_SEED: u64 = 0xa5b1_5b10_c4e0_0001;

// Pinned outputs for KAT_SEED, produced by the deployed evaluators and the
// literal references on first run and fixed here as known answers.
const KAT_DENSE_SCALE: [u32; 4] = [1661265894, 1258603996, 1552850070, 867151188];
const KAT_COVECTOR_ROW0: [u32; 4] = [2041676403, 1998946914, 632178510, 1427757014];
const KAT_COVECTOR_ROW_BLOCK6_LAST: [u32; 4] = [913299059, 1599146598, 33891394, 1568183202];
const KAT_COVECTOR_ROW_BLOCK28_FIRST: [u32; 4] = [1489058297, 314650999, 1461954341, 216787797];
const KAT_COVECTOR_ROW992: [u32; 4] = [2094580025, 999473457, 316089255, 713878507];
const KAT_FOLD_STATE_FIRST: [[u32; 4]; 4] = [
    [137886094, 687956445, 912486716, 2141096134],
    [161643384, 1980248812, 171376783, 23604127],
    [22966457, 1116381522, 100193223, 490362618],
    [1733672410, 1372632675, 1728201462, 400088887],
];
const KAT_FOLD_STATE_DIGESTS: [&str; 4] = [
    "ec3a63f69318394aaea865a0a601727b5dabe0ab5709636ad0b58a657bc0a7e5",
    "0bae3a1c7049bab18710d3c911d6c224490357ce6477d75108385a03d339eb23",
    "a3e592a5fb5f3d4d7e912827dce4822bde108f6e093fa43e9db7bc839e186feb",
    "359f5a5847f9d9e8f9f16746abb2444ee9df9d38cc314c8c207f4b4a904cb42a",
];
const KAT_STRUCTURED_TERM: [u32; 4] = [1298315799, 921259680, 1803368172, 693061067];
const KAT_MODE8_VALUE: [u32; 4] = [752719635, 1675071993, 983133, 544887339];
const KAT_SINK_MODE6: &str = "712f453a8d5cbfd6cfe438f157a99990a55ca34b0673d0379b0dfc097e412bb0";
const KAT_SINK_MODE7: &str = "3b50b08a79374e1c5e61ca627123a74bf6a29c8e6d18ce58e34ea8455a50b7d9";
const KAT_SINK_MODE8: &str = "4f9bbc51bf35280b6ce1a106196dda45b5a0981134e791970696bcc759c88e07";
const KAT_COMPACT_STATE_BYTES: usize = 540;

#[test]
fn kat_structured_compact_correspondence_with_pinned_vectors() {
    let data = synthetic_relation_account(KAT_SEED);
    let inputs = relation_inputs(&data);
    let expected = expected_relation_values(&data);

    let (_, _, dense_scale) = base_accumulator_and_value(&inputs, true);
    let structured = literal_structured_covector(&inputs.points[0], dense_scale);

    // Intermediate states after each of the four folds, digested over the
    // full level and pinned with the leading weight for diagnosis.
    let mut fold_first = Vec::new();
    let mut fold_digests = Vec::new();
    let mut reference = structured.clone();
    for alpha in inputs.alphas {
        reference = reference_fold(&reference, alpha);
        fold_first.push(limbs(reference[0]));
        let mut material = Vec::with_capacity(reference.len() * QM31_BYTES);
        for value in &reference {
            let mut bytes = [0u8; QM31_BYTES];
            value.write_le_bytes(&mut bytes);
            material.extend_from_slice(&bytes);
        }
        fold_digests.push(hex32(&hashv(&[b"kat-fold-state", &material]).to_bytes()));
    }
    let structured_term = (0..V5_CU_PROBE_RELATION_FINAL_VALUES).fold(QM31::ZERO, |sum, index| {
        sum.add(reference[index].mul(inputs.finals[index]))
    });

    let sink6 = probe_sink(V5_CU_PROBE_RELATION4_DENSE_MODE, &data).unwrap();
    let sink7 = probe_sink(V5_CU_PROBE_RELATION4_STANDALONE_DOT_MODE, &data).unwrap();
    let sink8 = probe_sink(V5_CU_PROBE_RELATION4_COMPACT_MODE, &data).unwrap();

    eprintln!("KAT dense_scale        = {:?}", limbs(dense_scale));
    eprintln!("KAT covector[0]        = {:?}", limbs(structured[0]));
    eprintln!(
        "KAT covector[6*32+27]  = {:?}",
        limbs(structured[6 * V5_CU_PROBE_B_BLOCK_ROWS + 27])
    );
    eprintln!(
        "KAT covector[28*32]    = {:?}",
        limbs(structured[28 * V5_CU_PROBE_B_BLOCK_ROWS])
    );
    eprintln!("KAT covector[992]      = {:?}", limbs(structured[992]));
    eprintln!("KAT fold_first         = {fold_first:?}");
    eprintln!("KAT fold_digests       = {fold_digests:?}");
    eprintln!("KAT structured_term    = {:?}", limbs(structured_term));
    eprintln!("KAT mode8_value        = {:?}", limbs(expected.mode8));
    eprintln!("KAT sink6              = {}", hex32(&sink6));
    eprintln!("KAT sink7              = {}", hex32(&sink7));
    eprintln!("KAT sink8              = {}", hex32(&sink8));
    eprintln!("KAT compact_state_bytes= {V5_CU_PROBE_B_COMPACT_STATE_BYTES}");

    assert_eq!(limbs(dense_scale), KAT_DENSE_SCALE);
    assert_eq!(limbs(structured[0]), KAT_COVECTOR_ROW0);
    assert_eq!(
        limbs(structured[6 * V5_CU_PROBE_B_BLOCK_ROWS + 27]),
        KAT_COVECTOR_ROW_BLOCK6_LAST
    );
    assert_eq!(
        limbs(structured[28 * V5_CU_PROBE_B_BLOCK_ROWS]),
        KAT_COVECTOR_ROW_BLOCK28_FIRST
    );
    assert_eq!(limbs(structured[992]), KAT_COVECTOR_ROW992);
    assert_eq!(structured[993], QM31::ZERO);
    for (fold, first) in fold_first.iter().enumerate() {
        assert_eq!(
            *first, KAT_FOLD_STATE_FIRST[fold],
            "fold {fold} first weight"
        );
        assert_eq!(
            fold_digests[fold], KAT_FOLD_STATE_DIGESTS[fold],
            "fold {fold} digest"
        );
    }
    assert_eq!(limbs(structured_term), KAT_STRUCTURED_TERM);
    assert_eq!(limbs(expected.mode8), KAT_MODE8_VALUE);
    assert_eq!(hex32(&sink6), KAT_SINK_MODE6);
    assert_eq!(hex32(&sink7), KAT_SINK_MODE7);
    assert_eq!(hex32(&sink8), KAT_SINK_MODE8);
    assert_eq!(V5_CU_PROBE_B_COMPACT_STATE_BYTES, KAT_COMPACT_STATE_BYTES);

    // The pinned sinks re-derive from the literal expected values.
    assert_eq!(
        sink6,
        relation_sink(V5_CU_PROBE_RELATION4_DENSE_MODE, expected.mode6)
    );
    assert_eq!(
        sink7,
        relation_sink(V5_CU_PROBE_RELATION4_STANDALONE_DOT_MODE, expected.mode7)
    );
    assert_eq!(
        sink8,
        relation_sink(V5_CU_PROBE_RELATION4_COMPACT_MODE, expected.mode8)
    );
}
