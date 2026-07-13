//! Privacy-only executable guards for the atomic profile-21 candidate.
//!
//! These tests deliberately do not turn a passing affine-rank probe into an
//! HVZK claim.  The current profile-21 proof has five salted private Merkle
//! trees, but its affine masks are still expanded from 256-bit seeds and the
//! protocol-specific EPRO simulation remains a separate proof obligation.

use aspis_core::circle_line_merkle::derive_circle_line_query_indices_for_count;
use aspis_core::field::{CM31, M31, QM31};
use aspis_core::state_only_hiding::{
    begin_state_only_hiding_precommit, state_only_mask_tower_basis, StateOnlyHidingContext,
};
use aspis_core::state_only_prefix::{
    run_atomic_state_only_profile21_transcript_schedule_host_unmined_for_diagnostics_v3,
    StateOnlyProfile21Prefix, STATE_ONLY_PROFILE21_PREFIX_LEN, STATE_ONLY_RATE512_SHAPE,
};
use aspis_core::state_only_profile21_openings::PROFILE21_PRIVATE_VALUE_WIDTHS;
use aspis_core::transcript::{label, Transcript};
use aspis_prover::state_only_candidate_prefix::{state_only_header, StateOnlyPowMode};
use aspis_prover::state_only_entropy::StateOnlyAttemptSecrets;
use aspis_prover::state_only_hiding::{
    derive_state_only_mask_seed, InMemoryStateOnlyMaskNonceStore,
};
use aspis_prover::state_only_hiding_rank::{
    probe_atomic_state_only_full_shared_hiding_rank,
    probe_atomic_state_only_native_full_root_x_joint_rank,
    probe_atomic_state_only_native_full_root_x_raw_only_control_rank,
    probe_atomic_state_only_profile21_g2_mask_rank,
    probe_atomic_state_only_profile21_masked_single_switch_joint_rank,
    probe_atomic_state_only_profile21_semantic_natural18_shared_c2_switch_joint_rank,
    probe_atomic_state_only_profile21_witness_difference_containment,
    probe_atomic_state_only_profile22_minimal_containment, profile21_good_schedule_degree_budget,
    StateOnlyHidingRankGateError, TailQm31MaskFactor,
};
use aspis_prover::state_only_profile21::build_hiding_atomic_state_only_profile21_proof_v3;
use aspis_prover::HOST_HASH;
use aspis_statement::atomic_state_only_trace::atomic_merkle_root_v3;
use aspis_statement::state_only_profile21::verify_atomic_state_only_profile21_unmined_for_diagnostics_v3;
use aspis_statement::{
    atomic_payment_statement_digest_v3, derive_nullifier, derive_owner_key, note_commitment,
    output_commitment, AtomicPaymentStatementV3, Digest, MerklePath, SpendPublic, SpendWitness,
};
use std::sync::atomic::{AtomicUsize, Ordering};

const ACTUAL_PROFILE21_PROOF: &[u8] = include_bytes!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../results/stage2/proofs/atomic_state_only_profile21_v3_unmined.bin"
));

static COUNTED_SQUEEZE_INPUTS: AtomicUsize = AtomicUsize::new(0);
static COUNTED_GRIND_INPUTS: AtomicUsize = AtomicUsize::new(0);
static COUNTED_ABSORB_INPUTS: AtomicUsize = AtomicUsize::new(0);
static COUNTED_ADVANCE_INPUTS: AtomicUsize = AtomicUsize::new(0);

fn counting_host_hash(inputs: &[&[u8]]) -> [u8; 32] {
    if inputs.len() >= 2 {
        match inputs[1].first().copied() {
            Some(0x00) => {
                COUNTED_ABSORB_INPUTS.fetch_add(1, Ordering::Relaxed);
            }
            Some(0x01) => {
                COUNTED_SQUEEZE_INPUTS.fetch_add(1, Ordering::Relaxed);
            }
            Some(0x02) => {
                COUNTED_ADVANCE_INPUTS.fetch_add(1, Ordering::Relaxed);
            }
            Some(0x03) => {
                COUNTED_GRIND_INPUTS.fetch_add(1, Ordering::Relaxed);
            }
            _ => {}
        }
    }
    HOST_HASH(inputs)
}

fn digest(seed: u32) -> Digest {
    core::array::from_fn(|index| M31(seed + 17 * index as u32))
}

fn fixture() -> (AtomicPaymentStatementV3, SpendWitness) {
    let nullifier_key = digest(101);
    let input_salt = digest(301);
    let output_salt = digest(501);
    let output_owner_key = digest(701);
    let asset_id = M31(17);
    let value = 1_000_000;
    let value_out = 999_999;
    let merkle_path = MerklePath {
        siblings: (0..20).map(|level| digest(1_000 + 31 * level)).collect(),
        index: 0x5_a5a5,
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
    let statement = AtomicPaymentStatementV3 {
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
    };
    (statement, witness)
}

fn actual_profile21_schedule(
) -> aspis_core::state_only_prefix::StateOnlyProfile21TranscriptScheduleResult {
    let (statement, _) = fixture();
    let statement_digest = atomic_payment_statement_digest_v3(&statement, HOST_HASH).unwrap();
    let (prefix, _) = StateOnlyProfile21Prefix::parse_from_proof(ACTUAL_PROFILE21_PROOF).unwrap();
    run_atomic_state_only_profile21_transcript_schedule_host_unmined_for_diagnostics_v3(
        HOST_HASH,
        &prefix,
        &statement_digest,
    )
    .unwrap()
}

fn actual_schedule() -> aspis_core::state_only_prefix::StateOnlyTranscriptScheduleResult {
    actual_profile21_schedule().base
}

#[test]
fn actual_profile21_fixture_is_exact_and_all_five_opening_sections_are_salted() {
    const EXPECTED_SHA256: [u8; 32] = [
        0xa8, 0x1b, 0xc7, 0xe2, 0xa8, 0x9b, 0x37, 0xa7, 0x99, 0x21, 0x73, 0x14, 0xfd, 0x7b, 0x50,
        0xd6, 0xca, 0x05, 0xd6, 0x65, 0xd4, 0xf6, 0xbc, 0xf0, 0x37, 0x54, 0x36, 0xd2, 0xe7, 0x9f,
        0xa2, 0xc2,
    ];
    assert_eq!(ACTUAL_PROFILE21_PROOF.len(), 62_214);
    assert_eq!(HOST_HASH(&[ACTUAL_PROFILE21_PROOF]), EXPECTED_SHA256);
    assert_eq!(STATE_ONLY_PROFILE21_PREFIX_LEN, 7_336);

    // The complete host verifier has deliberately large fixed arrays. Give
    // this integration guard an explicit stack instead of relying on the
    // test harness's platform-dependent worker-stack default.
    std::thread::Builder::new()
        .name("profile21-salted-wire-guard".into())
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let (statement, _) = fixture();
            let verified = verify_atomic_state_only_profile21_unmined_for_diagnostics_v3(
                ACTUAL_PROFILE21_PROOF,
                &statement,
                HOST_HASH,
                None,
            )
            .unwrap();
            let sections = [
                &verified.openings.c1,
                &verified.openings.c2,
                &verified.openings.later[0],
                &verified.openings.later[1],
                &verified.openings.later[2],
            ];
            for (section, expected_width) in
                sections.into_iter().zip(PROFILE21_PRIVATE_VALUE_WIDTHS)
            {
                assert_eq!(section.count, 16);
                assert_eq!(section.value_width, expected_width);
                assert_eq!(section.record_width(), expected_width + 32);
                for ordinal in 0..section.count {
                    assert_eq!(section.value(ordinal).unwrap().len(), expected_width);
                    assert_eq!(section.salt(ordinal).unwrap().len(), 32);
                }
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn production_mask_distribution_has_at_most_a_256_bit_seed_support() {
    // This pins the actual API/source distribution.  The affine rank proof
    // treats 22,820 M31 mask directions as independent, but the implemented
    // distribution expands one 32-byte seed.  It can support a computational
    // ROM/PRG argument; it cannot be substituted for uniform coins in a
    // statistical-HVZK translation proof.
    const PRIVATE_ENTROPY_BITS: usize = 32 * 8;
    const AFFINE_MASK_DIRECTIONS_M31: usize = 22_820;
    const AFFINE_MASK_SPACE_BITS_LOWER_BOUND: usize = AFFINE_MASK_DIRECTIONS_M31 * 30;
    assert_eq!(PRIVATE_ENTROPY_BITS, 256);
    assert!(AFFINE_MASK_SPACE_BITS_LOWER_BOUND > PRIVATE_ENTROPY_BITS);

    let (statement, _) = fixture();
    let statement_digest = atomic_payment_statement_digest_v3(&statement, HOST_HASH).unwrap();
    let context = StateOnlyHidingContext::atomic_v3(statement_digest, [0x91; 32]);
    let mut header = [0u8; aspis_core::proof::HEADER_LEN];
    state_only_header(STATE_ONLY_RATE512_SHAPE).write(&mut header);
    let mut transcript = Transcript::new(HOST_HASH);
    transcript.absorb(label::PROFILE, &header);
    transcript.absorb(
        label::M31_CIRCLE_BASIS,
        aspis_core::proof::M31_CIRCLE_BASIS_DISCRIMINATOR,
    );
    transcript.absorb(label::STATEMENT, &statement_digest);
    let binding = begin_state_only_hiding_precommit(&mut transcript, context).unwrap();
    let seed = derive_state_only_mask_seed(HOST_HASH, binding, context, [0xa1; 32]).unwrap();
    assert_eq!(seed.len() * 8, PRIVATE_ENTROPY_BITS);
}

#[test]
fn actual_profile21_opened_leaf_counts_pin_private_salt_wire_delta() {
    let schedule = actual_schedule();
    let indices = derive_circle_line_query_indices_for_count(
        &schedule.queries[..schedule.query_count],
        1usize << 17,
    )
    .unwrap();
    let counts = [
        indices.layer0.len(), // C1
        indices.layer0.len(), // C2, including shared X/F lanes
        indices.later[0].len(),
        indices.later[1].len(),
        indices.later[2].len(),
    ];
    // Shared X/F lanes occupy the already-opened C2 leaf and therefore do
    // not receive a second salt.  The selected direct-U binding has no U
    // tree.  This exact transcript has no q>>{2,4,6} collisions, so five
    // committed trees expose 80 salts: 2,560 additional proof bytes.
    assert_eq!(counts, [16, 16, 16, 16, 16]);
    assert_eq!(32 * counts.iter().sum::<usize>(), 2_560);
}

#[test]
fn transcript_programming_input_count_uses_bounded_sampler_cap_not_nominal_rounds() {
    // Count byte-exact RO squeeze/grind inputs on the integrated beta-free
    // profile-21 schedule. For the theorem we book the *bounded sampler*
    // maximum rather than the much smaller nominal/no-rejection count:
    //
    //   base QM31 calls <= 65, each <= 4 squeeze blocks;
    //   q16 sampler <= 64 words = 8 squeeze blocks;
    //   beta-free profile-21 delta sampling <= 3 QM31 calls.
    //
    // Hence 280 squeeze inputs suffice for the selected schedule.  A round
    // number such as 40 is not a valid programming-input cap.
    COUNTED_SQUEEZE_INPUTS.store(0, Ordering::Relaxed);
    COUNTED_GRIND_INPUTS.store(0, Ordering::Relaxed);
    COUNTED_ABSORB_INPUTS.store(0, Ordering::Relaxed);
    COUNTED_ADVANCE_INPUTS.store(0, Ordering::Relaxed);
    let (statement, _) = fixture();
    let statement_digest = atomic_payment_statement_digest_v3(&statement, HOST_HASH).unwrap();
    let (prefix, _) = StateOnlyProfile21Prefix::parse_from_proof(ACTUAL_PROFILE21_PROOF).unwrap();
    run_atomic_state_only_profile21_transcript_schedule_host_unmined_for_diagnostics_v3(
        counting_host_hash,
        &prefix,
        &statement_digest,
    )
    .unwrap();
    let actual_profile21_squeezes = COUNTED_SQUEEZE_INPUTS.load(Ordering::Relaxed);
    let actual_profile21_grinds = COUNTED_GRIND_INPUTS.load(Ordering::Relaxed);
    let actual_profile21_absorbs = COUNTED_ABSORB_INPUTS.load(Ordering::Relaxed);
    let actual_profile21_advances = COUNTED_ADVANCE_INPUTS.load(Ordering::Relaxed);
    assert_eq!(actual_profile21_absorbs, 46);
    assert_eq!(actual_profile21_squeezes, 51);
    assert_eq!(actual_profile21_grinds, 7);
    eprintln!(
        "literal profile21 transcript hash inputs: absorb={actual_profile21_absorbs} squeeze={actual_profile21_squeezes} advance={actual_profile21_advances} grind={actual_profile21_grinds}"
    );
    assert_eq!(actual_profile21_advances, actual_profile21_squeezes);

    // The selected direct-q source splice adds one source-work record, no
    // beta record, and at most three delta field calls.  The literal schedule
    // therefore has batch + four folds + source + final = seven work checks.
    const PROFILE21_WORK_RECORDS: usize = 1 + 4 + 1 + 1;
    assert_eq!(PROFILE21_WORK_RECORDS, 7);
    const PROFILE21_MAX_PROGRAMMED_SQUEEZE_INPUTS: usize = 280;
    assert!(actual_profile21_squeezes <= PROFILE21_MAX_PROGRAMMED_SQUEEZE_INPUTS);
}

#[test]
fn conditional_good_schedule_degree_and_retry_budget_is_pinned_but_not_overclaimed() {
    let budget = profile21_good_schedule_degree_budget();
    assert_eq!(budget.combined_minor_rows, 4_312);
    assert_eq!(budget.circle_tensor_denominator_exponent, 512);
    assert_eq!(
        budget.circle_parameter_norm_denominator_degree_per_sample,
        4_096
    );
    assert_eq!(budget.cleared_two_circle_denominator_degree, 8_192);
    assert_eq!(budget.target_entry_numerator_degree, 8_207);
    assert_eq!(budget.pcs_entry_numerator_degree, 8_490);
    assert_eq!(budget.raw_block_determinant_degree, 3_240);
    assert_eq!(budget.masked_sumcheck_determinant_degree, 37_800);
    assert_eq!(budget.baseline_pcs_determinant_degree, 6_044_880);
    assert_eq!(budget.switch_observation_determinant_degree, 32_968);
    assert_eq!(budget.switch_complement_determinant_degree, 577_320);
    assert_eq!(budget.combined_determinant_degree, 6_696_208);
    let per_attempt =
        budget.combined_determinant_degree as f64 / budget.m31_schwartz_zippel_denominator as f64;
    let bits_per_attempt = -per_attempt.log2();
    assert!((bits_per_attempt - 8.325_087_087_912_081).abs() < 1e-12);
    assert_eq!(budget.retry_cap_for_100_bit_completeness, 13);
    assert!(bits_per_attempt * budget.retry_cap_for_100_bit_completeness as f64 >= 100.0);
    assert_eq!(budget.retry_cap_for_128_bit_completeness, 16);
    assert!(bits_per_attempt * budget.retry_cap_for_128_bit_completeness as f64 >= 128.0);
    // Numeric nonzeroness is pinned only at the frozen tuple.  Until the
    // residual determinant is shown nonzero as a field polynomial for every
    // accepted discrete q tuple, neither retry cap is a theorem-backed
    // production availability claim.
    assert!(!budget.every_q_nonzero_polynomial_proved);
}

#[test]
fn conditional_epro_and_canonical_pow_error_ledger_is_pinned_but_not_system_privacy() {
    const LOGICAL_LEAVES: u128 = 305_152;
    const BOUNDED_FIELD_AND_SOURCE_EXPANDER_INPUTS: u128 = 46_260;
    const SEED_AND_BINDING_INPUTS: u128 = 8;
    const TRANSCRIPT_INPUTS: u128 = 46 + 280 + 280 + 7;
    const INPUTS_PER_ATTEMPT: u128 = 3 * LOGICAL_LEAVES
        + BOUNDED_FIELD_AND_SOURCE_EXPANDER_INPUTS
        + SEED_AND_BINDING_INPUTS
        + TRANSCRIPT_INPUTS;
    const ATTEMPTS: u128 = 16;

    // Three forest-sized terms conservatively cover salted-leaf preimages,
    // salt derivations and hidden internal nodes. The transcript count uses
    // the bounded 280 squeeze/advance cap, not the literal no-rejection 51.
    assert_eq!(TRANSCRIPT_INPUTS, 613);
    assert_eq!(INPUTS_PER_ATTEMPT, 962_337);
    assert!(INPUTS_PER_ATTEMPT < (1u128 << 24));

    let programmed_inputs = (ATTEMPTS * INPUTS_PER_ATTEMPT) as f64;
    let leading_bits_at_qh_128 = 256.0 - programmed_inputs.log2() - 128.0;
    assert!((leading_bits_at_qh_128 - 104.123_817_326_900_6).abs() < 1e-12);

    let internal_collision_pairs =
        (ATTEMPTS * INPUTS_PER_ATTEMPT * (ATTEMPTS * INPUTS_PER_ATTEMPT - 1) / 2) as f64;
    let internal_collision_bits = 256.0 - internal_collision_pairs.log2();
    assert!(internal_collision_bits > 209.247_634_747_498_5);

    let pow_exhaustion_bits =
        2f64.powi(25) / core::f64::consts::LN_2 - (7.0 * ATTEMPTS as f64).log2();
    assert!(pow_exhaustion_bits > 48_408_805.0);

    // These numbers close only the conditional no-prequery/PoW component.
    // The all-q affine predicate, post-seam rank, standard-model PRG terms
    // and fixed-release retry manager remain separate red gates.
    assert!(!profile21_good_schedule_degree_budget().every_q_nonzero_polynomial_proved);
}

#[test]
fn atomic_relation_free_rows_have_an_explicit_query_rank_reserve_per_column() {
    let cells =
        aspis_statement::atomic_state_only_registry::atomic_state_only_relation_free_mask_cells_v3(
        )
        .unwrap();
    let active =
        aspis_statement::atomic_state_only_terminal::atomic_state_only_copy_active_rows_v3()
            .iter()
            .copied()
            .collect::<std::collections::BTreeSet<_>>();
    let mut counts = [[0usize; 2]; 16];
    let mut last_inactive = [None; 16];
    let mut rows_by_column: [Vec<u16>; 16] = core::array::from_fn(|_| Vec::new());
    for cell in &cells {
        let column = usize::from(cell.column);
        let is_active = active.contains(&cell.row);
        counts[column][usize::from(!is_active)] += 1;
        rows_by_column[column].push(cell.row);
        if !is_active {
            last_inactive[column] = Some(cell.row);
        }
    }
    let longest_runs: [(u16, u16); 16] = core::array::from_fn(|column| {
        let rows = &rows_by_column[column];
        let mut best = (rows[0], rows[0]);
        let mut start = rows[0];
        let mut previous = rows[0];
        for &row in &rows[1..] {
            if row != previous + 1 {
                if previous - start > best.1 - best.0 {
                    best = (start, previous);
                }
                start = row;
            }
            previous = row;
        }
        if previous - start > best.1 - best.0 {
            best = (start, previous);
        }
        best
    });
    eprintln!("atomic relation-free active/inactive counts: {counts:?}");
    eprintln!("atomic semantic dependent rows: {last_inactive:?}");
    eprintln!("atomic semantic longest consecutive runs: {longest_runs:?}");
    assert_eq!(counts.iter().flatten().sum::<usize>(), 5_262);
    assert!(counts.iter().all(|count| count[0] + count[1] >= 65));
    assert!(last_inactive.iter().all(Option::is_some));

    // Rows 896..=1023 are a common, all-inactive, relation-free natural-basis
    // block in every semantic column.  Row 1023 is the balancing coordinate,
    // leaving 127 explicit source directions e_r-e_1023.  This shape is the
    // structural q-universality reserve used by the privacy note.
    for column_rows in &rows_by_column {
        for row in 896..=1023 {
            assert!(column_rows.binary_search(&row).is_ok());
            assert!(!active.contains(&row));
        }
    }
}

fn circle_basis_value(row: usize, point: aspis_core::circle_fri::BaseCirclePoint) -> M31 {
    let mut value = M31::ONE;
    let mut factor = point.y;
    for bit in 0..10 {
        if row & (1 << bit) != 0 {
            value = value.mul(factor);
        }
        factor = if bit == 0 {
            point.x
        } else {
            factor.mul(factor).double().sub(M31::ONE)
        };
    }
    value
}

#[test]
fn rate512_fiber_parameters_are_injective_and_common_high_factor_is_nonzero() {
    const DOMAIN_LOG: u32 = 19;
    const FIBERS: usize = 1 << (DOMAIN_LOG - 2);
    let mut t2_coordinates = Vec::with_capacity(FIBERS);
    for fiber in 0..FIBERS {
        let point =
            aspis_core::circle_fri::circle_fiber_point_for_domain_log(DOMAIN_LOG, fiber).unwrap();
        let mut doubled_x = point.x;
        let mut high_factor = M31::ONE;
        for power in 1..=8 {
            doubled_x = doubled_x.mul(doubled_x).double().sub(M31::ONE);
            if power == 1 {
                // T_2(x)=1 would force x=+/-1 and make the kernel witness's
                // coefficient sum vanish.
                assert_ne!(doubled_x, M31::ONE);
                t2_coordinates.push(doubled_x.0);
            }
            if (6..=8).contains(&power) {
                high_factor = high_factor.mul(doubled_x);
            }
        }
        assert_ne!(high_factor, M31::ZERO);
    }
    t2_coordinates.sort_unstable();
    t2_coordinates.dedup();
    assert_eq!(t2_coordinates.len(), FIBERS);
}

fn small_m31_column_rank(columns: &[Vec<M31>], rows: usize) -> usize {
    let mut pivots = vec![None::<Vec<M31>>; rows];
    let mut rank = 0;
    for raw in columns {
        let mut column = raw.clone();
        assert_eq!(column.len(), rows);
        for row in 0..rows {
            if column[row] == M31::ZERO {
                continue;
            }
            if let Some(pivot) = &pivots[row] {
                let scale = column[row];
                for (value, basis) in column.iter_mut().zip(pivot) {
                    *value = value.sub(scale.mul(*basis));
                }
            } else {
                let inverse = column[row].inv();
                for value in &mut column {
                    *value = value.mul(inverse);
                }
                pivots[row] = Some(column);
                rank += 1;
                break;
            }
        }
    }
    rank
}

fn natural_t_leading_coefficient(index: usize) -> M31 {
    // In the t=T_2(x) tensor basis, bit b selects T_(2^b)(t), whose
    // leading coefficient is 2^(2^b-1). Products preserve leading terms.
    let exponent = (0..5)
        .filter(|bit| index & (1usize << bit) != 0)
        .map(|bit| (1u64 << bit) - 1)
        .sum::<u64>();
    M31(2).pow(exponent)
}

#[test]
fn all_q_semantic_kernel_terminal12_has_a_query_independent_certificate() {
    // For any q16 tuple, the q64 kernel is g_q(t)*h in four
    // {1,x,y,xy} sectors, with monic deg(g_q)=16. Multiplication from h
    // natural degrees 12..15 to output blocks 28..31 is triangular. Its
    // diagonal depends only on natural-basis leading coefficients, never on
    // q or on the lower coefficients of g_q.
    let mut high_projection_determinant = M31::ONE;
    for degree in 12..16 {
        let diagonal = natural_t_leading_coefficient(degree)
            .mul(natural_t_leading_coefficient(16 + degree).inv());
        assert_ne!(diagonal, M31::ZERO);
        high_projection_determinant = high_projection_determinant.mul(diagonal.pow(4));
    }
    assert_ne!(high_projection_determinant, M31::ZERO);

    let i = QM31::from_cm31(CM31 {
        a: M31::ZERO,
        b: M31::ONE,
    });
    let u = QM31 {
        c0: CM31::ZERO,
        c1: CM31::ONE,
    };
    let iu = i.mul(u);
    let v = i.add(u).sub(iu.add(iu));
    let vu = v.mul(u);
    assert_ne!(iu, QM31::ZERO);
    assert_ne!(iu, QM31::ONE);

    // {1,i,u,iu} makes the z and xor sector maps full rank. For successor,
    // w=1-u and {1,v,w,vw} is equivalent to {1,v,u,vu}; the latter has
    // determinant -5 in the frozen tower basis.
    assert_eq!(
        small_m31_column_rank(
            &[QM31::ONE, i, u, iu]
                .into_iter()
                .map(|value| qm31_coordinates(value).to_vec())
                .collect::<Vec<_>>(),
            4,
        ),
        4,
    );
    assert_eq!(
        small_m31_column_rank(
            &[QM31::ONE, v, u, vu]
                .into_iter()
                .map(|value| qm31_coordinates(value).to_vec())
                .collect::<Vec<_>>(),
            4,
        ),
        4,
    );

    // At this legal challenge assignment, z is supported exactly on natural
    // block 29, xor12(z) on block 30, and successor(z) on blocks 28..31.
    // After quotienting blocks 29/30 and setting 28..30 to zero in the
    // q-kernel, successor sees block 31 with nonzero scale iu*(1-iu).
    let mut z = [QM31::ONE; 10];
    z[6] = QM31::ZERO;
    z[8] = i;
    z[9] = u;
    let successor = aspis_statement::binary_successor_point(&z);
    let absorption = aspis_statement::xor12_point(&z);
    assert_eq!(absorption[6], QM31::ONE);
    assert_eq!(absorption[7], QM31::ZERO);
    assert_eq!(successor[6], iu);
    assert_eq!(successor[7], QM31::ONE.sub(iu));
    assert_eq!(successor[8], v);
    assert_eq!(successor[9], QM31::ONE.sub(u));
    assert_ne!(iu.mul(QM31::ONE.sub(iu)), QM31::ZERO);
}

#[test]
fn generic_tower_point_retains_the_query_independent_terminal12_minor() {
    // The all-q kernel certificate above isolates natural output blocks
    // 28..31 in each of the four {1,x,y,xy} sectors.  Multiplication by the
    // monic g_q has a q-independent nonzero triangular diagonal on these
    // sixteen directions.  Check that the non-Boolean assignment used by
    // the raw+sumcheck liveness probe gives twelve independent terminal
    // functionals on precisely that q-independent high projection.
    let i = QM31::from_cm31(CM31 {
        a: M31::ZERO,
        b: M31::ONE,
    });
    let u = QM31 {
        c0: CM31::ZERO,
        c1: CM31::ONE,
    };
    let iu = i.mul(u);
    let z = core::array::from_fn(|variable| {
        let variable = variable as u32;
        QM31::ONE
            .mul_m31(M31(3 + 3 * variable))
            .add(i.mul_m31(M31(7 + 5 * variable)))
            .add(u.mul_m31(M31(10 + 7 * variable)))
            .add(iu.mul_m31(M31(16 + 11 * variable)))
    });
    assert!(z
        .iter()
        .all(|value| *value != QM31::ZERO && *value != QM31::ONE));
    let final_affine_offset = z[..9]
        .iter()
        .enumerate()
        .fold(QM31::ZERO, |sum, (variable, value)| {
            sum.add(value.mul_m31(M31((9 - variable) as u32)))
        });
    assert_ne!(final_affine_offset, QM31::ZERO);
    let terminal_points = [
        z,
        aspis_statement::binary_successor_point(&z),
        aspis_statement::xor12_point(&z),
    ];
    let columns = (28..32)
        .flat_map(|natural_block| {
            (0..4).map(move |sector| {
                let row = 896 + 4 * natural_block + sector;
                terminal_points
                    .iter()
                    .flat_map(|point| qm31_coordinates(eq_weight(point, row)))
                    .collect::<Vec<_>>()
            })
        })
        .collect::<Vec<_>>();
    assert_eq!(columns.len(), 16);
    assert_eq!(small_m31_column_rank(&columns, 12), 12);
}

#[test]
fn boolean_zero_terminal_collapse_is_not_a_physical_containment_counterexample() {
    // A diagnostic schedule with z=(0,...,0) makes every terminal functional
    // on the common physical B_c block 896..=1023 vanish: row zero is the
    // only Boolean coefficient selected by eq(z,-), and row zero is fixed
    // (hence excluded) in the same-statement source.  The mask raw rank and
    // the physical-target raw rank therefore both collapse from 76 to the
    // universal q64 rank.  Treating the probe's RawC1Rank{64,76} error as a
    // privacy counterexample would confuse full ambient rank with the exact
    // containment predicate.
    const DOMAIN_LOG: u32 = 19;
    const DEPENDENT: usize = 1023;
    const RAW_OBSERVATIONS: usize = 16 * 4 + 3 * 4;
    let schedule = actual_schedule();
    let zero = [QM31::ZERO; 10];
    let terminal_points = [
        zero,
        aspis_statement::binary_successor_point(&zero),
        aspis_statement::xor12_point(&zero),
    ];
    let columns = (896..DEPENDENT)
        .map(|row| {
            let mut image = Vec::with_capacity(RAW_OBSERVATIONS);
            for &fiber in &schedule.queries[..schedule.query_count] {
                let point = aspis_core::circle_fri::circle_fiber_point_for_domain_log(
                    DOMAIN_LOG,
                    fiber as usize,
                )
                .unwrap();
                let slots = [
                    point,
                    aspis_core::circle_fri::BaseCirclePoint {
                        x: point.x,
                        y: M31::ZERO.sub(point.y),
                    },
                    aspis_core::circle_fri::BaseCirclePoint {
                        x: M31::ZERO.sub(point.x),
                        y: M31::ZERO.sub(point.y),
                    },
                    aspis_core::circle_fri::BaseCirclePoint {
                        x: M31::ZERO.sub(point.x),
                        y: point.y,
                    },
                ];
                image.extend(slots.into_iter().map(|point| {
                    circle_basis_value(row, point).sub(circle_basis_value(DEPENDENT, point))
                }));
            }
            for point in &terminal_points {
                let value = eq_weight(point, row).sub(eq_weight(point, DEPENDENT));
                assert_eq!(value, QM31::ZERO);
                image.extend(qm31_coordinates(value));
            }
            image
        })
        .collect::<Vec<_>>();
    assert!(columns
        .iter()
        .all(|column| column[64..].iter().all(|value| *value == M31::ZERO)));
    assert_eq!(small_m31_column_rank(&columns, RAW_OBSERVATIONS), 64);
}

fn last_round_affine_degenerate_schedule(
) -> aspis_core::state_only_prefix::StateOnlyTranscriptScheduleResult {
    let mut schedule = actual_schedule();
    let i = QM31::from_cm31(CM31 {
        a: M31::ZERO,
        b: M31::ONE,
    });
    let u = QM31 {
        c0: CM31::ZERO,
        c1: CM31::ONE,
    };
    schedule.prefix.z.fill(QM31::ONE);
    schedule.prefix.z[6] = QM31::ZERO;
    schedule.prefix.z[7] = QM31::ONE;
    schedule.prefix.z[8] = i;
    schedule.prefix.z[9] = u;
    let thirty_two = QM31::from_cm31(CM31::from_m31(M31(32)));
    schedule.prefix.z[0] = QM31::ZERO.sub(thirty_two.add(i).mul_m31(M31(9).inv()));
    schedule
}

fn nonzero_last_round_determinant_counterexample_schedule(
) -> aspis_core::state_only_prefix::StateOnlyTranscriptScheduleResult {
    let mut schedule = actual_schedule();
    let i = state_only_mask_tower_basis(1);
    let u = state_only_mask_tower_basis(2);
    schedule.prefix.z.fill(QM31::ONE);
    schedule.prefix.z[6] = QM31::ZERO;
    schedule.prefix.z[8] = i;
    schedule.prefix.z[9] = u;
    schedule
}

fn shared_family_round_determinant(
    schedule: &aspis_core::state_only_prefix::StateOnlyTranscriptScheduleResult,
    round: usize,
    row: usize,
) -> QM31 {
    let mut c0 = QM31::ZERO;
    let mut c16 = QM31::ZERO;
    for variable in 0..10 {
        if variable == round {
            continue;
        }
        let value = if variable < round {
            schedule.prefix.z[variable]
        } else if row & (1 << (9 - variable)) == 0 {
            QM31::ZERO
        } else {
            QM31::ONE
        };
        c0 = c0.add(value.mul_m31(M31((3 + 22 * variable) as u32)));
        c16 = c16.add(value.mul_m31(M31((275 + 150 * variable) as u32)));
    }
    let a = M31((3 + 22 * round) as u32);
    let b = M31((275 + 150 * round) as u32);
    c16.mul_m31(a).sub(c0.mul_m31(b))
}

#[test]
fn a_nonzero_last_round_determinant_does_not_control_earlier_round_fibers() {
    let schedule = nonzero_last_round_determinant_counterexample_schedule();
    let mut queries = schedule.queries[..schedule.query_count].to_vec();
    queries.sort_unstable();
    queries.dedup();
    assert_eq!(schedule.query_count, 16);
    assert_eq!(queries.len(), 16);
    assert_eq!(
        &schedule.queries[..16],
        &[
            93_639, 54_546, 123_325, 32_023, 14_842, 43_771, 112_422, 59_949, 59_550, 124_581,
            101_914, 70_499, 122_059, 110_296, 58_525, 41_927,
        ]
    );
    assert_ne!(schedule.prefix.eta, QM31::ZERO);
    assert_ne!(schedule.prefix.gamma, QM31::ZERO);

    // For L_0=sum_v(3+22v)x_v and L_16=sum_v(275+150v)x_v,
    // the determinant on round r and Boolean suffix s is
    //
    //   Delta_r/5600 = sum_{v<r}(r-v)z_v + sum_{v>r}(r-v)s_v.
    //
    // Check the closed form against the direct restricted-line determinant
    // for every round and every Boolean suffix represented by a trace row.
    for round in 0..10 {
        for row in 0..1024 {
            let mut closed = QM31::ZERO;
            for variable in 0..round {
                closed =
                    closed.add(schedule.prefix.z[variable].mul_m31(M31((round - variable) as u32)));
            }
            for variable in round + 1..10 {
                if row & (1 << (9 - variable)) != 0 {
                    closed = closed.sub(QM31::from_cm31(CM31::from_m31(M31(
                        (variable - round) as u32
                    ))));
                }
            }
            assert_eq!(
                shared_family_round_determinant(&schedule, round, row),
                closed.mul_m31(M31(5_600)),
            );
        }
    }

    // The excluded last-round hyperplane is not hit:
    // Delta_9/5600 = 41+i != 0.  Nevertheless rounds 1..=4 contain
    // proportional L_0/L_16 suffix fibers on rows that are relation-free in
    // every semantic column.
    let i = state_only_mask_tower_basis(1);
    assert_eq!(
        shared_family_round_determinant(&schedule, 9, 0),
        QM31::from_cm31(CM31::from_m31(M31(41)))
            .add(i)
            .mul_m31(M31(5_600)),
    );
    assert_ne!(shared_family_round_determinant(&schedule, 9, 0), QM31::ZERO);
    let earlier_degenerate_rows = [(1usize, 896usize), (2, 912), (3, 897), (4, 915)];
    for &(round, row) in &earlier_degenerate_rows {
        assert_eq!(
            shared_family_round_determinant(&schedule, round, row),
            QM31::ZERO,
        );
    }

    let cells =
        aspis_statement::atomic_state_only_registry::atomic_state_only_relation_free_mask_cells_v3(
        )
        .unwrap();
    for column in 0..16u8 {
        for &(_, row) in &earlier_degenerate_rows {
            assert!(cells
                .iter()
                .any(|cell| cell.column == column && usize::from(cell.row) == row));
        }
        // FullSharedLinear assigns one M31 source lane the nonzero tower
        // rotation beta_(column mod 4); it does not grant an arbitrary QM31
        // coefficient for that semantic factor.
        let rotation = state_only_mask_tower_basis(usize::from(column) & 3);
        assert_eq!(rotation.mul(rotation.inv()), QM31::ONE);
    }
}

#[test]
#[ignore = "slow exact FullSharedLinear raw+sumcheck elimination; run in --release"]
fn single_last_round_exclusion_still_leaves_masked_sumcheck_rank_790() {
    let schedule = nonzero_last_round_determinant_counterexample_schedule();
    assert_ne!(shared_family_round_determinant(&schedule, 9, 0), QM31::ZERO);

    // The gate eliminates the exact relation-free semantic sources with their
    // column-mod-4 tower rotations, then all mask-only sources, then all four
    // G coordinates.  It checks each 76-M31 C1 raw block and the 268-M31 G
    // raw block before it reaches this 1080-M31 quotient rank error.
    assert_eq!(
        probe_atomic_state_only_full_shared_hiding_rank(&schedule),
        Err(StateOnlyHidingRankGateError::MaskedSumcheckRank {
            got: 790,
            want: 1080,
        })
    );
}

#[test]
#[ignore = "slow exact documented-direct-sum containment elimination; run in --release"]
fn single_last_round_exclusion_is_red_for_documented_minimal_containment() {
    let schedule = nonzero_last_round_determinant_counterexample_schedule();
    let report = probe_atomic_state_only_profile22_minimal_containment(&schedule).unwrap();

    // The old PCS-only comparison is a false green when the sumcheck image
    // is deficient: it discards 294 target pivots before comparing 712/712.
    assert_eq!(report.masked_sumcheck_rank, 790);
    assert_eq!(report.joint_pcs_rank, 712);
    assert_eq!(report.witness_semantic_superset_rank, 712);
    assert_eq!(report.witness_legal_sumcheck_rank, 712);
    assert_eq!(report.witness_compatibility_rank_m31, 294);

    // Literal block elimination of rank([A | D_phys]) preserves every raw,
    // sumcheck and PCS pivot.  Physical semantic sources add 145 M31
    // directions; the independent legal-sumcheck summand brings the total
    // increment to 294. Active helper targets add nothing further.
    assert_eq!(report.witness_direct_sum_mask_view_rank_m31, Some(3_746));
    assert_eq!(
        report.witness_direct_sum_physical_augmented_view_rank_m31,
        Some(3_891)
    );
    assert_eq!(
        report.witness_direct_sum_legal_augmented_view_rank_m31,
        Some(4_040)
    );
    assert_eq!(
        report.witness_direct_sum_helper_augmented_view_rank_m31,
        Some(4_040)
    );
    assert_eq!(report.witness_direct_sum_physical_contained, Some(false));
    assert_eq!(report.witness_direct_sum_legal_contained, Some(false));
    assert_eq!(report.witness_direct_sum_helper_contained, Some(false));
}

#[test]
#[ignore = "slow exact frozen-actual direct-sum/native-X elimination; run in --release"]
fn frozen_actual_direct_sum_is_red_and_native_x_does_not_repair_it() {
    let schedule = actual_schedule();
    let epsilon = QM31::ONE
        .add(state_only_mask_tower_basis(1))
        .add(state_only_mask_tower_basis(3));
    let report = probe_atomic_state_only_native_full_root_x_joint_rank(&schedule, epsilon).unwrap();
    eprintln!(
        "native_full_x_exact direct={:?}/{:?}/{:?}/{:?} late={}/{} obs={} kernel={}",
        report.witness_direct_sum_mask_view_rank_m31,
        report.witness_direct_sum_physical_augmented_view_rank_m31,
        report.witness_direct_sum_legal_augmented_view_rank_m31,
        report.witness_direct_sum_helper_augmented_view_rank_m31,
        report.late_switch_conditioned_rank,
        report.late_switch_semantic_augmented_rank,
        report.masked_switch_observation_rank_qm31,
        report.masked_switch_kernel_qm31,
    );

    // The frozen actual schedule has complete legal sumcheck rank, but four
    // physical semantic directions still sit outside the literal mask view.
    assert_eq!(report.masked_sumcheck_rank, 1_080);
    assert_eq!(report.joint_pcs_rank, 712);
    assert_eq!(report.witness_direct_sum_physical_contained, Some(false));
    assert_eq!(report.witness_direct_sum_legal_contained, Some(false));
    assert_eq!(report.witness_direct_sum_helper_contained, Some(false));

    // This is the exact affine replay, not the old late-only diagnostic: the
    // 65-QM31 public X block is counted literally, and ker(R_q,tX) is inserted
    // into the PCS mask before the physical target.  The target is still one
    // independent QM31 direction outside that enlarged mask.
    assert_eq!(report.witness_direct_sum_mask_view_rank_m31, Some(4_296));
    assert_eq!(
        report.witness_direct_sum_physical_augmented_view_rank_m31,
        Some(4_300)
    );
    assert_eq!(
        report.witness_direct_sum_legal_augmented_view_rank_m31,
        Some(4_300)
    );
    assert_eq!(
        report.witness_direct_sum_helper_augmented_view_rank_m31,
        Some(4_300)
    );
    assert_eq!(report.masked_switch_observation_rank_qm31, 65);
    assert_eq!(report.masked_switch_kernel_qm31, 959);
    assert_eq!(report.late_switch_conditioned_rank, 712);
    assert_eq!(report.late_switch_semantic_augmented_rank, 712);
}

#[test]
#[ignore = "slow exact protocol-coupled physical/terminal-kernel containment; run in --release"]
fn frozen_actual_protocol_coupled_view_is_contained() {
    let report = probe_atomic_state_only_profile22_minimal_containment(&actual_schedule()).unwrap();

    // The independent direct-sum stress target permits an invalid terminal
    // mismatch and remains red.  Its four pivots are exactly the four M31
    // limbs of compressed observation 270 (round-9 c27), a representative
    // of the verifier terminal functional.
    assert_eq!(report.witness_direct_sum_mask_view_rank_m31, Some(4_036));
    assert_eq!(
        report.witness_direct_sum_physical_augmented_view_rank_m31,
        Some(4_040)
    );
    assert_eq!(report.witness_direct_sum_physical_contained, Some(false));
    assert_eq!(
        report.witness_compatibility_pivot_rows_m31,
        [1_080, 1_081, 1_082, 1_083]
    );

    // In the actual protocol H is computed from the same committed masked
    // C1 values, so physical differences carry their exact H sumcheck image.
    // Conditional on the bound initial claim and verifier-computed terminal,
    // the remaining free sumcheck fiber has 269 QM31 = 1,076 M31 directions.
    assert_eq!(
        report.witness_coupled_physical_augmented_view_rank_m31,
        Some(4_036)
    );
    assert_eq!(
        report.witness_coupled_legal_augmented_view_rank_m31,
        Some(4_036)
    );
    assert_eq!(
        report.witness_coupled_helper_augmented_view_rank_m31,
        Some(4_036)
    );
    assert_eq!(report.witness_coupled_physical_contained, Some(true));
    assert_eq!(report.witness_coupled_legal_contained, Some(true));
    assert_eq!(report.witness_coupled_helper_contained, Some(true));
    assert_eq!(report.witness_coupled_legal_sumcheck_generators_m31, 1_076);
    assert_eq!(
        report.witness_coupled_terminal_dependent_observation,
        Some(270)
    );
    assert_eq!(
        report.witness_coupled_terminal_functional_fingerprint,
        0x6bad_5754_84b0_4bfd
    );
    assert!(report.witness_coupled_terminal_identity_guard);
    assert_eq!(
        report.witness_mask_raw_kernel_terminal_zero_sources_m31,
        17_324
    );
    assert!(report.witness_mask_raw_kernel_terminal_zero_guard);
    assert!(report.witness_h_zero_sumcheck_terminal_guard);
    assert!(report.witness_mask_sumcheck_equals_terminal_kernel);
    assert_eq!(report.joint_raw_sumcheck_minor.source_columns.len(), 3_324);
    assert_eq!(report.joint_raw_sumcheck_minor.pivot_rows.len(), 3_324);
    assert_eq!(
        report.joint_raw_sumcheck_minor.fingerprint,
        0xdc4f_4044_9cb8_c16f
    );
    assert_eq!(
        &report.joint_raw_sumcheck_minor.pivot_rows[..2_244],
        report.raw_opening_minor.pivot_rows
    );
    assert_eq!(
        report.joint_raw_sumcheck_minor.pivot_rows[2_244..]
            .iter()
            .map(|row| *row - 2_244)
            .collect::<Vec<_>>(),
        report.masked_sumcheck_minor.pivot_rows
    );
    assert_eq!(report.witness_compatibility_terminal_map_rank_m31, 4);
    assert_eq!(
        report.witness_compatibility_terminal_map_fingerprint,
        0xd581_9ed1_2907_e16d
    );
}

#[test]
#[ignore = "slow exact raw-only negative control; run in --release"]
fn frozen_actual_native_x_raw_only_control_localizes_the_tx_obstruction() {
    let schedule = actual_schedule();
    let epsilon = QM31::ONE
        .add(state_only_mask_tower_basis(1))
        .add(state_only_mask_tower_basis(3));
    let report =
        probe_atomic_state_only_native_full_root_x_raw_only_control_rank(&schedule, epsilon)
            .unwrap();
    eprintln!(
        "native_full_x_raw_only direct={:?}/{:?}/{:?}/{:?} late={}/{} obs={} kernel={}",
        report.witness_direct_sum_mask_view_rank_m31,
        report.witness_direct_sum_physical_augmented_view_rank_m31,
        report.witness_direct_sum_legal_augmented_view_rank_m31,
        report.witness_direct_sum_helper_augmented_view_rank_m31,
        report.late_switch_conditioned_rank,
        report.late_switch_semantic_augmented_rank,
        report.masked_switch_observation_rank_qm31,
        report.masked_switch_kernel_qm31,
    );
    assert_eq!(report.masked_switch_observation_rank_qm31, 64);
    assert_eq!(report.masked_switch_kernel_qm31, 960);
    assert_eq!(report.late_switch_conditioned_rank, 716);
    assert_eq!(report.witness_direct_sum_mask_view_rank_m31, Some(4_296));
    assert_eq!(
        report.witness_direct_sum_physical_augmented_view_rank_m31,
        Some(4_300)
    );
}

#[test]
#[ignore = "slow exact reduced natural-B18 shared-C2 direct-sum replay"]
fn frozen_actual_reduced_natural18_switch_tests_literal_direct_sum() {
    let report = probe_atomic_state_only_profile21_semantic_natural18_shared_c2_switch_joint_rank(
        &actual_profile21_schedule(),
    )
    .unwrap();
    eprintln!(
        "natural18_shared_c2 direct={:?}/{:?}/{:?}/{:?} late={}/{} obs={} shared_obs={} kernel={} shared_kernel={} pivots={:?}",
        report.witness_direct_sum_mask_view_rank_m31,
        report.witness_direct_sum_physical_augmented_view_rank_m31,
        report.witness_direct_sum_legal_augmented_view_rank_m31,
        report.witness_direct_sum_helper_augmented_view_rank_m31,
        report.late_switch_conditioned_rank,
        report.late_switch_semantic_augmented_rank,
        report.masked_switch_observation_rank_qm31,
        report.masked_switch_shared_c2_observation_rank_qm31,
        report.masked_switch_kernel_qm31,
        report.masked_switch_shared_c2_kernel_qm31,
        report.late_switch_semantic_new_pivots_m31,
    );
    assert_eq!(report.masked_switch_shared_c2_observation_rank_qm31, 33);
    assert_eq!(report.masked_switch_shared_c2_kernel_qm31, 1);
    assert_eq!(report.late_switch_conditioned_rank, 716);
    assert_eq!(report.witness_direct_sum_mask_view_rank_m31, Some(4_172));
    assert_eq!(
        report.witness_direct_sum_physical_augmented_view_rank_m31,
        Some(4_176)
    );
}

#[test]
#[ignore = "slow exact frozen-actual Shared0Pow23 G2 direct-sum elimination; run in --release"]
fn frozen_actual_shared0_pow23_g2_preserves_the_direct_sum_deficit() {
    let schedule = actual_schedule();
    let report =
        probe_atomic_state_only_profile21_g2_mask_rank(&schedule, TailQm31MaskFactor::Shared0Pow23)
            .unwrap();

    // The extra QM31 lane contributes one full 268-M31 raw block, shifting
    // both sides equally from 4036/4040 to 4304/4308.  It therefore does not
    // span any of the four missing documented-target directions.
    assert_eq!(report.masked_sumcheck_rank, 1_080);
    assert_eq!(report.joint_pcs_rank, 712);
    assert_eq!(report.tail_qm31_basis_m31, 4_092);
    assert_eq!(report.tail_qm31_raw_kernel_m31, 3_824);
    assert_eq!(report.witness_direct_sum_mask_view_rank_m31, Some(4_304));
    assert_eq!(
        report.witness_direct_sum_physical_augmented_view_rank_m31,
        Some(4_308)
    );
    assert_eq!(
        report.witness_direct_sum_legal_augmented_view_rank_m31,
        Some(4_308)
    );
    assert_eq!(
        report.witness_direct_sum_helper_augmented_view_rank_m31,
        Some(4_308)
    );
    assert_eq!(report.witness_direct_sum_physical_contained, Some(false));
    assert_eq!(report.witness_direct_sum_legal_contained, Some(false));
    assert_eq!(report.witness_direct_sum_helper_contained, Some(false));
}

#[test]
fn final_round_mask_linear_forms_have_an_explicit_affine_degeneracy() {
    let schedule = last_round_affine_degenerate_schedule();
    let weighted = schedule.prefix.z[..9]
        .iter()
        .enumerate()
        .fold(QM31::ZERO, |sum, (variable, value)| {
            sum.add(value.mul_m31(M31((9 - variable) as u32)))
        });
    assert_eq!(weighted, QM31::ZERO);

    // Along the last-round line x_9=t,
    //   L0  = C0  + 201 t,
    //   L16 = C16 + 1625 t,
    // and 201*C16 - 1625*C0 = 5600*sum_(v<9)(9-v)z_v.
    // Hence this schedule makes L16 a scalar multiple of L0.  The explicit
    // factor 1+L16^26 then lies in span{1,L0^26} and cannot fill the frozen
    // missing shared power L0^23.
    let (c0, c16) = schedule.prefix.z[..9].iter().enumerate().fold(
        (QM31::ZERO, QM31::ZERO),
        |(c0, c16), (variable, value)| {
            (
                c0.add(value.mul_m31(M31((3 + 22 * variable) as u32))),
                c16.add(value.mul_m31(M31((275 + 150 * variable) as u32))),
            )
        },
    );
    assert_eq!(c16.mul_m31(M31(201)), c0.mul_m31(M31(1625)));
    for t in [QM31::ZERO, QM31::ONE, i_plus_u()] {
        let l0 = c0.add(t.mul_m31(M31(201)));
        let l16 = c16.add(t.mul_m31(M31(1625)));
        assert_eq!(l16.mul_m31(M31(201)), l0.mul_m31(M31(1625)));
    }
}

fn i_plus_u() -> QM31 {
    QM31 {
        c0: CM31 {
            a: M31::ZERO,
            b: M31::ONE,
        },
        c1: CM31::ONE,
    }
}

#[test]
#[ignore = "slow exact raw+sumcheck elimination; explicit parser-valid schedule rank tooth"]
fn final_round_affine_degeneracy_drops_masked_sumcheck_rank_to_916() {
    let schedule = last_round_affine_degenerate_schedule();
    assert_eq!(schedule.query_count, 16);
    assert_eq!(schedule.prefix.eta != QM31::ZERO, true);
    assert_eq!(schedule.prefix.gamma != QM31::ZERO, true);
    assert_eq!(
        probe_atomic_state_only_profile21_witness_difference_containment(&schedule),
        Err(StateOnlyHidingRankGateError::MaskedSumcheckRank {
            got: 916,
            want: 1080,
        })
    );
}

#[test]
#[ignore = "slow retired-zero-gamma algebraic tooth; run in --release"]
fn zero_gamma_refutes_raw_plus_sumcheck_implies_containment() {
    let mut schedule = actual_schedule();
    // Profile 22 now samples `gamma` with exact nonzero rejection, so this is
    // no longer a parser-valid production schedule.  Retain it as an
    // algebraic negative tooth: it proves that raw and masked-sumcheck rank
    // alone do not imply containment unless the nonzero-gamma premise is
    // used essentially.
    schedule.prefix.gamma = QM31::ZERO;
    let report =
        probe_atomic_state_only_profile21_witness_difference_containment(&schedule).unwrap();

    // Every canonical raw block reached its pinned rank (otherwise the probe
    // would have returned RawC1Rank/RawGRank), and the entire legal masked
    // sumcheck quotient is still surjective.  Nevertheless the production
    // arity-4 PCS continuation does not contain either target class.
    assert_eq!(report.masked_sumcheck_rank, 1080);
    assert_eq!(report.joint_pcs_rank, 492);
    assert_eq!(report.witness_semantic_superset_rank, 712);
    assert_eq!(report.witness_legal_sumcheck_rank, 712);
    assert!(report.witness_semantic_superset_rank > report.joint_pcs_rank);
    assert!(report.witness_legal_sumcheck_rank > report.joint_pcs_rank);
}

#[test]
#[ignore = "slow three-factor exact G2 negative scan; run in --release"]
fn one_additive_g2_lane_does_not_repair_the_affine_degeneracy() {
    let schedule = last_round_affine_degenerate_schedule();
    for factor in [
        TailQm31MaskFactor::Shared0Pow23,
        TailQm31MaskFactor::Dense17Pow23,
        TailQm31MaskFactor::Dense17Pow26AddOne,
    ] {
        assert_eq!(
            probe_atomic_state_only_profile21_g2_mask_rank(&schedule, factor),
            Err(StateOnlyHidingRankGateError::MaskedSumcheckRank {
                got: 928,
                want: 1080,
            }),
            "unexpected additive-G2 result for {factor:?}",
        );
    }
}

fn eq_weight(point: &[QM31; 10], row: usize) -> QM31 {
    point
        .iter()
        .enumerate()
        .fold(QM31::ONE, |weight, (coordinate, value)| {
            let bit = (row >> (point.len() - 1 - coordinate)) & 1;
            weight.mul(if bit == 0 {
                QM31::ONE.sub(*value)
            } else {
                *value
            })
        })
}

fn qm31_coordinates(value: QM31) -> [M31; 4] {
    [value.c0.a, value.c0.b, value.c1.a, value.c1.b]
}

#[test]
fn frozen_schedule_common_free_block_has_full_query_and_terminal_rank() {
    const DOMAIN_LOG: u32 = 19;
    const DEPENDENT: usize = 1023;
    const RAW_OBSERVATIONS: usize = 16 * 4 + 3 * 4;
    let schedule = actual_schedule();
    let terminal_points = [
        schedule.prefix.z,
        aspis_statement::binary_successor_point(&schedule.prefix.z),
        aspis_statement::xor12_point(&schedule.prefix.z),
    ];
    let mut pivots: Vec<Option<Vec<M31>>> = vec![None; RAW_OBSERVATIONS];
    let mut pivot_source_rows = Vec::new();
    let mut pivot_rows = Vec::new();
    let mut pivot_values = Vec::new();
    for row in 896..DEPENDENT {
        let mut image = Vec::with_capacity(RAW_OBSERVATIONS);
        for &fiber in &schedule.queries[..schedule.query_count] {
            let point = aspis_core::circle_fri::circle_fiber_point_for_domain_log(
                DOMAIN_LOG,
                fiber as usize,
            )
            .unwrap();
            let slots = [
                point,
                aspis_core::circle_fri::BaseCirclePoint {
                    x: point.x,
                    y: M31::ZERO.sub(point.y),
                },
                aspis_core::circle_fri::BaseCirclePoint {
                    x: M31::ZERO.sub(point.x),
                    y: M31::ZERO.sub(point.y),
                },
                aspis_core::circle_fri::BaseCirclePoint {
                    x: M31::ZERO.sub(point.x),
                    y: point.y,
                },
            ];
            for point in slots {
                image
                    .push(circle_basis_value(row, point).sub(circle_basis_value(DEPENDENT, point)));
            }
        }
        for point in &terminal_points {
            image.extend(qm31_coordinates(
                eq_weight(point, row).sub(eq_weight(point, DEPENDENT)),
            ));
        }
        for coordinate in 0..RAW_OBSERVATIONS {
            if image[coordinate] == M31::ZERO {
                continue;
            }
            if let Some(pivot) = &pivots[coordinate] {
                let scale = image[coordinate];
                for (value, pivot_value) in image.iter_mut().zip(pivot) {
                    *value = value.sub(scale.mul(*pivot_value));
                }
            } else {
                let pivot_value = image[coordinate];
                let inverse = image[coordinate].inv();
                for value in &mut image {
                    *value = value.mul(inverse);
                }
                pivots[coordinate] = Some(image);
                pivot_source_rows.push(row);
                pivot_rows.push(coordinate);
                pivot_values.push(pivot_value.0);
                break;
            }
        }
    }
    eprintln!("common 896..1022 raw-view pivot rows: {pivot_source_rows:?}");
    assert_eq!(
        pivot_source_rows,
        (896..972).collect::<Vec<_>>(),
        "rows 896..959 must cover all 64 q symbols before rows 960..971 add the 12 terminal M31 coordinates",
    );
    let mut fingerprint = 0xcbf2_9ce4_8422_2325u64;
    for byte in b"aspis/profile21/terminal12-minor/v1" {
        fingerprint ^= u64::from(*byte);
        fingerprint = fingerprint.wrapping_mul(0x0000_0100_0000_01b3);
    }
    for ((source, pivot), value) in pivot_source_rows.iter().zip(&pivot_rows).zip(&pivot_values) {
        for byte in (*source as u64)
            .to_le_bytes()
            .into_iter()
            .chain((*pivot as u64).to_le_bytes())
            .chain(value.to_le_bytes())
        {
            fingerprint ^= u64::from(byte);
            fingerprint = fingerprint.wrapping_mul(0x0000_0100_0000_01b3);
        }
    }
    assert_eq!(fingerprint, 0xc444_0d2f_95d6_441e);
}

#[test]
#[ignore = "~25s exact elimination over the actual atomic-v3 transcript"]
fn actual_atomic_profile21_affine_field_view_rank_repin() {
    let schedule = actual_profile21_schedule();
    let baseline = probe_atomic_state_only_full_shared_hiding_rank(&schedule.base).unwrap();
    assert_eq!(baseline.masked_sumcheck_rank, 1080);
    assert_eq!(baseline.joint_pcs_rank, 712);
    assert_eq!(baseline.joint_pcs_declared_rank, 780);
    assert_eq!(baseline.baseline_ambient_deficit_m31, 68);
    assert!(baseline.baseline_valid_witness_containment);
    assert!(!baseline.complete_ambient_rank);

    let switched =
        probe_atomic_state_only_profile21_masked_single_switch_joint_rank(&schedule).unwrap();
    assert_eq!(switched.masked_sumcheck_rank, 1080);
    assert_eq!(switched.late_switch_conditioned_rank, 780);
    assert_eq!(switched.joint_pcs_declared_rank, 780);
    assert_eq!(switched.masked_switch_variables_qm31, 70);
    assert!(switched.masked_switch_universal_mds_basis);
    assert_eq!(switched.masked_switch_code_basis_rank_m31, 35);
    assert!(switched.masked_switch_query_abscissae_distinct);
    assert!(!switched.masked_switch_rank_retry_required);
    assert_eq!(
        switched.masked_switch_code_basis_fingerprint,
        0xceb3_5dd3_ee50_e051,
    );
    assert_eq!(switched.masked_switch_observation_rank_qm31, 52);
    assert_eq!(switched.masked_switch_kernel_qm31, 18);
    assert_eq!(switched.masked_switch_q_randomness_rank_qm31, 16);
    assert_eq!(switched.masked_switch_q_coopening_rank_qm31, 16);
    assert_eq!(switched.masked_switch_otp_rank_qm31, 35);
    assert_eq!(
        switched.masked_switch_u_plus_legacy_ood_diagnostic_rank_qm31,
        35
    );
    assert_eq!(switched.masked_switch_shared_c2_observation_rank_qm31, 52);
    assert_eq!(switched.masked_switch_shared_c2_kernel_qm31, 18);
    assert_eq!(switched.masked_switch_shared_c2_randomness_rank_qm31, 16);
    assert_eq!(switched.late_switch_complement_pivots_later_m31, 64);
    assert_eq!(switched.late_switch_complement_pivots_relation_m31, 4);
    assert!(switched.complete_ambient_rank);
    assert_eq!(switched.masked_sumcheck_minor.source_columns.len(), 1080);
    assert_eq!(switched.masked_sumcheck_minor.pivot_rows.len(), 1080);
    assert_eq!(switched.post_sumcheck_pcs_minor.source_columns.len(), 712);
    assert_eq!(switched.post_sumcheck_pcs_minor.pivot_rows.len(), 712);
    assert_eq!(
        switched.late_switch_complement_minor.source_columns.len(),
        68
    );
    assert_eq!(switched.late_switch_complement_minor.pivot_rows.len(), 68);
    assert_eq!(switched.raw_opening_minor.source_columns.len(), 2244);
    assert_eq!(switched.raw_opening_minor.pivot_rows.len(), 2244);
    assert_eq!(
        switched.late_switch_observation_minor.source_columns.len(),
        208
    );
    assert_eq!(switched.late_switch_observation_minor.pivot_rows.len(), 208);
    assert_eq!(
        switched.masked_sumcheck_minor.fingerprint,
        0x9d1b_1849_b90c_51d5
    );
    assert_eq!(
        switched.post_sumcheck_pcs_minor.fingerprint,
        0x2d95_0f0e_11ab_83e9
    );
    assert_eq!(
        switched.late_switch_complement_minor.fingerprint,
        0xfe79_46aa_9db1_eb0d
    );
    assert_eq!(
        switched.raw_opening_minor.fingerprint,
        0xb8b9_b449_d82c_c505
    );
    assert_eq!(
        switched.late_switch_observation_minor.fingerprint,
        0xd6be_533d_3afa_238e
    );
    assert_eq!(
        switched.late_switch_observation_minor.source_columns,
        (0..208).collect::<Vec<_>>()
    );
    let mut observation_rows = switched.late_switch_observation_minor.pivot_rows.clone();
    observation_rows.sort_unstable();
    assert_eq!(
        observation_rows,
        (0..140).chain(140..144).chain(148..212).collect::<Vec<_>>()
    );
    assert_eq!(
        switched.late_switch_complement_minor.source_columns,
        (208..276).collect::<Vec<_>>()
    );
    assert_eq!(
        switched.late_switch_complement_minor.pivot_rows,
        [
            280, 281, 282, 283, 292, 293, 294, 295, 300, 301, 302, 303, 328, 329, 330, 331, 332,
            333, 334, 335, 360, 361, 362, 363, 368, 369, 370, 371, 380, 381, 382, 383, 396, 397,
            398, 399, 420, 421, 422, 423, 432, 433, 434, 435, 448, 449, 450, 451, 460, 461, 462,
            463, 488, 489, 490, 491, 492, 493, 494, 495, 520, 521, 522, 523, 1084, 1085, 1086,
            1087,
        ]
    );
}

#[test]
#[ignore = "builds a second full q16/rate-1/512 atomic proof"]
fn same_statement_fresh_masks_change_every_private_commitment_class() {
    // This is a distinguisher smoke test, not a ZK proof.  A second *valid
    // spend witness* for the same binding statement is not available without
    // finding Poseidon commitment/nullifier/Merkle collisions.  The universal
    // witness-difference obligation is instead the exact containment gate.
    let (statement, witness) = fixture();
    let mut nonces = InMemoryStateOnlyMaskNonceStore::default();
    let fresh = build_hiding_atomic_state_only_profile21_proof_v3(
        &statement,
        &witness,
        StateOnlyAttemptSecrets::generate().unwrap(),
        &mut nonces,
        HOST_HASH,
        StateOnlyPowMode::UnminedZero,
    )
    .unwrap();
    verify_atomic_state_only_profile21_unmined_for_diagnostics_v3(
        &fresh.bytes,
        &statement,
        HOST_HASH,
        None,
    )
    .unwrap();
    let (old, _) = StateOnlyProfile21Prefix::parse_from_proof(ACTUAL_PROFILE21_PROOF).unwrap();
    let (new, _) = StateOnlyProfile21Prefix::parse_from_proof(&fresh.bytes).unwrap();
    assert_ne!(old.base.mask_nonce, new.base.mask_nonce);
    assert_ne!(old.base.c1_root, new.base.c1_root);
    assert_ne!(old.base.c2_root, new.base.c2_root);
    for layer in 1..4 {
        assert_ne!(old.base.rounds[layer].root, new.base.rounds[layer].root);
    }
    assert_ne!(
        old.base.initial_mask_claim_bytes,
        new.base.initial_mask_claim_bytes
    );
    assert_ne!(old.logical_u_bytes, new.logical_u_bytes);
    assert_ne!(fresh.bytes, ACTUAL_PROFILE21_PROOF);
    // The minimal-subtree suffix length is query-position dependent, so two
    // fresh Fiat--Shamir schedules need not have equal proof lengths.  Length
    // is part of the complete view and its *distribution* must be handled by
    // the FS simulator; bytewise alignment of two samples is not meaningful.
}
