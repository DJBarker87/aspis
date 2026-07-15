//! Arithmetic and release guard for the profile-23 D-after-G, q3 design.
//!
//! This executable pins the term-by-term Johnson soundness union, the
//! three-candidate rank-exhaustion/liveness bound, and the literal EPRO input
//! inventory. Normal mode also requires the fail-closed one-transaction
//! release certificate. `--calculation-only` evaluates the proof-independent
//! arithmetic without requiring that downstream certificate, breaking the
//! release-generation cycle without weakening the normal release guard. This
//! executable does not replace the separate root-neutral polynomial-kernel and
//! complete-view proofs.

use std::collections::HashSet;
use std::f64::consts::LN_2;
use std::path::Path;

use aspis_core::circle_hiding_prefix::PAYMENT_HIDING_QUERY_DRAW_LIMIT;
use aspis_core::field::{M31, P as M31_MODULUS};
use aspis_core::state_only_hiding::{
    STATE_ONLY_PROFILE23_D_GENERATOR_INDEX, STATE_ONLY_PROFILE23_G_GENERATOR_INDEX,
    STATE_ONLY_PROFILE23_QUERY_CANDIDATES, STATE_ONLY_PROFILE23_TOTAL_GENERATOR_WIDTH,
};
use aspis_core::state_only_prefix::{
    STATE_ONLY_LOG_ROWS, STATE_ONLY_PROFILE23_BATCH_GRINDING_BITS,
    STATE_ONLY_PROFILE23_D_CLAIM_COUNT, STATE_ONLY_PROFILE23_FOLD_GRINDING_BITS,
    STATE_ONLY_PROFILE23_GRINDING_BITS, STATE_ONLY_PROFILE23_QUERY_CANDIDATE_COUNT,
    STATE_ONLY_PROFILE23_QUERY_COUNT,
};
use aspis_core::transcript::label;
use aspis_prover::state_only_good23::{
    verify_profile23_selector_scope_lemma, PROFILE23_GOOD_SCHEDULE_MAX_ATTEMPTS,
    PROFILE23_SELECTOR_SCOPE_PROPOSITIONAL_CASES,
};

const P: f64 = M31_MODULUS as f64;
const FIELD_SIZE: f64 = P * P * P * P;
const JOHNSON_MULTIPLICITY: f64 = 10.0;
const FOLD_WORK: [u8; 4] = STATE_ONLY_PROFILE23_FOLD_GRINDING_BITS;
const ROOT_CAPS: [u64; 4] = [1_024, 255, 63, 15];
const QUERY_FIBERS: f64 = 131_072.0;
const QUERY_COUNT: u64 = 18;
const SELECTORS: u64 = 3;
const ATTEMPTS: u64 = 17;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SelectorScope {
    CommonPreselector,
    FinalQueryMiss,
}

/// Exact q18 complete-Good liveness pins from the optimized root-neutral minor.
/// Calculation-only mode does not need the downstream artifact or release;
/// normal release-guard mode cross-checks both and still fails closed on
/// accidental removal of these pins.
#[derive(Clone, Copy)]
struct Profile23GoodLivenessPins {
    query_degree: f64,
    root_neutral_minor_z_degree: f64,
    complete_good_z_degree: f64,
    gamma_degree: f64,
    continuous_degree: f64,
    rho_query: f64,
    beta_attempt: f64,
    bits_per_attempt: f64,
    rank_exhaustion_cap17_bits: f64,
    public_abort_bits: f64,
    root_minor_fingerprint: u64,
    remaining_gd_minor_fingerprint: u64,
    h1_minor_fingerprint: u64,
    product_fingerprint: u64,
}

const PROFILE23_Q18_GOOD_LIVENESS_PINS: Option<Profile23GoodLivenessPins> =
    Some(Profile23GoodLivenessPins {
        query_degree: 31_320.0,
        root_neutral_minor_z_degree: 41_040.0,
        complete_good_z_degree: 41_280.0,
        gamma_degree: 80_688.0,
        continuous_degree: 121_968.0,
        rho_query: 0.238_983_632_825_912_78,
        beta_attempt: 0.013_705_910_239_932_412,
        bits_per_attempt: 6.189_058_045_848_226,
        rank_exhaustion_cap17_bits: 105.213_986_779_419_84,
        public_abort_bits: 105.213_986_779_419_83,
        root_minor_fingerprint: 0x6b38_3866_2fbf_34db,
        remaining_gd_minor_fingerprint: 0x1f34_525d_b611_d292,
        h1_minor_fingerprint: 0xe702_15f0_b479_5f52,
        product_fingerprint: 0xfc07_06f3_a304_ae26,
    });

fn union_bits(bits: impl IntoIterator<Item = f64>) -> f64 {
    -bits
        .into_iter()
        .map(|bits| 2.0_f64.powf(-bits))
        .sum::<f64>()
        .log2()
}

fn local_bits(numerator: f64) -> f64 {
    FIELD_SIZE.log2() - numerator.log2()
}

fn local_nonzero_bits(numerator: f64) -> f64 {
    (FIELD_SIZE - 1.0).log2() - numerator.log2()
}

fn bcs_work_normalized_bits(round_bits: f64, random_oracle_queries: f64) -> f64 {
    const R: f64 = 32.0;
    const LAMBDA: f64 = 256.0;
    let epsilon_round = 2.0_f64.powf(-round_bits);
    let epsilon_bcs_per_query = (1.0 + R / random_oracle_queries) * epsilon_round
        + 3.0 * (random_oracle_queries + random_oracle_queries.recip()) * 2.0_f64.powf(-LAMBDA);
    -epsilon_bcs_per_query.log2()
}

fn close(actual: f64, expected: f64) {
    assert!(
        (actual - expected).abs() < 1e-9,
        "numeric repin: actual={actual:.15}, expected={expected:.15}"
    );
}

fn main() {
    let calculation_only = match std::env::args().skip(1).collect::<Vec<_>>().as_slice() {
        [] => false,
        [argument] if argument == "--calculation-only" => true,
        _ => panic!("usage: profile23_soundness_epro_ledger [--calculation-only]"),
    };

    assert_eq!(STATE_ONLY_PROFILE23_TOTAL_GENERATOR_WIDTH, 29);
    assert_eq!(STATE_ONLY_PROFILE23_G_GENERATOR_INDEX, 27);
    assert_eq!(STATE_ONLY_PROFILE23_D_GENERATOR_INDEX, 28);
    assert_eq!(STATE_ONLY_PROFILE23_QUERY_CANDIDATES, 3);
    assert_eq!(STATE_ONLY_PROFILE23_QUERY_CANDIDATE_COUNT, 3);
    assert_eq!(STATE_ONLY_PROFILE23_D_CLAIM_COUNT, 3);
    assert_eq!(STATE_ONLY_PROFILE23_QUERY_COUNT, QUERY_COUNT as u16);
    assert_eq!(PROFILE23_GOOD_SCHEDULE_MAX_ATTEMPTS, ATTEMPTS as usize);
    assert_eq!(STATE_ONLY_PROFILE23_BATCH_GRINDING_BITS, 37);
    assert_eq!(STATE_ONLY_PROFILE23_FOLD_GRINDING_BITS, [34, 33, 30, 25]);
    assert_eq!(STATE_ONLY_PROFILE23_GRINDING_BITS, 32);
    assert_eq!(label::M31_STATE_ONLY_ZERO_FACTOR_D_CLAIMS, 43);
    assert_eq!(label::M31_STATE_ONLY_QUERY_CANDIDATE, 44);
    let selector_scope_cases = verify_profile23_selector_scope_lemma();
    assert_eq!(
        selector_scope_cases,
        PROFILE23_SELECTOR_SCOPE_PROPOSITIONAL_CASES
    );

    // The q sampler selects distinct four-symbol fibers.  Exhaustively pin
    // that the implemented fiber->polynomial-root map is injective; this
    // discharges a separate root-collision event.  Root one is handled by the
    // exhaustive root-one count below; no degree-16 anchor is booked.
    let mut query_roots = HashSet::with_capacity(QUERY_FIBERS as usize);
    let mut root_one_count = 0usize;
    let mut line_root_one_count = 0usize;
    for query in 0..QUERY_FIBERS as usize {
        let point = aspis_core::circle_fri::circle_fiber_point_for_domain_log(
            STATE_ONLY_LOG_ROWS + 9,
            query,
        )
        .expect("profile23 query fiber point");
        let root = point.x.mul(point.x).double().sub(M31::ONE);
        let line_root =
            aspis_core::circle_fri::line_domain_x_for_circle(STATE_ONLY_LOG_ROWS + 9, 1, query)
                .expect("profile23 line-domain root");
        assert_eq!(root, line_root, "circle/line root mismatch at {query}");
        root_one_count += usize::from(root == M31::ONE);
        line_root_one_count += usize::from(line_root == M31::ONE);
        assert!(
            query_roots.insert(root.0),
            "fiber-root map collision at {query}"
        );
    }
    assert_eq!(query_roots.len(), QUERY_FIBERS as usize);
    assert_eq!(root_one_count, 0);
    assert_eq!(line_root_one_count, root_one_count);
    println!("profile23_query_root_one_count={root_one_count}");

    // Johnson / MCA terms.  Only the final q18 miss term receives the
    // malicious-selector union.  D changes the polynomial batching degree
    // 27->28, gamma numerator 29->30, and inactive-copy numerator 27->28.
    let rho: f64 = 1.0 / 512.0;
    let agreement_fraction = (1.0 + 1.0 / (2.0 * JOHNSON_MULTIPLICITY)) * rho.sqrt();
    let query_fibers = 131_072u64;
    let agreement_fibers = (agreement_fraction * query_fibers as f64).floor() as u64;
    assert_eq!(agreement_fibers, 6_082);

    let ell = (JOHNSON_MULTIPLICITY + 0.5) / rho.sqrt();
    let batch_numerator = 28.0 * ell * ((2.0 * ell.powi(4) / 3.0) * rho + 1.0) * 524_288.0;
    let batch_bits =
        (FIELD_SIZE / batch_numerator).log2() + f64::from(STATE_ONLY_PROFILE23_BATCH_GRINDING_BITS);

    let raw_query_bits = (0..QUERY_COUNT)
        .map(|i| -((agreement_fibers - i) as f64 / (query_fibers - i) as f64).log2())
        .sum::<f64>()
        + f64::from(STATE_ONLY_PROFILE23_GRINDING_BITS);
    let selected_query_bits = raw_query_bits - (SELECTORS as f64).log2();

    let output_symbols = [131_072u64, 32_768, 8_192, 2_048];
    let output_dimensions = [256u64, 64, 16, 4];
    let fold_rows = (0..4)
        .map(|round| {
            let round_rho = (output_dimensions[round] - 1) as f64 / output_symbols[round] as f64;
            let sqrt_rho = round_rho.sqrt();
            let m = (sqrt_rho / (2.0 * (agreement_fraction - sqrt_rho)))
                .ceil()
                .max(3.0);
            let ell = (m + 0.5) / sqrt_rho;
            let numerator = 3.0
                * ell
                * ((2.0 * ell.powi(4) / 3.0) * round_rho + 1.0)
                * output_symbols[round] as f64;
            (FIELD_SIZE / numerator).log2() + f64::from(FOLD_WORK[round])
        })
        .collect::<Vec<_>>();
    let folds_bits = union_bits(fold_rows.iter().copied());

    let ood_space = FIELD_SIZE - P * P;
    let list_pairs = (240u64 * 239 / 2) as f64;
    let ood_probability = ROOT_CAPS
        .into_iter()
        .map(|root| list_pairs * (root as f64 / ood_space).powi(2))
        .sum::<f64>();
    let ood_bits = -ood_probability.log2();

    let terms = [
        (
            "polynomial_batch_width_29",
            batch_bits,
            SelectorScope::CommonPreselector,
        ),
        (
            "four_fold_union",
            folds_bits,
            SelectorScope::CommonPreselector,
        ),
        (
            "final_q18_miss_times_3",
            selected_query_bits,
            SelectorScope::FinalQueryMiss,
        ),
        (
            "two_sample_ood_list_union",
            ood_bits,
            SelectorScope::CommonPreselector,
        ),
        (
            "relation_ood_mixers_24",
            local_bits(24.0),
            SelectorScope::CommonPreselector,
        ),
        (
            "nonzero_gamma_and_three_point_batch_30",
            local_nonzero_bits(30.0),
            SelectorScope::CommonPreselector,
        ),
        (
            "copy_inactive_nonzero_gamma_28",
            local_nonzero_bits(28.0),
            SelectorScope::CommonPreselector,
        ),
        (
            "atomic_tuple_compression",
            local_bits(183.0 * 17.0),
            SelectorScope::CommonPreselector,
        ),
        (
            "atomic_copy_range_poles",
            local_bits(4.0 * (183.0 + 1_024.0)),
            SelectorScope::CommonPreselector,
        ),
        (
            "atomic_theta_collision",
            local_bits(24.0),
            SelectorScope::CommonPreselector,
        ),
        (
            "zerocheck_equality_point",
            local_bits(10.0),
            SelectorScope::CommonPreselector,
        ),
        (
            "zero_sum_h1_helper",
            local_bits(1.0),
            SelectorScope::CommonPreselector,
        ),
        (
            "mask_original_nonzero_eta",
            (FIELD_SIZE - 1.0).log2(),
            SelectorScope::CommonPreselector,
        ),
        (
            "ten_degree_27_zerocheck_rounds",
            local_bits(270.0),
            SelectorScope::CommonPreselector,
        ),
        (
            "poseidon2_assumption",
            124.0,
            SelectorScope::CommonPreselector,
        ),
        (
            "sha256_rom_assumption",
            128.0,
            SelectorScope::CommonPreselector,
        ),
    ];
    assert_eq!(
        terms
            .iter()
            .filter(|(_, _, scope)| *scope == SelectorScope::FinalQueryMiss)
            .map(|(name, _, _)| *name)
            .collect::<Vec<_>>(),
        ["final_q18_miss_times_3"]
    );
    let event_union_bits = union_bits(terms.iter().map(|(_, bits, _)| *bits));

    // Coarse sensitivity: start from Profile23's own unselected ledger, apply
    // the Profile23 BCS boundary count, then pessimistically multiply the
    // entire ledger by the three selector branches.  It is intentionally
    // distinct from the refined ledger above, where only the final q18 miss
    // receives the selector union.
    let coarse_event_union_bits = union_bits(terms.iter().map(|(_, bits, scope)| {
        if *scope == SelectorScope::FinalQueryMiss {
            raw_query_bits
        } else {
            *bits
        }
    }));

    // Work-normalized BCS/Fiat-Shamir instantiation with R=32, lambda=256 and
    // 1 <= T <= 2^128 random-oracle queries.  The maximum error is checked at
    // both interval endpoints.  At T=1 the leading factor is 1+R=33, not 32.
    let bcs_t_min = 1.0_f64;
    let bcs_t_max = 2.0_f64.powi(128);
    let bcs_selected_t1_bits = bcs_work_normalized_bits(event_union_bits, bcs_t_min);
    let bcs_selected_tmax_bits = bcs_work_normalized_bits(event_union_bits, bcs_t_max);
    let after_bcs_work_normalized_bits = bcs_selected_t1_bits.min(bcs_selected_tmax_bits);
    let after_factor40_bits = event_union_bits - 40.0_f64.log2();
    let bcs_coarse_t1_bits = bcs_work_normalized_bits(coarse_event_union_bits, bcs_t_min);
    let bcs_coarse_tmax_bits = bcs_work_normalized_bits(coarse_event_union_bits, bcs_t_max);
    let coarse_after_bcs_work_normalized_bits = bcs_coarse_t1_bits.min(bcs_coarse_tmax_bits);
    let coarse_whole_ledger_times_three_bits =
        coarse_after_bcs_work_normalized_bits - (SELECTORS as f64).log2();

    // EPRO inventory.  D is one full 1,024-coefficient QM31 mask lane:
    // 4,096 new M31 outputs, booked at two SHA inputs per output.  The three
    // q18 branches add two extra eight-block squeeze+advance streams. The
    // 64-draw cap still bounds each branch by eight blocks, so q18 does not
    // increase this worst-case distinct-input inventory. The
    // literal transcript also has three candidate-label absorbs and the
    // separate label-43 D-claims absorb.
    let leaves = 305_152u64;
    let profile22_field_outputs_m31 = 22_850u64;
    let d_field_outputs_m31 = 1_024u64 * 4;
    let field_expander_inputs = 2 * (profile22_field_outputs_m31 + d_field_outputs_m31);
    let query_squeeze_blocks = (PAYMENT_HIDING_QUERY_DRAW_LIMIT as u64 + 7) / 8;
    assert_eq!(query_squeeze_blocks, 8);
    let programmed_squeeze_inputs = 67u64 * 4 + SELECTORS * query_squeeze_blocks;
    let literal_absorb_inputs = 43u64 + 1 + SELECTORS;
    let work_predicate_inputs = 2 + FOLD_WORK.len() as u64;
    let transcript_inputs =
        literal_absorb_inputs + 2 * programmed_squeeze_inputs + work_predicate_inputs;
    let epro_inventory = 3 * leaves + field_expander_inputs + 8 + transcript_inputs;
    let q_h_log2 = 128.0;
    let leading_epro_bits = 256.0 - q_h_log2 - (ATTEMPTS as f64 * epro_inventory as f64).log2();
    // The EPRO hybrid compares one real execution with the common
    // witness-independent simulator.  The published two-witness statement
    // is Real(w0) -> Sim -> Real(w1), hence the explicit factor two.
    let pairwise_hiding_bits = leading_epro_bits - 1.0;
    let programmed_inputs = ATTEMPTS as f64 * epro_inventory as f64;
    let collision_bits = 256.0 - (programmed_inputs * (programmed_inputs - 1.0) / 2.0).log2();
    let max_work_bits = FOLD_WORK
        .into_iter()
        .chain([
            STATE_ONLY_PROFILE23_BATCH_GRINDING_BITS,
            STATE_ONLY_PROFILE23_GRINDING_BITS,
        ])
        .max()
        .expect("nonempty Profile23 work schedule");
    assert_eq!(max_work_bits, 37);
    let work_nonce_expected_hits_exponent = 64 - i32::from(max_work_bits);
    let work_exhaustion_bits = 2.0_f64.powi(work_nonce_expected_hits_exponent) / LN_2
        - (work_predicate_inputs as f64 * ATTEMPTS as f64).log2();

    // If a 64-draw q18 sampler fails, at least 47 draws duplicated one of at
    // most 17 accepted indices. This is completeness, not soundness.
    let max_unique_on_failure = QUERY_COUNT - 1;
    let duplicate_draws = PAYMENT_HIDING_QUERY_DRAW_LIMIT as u64 - max_unique_on_failure;
    assert_eq!((max_unique_on_failure, duplicate_draws), (17, 47));
    let log2_binomial_64_47 = (1..=duplicate_draws)
        .map(|i| {
            ((PAYMENT_HIDING_QUERY_DRAW_LIMIT as u64 - duplicate_draws + i) as f64 / i as f64)
                .log2()
        })
        .sum::<f64>();
    let sampler_one_bits = -(log2_binomial_64_47
        + duplicate_draws as f64 * (max_unique_on_failure as f64 / QUERY_FIBERS).log2());
    let sampler_cap17_m3_bits = sampler_one_bits - ((ATTEMPTS * SELECTORS) as f64).log2();

    // Initial exact pins are printed below; close calls make every subsequent
    // protocol/count change an explicit repin rather than a silent drift.
    close(batch_bits, 107.316_020_114_355_38);
    close(raw_query_bits, 111.768_701_634_364_65);
    close(selected_query_bits, 110.183_739_133_643_48);
    for (actual, expected) in fold_rows.iter().copied().zip([
        109.529_942_692_338_42,
        111.226_281_804_531_75,
        112.858_135_080_222_61,
        113.840_648_013_834_85,
    ]) {
        close(actual, expected);
    }
    close(folds_bits, 108.985_432_265_750_69);
    close(event_union_bits, 106.702_033_487_302_9);
    close(bcs_selected_t1_bits, 101.657_639_367_944_44);
    close(bcs_selected_tmax_bits, 106.702_031_808_619_58);
    close(after_bcs_work_normalized_bits, 101.657_639_367_944_44);
    close(after_factor40_bits, 101.380_105_392_415_53);
    close(coarse_event_union_bits, 106.790_806_002_954_17);
    close(bcs_coarse_t1_bits, 101.746_411_883_595_71);
    close(bcs_coarse_tmax_bits, 106.790_804_217_733_32);
    close(coarse_whole_ledger_times_three_bits, 100.161_449_382_874_55);
    assert_eq!(field_expander_inputs, 53_892);
    assert_eq!(programmed_squeeze_inputs, 292);
    assert_eq!(literal_absorb_inputs, 47);
    assert_eq!(transcript_inputs, 637);
    assert_eq!(epro_inventory, 969_993);
    close(leading_epro_bits, 104.024_922_348_251_98);
    close(pairwise_hiding_bits, 103.024_922_348_251_98);
    close(collision_bits, 209.049_844_783_993_68);
    close(work_exhaustion_bits, 193_635_243.912_558_44);
    close(sampler_one_bits, 556.596_315_359_622);
    close(sampler_cap17_m3_bits, 550.923_890_017_650_6);

    println!("profile23_candidate_query_count={QUERY_COUNT}");
    println!("profile23_candidate_batch_work_bits={STATE_ONLY_PROFILE23_BATCH_GRINDING_BITS}");
    println!("profile23_candidate_fold_work_bits={FOLD_WORK:?}");
    println!("profile23_candidate_final_work_bits={STATE_ONLY_PROFILE23_GRINDING_BITS}");
    println!("profile23_candidate_attempt_cap={ATTEMPTS}");
    println!("profile23_selector_scope_propositional_cases={selector_scope_cases}");
    for (name, bits, _) in terms {
        println!("profile23_soundness_term_{name}={bits:.13}");
    }
    println!("profile23_soundness_event_union_bits={event_union_bits:.13}");
    println!("profile23_soundness_bcs_t1_bits={bcs_selected_t1_bits:.13}");
    println!("profile23_soundness_bcs_t2p128_bits={bcs_selected_tmax_bits:.13}");
    println!(
        "profile23_soundness_after_bcs_work_normalized_bits={after_bcs_work_normalized_bits:.13}"
    );
    println!("profile23_soundness_after_factor40_bits={after_factor40_bits:.13}");
    println!(
        "profile23_soundness_coarse_whole_ledger_times_three_bits={coarse_whole_ledger_times_three_bits:.13}"
    );
    println!("profile23_epro_field_expander_inputs={field_expander_inputs}");
    println!("profile23_epro_transcript_inputs={transcript_inputs}");
    println!("profile23_epro_inventory={epro_inventory}");
    println!("profile23_epro_leading_bits={leading_epro_bits:.13}");
    println!("profile23_epro_pairwise_witness_bits={pairwise_hiding_bits:.13}");
    println!("profile23_epro_collision_bits={collision_bits:.13}");
    println!("profile23_epro_work_exhaustion_bits={work_exhaustion_bits:.8}");
    println!("profile23_sampler_cap17_m3_union_bits={sampler_cap17_m3_bits:.13}");

    let independent_arithmetic_bookable =
        coarse_whole_ledger_times_three_bits >= 100.0 && pairwise_hiding_bits >= 100.0;
    assert!(
        independent_arithmetic_bookable,
        "Profile23 q18 independent arithmetic is below the release floor"
    );
    println!("profile23_independent_arithmetic_bookable={independent_arithmetic_bookable}");

    let liveness = PROFILE23_Q18_GOOD_LIVENESS_PINS.expect(
        "Profile23 q18 complete-Good liveness pins are missing; normal release mode is fail-closed",
    );
    // The complete Good predicate additionally retains two independent raw
    // 12-M31 terminal certificates: the remaining G/D direction and H1
    // inactive padding. Each contributes 12*10=120 degrees.
    let complete_good_z_degree = liveness.root_neutral_minor_z_degree + 120.0 + 120.0;
    let continuous_degree = complete_good_z_degree + liveness.gamma_degree;
    let query_sampling_denominator = QUERY_FIBERS - (QUERY_COUNT - 1) as f64;
    close(query_sampling_denominator, 131_055.0);
    let rho_query = liveness.query_degree / query_sampling_denominator;
    let beta_attempt = continuous_degree / P + rho_query.powi(SELECTORS as i32);
    let bits_per_attempt = -beta_attempt.log2();
    let rank_exhaustion_cap17_bits = ATTEMPTS as f64 * bits_per_attempt;
    let build_abort = 128.0 / P.powi(6);
    let public_abort_probability =
        ATTEMPTS as f64 * build_abort + beta_attempt.powf(ATTEMPTS as f64);
    let public_abort_bits = -public_abort_probability.log2();
    close(complete_good_z_degree, liveness.complete_good_z_degree);
    close(continuous_degree, liveness.continuous_degree);
    close(rho_query, liveness.rho_query);
    close(beta_attempt, liveness.beta_attempt);
    close(bits_per_attempt, liveness.bits_per_attempt);
    close(
        rank_exhaustion_cap17_bits,
        liveness.rank_exhaustion_cap17_bits,
    );
    close(public_abort_bits, liveness.public_abort_bits);
    println!("profile23_rho_query={rho_query:.16}");
    println!("profile23_beta_attempt={beta_attempt:.16}");
    println!("profile23_cap17_rank_exhaustion_bits={rank_exhaustion_cap17_bits:.13}");
    println!("profile23_public_abort_bits={public_abort_bits:.13}");
    println!(
        "profile23_root_minor_fingerprint=0x{:016x}",
        liveness.root_minor_fingerprint
    );
    println!(
        "profile23_remaining_gd_minor_fingerprint=0x{:016x}",
        liveness.remaining_gd_minor_fingerprint
    );
    println!(
        "profile23_h1_minor_fingerprint=0x{:016x}",
        liveness.h1_minor_fingerprint
    );
    println!(
        "profile23_product_fingerprint=0x{:016x}",
        liveness.product_fingerprint
    );
    let liveness_bookable = rank_exhaustion_cap17_bits >= 100.0 && public_abort_bits >= 100.0;
    assert!(
        liveness_bookable,
        "Profile23 q18 cap-17 complete-Good liveness is below the release floor"
    );
    println!("profile23_liveness_bookable={liveness_bookable}");

    if calculation_only {
        println!("profile23_good_liveness_artifact_check_skipped=true");
        println!("profile23_calculation_only=true");
        return;
    }

    let complete_good_path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../results/stage2/profile23_complete_good_product.json");
    let complete_good_bytes = std::fs::read(&complete_good_path)
        .unwrap_or_else(|error| panic!("read {}: {error}", complete_good_path.display()));
    let complete_good: serde_json::Value = serde_json::from_slice(&complete_good_bytes)
        .unwrap_or_else(|error| panic!("parse {}: {error}", complete_good_path.display()));
    let fingerprint = |value: u64| format!("0x{value:016x}");
    let root_minor_fingerprint = fingerprint(liveness.root_minor_fingerprint);
    let remaining_gd_minor_fingerprint = fingerprint(liveness.remaining_gd_minor_fingerprint);
    let h1_minor_fingerprint = fingerprint(liveness.h1_minor_fingerprint);
    let product_fingerprint = fingerprint(liveness.product_fingerprint);
    assert_eq!(
        complete_good["artifact"].as_str(),
        Some("profile23_complete_good_product")
    );
    assert_eq!(
        complete_good["root_neutral_minor"]["fingerprint"].as_str(),
        Some(root_minor_fingerprint.as_str())
    );
    assert_eq!(
        complete_good["remaining_gd_terminal_schur"]["fingerprint"].as_str(),
        Some(remaining_gd_minor_fingerprint.as_str())
    );
    assert_eq!(
        complete_good["h1_inactive_padding_terminal_schur"]["fingerprint"].as_str(),
        Some(h1_minor_fingerprint.as_str())
    );
    assert_eq!(
        complete_good["bound_product"]["fingerprint"].as_str(),
        Some(product_fingerprint.as_str())
    );
    assert_eq!(
        complete_good["bound_product"]["q_total_degree_bound"].as_u64(),
        Some(liveness.query_degree as u64)
    );
    assert_eq!(
        complete_good["bound_product"]["root_neutral_z_degree_bound"].as_u64(),
        Some(liveness.root_neutral_minor_z_degree as u64)
    );
    assert_eq!(
        complete_good["bound_product"]["complete_good_z_degree_bound"].as_u64(),
        Some(liveness.complete_good_z_degree as u64)
    );
    assert_eq!(
        complete_good["bound_product"]["gamma_coordinate_total_degree_bound"].as_u64(),
        Some(liveness.gamma_degree as u64)
    );
    assert_eq!(
        complete_good["bound_product"]["continuous_total_degree_bound"].as_u64(),
        Some(liveness.continuous_degree as u64)
    );
    assert_eq!(
        complete_good["bound_product"]["complete"].as_bool(),
        Some(true)
    );
    assert_eq!(
        complete_good["liveness_bound_bookable_for_prospective_profile23"].as_bool(),
        Some(true)
    );

    let release_path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../results/stage2/profile23_one_transaction_release.json");
    let release_bytes = std::fs::read(&release_path)
        .unwrap_or_else(|error| panic!("read {}: {error}", release_path.display()));
    let release: serde_json::Value = serde_json::from_slice(&release_bytes)
        .unwrap_or_else(|error| panic!("parse {}: {error}", release_path.display()));
    let theorem_bookable = independent_arithmetic_bookable && liveness_bookable;
    assert!(
        theorem_bookable,
        "Profile23 q18 theorem ledger is not bookable"
    );
    println!("profile23_bookable={theorem_bookable}");

    assert_eq!(
        release["released"].as_bool(),
        Some(true),
        "normal mode requires a current green Profile23 release; use --calculation-only while q18 release evidence is pending"
    );
    let release_selected_soundness = release["selected_soundness_floor_bits"]
        .as_f64()
        .expect("Profile23 release omitted selected soundness floor");
    let release_coarse_soundness = release["coarse_whole_soundness_floor_bits"]
        .as_f64()
        .expect("Profile23 release omitted coarse soundness floor");
    let release_real_vs_simulator = release["computational_hiding_real_vs_simulator_bound_bits"]
        .as_f64()
        .expect("Profile23 release omitted real-vs-simulator hiding floor");
    let release_pairwise = release["computational_hiding_pairwise_witness_bound_bits"]
        .as_f64()
        .expect("Profile23 release omitted pairwise hiding floor");
    close(release_selected_soundness, after_factor40_bits);
    close(
        release_coarse_soundness,
        coarse_whole_ledger_times_three_bits,
    );
    close(release_real_vs_simulator, leading_epro_bits);
    close(release_pairwise, pairwise_hiding_bits);
    let release_bookable = release["failed_gates"]
        .as_array()
        .is_some_and(Vec::is_empty)
        && release["max_literal_production_tag65_cu"]
            .as_u64()
            .is_some_and(|cu| cu <= 1_400_000)
        && release_selected_soundness >= 100.0
        && release_real_vs_simulator >= 100.0
        && release_pairwise >= 100.0;
    assert!(
        release_bookable,
        "claimed Profile23 release certificate is not bookable"
    );
    println!("profile23_release_bookable=true");
}
