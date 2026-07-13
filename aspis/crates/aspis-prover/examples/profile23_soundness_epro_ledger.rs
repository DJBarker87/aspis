//! Arithmetic and release guard for the profile-23 D-after-G, q3 design.
//!
//! This executable pins the term-by-term Johnson soundness union, the
//! three-candidate rank-exhaustion/liveness bound, and the literal EPRO input
//! inventory. It also requires the fail-closed one-transaction release
//! certificate; it does not replace the separate root-neutral polynomial-
//! kernel and complete-view proofs.

use std::collections::HashSet;
use std::f64::consts::LN_2;
use std::path::Path;

use aspis_core::circle_prefix::RATE16_HARDENED_FOLD_POW_BITS;
use aspis_core::field::{M31, P as M31_MODULUS};
use aspis_core::state_only_hiding::{
    STATE_ONLY_PROFILE23_D_GENERATOR_INDEX, STATE_ONLY_PROFILE23_G_GENERATOR_INDEX,
    STATE_ONLY_PROFILE23_QUERY_CANDIDATES, STATE_ONLY_PROFILE23_TOTAL_GENERATOR_WIDTH,
};
use aspis_core::state_only_prefix::{
    STATE_ONLY_LOG_ROWS, STATE_ONLY_PROFILE23_BATCH_GRINDING_BITS,
    STATE_ONLY_PROFILE23_D_CLAIM_COUNT, STATE_ONLY_PROFILE23_GRINDING_BITS,
    STATE_ONLY_PROFILE23_QUERY_CANDIDATE_COUNT,
};
use aspis_core::transcript::label;

const P: f64 = M31_MODULUS as f64;
const FIELD_SIZE: f64 = P * P * P * P;
const JOHNSON_MULTIPLICITY: f64 = 10.0;
const FOLD_WORK: [u8; 4] = [39, 35, 31, 27];
const ROOT_CAPS: [u64; 4] = [1_024, 255, 63, 15];
const QUERY_FIBERS: f64 = 131_072.0;
const QUERY_COUNT: f64 = 16.0;
const SELECTORS: i32 = 3;
const ATTEMPTS: f64 = 16.0;

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

fn close(actual: f64, expected: f64) {
    assert!(
        (actual - expected).abs() < 1e-9,
        "numeric repin: actual={actual:.15}, expected={expected:.15}"
    );
}

fn main() {
    assert_eq!(STATE_ONLY_PROFILE23_TOTAL_GENERATOR_WIDTH, 29);
    assert_eq!(STATE_ONLY_PROFILE23_G_GENERATOR_INDEX, 27);
    assert_eq!(STATE_ONLY_PROFILE23_D_GENERATOR_INDEX, 28);
    assert_eq!(STATE_ONLY_PROFILE23_QUERY_CANDIDATES, 3);
    assert_eq!(STATE_ONLY_PROFILE23_QUERY_CANDIDATE_COUNT, 3);
    assert_eq!(STATE_ONLY_PROFILE23_D_CLAIM_COUNT, 3);
    assert_eq!(STATE_ONLY_PROFILE23_BATCH_GRINDING_BITS, 38);
    assert_eq!(STATE_ONLY_PROFILE23_GRINDING_BITS, 38);
    assert_eq!(RATE16_HARDENED_FOLD_POW_BITS, FOLD_WORK);
    assert_eq!(label::M31_STATE_ONLY_ZERO_FACTOR_D_CLAIMS, 43);
    assert_eq!(label::M31_STATE_ONLY_QUERY_CANDIDATE, 44);

    // The executable root-neutral minor selects 1,404 columns.  Its safe
    // M31-scalar inverse clearing gives q-degree 28,544.  The exhaustive
    // implemented-domain check below proves that q-root one cannot occur, so
    // the old hypothetical degree-16 anchor guard is unnecessary.  The z and
    // gamma degrees are 41,040 and 92,436.  These are deliberately not
    // replaced by the invalid QM31 column-rescaling shortcut.
    let query_degree = 28_544.0;
    let root_neutral_minor_z_degree = 41_040.0;
    // The complete Good predicate additionally retains two independent raw
    // 12-M31 terminal certificates: the remaining G/D direction and H1
    // inactive padding.  Each contributes 12*10=120 degrees.  Keep both
    // separate from the D-after-G root-neutral minor so the determinants
    // cannot be silently conflated or double-counted.
    let remaining_gd_terminal_z_degree = 120.0;
    let h1_padding_terminal_z_degree = 120.0;
    let complete_good_z_degree =
        root_neutral_minor_z_degree + remaining_gd_terminal_z_degree + h1_padding_terminal_z_degree;
    let gamma_degree = 92_436.0;
    let continuous_degree = complete_good_z_degree + gamma_degree;
    let rho_query = query_degree / (QUERY_FIBERS - (QUERY_COUNT - 1.0));
    let beta_attempt = continuous_degree / P + rho_query.powi(SELECTORS);
    let bits_per_attempt = -beta_attempt.log2();
    let cap16_rank_exhaustion_bits = ATTEMPTS * bits_per_attempt;

    // A bounded source construction uses at most 128*p^-6 per attempt.  Rank
    // exhaustion happens only when all 16 independent attempts are bad.
    let build_abort = 128.0 / P.powi(6);
    let public_abort_probability = ATTEMPTS * build_abort + beta_attempt.powf(ATTEMPTS);
    let public_abort_bits = -public_abort_probability.log2();

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

    // Johnson / MCA terms.  Only the final q16 miss term receives the
    // malicious-selector union.  D changes the polynomial batching degree
    // 27->28, gamma numerator 29->30, and inactive-copy numerator 27->28.
    let rho: f64 = 1.0 / 512.0;
    let agreement_fraction = (1.0 + 1.0 / (2.0 * JOHNSON_MULTIPLICITY)) * rho.sqrt();
    let query_fibers = 131_072u64;
    let agreement_fibers = (agreement_fraction * query_fibers as f64).floor() as u64;
    assert_eq!(agreement_fibers, 6_082);

    let ell = (JOHNSON_MULTIPLICITY + 0.5) / rho.sqrt();
    let batch_numerator = 28.0 * ell * ((2.0 * ell.powi(4) / 3.0) * rho + 1.0) * 524_288.0;
    let batch_bits = (FIELD_SIZE / batch_numerator).log2() + 38.0;

    let raw_query_bits = (0..16u64)
        .map(|i| -((agreement_fibers - i) as f64 / (query_fibers - i) as f64).log2())
        .sum::<f64>()
        + 38.0;
    let selected_query_bits = raw_query_bits - f64::from(SELECTORS).log2();

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
        ("polynomial_batch_width_29", batch_bits),
        ("four_fold_union", folds_bits),
        ("final_q16_miss_times_3", selected_query_bits),
        ("two_sample_ood_list_union", ood_bits),
        ("relation_ood_mixers_24", local_bits(24.0)),
        (
            "nonzero_gamma_and_three_point_batch_30",
            local_nonzero_bits(30.0),
        ),
        ("copy_inactive_nonzero_gamma_28", local_nonzero_bits(28.0)),
        ("atomic_tuple_compression", local_bits(183.0 * 17.0)),
        (
            "atomic_copy_range_poles",
            local_bits(4.0 * (183.0 + 1_024.0)),
        ),
        ("atomic_theta_collision", local_bits(24.0)),
        ("zerocheck_equality_point", local_bits(10.0)),
        ("zero_sum_h1_helper", local_bits(1.0)),
        ("mask_original_nonzero_eta", (FIELD_SIZE - 1.0).log2()),
        ("ten_degree_27_zerocheck_rounds", local_bits(270.0)),
        ("poseidon2_assumption", 124.0),
        ("sha256_rom_assumption", 128.0),
    ];
    let event_union_bits = union_bits(terms.iter().map(|(_, bits)| *bits));

    // Coarse sensitivity: start from Profile23's own unselected ledger, apply
    // the Profile23 BCS boundary count, then pessimistically multiply the
    // entire ledger by the three selector branches.  It is intentionally
    // distinct from the refined ledger above, where only the final q16 miss
    // receives the selector union.
    let coarse_event_union_bits = union_bits(terms.iter().map(|(name, bits)| {
        if *name == "final_q16_miss_times_3" {
            raw_query_bits
        } else {
            *bits
        }
    }));

    // Profile 23 adds a prover-selected message boundary between the final
    // nonce and q16.  The conservative BCS compiler factor is therefore 32,
    // not profile 22's factor 31.  Factor 40 remains the selected sensitivity
    // floor used by the release ledger.
    let bcs_boundary_factor = 32.0_f64;
    let after_bcs32_bits = event_union_bits - bcs_boundary_factor.log2();
    let after_factor40_bits = event_union_bits - 40.0_f64.log2();
    let coarse_whole_ledger_times_three_bits =
        coarse_event_union_bits - bcs_boundary_factor.log2() - f64::from(SELECTORS).log2();

    // EPRO inventory.  D is one full 1,024-coefficient QM31 mask lane:
    // 4,096 new M31 outputs, booked at two SHA inputs per output.  The three
    // q16 branches add two extra eight-block squeeze+advance streams.  The
    // literal transcript also has three candidate-label absorbs and the
    // separate label-43 D-claims absorb.
    let leaves = 305_152u64;
    let profile22_field_outputs_m31 = 22_850u64;
    let d_field_outputs_m31 = 1_024u64 * 4;
    let field_expander_inputs = 2 * (profile22_field_outputs_m31 + d_field_outputs_m31);
    let programmed_squeeze_inputs = 67u64 * 4 + SELECTORS as u64 * 8;
    let literal_absorb_inputs = 43u64 + 1 + SELECTORS as u64;
    let work_predicate_inputs = 6u64;
    let transcript_inputs =
        literal_absorb_inputs + 2 * programmed_squeeze_inputs + work_predicate_inputs;
    let epro_inventory = 3 * leaves + field_expander_inputs + 8 + transcript_inputs;
    let q_h_log2 = 128.0;
    let leading_epro_bits = 256.0 - q_h_log2 - (ATTEMPTS * epro_inventory as f64).log2();
    // The EPRO hybrid compares one real execution with the common
    // witness-independent simulator.  The published two-witness statement
    // is Real(w0) -> Sim -> Real(w1), hence the explicit factor two.
    let pairwise_hiding_bits = leading_epro_bits - 1.0;
    let programmed_inputs = ATTEMPTS * epro_inventory as f64;
    let collision_bits = 256.0 - (programmed_inputs * (programmed_inputs - 1.0) / 2.0).log2();
    let work_exhaustion_bits = 2.0_f64.powi(25) / LN_2 - (6.0 * ATTEMPTS).log2();

    // If a 64-draw q16 sampler fails, at least 49 draws duplicated one of at
    // most 15 accepted indices.  This is completeness, not soundness.
    let log2_binomial_64_49 = (1..=49)
        .map(|i| ((64 - 49 + i) as f64 / i as f64).log2())
        .sum::<f64>();
    let sampler_one_bits = -(log2_binomial_64_49 + 49.0 * (15.0 / QUERY_FIBERS).log2());
    let sampler_cap16_m3_bits = sampler_one_bits - (ATTEMPTS * f64::from(SELECTORS)).log2();

    // Initial exact pins are printed below; close calls make every subsequent
    // protocol/count change an explicit repin rather than a silent drift.
    close(rho_query, 0.217_798_362_544_541_68);
    close(beta_attempt, 0.010_393_777_091_336_816);
    close(bits_per_attempt, 6.588_136_165_878_648);
    close(cap16_rank_exhaustion_bits, 105.410_178_654_058_37);
    close(public_abort_bits, 105.410_178_654_058_37);
    close(batch_bits, 108.316_020_114_355_38);
    close(selected_query_bits, 107.316_924_096_519_47);
    close(event_union_bits, 106.624_234_677_717_88);
    close(after_bcs32_bits, 101.624_234_677_717_88);
    close(after_factor40_bits, 101.302_306_582_830_51);
    close(coarse_whole_ledger_times_three_bits, 100.806_528_614_227_49);
    assert_eq!(field_expander_inputs, 53_892);
    assert_eq!(programmed_squeeze_inputs, 292);
    assert_eq!(literal_absorb_inputs, 47);
    assert_eq!(transcript_inputs, 637);
    assert_eq!(epro_inventory, 969_993);
    close(leading_epro_bits, 104.112_385_189_502_32);
    close(pairwise_hiding_bits, 103.112_385_189_502_32);
    close(collision_bits, 209.224_770_471_962_47);
    close(work_exhaustion_bits, 48_408_806.061_283_44);
    close(sampler_cap16_m3_bits, 588.796_676_716_435_5);

    println!("profile23_rho_query={rho_query:.16}");
    println!("profile23_beta_attempt={beta_attempt:.16}");
    println!("profile23_cap16_rank_exhaustion_bits={cap16_rank_exhaustion_bits:.13}");
    println!("profile23_public_abort_bits={public_abort_bits:.13}");
    for (name, bits) in terms {
        println!("profile23_soundness_term_{name}={bits:.13}");
    }
    println!("profile23_soundness_event_union_bits={event_union_bits:.13}");
    println!("profile23_soundness_after_bcs32_bits={after_bcs32_bits:.13}");
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
    println!("profile23_sampler_cap16_m3_union_bits={sampler_cap16_m3_bits:.13}");

    let release_path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../results/stage2/profile23_one_transaction_release.json");
    let release_bytes = std::fs::read(&release_path)
        .unwrap_or_else(|error| panic!("read {}: {error}", release_path.display()));
    let release: serde_json::Value = serde_json::from_slice(&release_bytes)
        .unwrap_or_else(|error| panic!("parse {}: {error}", release_path.display()));
    let bookable = after_factor40_bits >= 100.0
        && coarse_whole_ledger_times_three_bits >= 100.0
        && pairwise_hiding_bits >= 100.0
        && release["released"].as_bool() == Some(true)
        && release["failed_gates"]
            .as_array()
            .is_some_and(Vec::is_empty)
        && release["max_literal_production_tag60_cu"]
            .as_u64()
            .is_some_and(|cu| cu <= 1_400_000)
        && release["coarse_whole_soundness_floor_bits"]
            .as_f64()
            .is_some_and(|bits| bits >= 100.0)
        && release["computational_hiding_real_vs_simulator_bound_bits"]
            .as_f64()
            .is_some_and(|bits| bits >= 100.0)
        && release["computational_hiding_pairwise_witness_bound_bits"]
            .as_f64()
            .is_some_and(|bits| bits >= 100.0);
    assert!(bookable, "Profile23 release certificate is not bookable");
    println!("profile23_bookable={bookable}");
}
