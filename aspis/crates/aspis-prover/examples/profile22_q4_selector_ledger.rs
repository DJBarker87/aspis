//! Arithmetic guard for the conditional profile-22 four-query-selector design.
//!
//! This executable does not prove the required polynomial-kernel minor or
//! enable the selector wire.  It freezes the probability, soundness and EPRO
//! arithmetic that becomes usable only after those algebraic and protocol
//! gates close.

fn union_bits(bits: impl IntoIterator<Item = f64>) -> f64 {
    -bits
        .into_iter()
        .map(|bits| 2.0_f64.powf(-bits))
        .sum::<f64>()
        .log2()
}

fn close(actual: f64, expected: f64) {
    assert!(
        (actual - expected).abs() < 1e-9,
        "numeric repin: actual={actual:.15}, expected={expected:.15}"
    );
}

fn main() {
    const P: f64 = 2_147_483_647.0;
    const QUERY_FIBERS: f64 = 131_072.0;
    const QUERY_COUNT: f64 = 16.0;
    // Mixed polynomial-kernel witness: 880 selected common-tail columns have
    // q degree one, 524 selected full-domain balanced columns have numerator
    // degree two, and the one shared balance denominator contributes 16 to
    // the total-degree union after clearing.
    const QUERY_DEGREE: f64 = 30_864.0;
    const CONTINUOUS_DEGREE: f64 = 41_040.0;
    const SELECTORS: i32 = 4;
    const ATTEMPTS: f64 = 16.0;

    let rho_query = QUERY_DEGREE / (QUERY_FIBERS - (QUERY_COUNT - 1.0));
    let beta_attempt = CONTINUOUS_DEGREE / P + rho_query.powi(SELECTORS);
    let bits_per_attempt = -beta_attempt.log2();
    let cap16_rank_exhaustion_bits = ATTEMPTS * bits_per_attempt;

    close(rho_query, 0.235_500_583_715_482_58);
    close(beta_attempt, 0.003_094_980_564_788_099);
    close(bits_per_attempt, 8.335_853_934_728_805);
    close(cap16_rank_exhaustion_bits, 133.373_662_955_660_88);

    // Only the final q16 miss event receives the four-way malicious-selector
    // union. Every other row precedes the selector in the frozen transcript.
    let mut soundness_terms = [
        108.368_487_534_249_52, // width-28 batching after g38
        112.079_790_788_536_77, // four-fold union
        108.901_886_597_240_66, // q16 miss after final g38
        213.100_018_394_892_15, // two-sample OOD list union
        119.415_037_496_591_61,
        119.142_019_002_185_2,
        119.245_112_495_149_3,
        112.396_837_317_778_39,
        111.762_790_036_557_75,
        119.415_037_496_591_61,
        120.678_071_902_425_4,
        123.999_999_997_312_77,
        123.999_999_997_312_77,
        115.923_184_400_261_93,
        124.0,
        128.0,
    ];
    soundness_terms[2] -= f64::from(SELECTORS).log2();
    let event_union_bits = union_bits(soundness_terms);
    let after_bcs31_bits = event_union_bits - 31.0_f64.log2();
    let after_factor40_bits = event_union_bits - 40.0_f64.log2();

    close(event_union_bits, 106.367_023_363_140_75);
    close(after_bcs31_bits, 101.412_827_052_753_87);
    close(after_factor40_bits, 101.045_095_268_253_38);
    assert!(after_factor40_bits > 100.0);

    // Four hidden candidate streams replace one stream. At the bounded eight
    // blocks per stream this adds 48 squeeze/advance oracle inputs, and the
    // four domain-tagged selector absorbs add another four inputs.
    let transcript_inputs = 601u64 + 48 + 4;
    let epro_inventory = 3 * 305_152u64 + 45_700 + 8 + transcript_inputs;
    let epro_leading_bits = 256.0 - 128.0 - (ATTEMPTS * epro_inventory as f64).log2();
    assert_eq!(transcript_inputs, 653);
    assert_eq!(epro_inventory, 961_817);
    close(epro_leading_bits, 104.124_597_099_662_58);

    // If a 64-draw q16 sampler fails, at least 49 draws duplicated one of at
    // most 15 accepted indices. This is a completeness abort, not soundness.
    let log2_binomial_64_49 = (1..=49)
        .map(|i| ((64 - 49 + i) as f64 / i as f64).log2())
        .sum::<f64>();
    let sampler_one_bits = -(log2_binomial_64_49 + 49.0 * (15.0 / QUERY_FIBERS).log2());
    let sampler_cap16_m4_bits = sampler_one_bits - (ATTEMPTS * f64::from(SELECTORS)).log2();
    close(sampler_one_bits, 594.381_639_217_156_7);
    close(sampler_cap16_m4_bits, 588.381_639_217_156_7);

    println!("profile22_q4_conditional_rho_query={rho_query:.16}");
    println!("profile22_q4_conditional_beta_attempt={beta_attempt:.16}");
    println!("profile22_q4_conditional_cap16_rank_bits={cap16_rank_exhaustion_bits:.13}");
    println!("profile22_q4_soundness_event_union_bits={event_union_bits:.13}");
    println!("profile22_q4_soundness_after_bcs31_bits={after_bcs31_bits:.13}");
    println!("profile22_q4_soundness_factor40_bits={after_factor40_bits:.13}");
    println!("profile22_q4_epro_inventory={epro_inventory}");
    println!("profile22_q4_epro_qh128_r16_leading_bits={epro_leading_bits:.13}");
    println!("profile22_q4_sampler_cap16_union_bits={sampler_cap16_m4_bits:.13}");
    println!("profile22_q4_bookable=false");
}
