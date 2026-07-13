use aspis_prover::state_only_hiding_rank::profile21_high_switch_carry_certificate;

fn assert_certificate(queries: &[u32]) {
    let certificate = profile21_high_switch_carry_certificate(queries).unwrap();
    assert_eq!(certificate.query_count, 16);
    assert!(certificate.distinct_abscissae);
    assert_eq!(certificate.evaluation_plus_leading_rank_qm31, 17);
    assert_ne!(certificate.vanishing_witness_natural_coefficient_18, 0);
}

#[test]
fn high_coefficient_carry_is_full_on_structured_q16_schedules() {
    assert_certificate(&[
        44_925, 13_356, 15_947, 88_889, 31_631, 19_948, 123_543, 53_452, 97_905, 114_664, 49_080,
        10_990, 125_912, 3_319, 128_135, 77_542,
    ]);
    assert_certificate(&(0..16).collect::<Vec<_>>());
    assert_certificate(&(0..16).map(|index| index * 8_191).collect::<Vec<_>>());
    assert_certificate(&(0..16).map(|index| index << 13).collect::<Vec<_>>());
    // One complete T_16 fiber in the production root-one domain.  This is a
    // deliberately subgroup-shaped tuple, not a random-regression sample.
    assert_certificate(&(50_752..50_768).collect::<Vec<_>>());
}

#[test]
fn high_coefficient_carry_certificate_survives_deterministic_fuzz() {
    const DOMAIN: u32 = 1 << 17;
    let mut state = 0x8e31_d4a7u32;
    for _ in 0..64 {
        let mut queries = Vec::with_capacity(16);
        while queries.len() < 16 {
            state = state.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
            let query = state & (DOMAIN - 1);
            if !queries.contains(&query) {
                queries.push(query);
            }
        }
        assert_certificate(&queries);
    }
}
