//! Geometry-only probe for mapping Plonky3's prefix-interleaved HVZK-WHIR
//! pipeline to the frozen Aspis rate-1/32, q29, arity-four circle profile.
//!
//! This test deliberately performs no encoding and makes no circle-HVZK
//! theorem claim.  It pins the dimensions that an implementation and an
//! eventual commutative-diagram proof must realize.

const TRACE_VARIABLES: usize = 10;
const FOLD_VARIABLES: usize = 2;
const FOLD_WIDTH: usize = 1 << FOLD_VARIABLES;
const FOLD_BATCHES: usize = 4;
const CODE_SWITCH_ROUNDS: usize = FOLD_BATCHES - 1;
const LOG_INV_RATE: usize = 5;
const ORACLE_QUERIES: usize = 29;
const OOD_SAMPLES: usize = 2;

const TARGET_BITS: usize = 100;
const MASK_UNION_BITS: usize = 3; // ceil(log2(2 * 3 + 2)).
const MASK_LOG_INV_RATE: usize = 5;

// Plonky3's implemented WHIR source claim is quadratic, so ell_zk = 3 is
// sufficient there.  Aspis has two different objects and they must not be
// conflated:
// - four internal arity-four PCS relation sumcheck batches of degree six;
// - one external ten-round statement zerocheck of degree 27.
// A generalized Construction-6.3-style mask would need degree-covering
// message lengths seven and 28 respectively.  Geometry is not that lemma.
const UPSTREAM_PCS_ELL_ZK: usize = 3;
const ASPIS_PCS_DEGREE_6_ELL_ZK: usize = 7;
const ASPIS_EXTERNAL_DEGREE_27_ELL_ZK: usize = 28;
const EXTERNAL_ZEROCHECK_MASK_WIDTH: usize = 10;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct OracleGeometry {
    stage: usize,
    source_message: usize,
    limb_message: usize,
    randomness_per_limb: usize,
    randomness_total: usize,
    leaf_rows: usize,
    padded_dimension: usize,
    limb_degree: usize,
    folded_message: usize,
}

fn oracle_geometry(stage: usize) -> OracleGeometry {
    let source_message = 1usize << (TRACE_VARIABLES - FOLD_VARIABLES * stage);
    let limb_message = source_message / FOLD_WIDTH;
    let leaf_rows = limb_message << LOG_INV_RATE;
    OracleGeometry {
        stage,
        source_message,
        limb_message,
        randomness_per_limb: ORACLE_QUERIES,
        randomness_total: ORACLE_QUERIES * FOLD_WIDTH,
        leaf_rows,
        padded_dimension: limb_message + ORACLE_QUERIES,
        limb_degree: limb_message + ORACLE_QUERIES - 1,
        folded_message: limb_message,
    }
}

fn johnson_bits_per_query(log_inv_rate: usize) -> f64 {
    // Upstream SecurityAssumption::JohnsonBound uses
    //   1 - delta = sqrt(rho) + sqrt(rho)/20.
    let rho = 2f64.powi(-(log_inv_rate as i32));
    -(rho.sqrt() * 1.05).log2()
}

fn johnson_bits_per_query_from_rate(rate: f64) -> f64 {
    -(rate.sqrt() * 1.05).log2()
}

fn johnson_queries(bits: usize, log_inv_rate: usize) -> usize {
    (bits as f64 / johnson_bits_per_query(log_inv_rate)).ceil() as usize
}

fn next_power_of_two(value: usize) -> usize {
    value.next_power_of_two()
}

fn mask_domain(message_len: usize, queries: usize, log_inv_rate: usize) -> usize {
    next_power_of_two(message_len + queries) << log_inv_rate
}

fn min_self_consistent_source_queries(
    message_len: usize,
    domain_size: usize,
    target_bits: f64,
    work_bits: f64,
) -> Option<(usize, f64)> {
    (1..domain_size - message_len).find_map(|queries| {
        let rate = (message_len + queries) as f64 / domain_size as f64;
        let per_query = johnson_bits_per_query_from_rate(rate);
        let bits = queries as f64 * per_query + work_bits;
        (per_query > 0.0 && bits >= target_bits).then_some((queries, bits))
    })
}

#[test]
fn rate32_q29_hvzk_geometry_is_pinned() {
    let oracles = (0..FOLD_BATCHES).map(oracle_geometry).collect::<Vec<_>>();

    assert_eq!(
        oracles,
        vec![
            OracleGeometry {
                stage: 0,
                source_message: 1024,
                limb_message: 256,
                randomness_per_limb: 29,
                randomness_total: 116,
                leaf_rows: 8192,
                padded_dimension: 285,
                limb_degree: 284,
                folded_message: 256,
            },
            OracleGeometry {
                stage: 1,
                source_message: 256,
                limb_message: 64,
                randomness_per_limb: 29,
                randomness_total: 116,
                leaf_rows: 2048,
                padded_dimension: 93,
                limb_degree: 92,
                folded_message: 64,
            },
            OracleGeometry {
                stage: 2,
                source_message: 64,
                limb_message: 16,
                randomness_per_limb: 29,
                randomness_total: 116,
                leaf_rows: 512,
                padded_dimension: 45,
                limb_degree: 44,
                folded_message: 16,
            },
            OracleGeometry {
                stage: 3,
                source_message: 16,
                limb_message: 4,
                randomness_per_limb: 29,
                randomness_total: 116,
                leaf_rows: 128,
                padded_dimension: 33,
                limb_degree: 32,
                folded_message: 4,
            },
        ]
    );

    // The final virtual source is [four message coefficients || 29 random
    // coefficients] evaluated on the last 128-row folded domain.
    assert_eq!(oracles.last().unwrap().folded_message, 4);
    assert_eq!(oracles.last().unwrap().limb_degree, 32);
    assert!(4 + ORACLE_QUERIES < 128);

    // "Rate 1/32" describes the unmasked message rows.  Appending q29
    // randomness raises the actual source-code rates, especially at the
    // terminal.  A soundness ledger must use these padded dimensions.
    assert_eq!(
        oracles
            .iter()
            .map(|oracle| (oracle.padded_dimension, oracle.leaf_rows))
            .collect::<Vec<_>>(),
        vec![(285, 8192), (93, 2048), (45, 512), (33, 128)]
    );
    let final_bits = johnson_bits_per_query_from_rate(33.0 / 128.0) * 29.0;
    assert!((final_bits - 26.314_994_760_451_885).abs() < 1e-12);

    let mask_target = TARGET_BITS + MASK_UNION_BITS;
    let mask_queries = johnson_queries(mask_target, MASK_LOG_INV_RATE);
    assert_eq!(mask_target, 103);
    assert_eq!(mask_queries, 43);

    let switch_message = ORACLE_QUERIES + OOD_SAMPLES;
    assert_eq!(switch_message, 31);

    // Exact upstream PCS-only shape (quadratic source claim).
    assert_eq!(
        mask_domain(UPSTREAM_PCS_ELL_ZK, mask_queries, MASK_LOG_INV_RATE),
        2048
    );
    assert_eq!(
        mask_domain(switch_message, mask_queries, MASK_LOG_INV_RATE),
        4096
    );

    // Aspis internal PCS relation batches are degree six, not degree 27.
    assert_eq!(
        mask_domain(ASPIS_PCS_DEGREE_6_ELL_ZK, mask_queries, MASK_LOG_INV_RATE),
        2048
    );

    // The external ten-round statement zerocheck is a separate width-ten
    // mask group.  It is not one of the seven Hiding-WHIR PCS groups.
    assert_eq!(
        mask_domain(
            ASPIS_EXTERNAL_DEGREE_27_ELL_ZK,
            mask_queries,
            MASK_LOG_INV_RATE
        ),
        4096
    );

    // Four sumcheck groups of width two and three switch groups of width one.
    let group_widths = [2usize, 1, 2, 1, 2, 1, 2];
    assert_eq!(group_widths.len(), 2 * CODE_SWITCH_ROUNDS + 1);
    assert_eq!(group_widths.iter().sum::<usize>(), 11);

    // Hiding-WHIR PCS base-case cleartext OTP reveals: source (4+29), eight
    // internal degree-six sumcheck masks (7+43), and three switch masks
    // (31+43).
    let source_reveal = 4 + ORACLE_QUERIES;
    let pcs_mask_reveals =
        8 * (ASPIS_PCS_DEGREE_6_ELL_ZK + mask_queries) + 3 * (switch_message + mask_queries);
    assert_eq!(source_reveal, 33);
    assert_eq!(pcs_mask_reveals, 622);
    assert_eq!(source_reveal + pcs_mask_reveals, 655);

    // If the external statement zerocheck mask is composed into the same
    // terminal relation, it contributes ten more OTP reveals and one more
    // carried/fresh group pair.  This is a candidate cost, not a theorem.
    let external_mask_reveals =
        EXTERNAL_ZEROCHECK_MASK_WIDTH * (ASPIS_EXTERNAL_DEGREE_27_ELL_ZK + mask_queries);
    assert_eq!(external_mask_reveals, 710);
    assert_eq!(
        source_reveal + pcs_mask_reveals + external_mask_reveals,
        1365
    );

    // Authentication objects in the exact upstream topology:
    // - three code-switch openings of the active source;
    // - source plus fresh-main openings at the base case;
    // - carried plus fresh openings for each of seven mask groups.
    let source_multiproofs = CODE_SWITCH_ROUNDS + 2;
    let mask_multiproofs = 2 * group_widths.len();
    assert_eq!(source_multiproofs, 5);
    assert_eq!(mask_multiproofs, 14);
    assert_eq!(source_multiproofs + mask_multiproofs, 19);

    // Whole-system candidate with the separate external width-ten group.
    assert_eq!(source_multiproofs + mask_multiproofs + 2, 21);

    println!(
        "rate32 HVZK geometry: oracles={oracles:?}; mask_queries={mask_queries}; \
         groups={group_widths:?}; pcs_base_reveals={}; with_external={}; \
         pcs_multiproofs=19; with_external=21",
        source_reveal + pcs_mask_reveals,
        source_reveal + pcs_mask_reveals + external_mask_reveals
    );
}

#[test]
fn mask_rate_tradeoff_is_explicit() {
    let target = TARGET_BITS + MASK_UNION_BITS;
    let switch_message = ORACLE_QUERIES + OOD_SAMPLES;
    let expected = [
        // log inverse rate, Johnson queries, external ell=28 domain, switch domain
        (1usize, 240usize, 1024usize, 1024usize),
        (2, 111, 1024, 1024),
        (3, 73, 1024, 1024),
        (4, 54, 2048, 2048),
        (5, 43, 4096, 4096),
        (6, 36, 4096, 8192),
    ];
    for (log_rate, queries, sumcheck_domain, switch_domain) in expected {
        assert_eq!(johnson_queries(target, log_rate), queries);
        assert_eq!(
            mask_domain(ASPIS_EXTERNAL_DEGREE_27_ELL_ZK, queries, log_rate),
            sumcheck_domain
        );
        assert_eq!(
            mask_domain(switch_message, queries, log_rate),
            switch_domain
        );
    }
}

#[test]
fn source_query_budget_is_self_consistent_or_rejected() {
    let sources = [(256usize, 8192usize), (64, 2048), (16, 512), (4, 128)];

    // The query budget is also the number of appended private coefficients.
    // Re-solving that fixed point (rather than holding randomness at 29)
    // gives the first passing counts below with one 36-bit query grind.
    let at_103 = sources
        .into_iter()
        .map(|(message, domain)| {
            min_self_consistent_source_queries(message, domain, 103.0, 36.0)
                .map(|(queries, _)| queries)
        })
        .collect::<Vec<_>>();
    assert_eq!(at_103, vec![Some(29), Some(32), Some(47), None]);

    let at_104 = sources
        .into_iter()
        .map(|(message, domain)| {
            min_self_consistent_source_queries(message, domain, 104.0, 36.0)
                .map(|(queries, _)| queries)
        })
        .collect::<Vec<_>>();
    assert_eq!(at_104, vec![Some(29), Some(32), Some(48), None]);

    // A 128-point final source cannot reach either target for any legal q:
    // increasing q also raises the code dimension.  Expanding only that
    // source to 512 points yields q40/q41 fixed points.
    assert_eq!(
        min_self_consistent_source_queries(4, 512, 103.0, 36.0).map(|(queries, _)| queries),
        Some(40)
    );
    assert_eq!(
        min_self_consistent_source_queries(4, 512, 104.0, 36.0).map(|(queries, _)| queries),
        Some(41)
    );

    // If 104 bits is desired *after* unioning four source stages, allocate
    // 106 bits per branch.  The first three need q30/q33/q50 and a 512-point
    // final needs q42.
    let branch_106 = [(256usize, 8192usize), (64, 2048), (16, 512), (4, 512)]
        .into_iter()
        .map(|(message, domain)| {
            min_self_consistent_source_queries(message, domain, 106.0, 36.0)
                .map(|(queries, _)| queries)
        })
        .collect::<Vec<_>>();
    assert_eq!(branch_106, vec![Some(30), Some(33), Some(50), Some(42)]);
}

#[test]
fn padded_rate_preserving_code_switch_schedule_restores_q29_bound() {
    let dimensions = [285usize, 93, 45, 33];
    let leaf_domains = [16384usize, 4096, 2048, 2048];
    let unpadded_leaf_domains = [8192usize, 2048, 512, 128];

    for (&dimension, &domain) in dimensions.iter().zip(&leaf_domains) {
        assert!(domain.is_power_of_two());
        assert!(domain >= 32 * dimension);
        let rate = dimension as f64 / domain as f64;
        let bits = ORACLE_QUERIES as f64 * johnson_bits_per_query_from_rate(rate) + 36.0;
        assert!(bits >= 106.0);
    }

    let exact_bits = dimensions
        .iter()
        .zip(&leaf_domains)
        .map(|(&dimension, &domain)| {
            ORACLE_QUERIES as f64
                * johnson_bits_per_query_from_rate(dimension as f64 / domain as f64)
                + 36.0
        })
        .collect::<Vec<_>>();
    let expected = [
        118.713_846_909_893_95,
        113.140_906_730_083,
        113.826_839_594_369_18,
        120.314_994_760_451_88,
    ];
    for (actual, expected) in exact_bits.iter().zip(expected) {
        assert!((*actual - expected).abs() < 1e-12);
    }

    // Four correctly positioned upstream-style grinds can allocate a
    // 106-bit branch target without reusing one nonce across rounds.
    let no_work = exact_bits.iter().map(|bits| bits - 36.0);
    let work = [24.0f64, 29.0, 29.0, 22.0];
    let branch_bits = no_work
        .zip(work)
        .map(|(bits, work)| bits + work)
        .collect::<Vec<_>>();
    assert!(branch_bits.iter().all(|bits| *bits >= 106.0));
    assert!(branch_bits.iter().copied().fold(f64::INFINITY, f64::min) - 2.0 >= 104.0);

    // One four-word interleaved source leaf per row.  The initial genuine
    // circle word and the later line words therefore contain 4*N symbols.
    assert_eq!(
        leaf_domains.map(|domain| FOLD_WIDTH * domain),
        [65536, 16384, 8192, 8192]
    );

    // Binary log-depth deltas of the source leaf trees.  The production
    // radix-four verifier has corresponding level/sibling deltas, but those
    // are measured separately because multiproofs share branches.
    assert_eq!(
        leaf_domains
            .iter()
            .zip(&unpadded_leaf_domains)
            .map(|(&new, &old)| new.ilog2() as i32 - old.ilog2() as i32)
            .collect::<Vec<_>>(),
        vec![1, 1, 2, 4]
    );
}
