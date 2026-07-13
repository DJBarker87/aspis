//! Numeric guard for the no-source private profile-22 theorem ledger.
//!
//! This executable checks arithmetic only.  It does not prove the cited
//! Johnson/MCA reductions, affine-view universality, or the release policy.

use std::f64::consts::LN_2;

use aspis_core::circle_prefix::RATE16_HARDENED_FOLD_POW_BITS;
use aspis_core::field::P as M31_MODULUS;
use aspis_core::state_only_prefix::{
    STATE_ONLY_PROFILE22_BATCH_GRINDING_BITS, STATE_ONLY_PROFILE22_GRINDING_BITS,
};
use aspis_core::state_only_profile22_openings::{
    PROFILE22_PRIVATE_DEPTHS, PROFILE22_PRIVATE_VALUE_WIDTHS,
};

const P: f64 = M31_MODULUS as f64;
const FIELD_SIZE: f64 = P * P * P * P;
const JOHNSON_MULTIPLICITY: f64 = 10.0;
const FOLD_WORK: [u8; 4] = [39, 35, 31, 27];
const ROOT_CAPS: [u64; 4] = [1_024, 255, 63, 15];

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
    assert_eq!(STATE_ONLY_PROFILE22_BATCH_GRINDING_BITS, 38);
    assert_eq!(STATE_ONLY_PROFILE22_GRINDING_BITS, 38);
    assert_eq!(RATE16_HARDENED_FOLD_POW_BITS, FOLD_WORK);
    assert_eq!(PROFILE22_PRIVATE_DEPTHS, [17, 17, 15, 13, 11]);
    assert_eq!(PROFILE22_PRIVATE_VALUE_WIDTHS, [416, 128, 64, 64, 64]);

    let rho: f64 = 1.0 / 512.0;
    let agreement_fraction = (1.0 + 1.0 / (2.0 * JOHNSON_MULTIPLICITY)) * rho.sqrt();
    let query_fibers = 131_072u64;
    let agreement_fibers = (agreement_fraction * query_fibers as f64).floor() as u64;
    assert_eq!(agreement_fibers, 6_082);

    let ell = (JOHNSON_MULTIPLICITY + 0.5) / rho.sqrt();
    let batch_numerator = 27.0 * ell * ((2.0 * ell.powi(4) / 3.0) * rho + 1.0) * 524_288.0;
    let batch_bits = (FIELD_SIZE / batch_numerator).log2() + 36.0;

    let query_bits = (0..16u64)
        .map(|i| -((agreement_fibers - i) as f64 / (query_fibers - i) as f64).log2())
        .sum::<f64>()
        + 36.0;

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

    let g36_terms = [
        batch_bits,
        folds_bits,
        query_bits,
        ood_bits,
        local_bits(24.0),                    // relation/OOD mixers
        local_nonzero_bits(29.0),            // nonzero gamma plus three-point batching
        local_nonzero_bits(27.0),            // copy-inactive nonzero-gamma claim
        local_bits(183.0 * 17.0),            // atomic tuple compression
        local_bits(4.0 * (183.0 + 1_024.0)), // atomic copy/range poles
        local_bits(24.0),                    // atomic theta collision
        local_bits(10.0),                    // zerocheck equality-point reduction
        local_bits(1.0),                     // zero-sum h1 helper under mu
        (FIELD_SIZE - 1.0).log2(),           // mask/original binding under nonzero eta
        local_bits(270.0),                   // ten degree-27 zerocheck rounds
        124.0,                               // Poseidon2 assumption
        128.0,                               // SHA-256/ROM assumption
    ];
    let bcs_factor = 31.0_f64;
    let sensitivity = [36u8, 37, 38].map(|work| {
        let delta = f64::from(work - 36);
        let mut terms = g36_terms;
        terms[0] += delta;
        terms[2] += delta;
        let event_union_bits = union_bits(terms);
        (
            event_union_bits,
            event_union_bits - bcs_factor.log2(),
            event_union_bits - 40.0_f64.log2(),
        )
    });
    let (event_union_bits, after_bcs_bits, factor40_bits) = sensitivity[2];

    close(batch_bits, 106.368_487_534_249_52);
    close(folds_bits, 112.079_790_788_536_77);
    close(query_bits, 106.901_886_597_240_66);
    close(ood_bits, 213.100_018_394_892_15);
    close(sensitivity[0].0, 105.560_295_761_040_58);
    close(sensitivity[0].1, 100.606_099_450_653_7);
    close(sensitivity[0].2, 100.238_367_666_153_21);
    close(sensitivity[1].0, 106.511_616_673_627_64);
    close(sensitivity[1].1, 101.557_420_363_240_77);
    close(sensitivity[1].2, 101.189_688_578_740_27);
    close(event_union_bits, 107.418_925_168_071_58);
    close(after_bcs_bits, 102.464_728_857_684_7);
    close(factor40_bits, 102.096_997_073_184_21);

    // Mining counts predicate evaluations, i.e. K+1 trials for a zero-based
    // geometric minimum K.  E[K+1]=2^g; E[K]=2^g-1 failures.
    let mining_totals = [36u8, 37, 38].map(|work| {
        2u64 * (1u64 << work) + FOLD_WORK.into_iter().map(|bits| 1u64 << bits).sum::<u64>()
    });
    assert_eq!(
        mining_totals,
        [723_836_207_104, 861_275_160_576, 1_136_153_067_520]
    );
    assert_eq!(mining_totals[2] - mining_totals[0], 412_316_860_416);

    // Five full binary trees of depths 17,17,15,13,11.
    let leaves = (1u64 << 17) + (1u64 << 17) + (1u64 << 15) + (1u64 << 13) + (1u64 << 11);
    let exact_internal_nodes = leaves - 5;
    assert_eq!(leaves, 305_152);
    assert_eq!(exact_internal_nodes, 305_147);

    // The bounded transcript has 67 QM31 calls at at most four blocks each:
    // both eta and profile-22 gamma permit up to three nonzero draws. Add at
    // most eight blocks for q16 without replacement.
    let programmed_squeeze_inputs = 67u64 * 4 + 8;
    let transcript_inputs = 43 + programmed_squeeze_inputs * 2 + 6;
    assert_eq!(programmed_squeeze_inputs, 276);
    assert_eq!(transcript_inputs, 601);

    // Book N rather than N-5 node inputs, retaining five inputs of slack.
    let c_bound = 3 * leaves + 45_700 + 8 + transcript_inputs;
    assert_eq!(c_bound, 961_765);
    let q_h_log2 = 128.0;
    let attempts = 16.0_f64;
    let leading_epro_bits = 256.0 - q_h_log2 - (attempts * c_bound as f64).log2();
    let programmed_inputs = attempts * c_bound as f64;
    let collision_bits = 256.0 - (programmed_inputs * (programmed_inputs - 1.0) / 2.0).log2();
    let work_exhaustion_bits = 2.0_f64.powi(25) / LN_2 - (6.0 * attempts).log2();

    close(leading_epro_bits, 104.124_675_100_124_36);
    close(collision_bits, 209.249_350_294_001_83);
    close(work_exhaustion_bits, 48_408_806.061_283_44);

    for (index, work) in [36u8, 37, 38].into_iter().enumerate() {
        println!(
            "profile22_g{work}_union={:.13} bcs31={:.13} factor40={:.13} expected_total_mining_hashes={}",
            sensitivity[index].0,
            sensitivity[index].1,
            sensitivity[index].2,
            mining_totals[index]
        );
    }
    println!("profile22_selected_work_bits=38");
    println!("profile22_selected_soundness_event_union_bits={event_union_bits:.13}");
    println!("profile22_selected_soundness_after_bcs31_bits={after_bcs_bits:.13}");
    println!("profile22_selected_soundness_factor40_bits={factor40_bits:.13}");
    println!("profile22_epro_inventory_bound={c_bound}");
    println!("profile22_epro_qh128_r16_leading_bits={leading_epro_bits:.13}");
    println!("profile22_epro_qh128_r16_collision_bits={collision_bits:.13}");
    println!("profile22_epro_qh128_r16_work_exhaustion_bits={work_exhaustion_bits:.8}");
}
