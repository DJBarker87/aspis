//! Production-neutral projection tooth for the four-M31 profile-21 semantic quotient.

use std::fs;

use aspis_core::field::{M31, QM31};
use aspis_core::state_only_hiding::STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS;
use aspis_core::state_only_prefix::{
    run_atomic_state_only_profile21_transcript_schedule_host_unmined_for_diagnostics_v3,
    StateOnlyProfile21Prefix,
};
use aspis_prover::state_only_hiding_rank::project_atomic_state_only_profile21_witness_difference;
use aspis_prover::HOST_HASH;

const STATEMENT_DIGEST: [u8; 32] = [
    0x52, 0xe9, 0x6f, 0x99, 0x75, 0x6f, 0xe8, 0xfd, 0x2d, 0x8b, 0x7a, 0x70, 0x00, 0x19, 0xb1, 0x43,
    0xd7, 0xeb, 0x54, 0x9a, 0xf1, 0xbf, 0x1a, 0xe9, 0x87, 0xe9, 0x9a, 0x75, 0xca, 0xdc, 0xd4, 0xc9,
];

const COMPATIBILITY_COEFFICIENTS: [[u32; 4]; 4] = [
    [350_845_536, 249_757_693, 1_206_727_637, 1_279_178_930],
    [1_016_364_350, 411_809_830, 1_907_580_655, 220_234_897],
    [1_896_196_302, 418_285_848, 1_665_917_791, 379_859_693],
    [2_024_538_732, 54_457_632, 1_743_708_851, 1_698_678_299],
];

fn main() {
    let path = std::env::args().nth(1).unwrap_or_else(|| {
        "results/stage2/proofs/atomic_state_only_profile21_v3_unmined.bin".to_owned()
    });
    let proof = fs::read(path).expect("read profile-21 fixture");
    let (prefix, _) =
        StateOnlyProfile21Prefix::parse_from_proof(&proof).expect("profile-21 prefix");
    let schedule =
        run_atomic_state_only_profile21_transcript_schedule_host_unmined_for_diagnostics_v3(
            HOST_HASH,
            &prefix,
            &STATEMENT_DIGEST,
        )
        .expect("profile-21 schedule");

    // Sum the four canonical compatible directions. Each direction is one
    // representative plus its four coefficients against c0r1..c0r4.
    let mut semantic = vec![vec![M31::ZERO; 1024]; 16];
    for compatibility in 0..4 {
        semantic[0][compatibility + 1] = COMPATIBILITY_COEFFICIENTS
            .iter()
            .fold(M31::ZERO, |sum, row| sum.add(M31(row[compatibility])));
    }
    semantic[0][5] = M31::ONE;
    semantic[1][1] = M31::ONE;
    semantic[2][1] = M31::ONE;
    semantic[3][1] = M31::ONE;

    let sumcheck = vec![QM31::ZERO; STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS];
    let report = project_atomic_state_only_profile21_witness_difference(
        &schedule.base,
        &semantic,
        &sumcheck,
    )
    .expect("semantic quotient projection");

    assert!(report.compatibility_kernel);
    assert!(report.inside_conservative_superset);
    assert_eq!(
        report.semantic_quotient_pivot_rows_m31,
        [276, 277, 278, 279]
    );
    assert!(report
        .semantic_quotient_coordinates_m31
        .iter()
        .all(|coordinate| *coordinate != 0));
    println!("{report:#?}");
}
