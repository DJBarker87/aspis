use std::fmt::Write as _;
use std::fs;
use std::time::Instant;

use aspis_core::state_only_prefix::{
    run_atomic_state_only_profile21_transcript_schedule_host_unmined_for_diagnostics_v3,
    StateOnlyProfile21Prefix,
};
use aspis_prover::state_only_hiding_rank::{
    probe_atomic_state_only_profile21_zero_slice_embedding_at,
    AtomicProfile21ZeroSliceEmbeddingFailureReport, AtomicProfile21ZeroSliceEmbeddingScanReport,
    AtomicProfile21ZeroSliceEmbeddingVariantReport, StateOnlyHidingRankGateError,
};
use aspis_prover::HOST_HASH;

const STATEMENT_DIGEST: [u8; 32] = [
    0x52, 0xe9, 0x6f, 0x99, 0x75, 0x6f, 0xe8, 0xfd, 0x2d, 0x8b, 0x7a, 0x70, 0x00, 0x19, 0xb1, 0x43,
    0xd7, 0xeb, 0x54, 0x9a, 0xf1, 0xbf, 0x1a, 0xe9, 0x87, 0xe9, 0x9a, 0x75, 0xca, 0xdc, 0xd4, 0xc9,
];

fn json(report: &AtomicProfile21ZeroSliceEmbeddingScanReport) -> String {
    let mut output = String::new();
    writeln!(output, "{{").unwrap();
    writeln!(
        output,
        "  \"schema\": \"aspis.profile21.zero_slice_embedding_scan.v1\","
    )
    .unwrap();
    writeln!(output, "  \"production_neutral\": true,").unwrap();
    writeln!(
        output,
        "  \"complete\": {},",
        report.variants.len() + report.failures.len() == 11
    )
    .unwrap();
    writeln!(output, "  \"query_count\": {},", report.query_count).unwrap();
    writeln!(
        output,
        "  \"message_embedding\": \"old 10-bit row at inserted bit 0; fresh full-QM31 G helper mask at inserted bit 1\","
    )
    .unwrap();
    writeln!(
        output,
        "  \"claim_embedding\": \"z, successor(z), xor12(z), and inactive-row functional extended with inserted coordinate zero\","
    )
    .unwrap();
    writeln!(
        output,
        "  \"codeword_domain_log\": {},",
        report.codeword_domain_log
    )
    .unwrap();
    writeln!(
        output,
        "  \"rate_denominator\": {},",
        report.rate_denominator
    )
    .unwrap();
    let b0 = report
        .variants
        .iter()
        .find(|variant| variant.insertion_coordinate == 0);
    let b0_passed = b0.is_some_and(|variant| {
        variant.baseline_pcs_rank_m31 == 712
            && variant.mask_augmented_pcs_rank_m31 == 808
            && variant.semantic_augmented_rank_m31 == 812
            && variant.legal_sumcheck_augmented_rank_m31 == 812
            && variant.semantic_new_pivots_m31 == [1084, 1085, 1086, 1087]
            && variant.legal_sumcheck_new_pivots_m31.is_empty()
            && !variant.contains_conservative_semantic_and_legal_sumcheck
    });
    writeln!(output, "  \"b0_reference_equivalence\": {{").unwrap();
    writeln!(output, "    \"expected_ranks_m31\": [712, 808, 812, 812],").unwrap();
    writeln!(
        output,
        "    \"expected_semantic_pivots_m31\": [1084, 1085, 1086, 1087],"
    )
    .unwrap();
    writeln!(output, "    \"passed\": {}", b0_passed).unwrap();
    writeln!(output, "  }},").unwrap();
    writeln!(output, "  \"variants\": [").unwrap();
    for (index, variant) in report.variants.iter().enumerate() {
        writeln!(output, "    {{").unwrap();
        writeln!(
            output,
            "      \"insertion_coordinate_msb_first\": {},",
            variant.insertion_coordinate
        )
        .unwrap();
        writeln!(
            output,
            "      \"baseline_pcs_rank_m31\": {},",
            variant.baseline_pcs_rank_m31
        )
        .unwrap();
        writeln!(
            output,
            "      \"mask_augmented_pcs_rank_m31\": {},",
            variant.mask_augmented_pcs_rank_m31
        )
        .unwrap();
        writeln!(
            output,
            "      \"mask_new_pivots_m31\": {:?},",
            variant.mask_new_pivots_m31
        )
        .unwrap();
        writeln!(
            output,
            "      \"semantic_augmented_rank_m31\": {},",
            variant.semantic_augmented_rank_m31
        )
        .unwrap();
        writeln!(
            output,
            "      \"semantic_new_pivots_m31\": {:?},",
            variant.semantic_new_pivots_m31
        )
        .unwrap();
        writeln!(
            output,
            "      \"legal_sumcheck_augmented_rank_m31\": {},",
            variant.legal_sumcheck_augmented_rank_m31
        )
        .unwrap();
        writeln!(
            output,
            "      \"legal_sumcheck_new_pivots_m31\": {:?},",
            variant.legal_sumcheck_new_pivots_m31
        )
        .unwrap();
        writeln!(
            output,
            "      \"contains_conservative_semantic_and_legal_sumcheck\": {},",
            variant.contains_conservative_semantic_and_legal_sumcheck
        )
        .unwrap();
        writeln!(
            output,
            "      \"elapsed_millis\": {}",
            variant.elapsed_millis
        )
        .unwrap();
        writeln!(
            output,
            "    }}{}",
            if index + 1 == report.variants.len() {
                ""
            } else {
                ","
            }
        )
        .unwrap();
    }
    writeln!(output, "  ],").unwrap();
    writeln!(output, "  \"failures\": [").unwrap();
    for (index, failure) in report.failures.iter().enumerate() {
        writeln!(output, "    {{").unwrap();
        writeln!(
            output,
            "      \"insertion_coordinate_msb_first\": {},",
            failure.insertion_coordinate
        )
        .unwrap();
        writeln!(output, "      \"stage\": \"{}\",", failure.stage).unwrap();
        match failure.column {
            Some(column) => writeln!(output, "      \"column\": {column},").unwrap(),
            None => writeln!(output, "      \"column\": null,").unwrap(),
        }
        writeln!(output, "      \"got_rank_m31\": {},", failure.got_rank_m31).unwrap();
        writeln!(
            output,
            "      \"want_rank_m31\": {},",
            failure.want_rank_m31
        )
        .unwrap();
        writeln!(
            output,
            "      \"elapsed_millis\": {}",
            failure.elapsed_millis
        )
        .unwrap();
        writeln!(
            output,
            "    }}{}",
            if index + 1 == report.failures.len() {
                ""
            } else {
                ","
            }
        )
        .unwrap();
    }
    writeln!(output, "  ],").unwrap();
    writeln!(output, "  \"elapsed_millis\": {}", report.elapsed_millis).unwrap();
    writeln!(output, "}}").unwrap();
    output
}

fn main() {
    let proof_path = std::env::args().nth(1).unwrap_or_else(|| {
        "results/stage2/proofs/atomic_state_only_profile21_v3_unmined.bin".into()
    });
    let output_path = std::env::args()
        .nth(2)
        .unwrap_or_else(|| "results/stage2/profile21_zero_slice_embedding_scan.json".into());
    let proof = fs::read(proof_path).expect("read profile-21 fixture");
    let (prefix, _) =
        StateOnlyProfile21Prefix::parse_from_proof(&proof).expect("parse profile-21 prefix");
    let schedule =
        run_atomic_state_only_profile21_transcript_schedule_host_unmined_for_diagnostics_v3(
            HOST_HASH,
            &prefix,
            &STATEMENT_DIGEST,
        )
        .expect("replay profile-21 schedule");
    let started = Instant::now();
    let coordinates = (0..=10).collect::<Vec<_>>();
    let mut variants = Vec::with_capacity(coordinates.len());
    let mut failures = Vec::new();
    for batch in coordinates.chunks(4) {
        let schedule_ref = &schedule;
        let reports = std::thread::scope(|scope| {
            let handles = batch
                .iter()
                .copied()
                .map(|insertion_coordinate| {
                    scope.spawn(move || {
                        let coordinate_started = Instant::now();
                        let report = probe_atomic_state_only_profile21_zero_slice_embedding_at(
                            schedule_ref,
                            insertion_coordinate,
                        );
                        (insertion_coordinate, coordinate_started.elapsed(), report)
                    })
                })
                .collect::<Vec<_>>();
            handles
                .into_iter()
                .map(|handle| handle.join().expect("zero-slice coordinate thread"))
                .collect::<Vec<_>>()
        });
        for (insertion_coordinate, elapsed, report) in reports {
            let report = match report {
                Ok(report) => report,
                Err(StateOnlyHidingRankGateError::RawC1Rank { column, got, want }) => {
                    failures.push(AtomicProfile21ZeroSliceEmbeddingFailureReport {
                        insertion_coordinate,
                        stage: "raw_c1_rank",
                        column: Some(column),
                        got_rank_m31: got,
                        want_rank_m31: want,
                        elapsed_millis: elapsed.as_millis(),
                    });
                    continue;
                }
                Err(error) => panic!("zero-slice coordinate {insertion_coordinate}: {error:?}"),
            };
            let mask = report
                .variants
                .iter()
                .find(|variant| variant.support == "upper_g_only")
                .expect("upper G variant");
            variants.push(AtomicProfile21ZeroSliceEmbeddingVariantReport {
                insertion_coordinate,
                baseline_pcs_rank_m31: report.baseline_pcs_rank_m31,
                mask_augmented_pcs_rank_m31: mask.pcs_rank,
                mask_new_pivots_m31: mask.upper_new_pivots_m31.clone(),
                semantic_augmented_rank_m31: mask.semantic_augmented_rank,
                semantic_new_pivots_m31: mask.semantic_new_pivots_m31.clone(),
                legal_sumcheck_augmented_rank_m31: mask.legal_sumcheck_augmented_rank,
                legal_sumcheck_new_pivots_m31: mask.legal_sumcheck_new_pivots_m31.clone(),
                contains_conservative_semantic_and_legal_sumcheck: mask
                    .contains_conservative_semantic_and_legal_sumcheck,
                elapsed_millis: elapsed.as_millis(),
            });
        }
        variants.sort_by_key(|variant| variant.insertion_coordinate);
        failures.sort_by_key(|failure| failure.insertion_coordinate);
        let checkpoint = AtomicProfile21ZeroSliceEmbeddingScanReport {
            query_count: schedule.base.query_count,
            codeword_domain_log: 19,
            rate_denominator: 256,
            variants: variants.clone(),
            failures: failures.clone(),
            elapsed_millis: started.elapsed().as_millis(),
        };
        fs::write(&output_path, json(&checkpoint)).expect("checkpoint zero-slice scan artifact");
    }
    let report = AtomicProfile21ZeroSliceEmbeddingScanReport {
        query_count: schedule.base.query_count,
        codeword_domain_log: 19,
        rate_denominator: 256,
        variants,
        failures,
        elapsed_millis: started.elapsed().as_millis(),
    };
    let output = json(&report);
    fs::write(&output_path, &output).expect("write final zero-slice scan artifact");
    print!("{output}");
}
