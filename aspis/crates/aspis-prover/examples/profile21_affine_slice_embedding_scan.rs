use std::fmt::Write as _;
use std::fs;

use aspis_core::state_only_prefix::{
    run_atomic_state_only_profile21_transcript_schedule_host_unmined_for_diagnostics_v3,
    StateOnlyProfile21Prefix,
};
use aspis_prover::state_only_hiding_rank::{
    probe_atomic_state_only_profile21_affine_slice_embedding_scan,
    AtomicProfile21AffineSliceEmbeddingScanReport,
};
use aspis_prover::HOST_HASH;

const STATEMENT_DIGEST: [u8; 32] = [
    0x52, 0xe9, 0x6f, 0x99, 0x75, 0x6f, 0xe8, 0xfd, 0x2d, 0x8b, 0x7a, 0x70, 0x00, 0x19, 0xb1, 0x43,
    0xd7, 0xeb, 0x54, 0x9a, 0xf1, 0xbf, 0x1a, 0xe9, 0x87, 0xe9, 0x9a, 0x75, 0xca, 0xdc, 0xd4, 0xc9,
];

fn json(report: &AtomicProfile21AffineSliceEmbeddingScanReport) -> String {
    let mut output = String::new();
    writeln!(output, "{{").unwrap();
    writeln!(
        output,
        "  \"schema\": \"aspis.profile21.affine_slice_embedding_scan.v1\","
    )
    .unwrap();
    writeln!(output, "  \"production_neutral\": true,").unwrap();
    writeln!(output, "  \"query_count\": {},", report.query_count).unwrap();
    writeln!(
        output,
        "  \"construction\": \"F(x,s)=F(x)+(s-c)R(x); paired helper coefficients (-c*r,(1-c)*r)\","
    )
    .unwrap();
    writeln!(
        output,
        "  \"claim_embedding\": \"all evaluation claims at s=c; inactive functional tensored by (1-c,c)\","
    )
    .unwrap();
    writeln!(output, "  \"slice_values_m31\": [2, 3, 5, 7],").unwrap();
    writeln!(
        output,
        "  \"insertion_order_msb_first\": [10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0],"
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
    writeln!(
        output,
        "  \"stopped_on_first_containment\": {},",
        report.stopped_on_first_containment
    )
    .unwrap();
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
            "      \"slice_value_m31\": {},",
            variant.slice_value_m31
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
        .unwrap_or_else(|| "results/stage2/profile21_affine_slice_embedding_scan.json".into());
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
    let report = probe_atomic_state_only_profile21_affine_slice_embedding_scan(&schedule)
        .expect("affine-slice embedding scan");
    let output = json(&report);
    fs::write(&output_path, &output).expect("write affine-slice scan artifact");
    print!("{output}");
}
