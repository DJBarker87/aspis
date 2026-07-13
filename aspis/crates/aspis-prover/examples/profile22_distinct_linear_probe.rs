//! Zero-width host probe for deterministic distinct dense-linear masking
//! factors on the frozen atomic Profile-22 q16 schedule.
//!
//! This example changes no production factor table, proof wire, transcript
//! tag, generator width, or verifier predicate.  It is an exact rank and
//! containment counterexample finder for a small predeclared family.

use std::env;
use std::fs;

use aspis_core::field::{CM31, M31, QM31};
use aspis_core::state_only_hiding::state_only_mask_tower_basis;
use aspis_core::state_only_prefix::{
    run_atomic_state_only_transcript_schedule_host_unmined_for_diagnostics_v3,
    StateOnlyCandidatePrefix,
};
use aspis_prover::state_only_hiding_rank::{
    probe_atomic_state_only_profile22_distinct_linear_containment,
    probe_atomic_state_only_profile22_distinct_linear_root_neutral_sumcheck,
    DistinctLinearAssignment, DistinctLinearGFactor,
};
use aspis_prover::HOST_HASH;

const STATEMENT_DIGEST: [u8; 32] = [
    0x52, 0xe9, 0x6f, 0x99, 0x75, 0x6f, 0xe8, 0xfd, 0x2d, 0x8b, 0x7a, 0x70, 0x00, 0x19, 0xb1, 0x43,
    0xd7, 0xeb, 0x54, 0x9a, 0xf1, 0xbf, 0x1a, 0xe9, 0x87, 0xe9, 0x9a, 0x75, 0xca, 0xdc, 0xd4, 0xc9,
];

fn assignment(token: &str) -> DistinctLinearAssignment {
    match token {
        "lane" => DistinctLinearAssignment::LanePlusOne,
        "affine" => DistinctLinearAssignment::AffineSevenPlusThree,
        "reverse" => DistinctLinearAssignment::Reverse,
        _ => panic!("assignment must be lane, affine, or reverse"),
    }
}

fn g_factor(token: &str) -> DistinctLinearGFactor {
    match token {
        "g23" => DistinctLinearGFactor::MissingDegree23,
        "g26" => DistinctLinearGFactor::Degree26AddOne,
        _ => panic!("G factor must be g23 or g26"),
    }
}

fn main() {
    let schedule_mode = env::args().nth(1).unwrap_or_else(|| "actual".into());
    let assignment = assignment(&env::args().nth(2).unwrap_or_else(|| "lane".into()));
    let g_factor = g_factor(&env::args().nth(3).unwrap_or_else(|| "g23".into()));
    let prefix_m31_lanes = env::args()
        .nth(4)
        .map(|value| value.parse::<usize>().expect("M31 prefix lane count"))
        .unwrap_or(26);
    let view = env::args().nth(5).unwrap_or_else(|| "both".into());
    let path = env::args().nth(6).unwrap_or_else(|| {
        "results/stage2/proofs/atomic_state_only_profile22_v3_unmined.bin".into()
    });

    let proof = fs::read(path).expect("read frozen Profile-22 fixture");
    let (prefix, _) = StateOnlyCandidatePrefix::parse_from_proof(&proof).expect("parse prefix");
    let mut schedule = run_atomic_state_only_transcript_schedule_host_unmined_for_diagnostics_v3(
        HOST_HASH,
        &prefix,
        &STATEMENT_DIGEST,
    )
    .expect("replay frozen atomic schedule");

    match schedule_mode.as_str() {
        "actual" => {}
        "affine-degenerate" => {
            let i = state_only_mask_tower_basis(1);
            let u = state_only_mask_tower_basis(2);
            schedule.prefix.z.fill(QM31::ONE);
            schedule.prefix.z[6] = QM31::ZERO;
            schedule.prefix.z[7] = QM31::ONE;
            schedule.prefix.z[8] = i;
            schedule.prefix.z[9] = u;
            let thirty_two = QM31::from_cm31(CM31::from_m31(M31(32)));
            schedule.prefix.z[0] =
                QM31::ZERO.sub(thirty_two.add(i).mul_m31(M31(9).inv()));
        }
        "terminal-certificate" => {
            let i = state_only_mask_tower_basis(1);
            let u = state_only_mask_tower_basis(2);
            schedule.prefix.z.fill(QM31::ONE);
            schedule.prefix.z[6] = QM31::ZERO;
            schedule.prefix.z[8] = i;
            schedule.prefix.z[9] = u;
        }
        "boolean-z" => {
            schedule.prefix.z.fill(QM31::ZERO);
            schedule.prefix.point_scale = QM31::ONE;
            schedule.mu[0].fill(QM31::ZERO);
        }
        "consecutive" => {
            for (index, query) in schedule.queries[..16].iter_mut().enumerate() {
                *query = index as u32;
            }
        }
        "same-coset" => {
            for (index, query) in schedule.queries[..16].iter_mut().enumerate() {
                *query = (index as u32) << 13;
            }
        }
        _ => panic!(
            "schedule must be actual, affine-degenerate, terminal-certificate, boolean-z, consecutive, or same-coset"
        ),
    }

    assert_eq!(schedule.query_count, 16);
    println!("schedule={schedule_mode}");
    println!("assignment={}", assignment.label());
    println!("g_factor={}", g_factor.label());
    println!("prefix_m31_lanes={prefix_m31_lanes}");
    println!("query_count={}", schedule.query_count);
    println!("queries={:?}", &schedule.queries[..schedule.query_count]);

    if view == "both" || view == "containment" {
        match probe_atomic_state_only_profile22_distinct_linear_containment(
            &schedule,
            assignment,
            g_factor,
            prefix_m31_lanes,
        ) {
            Ok(report) => {
                println!(
                    "raw_opening_rank={}",
                    report.raw_opening_minor.pivot_rows.len()
                );
                println!(
                    "masked_sumcheck_rank={}/{}",
                    report.masked_sumcheck_rank,
                    report.masked_sumcheck_m31 - 4
                );
                println!(
                    "joint_pcs_rank={}/{}",
                    report.joint_pcs_rank, report.joint_pcs_declared_rank
                );
                println!(
                    "physical_direct_sum={:?}/{:?} contained={:?}",
                    report.witness_direct_sum_physical_augmented_view_rank_m31,
                    report.witness_direct_sum_mask_view_rank_m31,
                    report.witness_direct_sum_physical_contained,
                );
                println!(
                    "legal_direct_sum={:?}/{:?} contained={:?}",
                    report.witness_direct_sum_legal_augmented_view_rank_m31,
                    report.witness_direct_sum_mask_view_rank_m31,
                    report.witness_direct_sum_legal_contained,
                );
                println!("complete_ambient_rank={}", report.complete_ambient_rank);
                println!("containment_elapsed_millis={}", report.elapsed_millis);
            }
            Err(error) => println!("containment_error={error:?}"),
        }
    }

    if view == "both" || view == "root-neutral" {
        match probe_atomic_state_only_profile22_distinct_linear_root_neutral_sumcheck(
            &schedule,
            assignment,
            g_factor,
            prefix_m31_lanes,
        ) {
            Ok(report) => {
                println!(
                    "root_neutral_rank={}/{} complete={}",
                    report.root_neutral_legal_sumcheck_rank_m31,
                    report.legal_sumcheck_m31,
                    report.complete,
                );
                println!(
                    "root_neutral_mask_only_rank={}",
                    report.mask_only_root_neutral_legal_sumcheck_rank_m31
                );
                println!("root_neutral_elapsed_millis={}", report.elapsed_millis);
            }
            Err(error) => println!("root_neutral_error={error:?}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deterministic_assignments_are_bijections_over_families_one_through_twenty_seven() {
        for assignment in [
            DistinctLinearAssignment::LanePlusOne,
            DistinctLinearAssignment::AffineSevenPlusThree,
            DistinctLinearAssignment::Reverse,
        ] {
            let mut families = (0..27)
                .map(|lane| assignment.family_for_lane(lane))
                .collect::<Vec<_>>();
            families.sort_unstable();
            assert_eq!(families, (1u8..=27).collect::<Vec<_>>());
        }
    }
}
