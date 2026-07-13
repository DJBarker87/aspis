use std::env;
use std::fs;

use aspis_core::circle_line_merkle::derive_circle_line_query_indices_for_count;
use aspis_core::field::{CM31, M31, QM31};
use aspis_core::state_only_hiding::state_only_mask_tower_basis;
use aspis_core::state_only_prefix::{
    run_atomic_state_only_transcript_schedule_host_unmined_for_diagnostics_v3,
    run_state_only_transcript_schedule_host_unmined_for_diagnostics, StateOnlyCandidatePrefix,
};
use aspis_prover::state_only_hiding_rank::{
    check_state_only_complete_hiding_rank,
    check_state_only_complete_hiding_rank_with_tail_qm31_probe,
    check_state_only_sparse_row_map_reference, probe_atomic_state_only_full_shared_hiding_rank,
    probe_atomic_state_only_masked_single_switch_joint_rank,
    probe_atomic_state_only_profile22_complete_shared_power_root_neutral_sumcheck,
    probe_atomic_state_only_profile22_g_add_shared_power_containment,
    probe_atomic_state_only_profile22_g_add_shared_power_root_neutral_sumcheck,
    probe_atomic_state_only_profile22_multi_g_mask_rank,
    probe_atomic_state_only_profile22_root_neutral_sumcheck,
    probe_atomic_state_only_profile22_shared_degree_cover_containment,
    probe_atomic_state_only_profile22_shared_degree_cover_root_neutral_sumcheck,
    probe_state_only_coordinate_factored_late_switch_rank,
    probe_state_only_full_shared_hiding_rank, probe_state_only_full_shared_late_switch_rank,
    probe_state_only_hybrid_arity8_rank, probe_state_only_late_switch_rank,
    probe_state_only_log11_upper_g_rank, probe_state_only_masked_single_switch_joint_rank,
    probe_state_only_root1_distinct_folded_rank, TailQm31MaskFactor,
};
use aspis_prover::HOST_HASH;

/// Deliberately small and predeclared: family 16 is the production explicit-G
/// family implicated in the affine degeneracy, so the bounded fallback uses
/// the sixteen neighboring nonproduction families 1..=15 and 17.
const MULTI_G_DENSE_FAMILIES: [u8; 16] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17];
const MULTI_G_DENSE17_EXPONENTS: [u8; 27] = [
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
    26,
];

fn multi_g_dense_factors(count: usize) -> Option<Vec<TailQm31MaskFactor>> {
    let families = MULTI_G_DENSE_FAMILIES.get(..count)?;
    Some(
        families
            .iter()
            .copied()
            .map(|family| TailQm31MaskFactor::DensePower {
                family,
                exponent: 26,
                add_one: true,
            })
            .collect(),
    )
}

fn multi_g_dense17_power_factors(count: usize) -> Option<Vec<TailQm31MaskFactor>> {
    let exponents = MULTI_G_DENSE17_EXPONENTS.get(..count)?;
    Some(
        exponents
            .iter()
            .copied()
            .map(|exponent| TailQm31MaskFactor::DensePower {
                family: 17,
                exponent,
                add_one: false,
            })
            .collect(),
    )
}

fn multi_g_diagonal_factors(count: usize) -> Option<Vec<TailQm31MaskFactor>> {
    let families = MULTI_G_DENSE_FAMILIES.get(..count)?;
    let exponents = MULTI_G_DENSE17_EXPONENTS.get(..count)?;
    Some(
        families
            .iter()
            .copied()
            .zip(exponents.iter().copied())
            .map(|(family, exponent)| TailQm31MaskFactor::DensePower {
                family,
                exponent,
                add_one: false,
            })
            .collect(),
    )
}

fn main() {
    let path = env::args()
        .nth(1)
        .expect("usage: state_only_hiding_rank_gate <proof> [statement-byte]");
    let statement_digest = env::args()
        .nth(2)
        .map(|value| {
            if value.len() == 64 {
                let mut digest = [0u8; 32];
                for (index, byte) in digest.iter_mut().enumerate() {
                    *byte = u8::from_str_radix(&value[2 * index..2 * index + 2], 16)
                        .expect("statement digest hex");
                }
                digest
            } else {
                [value.parse::<u8>().expect("statement byte"); 32]
            }
        })
        .unwrap_or([0x51; 32]);
    let proof = fs::read(path).expect("read proof");
    let (prefix, _) = StateOnlyCandidatePrefix::parse_from_proof(&proof).expect("parse proof");
    let mode = env::args().nth(3).unwrap_or_default();
    let mut schedule = if mode.starts_with("atomic-") {
        run_atomic_state_only_transcript_schedule_host_unmined_for_diagnostics_v3(
            HOST_HASH,
            &prefix,
            &statement_digest,
        )
    } else {
        run_state_only_transcript_schedule_host_unmined_for_diagnostics(
            HOST_HASH,
            &prefix,
            &statement_digest,
        )
    }
    .expect("replay schedule");
    if mode.ends_with("-bad-affine") {
        let i = state_only_mask_tower_basis(1);
        let u = state_only_mask_tower_basis(2);
        schedule.prefix.z.fill(QM31::ONE);
        schedule.prefix.z[6] = QM31::ZERO;
        schedule.prefix.z[7] = QM31::ONE;
        schedule.prefix.z[8] = i;
        schedule.prefix.z[9] = u;
        let thirty_two = QM31::from_cm31(CM31::from_m31(M31(32)));
        schedule.prefix.z[0] = QM31::ZERO.sub(thirty_two.add(i).mul_m31(M31(9).inv()));
    }
    if mode == "query-indices" {
        let indices = derive_circle_line_query_indices_for_count(
            &schedule.queries[..schedule.query_count],
            1usize << 17,
        )
        .expect("query indices");
        println!("queries={:?}", &schedule.queries[..schedule.query_count]);
        println!("layer0={:?}", indices.layer0);
        println!(
            "unique_counts=[{},{},{},{}] later={:?}",
            indices.layer0.len(),
            indices.later[0].len(),
            indices.later[1].len(),
            indices.later[2].len(),
            indices.later,
        );
        return;
    }
    if mode == "sparse-reference" {
        check_state_only_sparse_row_map_reference(&schedule).expect("sparse/full reference");
        println!("sparse/full row-map reference: green");
        return;
    }
    if let Some(exponent) = mode.strip_prefix("atomic-root-neutral-g-add-l0-") {
        let exponent = exponent.parse::<usize>().expect("shared G exponent 0..=26");
        let report = probe_atomic_state_only_profile22_g_add_shared_power_root_neutral_sumcheck(
            &schedule,
            exponent,
            M31::ONE,
        )
        .expect("same-lane G shared-power root-neutral probe");
        println!("exponent={exponent}");
        println!(
            "root_neutral_rank={}/{} complete={}",
            report.root_neutral_legal_sumcheck_rank_m31, report.legal_sumcheck_m31, report.complete
        );
        println!(
            "mask_only_root_neutral_rank={}",
            report.mask_only_root_neutral_legal_sumcheck_rank_m31
        );
        println!("elapsed_millis={}", report.elapsed_millis);
        return;
    }
    if let Some(exponent) = mode.strip_prefix("atomic-g-add-l0-") {
        let exponent = exponent.parse::<usize>().expect("shared G exponent 0..=26");
        let report = probe_atomic_state_only_profile22_g_add_shared_power_containment(
            &schedule,
            exponent,
            M31::ONE,
        )
        .expect("same-lane G shared-power containment probe");
        println!("exponent={exponent}");
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
            "direct_sum_mask_view_rank={:?}",
            report.witness_direct_sum_mask_view_rank_m31
        );
        println!(
            "physical_augmented_rank={:?} contained={:?}",
            report.witness_direct_sum_physical_augmented_view_rank_m31,
            report.witness_direct_sum_physical_contained
        );
        println!(
            "legal_augmented_rank={:?} contained={:?}",
            report.witness_direct_sum_legal_augmented_view_rank_m31,
            report.witness_direct_sum_legal_contained
        );
        println!("elapsed_millis={}", report.elapsed_millis);
        return;
    }
    if matches!(
        mode.as_str(),
        "atomic-root-neutral-sumcheck"
            | "root-neutral-sumcheck"
            | "atomic-root-neutral-sumcheck-bad-affine"
            | "atomic-root-neutral-complete23"
            | "atomic-root-neutral-complete23-bad-affine"
            | "atomic-root-neutral-shared-degree-cover"
            | "atomic-root-neutral-shared-degree-cover-bad-affine"
    ) {
        let report = if mode.contains("shared-degree-cover") {
            probe_atomic_state_only_profile22_shared_degree_cover_root_neutral_sumcheck(&schedule)
        } else if mode.contains("complete23") {
            probe_atomic_state_only_profile22_complete_shared_power_root_neutral_sumcheck(&schedule)
        } else {
            probe_atomic_state_only_profile22_root_neutral_sumcheck(&schedule)
        }
        .expect("root-neutral sumcheck probe");
        println!("{report:#?}");
        return;
    }
    if matches!(
        mode.as_str(),
        "atomic-shared-degree-cover" | "atomic-shared-degree-cover-bad-affine"
    ) {
        let report = probe_atomic_state_only_profile22_shared_degree_cover_containment(&schedule)
            .expect("shared degree-cover containment probe");
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
            "direct_sum_mask_view_rank={:?}",
            report.witness_direct_sum_mask_view_rank_m31
        );
        println!(
            "physical_augmented_rank={:?} contained={:?}",
            report.witness_direct_sum_physical_augmented_view_rank_m31,
            report.witness_direct_sum_physical_contained
        );
        println!(
            "legal_augmented_rank={:?} contained={:?}",
            report.witness_direct_sum_legal_augmented_view_rank_m31,
            report.witness_direct_sum_legal_contained
        );
        println!("elapsed_millis={}", report.elapsed_millis);
        return;
    }
    if let Some(lane_token) = mode.strip_prefix("atomic-multi-g-dense26-") {
        let lane_token = lane_token.strip_suffix("-bad-affine").unwrap_or(lane_token);
        let lane_count = if lane_token == "all" {
            MULTI_G_DENSE_FAMILIES.len()
        } else {
            lane_token.parse::<usize>().expect("multi-G lane count")
        };
        let factors = multi_g_dense_factors(lane_count).expect("bounded multi-G lane count 1..=16");
        let report = probe_atomic_state_only_profile22_multi_g_mask_rank(&schedule, &factors)
            .expect("multi-G rank probe");
        println!("{report:#?}");
        return;
    }
    if let Some(lane_token) = mode.strip_prefix("atomic-multi-g-powers17-") {
        let lane_token = lane_token.strip_suffix("-bad-affine").unwrap_or(lane_token);
        let lane_count = if lane_token == "all" {
            MULTI_G_DENSE17_EXPONENTS.len()
        } else {
            lane_token.parse::<usize>().expect("multi-G lane count")
        };
        let factors =
            multi_g_dense17_power_factors(lane_count).expect("bounded multi-G lane count 1..=27");
        let report = probe_atomic_state_only_profile22_multi_g_mask_rank(&schedule, &factors)
            .expect("multi-G rank probe");
        println!("{report:#?}");
        return;
    }
    if let Some(lane_token) = mode.strip_prefix("atomic-multi-g-diagonal-") {
        let lane_token = lane_token.strip_suffix("-bad-affine").unwrap_or(lane_token);
        let lane_count = if lane_token == "all" {
            MULTI_G_DENSE_FAMILIES.len()
        } else {
            lane_token.parse::<usize>().expect("multi-G lane count")
        };
        let factors =
            multi_g_diagonal_factors(lane_count).expect("bounded multi-G lane count 1..=16");
        let report = probe_atomic_state_only_profile22_multi_g_mask_rank(&schedule, &factors)
            .expect("multi-G rank probe");
        println!("{report:#?}");
        return;
    }
    let report = match mode.as_str() {
        "tail" => check_state_only_complete_hiding_rank_with_tail_qm31_probe(&schedule),
        "switch" => probe_state_only_late_switch_rank(&schedule, false),
        "switch-shared" => probe_state_only_late_switch_rank(&schedule, true),
        "switch-full-shared" => probe_state_only_full_shared_late_switch_rank(&schedule),
        "baseline-full-shared" => probe_state_only_full_shared_hiding_rank(&schedule),
        "switch-masked-joint" => probe_state_only_masked_single_switch_joint_rank(&schedule),
        "atomic-baseline-full-shared" => probe_atomic_state_only_full_shared_hiding_rank(&schedule),
        "atomic-switch-masked-joint" => {
            probe_atomic_state_only_masked_single_switch_joint_rank(&schedule)
        }
        "switch-distinct" => probe_state_only_root1_distinct_folded_rank(&schedule),
        "log11-upper-g" => probe_state_only_log11_upper_g_rank(&schedule),
        "hybrid-arity8" => probe_state_only_hybrid_arity8_rank(&schedule),
        mode if mode.starts_with("switch-coordinate-shared-") => {
            let columns = mode["switch-coordinate-shared-".len()..]
                .parse::<usize>()
                .expect("coordinate column count");
            probe_state_only_coordinate_factored_late_switch_rank(&schedule, true, columns)
        }
        mode if mode.starts_with("switch-coordinate-") => {
            let columns = mode["switch-coordinate-".len()..]
                .parse::<usize>()
                .expect("coordinate column count");
            probe_state_only_coordinate_factored_late_switch_rank(&schedule, false, columns)
        }
        _ => check_state_only_complete_hiding_rank(&schedule),
    }
    .expect("rank gate");
    println!("{report:#?}");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bounded_multi_g_family_is_exact_and_excludes_degenerate_family_16() {
        assert_eq!(MULTI_G_DENSE_FAMILIES.len(), 16);
        assert!(!MULTI_G_DENSE_FAMILIES.contains(&16));
        assert_eq!(multi_g_dense_factors(0).unwrap(), []);
        assert_eq!(multi_g_dense_factors(16).unwrap().len(), 16);
        assert!(multi_g_dense_factors(17).is_none());
        assert_eq!(multi_g_dense17_power_factors(27).unwrap().len(), 27);
        assert!(multi_g_dense17_power_factors(28).is_none());
        assert_eq!(multi_g_diagonal_factors(16).unwrap().len(), 16);
        assert!(multi_g_diagonal_factors(17).is_none());
    }
}
