//! Diagnostic rank replay for adversarial-but-valid profile-21 q16 tuples.
//!
//! This is evidence and a counterexample finder, not an all-q theorem.

use std::collections::BTreeMap;
use std::env;
use std::fs;

use aspis_core::circle_fri::line_domain_x_for_circle;
use aspis_core::field::QM31;
use aspis_core::state_only_hiding::state_only_mask_tower_basis;
use aspis_core::state_only_prefix::{
    run_atomic_state_only_profile21_transcript_schedule_host_unmined_for_diagnostics_v3,
    StateOnlyProfile21Prefix,
};
use aspis_prover::state_only_hiding_rank::{
    probe_atomic_state_only_full_shared_tail_qm31_rank,
    probe_atomic_state_only_native_full_root_x_joint_rank,
    probe_atomic_state_only_profile21_full_x_first_later_joint_rank,
    probe_atomic_state_only_profile21_full_x_first_later_polynomial_joint_rank,
    probe_atomic_state_only_profile21_full_x_gamma_kernel_lane_joint_rank,
    probe_atomic_state_only_profile21_full_x_gamma_kernel_polynomial_joint_rank,
    probe_atomic_state_only_profile21_full_x_gamma_lane_joint_rank,
    probe_atomic_state_only_profile21_g2_mask_rank,
    probe_atomic_state_only_profile21_masked_high_switch_joint_rank,
    probe_atomic_state_only_profile21_masked_single_switch_joint_rank,
    probe_atomic_state_only_profile21_semantic_high_shared_c2_switch_joint_rank,
    probe_atomic_state_only_profile21_semantic_high_switch_joint_rank,
    probe_atomic_state_only_profile21_witness_difference_containment,
    probe_atomic_state_only_profile22_complete_shared_power_containment,
    probe_atomic_state_only_profile22_minimal_containment,
    probe_atomic_state_only_profile22_root_neutral_rank,
    probe_atomic_state_only_profile22_weighted_all_inactive_sum_rank,
    probe_atomic_state_only_profile22_weighted_inactive_sum_rank,
    probe_atomic_state_only_profile22_weighted_inactive_sum_rank_for_columns,
    probe_atomic_state_only_profile22_weighted_inactive_sum_root_rank,
    probe_atomic_state_only_profile22_weighted_semantic_inactive_sum_rank_for_columns,
    FirstLaterXMultiplier, TailQm31MaskFactor,
};
use aspis_prover::HOST_HASH;

const STATEMENT_DIGEST: [u8; 32] = [
    0x52, 0xe9, 0x6f, 0x99, 0x75, 0x6f, 0xe8, 0xfd, 0x2d, 0x8b, 0x7a, 0x70, 0x00, 0x19, 0xb1, 0x43,
    0xd7, 0xeb, 0x54, 0x9a, 0xf1, 0xbf, 0x1a, 0xe9, 0x87, 0xe9, 0x9a, 0x75, 0xca, 0xdc, 0xd4, 0xc9,
];

fn main() {
    let requested_mode = env::args().nth(1).unwrap_or_else(|| "actual".into());
    let (switch, mode) = if let Some(mode) = requested_mode.strip_prefix("high-") {
        ("high", mode)
    } else if let Some(mode) = requested_mode.strip_prefix("semhigh-") {
        ("semhigh", mode)
    } else if let Some(mode) = requested_mode.strip_prefix("semhighraw-") {
        ("semhighraw", mode)
    } else if let Some(mode) = requested_mode.strip_prefix("fullx-") {
        ("fullx", mode)
    } else if let Some(mode) = requested_mode.strip_prefix("nativefull-") {
        ("nativefull", mode)
    } else if let Some(mode) = requested_mode.strip_prefix("fullxker-") {
        ("fullxker", mode)
    } else if let Some(mode) = requested_mode.strip_prefix("fullxkerp1-") {
        ("fullxkerp1", mode)
    } else if let Some(mode) = requested_mode.strip_prefix("fullxkerp2-") {
        ("fullxkerp2", mode)
    } else if let Some(mode) = requested_mode.strip_prefix("fullxlate-") {
        ("fullxlate", mode)
    } else if let Some(mode) = requested_mode.strip_prefix("tail-") {
        ("tail", mode)
    } else if let Some(mode) = requested_mode.strip_prefix("witness-") {
        ("witness", mode)
    } else if let Some(mode) = requested_mode.strip_prefix("minimal-") {
        ("minimal", mode)
    } else if let Some(mode) = requested_mode.strip_prefix("auroot-") {
        ("auroot", mode)
    } else if let Some(mode) = requested_mode.strip_prefix("au10-") {
        ("au10", mode)
    } else if let Some(mode) = requested_mode.strip_prefix("as16-") {
        ("as16", mode)
    } else if let Some(mode) = requested_mode.strip_prefix("asu26-") {
        ("asu26", mode)
    } else if let Some(mode) = requested_mode.strip_prefix("au-") {
        ("au", mode)
    } else if let Some(mode) = requested_mode.strip_prefix("complete23-") {
        ("complete23", mode)
    } else if let Some(mode) = requested_mode.strip_prefix("rootneutral-") {
        ("rootneutral", mode)
    } else if let Some(mode) = requested_mode.strip_prefix("g2l26-") {
        ("g2l26", mode)
    } else if let Some(mode) = requested_mode.strip_prefix("g2l23-") {
        ("g2l23", mode)
    } else if let Some(mode) = requested_mode.strip_prefix("g2shared23-") {
        ("g2shared23", mode)
    } else if let Some(mode) = requested_mode.strip_prefix("px1-") {
        ("px1", mode)
    } else if let Some(mode) = requested_mode.strip_prefix("px2-") {
        ("px2", mode)
    } else {
        ("legacy", requested_mode.as_str())
    };
    let path = env::args().nth(2).unwrap_or_else(|| {
        "results/stage2/proofs/atomic_state_only_profile21_v3_unmined.bin".into()
    });
    let proof = fs::read(path).expect("read profile-21 fixture");
    let (prefix, _) =
        StateOnlyProfile21Prefix::parse_from_proof(&proof).expect("profile-21 prefix");
    let mut schedule =
        run_atomic_state_only_profile21_transcript_schedule_host_unmined_for_diagnostics_v3(
            HOST_HASH,
            &prefix,
            &STATEMENT_DIGEST,
        )
        .expect("profile-21 schedule");

    match mode {
        "actual" => {}
        "consecutive" => {
            for (index, query) in schedule.base.queries[..16].iter_mut().enumerate() {
                *query = index as u32;
            }
        }
        "stride8191" => {
            for (index, query) in schedule.base.queries[..16].iter_mut().enumerate() {
                *query = (index as u32) * 8_191;
            }
        }
        "same-coset" => {
            for (index, query) in schedule.base.queries[..16].iter_mut().enumerate() {
                *query = (index as u32) << 13;
            }
        }
        "t16-roots" | "t16-fiber" => {
            let mut roots = Vec::new();
            let mut fibers = BTreeMap::<u32, Vec<u32>>::new();
            for query in 0..(1u32 << 17) {
                let mut value = line_domain_x_for_circle(19, 1, query as usize)
                    .expect("root-one line point");
                for _ in 0..4 {
                    value = value.mul(value).double().sub(aspis_core::field::M31::ONE);
                }
                if value == aspis_core::field::M31::ZERO {
                    roots.push(query);
                }
                fibers.entry(value.0).or_default().push(query);
            }
            if mode == "t16-roots" {
                assert_eq!(roots.len(), 16, "T16 must have exactly 16 root-one roots");
                schedule.base.queries[..16].copy_from_slice(&roots);
            } else {
                let (&target, queries) = fibers
                    .iter()
                    .find(|(_, queries)| queries.len() == 16)
                    .expect("one 16-point T16 fiber");
                assert_ne!(target, 0);
                schedule.base.queries[..16].copy_from_slice(queries);
                println!("t16_target={target}");
            }
        }
        "bad-t8-pair" => {
            let mut fibers = BTreeMap::<u32, Vec<u32>>::new();
            for query in 0..(1u32 << 17) {
                let mut value = line_domain_x_for_circle(19, 1, query as usize)
                    .expect("root-one line point");
                for _ in 0..3 {
                    value = value.mul(value).double().sub(aspis_core::field::M31::ONE);
                }
                fibers.entry(value.0).or_default().push(query);
            }
            let two_inverse = aspis_core::field::M31(2).inv();
            let (left, right) = fibers
                .iter()
                .find_map(|(&left, queries)| {
                    let left = aspis_core::field::M31(left);
                    let right = aspis_core::field::M31::ZERO
                        .sub(two_inverse.mul(left.inv()));
                    fibers
                        .get(&right.0)
                        .filter(|other| queries.len() == 8 && other.len() == 8)
                        .map(|other| (queries, other))
                })
                .expect("two eight-point T8 fibers with product -1/2");
            let mut queries = left.clone();
            queries.extend_from_slice(right);
            queries.sort_unstable();
            queries.dedup();
            assert_eq!(queries.len(), 16);
            schedule.base.queries[..16].copy_from_slice(&queries);
        }
        "boolean-target" => {
            schedule.base.prefix.z.fill(aspis_core::field::QM31::ZERO);
            schedule.base.prefix.point_scale = aspis_core::field::QM31::ONE;
            schedule.base.mu[0].fill(aspis_core::field::QM31::ZERO);
        }
        "boolean-target-consecutive" => {
            for (index, query) in schedule.base.queries[..16].iter_mut().enumerate() {
                *query = index as u32;
            }
            schedule.base.prefix.z.fill(aspis_core::field::QM31::ZERO);
            schedule.base.prefix.point_scale = aspis_core::field::QM31::ONE;
            schedule.base.mu[0].fill(aspis_core::field::QM31::ZERO);
        }
        "unit-front" => {
            // Parser-valid, nonzero challenge stress point.  This is a
            // counterexample search, not an FS transcript fixture: retain
            // the real q16/OOD/fold schedule while collapsing the front
            // affine scalars to the multiplicative identity.
            schedule.base.prefix.eta = aspis_core::field::QM31::ONE;
            schedule.base.prefix.gamma = aspis_core::field::QM31::ONE;
            schedule.base.prefix.point_scale = aspis_core::field::QM31::ONE;
        }
        "unit-folds" => {
            // Same policy as `unit-front`, but collapse every nonzero fold
            // and OOD mixing scalar as well.  Secure-circle/line sample
            // points and the distinct q16 tuple remain unchanged.
            schedule.base.prefix.eta = aspis_core::field::QM31::ONE;
            schedule.base.prefix.gamma = aspis_core::field::QM31::ONE;
            schedule.base.prefix.point_scale = aspis_core::field::QM31::ONE;
            schedule.base.alpha.fill(aspis_core::field::QM31::ONE);
            for mixes in &mut schedule.base.mu {
                mixes.fill(aspis_core::field::QM31::ONE);
            }
        }
        "zero-later" => {
            // Research-only polynomial witness assignment.  Zero is useful
            // for deciding whether the exact containment minors are the zero
            // polynomial; production challenge samplers remain unchanged.
            schedule.base.alpha.fill(aspis_core::field::QM31::ZERO);
            for mixes in &mut schedule.base.mu {
                mixes.fill(aspis_core::field::QM31::ZERO);
            }
        }
        "zero-mixes" => {
            for mixes in &mut schedule.base.mu {
                mixes.fill(aspis_core::field::QM31::ZERO);
            }
        }
        "zero-point-scale" => {
            schedule.base.prefix.point_scale = aspis_core::field::QM31::ZERO;
        }
        "zero-gamma" => {
            // Retired algebraic negative tooth. Profile 22 now samples gamma
            // with exact nonzero rejection, so this is not a parser-valid
            // production schedule. It remains useful for proving that the
            // nonzero premise is load-bearing.
            schedule.base.prefix.gamma = aspis_core::field::QM31::ZERO;
        }
        "minus-one-gamma" => {
            schedule.base.prefix.gamma = aspis_core::field::QM31::ZERO
                .sub(aspis_core::field::QM31::ONE);
        }
        "i-gamma" => {
            schedule.base.prefix.gamma = state_only_mask_tower_basis(1);
        }
        "u-gamma" => {
            schedule.base.prefix.gamma = state_only_mask_tower_basis(2);
        }
        "cube-root-gamma" => {
            let root = (2u32..100)
                .map(|base| {
                    aspis_core::field::M31(base).pow((2_147_483_647u64 - 1) / 3)
                })
                .find(|root| *root != aspis_core::field::M31::ONE)
                .expect("nontrivial M31 cube root");
            schedule.base.prefix.gamma =
                aspis_core::field::QM31::from_cm31(aspis_core::field::CM31::from_m31(root));
        }
        "cube-root-point-scale" => {
            let root = (2u32..100)
                .map(|base| {
                    aspis_core::field::M31(base).pow((2_147_483_647u64 - 1) / 3)
                })
                .find(|root| *root != aspis_core::field::M31::ONE)
                .expect("nontrivial M31 cube root");
            assert_eq!(root.pow(3), aspis_core::field::M31::ONE);
            schedule.base.prefix.point_scale =
                aspis_core::field::QM31::from_cm31(aspis_core::field::CM31::from_m31(root));
        }
        "generic-base-two" => {
            // Research-only negative control for simple nonzero/non-Boolean
            // coordinate conditions.  This keeps every z_v away from 0/1
            // and makes the final affine determinant nonzero, but remains
            // entirely in M31 and therefore cannot supply the twelve M31
            // terminal directions required by each raw block.
            schedule.base.prefix.z.fill(QM31::from_cm31(
                aspis_core::field::CM31::from_m31(aspis_core::field::M31(2)),
            ));
        }
        "generic-tower"
        | "generic-tower-consecutive"
        | "generic-tower-same-coset"
        | "generic-tower-t16-fiber" => {
            // Research-only non-Boolean candidate whose high natural-degree
            // terminal minor is q-independent and full (see the matching
            // privacy regression).  It also keeps the last-round affine
            // determinant nonzero.
            let i = state_only_mask_tower_basis(1);
            let u = state_only_mask_tower_basis(2);
            let iu = i.mul(u);
            schedule.base.prefix.z = core::array::from_fn(|variable| {
                let variable = variable as u32;
                QM31::ONE
                    .mul_m31(aspis_core::field::M31(3 + 3 * variable))
                    .add(i.mul_m31(aspis_core::field::M31(7 + 5 * variable)))
                    .add(u.mul_m31(aspis_core::field::M31(10 + 7 * variable)))
                    .add(iu.mul_m31(aspis_core::field::M31(16 + 11 * variable)))
            });
            if mode == "generic-tower-consecutive" {
                for (index, query) in schedule.base.queries[..16].iter_mut().enumerate() {
                    *query = index as u32;
                }
            } else if mode == "generic-tower-same-coset" {
                for (index, query) in schedule.base.queries[..16].iter_mut().enumerate() {
                    *query = (index as u32) << 13;
                }
            } else if mode == "generic-tower-t16-fiber" {
                let mut fibers = BTreeMap::<u32, Vec<u32>>::new();
                for query in 0..(1u32 << 17) {
                    let mut value = line_domain_x_for_circle(19, 1, query as usize)
                        .expect("root-one line point");
                    for _ in 0..4 {
                        value = value.mul(value).double().sub(aspis_core::field::M31::ONE);
                    }
                    fibers.entry(value.0).or_default().push(query);
                }
                let (_, queries) = fibers
                    .iter()
                    .find(|(target, queries)| **target != 0 && queries.len() == 16)
                    .expect("one nonzero 16-point T16 fiber");
                schedule.base.queries[..16].copy_from_slice(queries);
            }
        }
        "terminal-certificate"
        | "terminal-certificate-consecutive"
        | "terminal-certificate-same-coset" => {
            // Research-only fixed assignment from the all-q semantic
            // terminal certificate.  This is a candidate q-independent
            // witness assignment for the *combined* raw+sumcheck minor; it
            // is not a production transcript fixture.
            let i = state_only_mask_tower_basis(1);
            let u = state_only_mask_tower_basis(2);
            schedule.base.prefix.z.fill(QM31::ONE);
            schedule.base.prefix.z[6] = QM31::ZERO;
            schedule.base.prefix.z[8] = i;
            schedule.base.prefix.z[9] = u;
            if mode == "terminal-certificate-consecutive" {
                for (index, query) in schedule.base.queries[..16].iter_mut().enumerate() {
                    *query = index as u32;
                }
            } else if mode == "terminal-certificate-same-coset" {
                for (index, query) in schedule.base.queries[..16].iter_mut().enumerate() {
                    *query = (index as u32) << 13;
                }
            }
        }
        "last-round-affine-degenerate" => {
            // At the final sumcheck round the two public mask linear forms
            // satisfy
            //   L16 = (1625/201) L0 + (5600/201) * sum_{v<9}(9-v)z_v.
            // Force the affine offset to zero while retaining extension-field
            // coordinates.  Then `1+L16^26` lies in span{1,L0^26} and cannot
            // replace the deliberately missing shared factor L0^23.  This is
            // a parser-valid nonzero-challenge counterexample search for the
            // claimed universal 1080-dimensional sumcheck quotient.
            let i = state_only_mask_tower_basis(1);
            let u = state_only_mask_tower_basis(2);
            schedule.base.prefix.z.fill(QM31::ONE);
            schedule.base.prefix.z[6] = QM31::ZERO;
            schedule.base.prefix.z[7] = QM31::ONE;
            schedule.base.prefix.z[8] = i;
            schedule.base.prefix.z[9] = u;
            let weighted_tail = QM31::from_cm31(aspis_core::field::CM31::from_m31(
                aspis_core::field::M31(32),
            ))
            .add(i);
            schedule.base.prefix.z[0] = QM31::ZERO.sub(
                weighted_tail.mul_m31(aspis_core::field::M31(9).inv()),
            );
            let weighted = schedule.base.prefix.z[..9]
                .iter()
                .enumerate()
                .fold(QM31::ZERO, |sum, (variable, value)| {
                    sum.add(value.mul_m31(aspis_core::field::M31((9 - variable) as u32)))
                });
            assert_eq!(weighted, QM31::ZERO);
        }
        _ => panic!(
            "mode must be actual, consecutive, stride8191, same-coset, t16-roots, t16-fiber, bad-t8-pair, boolean-target, boolean-target-consecutive, unit-front, unit-folds, zero-later, zero-mixes, zero-point-scale, zero-gamma, minus-one-gamma, i-gamma, u-gamma, cube-root-gamma, cube-root-point-scale, generic-base-two, generic-tower, generic-tower-consecutive, generic-tower-same-coset, generic-tower-t16-fiber, terminal-certificate, terminal-certificate-consecutive, terminal-certificate-same-coset, or last-round-affine-degenerate"
        ),
    }

    let auxiliary_delta = QM31::ONE
        .add(state_only_mask_tower_basis(1))
        .add(state_only_mask_tower_basis(2).mul_m31(aspis_core::field::M31(7)))
        .add(state_only_mask_tower_basis(3).mul_m31(aspis_core::field::M31(11)));
    let report = match switch {
        "nativefull" => probe_atomic_state_only_native_full_root_x_joint_rank(
            &schedule.base,
            QM31::ONE
                .add(state_only_mask_tower_basis(1))
                .add(state_only_mask_tower_basis(3)),
        ),
        "high" => probe_atomic_state_only_profile21_masked_high_switch_joint_rank(&schedule),
        "semhigh" => probe_atomic_state_only_profile21_semantic_high_switch_joint_rank(&schedule),
        "semhighraw" => {
            probe_atomic_state_only_profile21_semantic_high_shared_c2_switch_joint_rank(&schedule)
        }
        "fullx" => probe_atomic_state_only_profile21_full_x_gamma_lane_joint_rank(&schedule),
        "fullxker" => {
            probe_atomic_state_only_profile21_full_x_gamma_kernel_lane_joint_rank(&schedule)
        }
        "fullxkerp1" => {
            probe_atomic_state_only_profile21_full_x_gamma_kernel_polynomial_joint_rank(
                &schedule,
                FirstLaterXMultiplier::X2PlusOnePower(1),
            )
        }
        "fullxkerp2" => {
            probe_atomic_state_only_profile21_full_x_gamma_kernel_polynomial_joint_rank(
                &schedule,
                FirstLaterXMultiplier::X2PlusOnePower(2),
            )
        }
        "fullxlate" => probe_atomic_state_only_profile21_full_x_first_later_joint_rank(&schedule),
        "tail" => probe_atomic_state_only_full_shared_tail_qm31_rank(&schedule.base),
        "witness" => {
            probe_atomic_state_only_profile21_witness_difference_containment(&schedule.base)
        }
        "minimal" => probe_atomic_state_only_profile22_minimal_containment(&schedule.base),
        "au" => probe_atomic_state_only_profile22_weighted_inactive_sum_rank(
            &schedule.base,
            auxiliary_delta,
        )
        .map(|weighted| {
            println!(
                "weighted_inactive_sum=selected:{:?} sources:{} claim_rank:{} claim_minor:{:#018x} kernel:{} delta_nonzero:{} pcs:{} conditioned:{:?}/{:?}/{:?}/{:?}",
                weighted.selected_columns,
                weighted.additional_private_sources_m31,
                weighted.aggregate_claim_rank_m31,
                weighted.aggregate_claim_minor.fingerprint,
                weighted.conditioned_kernel_m31,
                weighted.auxiliary_delta_nonzero,
                weighted.pcs_schedule,
                weighted.conditioned_mask_view_rank_m31,
                weighted.conditioned_physical_augmented_view_rank_m31,
                weighted.conditioned_legal_augmented_view_rank_m31,
                weighted.conditioned_helper_augmented_view_rank_m31,
            );
            weighted.complete_view
        }),
        "au10" => probe_atomic_state_only_profile22_weighted_inactive_sum_rank_for_columns(
            &schedule.base,
            auxiliary_delta,
            &(0..10).collect::<Vec<_>>(),
        )
        .map(|weighted| {
            println!(
                "weighted_inactive_sum=selected:{:?} sources:{} claim_rank:{} claim_minor:{:#018x} kernel:{} delta_nonzero:{} pcs:{} conditioned:{:?}/{:?}/{:?}/{:?}",
                weighted.selected_columns,
                weighted.additional_private_sources_m31,
                weighted.aggregate_claim_rank_m31,
                weighted.aggregate_claim_minor.fingerprint,
                weighted.conditioned_kernel_m31,
                weighted.auxiliary_delta_nonzero,
                weighted.pcs_schedule,
                weighted.conditioned_mask_view_rank_m31,
                weighted.conditioned_physical_augmented_view_rank_m31,
                weighted.conditioned_legal_augmented_view_rank_m31,
                weighted.conditioned_helper_augmented_view_rank_m31,
            );
            weighted.complete_view
        }),
        "as16" =>
            probe_atomic_state_only_profile22_weighted_semantic_inactive_sum_rank_for_columns(
                &schedule.base,
                auxiliary_delta,
                &(0..16).collect::<Vec<_>>(),
            )
            .map(|weighted| {
                println!(
                    "weighted_inactive_sum=group:{} selected:{:?} sources:{} claim_rank:{} claim_minor:{:#018x} kernel:{} delta_nonzero:{} pcs:{} conditioned:{:?}/{:?}/{:?}/{:?} unbalanced:{:?}",
                    weighted.source_group,
                    weighted.selected_columns,
                    weighted.additional_private_sources_m31,
                    weighted.aggregate_claim_rank_m31,
                    weighted.aggregate_claim_minor.fingerprint,
                    weighted.conditioned_kernel_m31,
                    weighted.auxiliary_delta_nonzero,
                    weighted.pcs_schedule,
                    weighted.conditioned_mask_view_rank_m31,
                    weighted.conditioned_physical_augmented_view_rank_m31,
                    weighted.conditioned_legal_augmented_view_rank_m31,
                    weighted.conditioned_helper_augmented_view_rank_m31,
                    weighted.conditioned_unbalanced_physical_augmented_view_rank_m31,
                );
                weighted.complete_view
            }),
        "asu26" => probe_atomic_state_only_profile22_weighted_all_inactive_sum_rank(
            &schedule.base,
            auxiliary_delta,
        )
        .map(|weighted| {
            println!(
                "weighted_inactive_sum=group:{} selected:{:?} sources:{} claim_rank:{} claim_minor:{:#018x} kernel:{} delta_nonzero:{} pcs:{} conditioned:{:?}/{:?}/{:?}/{:?} unbalanced:{:?}",
                weighted.source_group,
                weighted.selected_columns,
                weighted.additional_private_sources_m31,
                weighted.aggregate_claim_rank_m31,
                weighted.aggregate_claim_minor.fingerprint,
                weighted.conditioned_kernel_m31,
                weighted.auxiliary_delta_nonzero,
                weighted.pcs_schedule,
                weighted.conditioned_mask_view_rank_m31,
                weighted.conditioned_physical_augmented_view_rank_m31,
                weighted.conditioned_legal_augmented_view_rank_m31,
                weighted.conditioned_helper_augmented_view_rank_m31,
                weighted.conditioned_unbalanced_physical_augmented_view_rank_m31,
            );
            weighted.complete_view
        }),
        "auroot" => probe_atomic_state_only_profile22_weighted_inactive_sum_root_rank(
            &schedule.base,
            auxiliary_delta,
        )
        .map(|weighted| {
            println!(
                "weighted_inactive_sum=selected:{:?} sources:{} claim_rank:{} claim_minor:{:#018x} kernel:{} delta_nonzero:{} pcs:{} conditioned:{:?}/{:?}/{:?}/{:?}",
                weighted.selected_columns,
                weighted.additional_private_sources_m31,
                weighted.aggregate_claim_rank_m31,
                weighted.aggregate_claim_minor.fingerprint,
                weighted.conditioned_kernel_m31,
                weighted.auxiliary_delta_nonzero,
                weighted.pcs_schedule,
                weighted.conditioned_mask_view_rank_m31,
                weighted.conditioned_physical_augmented_view_rank_m31,
                weighted.conditioned_legal_augmented_view_rank_m31,
                weighted.conditioned_helper_augmented_view_rank_m31,
            );
            weighted.complete_view
        }),
        "complete23" => {
            probe_atomic_state_only_profile22_complete_shared_power_containment(&schedule.base)
        }
        "rootneutral" => probe_atomic_state_only_profile22_root_neutral_rank(&schedule.base),
        "g2l26" => probe_atomic_state_only_profile21_g2_mask_rank(
            &schedule.base,
            TailQm31MaskFactor::Dense17Pow26AddOne,
        ),
        "g2l23" => probe_atomic_state_only_profile21_g2_mask_rank(
            &schedule.base,
            TailQm31MaskFactor::Dense17Pow23,
        ),
        "g2shared23" => probe_atomic_state_only_profile21_g2_mask_rank(
            &schedule.base,
            TailQm31MaskFactor::Shared0Pow23,
        ),
        "px1" => probe_atomic_state_only_profile21_full_x_first_later_polynomial_joint_rank(
            &schedule,
            FirstLaterXMultiplier::X2PlusOnePower(1),
        ),
        "px2" => probe_atomic_state_only_profile21_full_x_first_later_polynomial_joint_rank(
            &schedule,
            FirstLaterXMultiplier::X2PlusOnePower(2),
        ),
        _ => probe_atomic_state_only_profile21_masked_single_switch_joint_rank(&schedule),
    }
    .expect("complete-view rank replay");
    println!("mode={requested_mode}");
    println!("queries={:?}", &schedule.base.queries[..16]);
    println!("complete_ambient_rank={}", report.complete_ambient_rank);
    println!("tail_qm31_mask_factor={}", report.tail_qm31_mask_factor);
    println!(
        "first_later_x_multiplier={} degree={}",
        report.first_later_x_multiplier, report.first_later_x_multiplier_degree
    );
    println!("masked_sumcheck_rank={}", report.masked_sumcheck_rank);
    let masked_sumcheck_structure_fingerprint = report
        .masked_sumcheck_minor
        .source_columns
        .iter()
        .chain(&report.masked_sumcheck_minor.pivot_rows)
        .fold(0xcbf2_9ce4_8422_2325u64, |hash, &value| {
            (hash ^ value as u64).wrapping_mul(0x100_0000_01b3)
        });
    println!(
        "raw_opening_minor={:#018x} masked_sumcheck_minor={:#018x} joint_raw_sumcheck_minor={:#018x} structure={:#018x} sources={} rows={}",
        report.raw_opening_minor.fingerprint,
        report.masked_sumcheck_minor.fingerprint,
        report.joint_raw_sumcheck_minor.fingerprint,
        masked_sumcheck_structure_fingerprint,
        report.masked_sumcheck_minor.source_columns.len(),
        report.masked_sumcheck_minor.pivot_rows.len(),
    );
    if env::var_os("ASPIS_DUMP_MASKED_SUMCHECK_MINOR").is_some() {
        println!(
            "masked_sumcheck_minor_sources={:?}",
            report.masked_sumcheck_minor.source_columns
        );
        println!(
            "masked_sumcheck_minor_rows={:?}",
            report.masked_sumcheck_minor.pivot_rows
        );
    }
    println!("joint_pcs_rank={}", report.joint_pcs_rank);
    println!("joint_pcs_declared_rank={}", report.joint_pcs_declared_rank);
    println!("tail_qm31_basis_m31={}", report.tail_qm31_basis_m31);
    println!(
        "tail_qm31_raw_kernel_m31={}",
        report.tail_qm31_raw_kernel_m31
    );
    println!("pre_helper_pcs_rank={}", report.pre_helper_pcs_rank);
    println!(
        "witness_semantic_superset={}/{} generators={}",
        report.joint_pcs_rank,
        report.witness_semantic_superset_rank,
        report.witness_semantic_superset_generators_m31
    );
    println!(
        "witness_legal_sumcheck={}/{} generators={}",
        report.joint_pcs_rank,
        report.witness_legal_sumcheck_rank,
        report.witness_legal_sumcheck_generators_m31
    );
    println!(
        "witness_compatibility_rank_m31={}",
        report.witness_compatibility_rank_m31
    );
    println!(
        "witness_direct_sum_view_ranks=mask:{:?} physical:{:?} legal:{:?} helper:{:?}",
        report.witness_direct_sum_mask_view_rank_m31,
        report.witness_direct_sum_physical_augmented_view_rank_m31,
        report.witness_direct_sum_legal_augmented_view_rank_m31,
        report.witness_direct_sum_helper_augmented_view_rank_m31,
    );
    println!(
        "witness_direct_sum_contained=physical:{:?} legal:{:?} helper:{:?}",
        report.witness_direct_sum_physical_contained,
        report.witness_direct_sum_legal_contained,
        report.witness_direct_sum_helper_contained,
    );
    println!(
        "witness_direct_sum_unbalanced_physical=rank:{:?} contained:{:?}",
        report.witness_direct_sum_unbalanced_physical_augmented_view_rank_m31,
        report.witness_direct_sum_unbalanced_physical_contained,
    );
    println!(
        "witness_coupled_view_ranks=physical:{:?} legal:{:?} helper:{:?}",
        report.witness_coupled_physical_augmented_view_rank_m31,
        report.witness_coupled_legal_augmented_view_rank_m31,
        report.witness_coupled_helper_augmented_view_rank_m31,
    );
    println!(
        "witness_coupled_contained=physical:{:?} legal:{:?} helper:{:?}",
        report.witness_coupled_physical_contained,
        report.witness_coupled_legal_contained,
        report.witness_coupled_helper_contained,
    );
    println!(
        "witness_coupled_terminal_kernel=generators:{} dependent:{:?} fingerprint:{:#018x} identity_guard:{}",
        report.witness_coupled_legal_sumcheck_generators_m31,
        report.witness_coupled_terminal_dependent_observation,
        report.witness_coupled_terminal_functional_fingerprint,
        report.witness_coupled_terminal_identity_guard,
    );
    println!(
        "witness_terminal_kernel_proof=raw_kernel_sources:{} raw_kernel_zero:{} h_zero:{} image_equals_kernel:{} compatibility_map_rank:{} compatibility_map_fingerprint:{:#018x}",
        report.witness_mask_raw_kernel_terminal_zero_sources_m31,
        report.witness_mask_raw_kernel_terminal_zero_guard,
        report.witness_h_zero_sumcheck_terminal_guard,
        report.witness_mask_sumcheck_equals_terminal_kernel,
        report.witness_compatibility_terminal_map_rank_m31,
        report.witness_compatibility_terminal_map_fingerprint,
    );
    println!(
        "witness_compatibility_pivot_sources={:?}",
        report.witness_compatibility_pivot_sources
    );
    println!(
        "witness_compatibility_pivot_rows_m31={:?}",
        report.witness_compatibility_pivot_rows_m31
    );
    println!(
        "witness_semantic_kernel_coefficients_m31={:?}",
        report.witness_semantic_kernel_coefficients_m31
    );
    println!(
        "witness_physical_sparse_dense_guard={} fingerprint={:#018x}",
        report.witness_semantic_sparse_dense_guard,
        report.witness_semantic_sparse_dense_fingerprint,
    );
    println!(
        "witness_semantic_minor={:#018x} sources={:?} rows={:?} values={:?}",
        report.witness_semantic_superset_minor.fingerprint,
        report.witness_semantic_superset_minor.source_columns,
        report.witness_semantic_superset_minor.pivot_rows,
        report.witness_semantic_superset_minor.pivot_values_m31,
    );
    println!(
        "witness_unbalanced_upper_oracle={}/{} generators={} compatibility_rank={} pivots={:?}",
        report.joint_pcs_rank,
        report.witness_unbalanced_semantic_superset_rank,
        report.witness_unbalanced_semantic_superset_generators_m31,
        report.witness_unbalanced_compatibility_rank_m31,
        report.witness_unbalanced_compatibility_pivot_sources,
    );
    println!(
        "witness_unbalanced_sparse_dense_guard={} fingerprint={:#018x}",
        report.witness_unbalanced_sparse_dense_guard,
        report.witness_unbalanced_sparse_dense_fingerprint,
    );
    println!(
        "witness_unbalanced_minor={:#018x} sources={:?} rows={:?} values={:?}",
        report
            .witness_unbalanced_semantic_superset_minor
            .fingerprint,
        report
            .witness_unbalanced_semantic_superset_minor
            .source_columns,
        report.witness_unbalanced_semantic_superset_minor.pivot_rows,
        report
            .witness_unbalanced_semantic_superset_minor
            .pivot_values_m31,
    );
    println!(
        "witness_sumcheck_minor={:#018x} sources={:?} rows={:?}",
        report.witness_legal_sumcheck_minor.fingerprint,
        report.witness_legal_sumcheck_minor.source_columns,
        report.witness_legal_sumcheck_minor.pivot_rows
    );
    println!(
        "late_switch_conditioned_rank={}",
        report.late_switch_conditioned_rank
    );
    println!(
        "late_switch_source_rows={:?}",
        report.late_switch_source_rows
    );
    println!(
        "switch_variables={} folded_observation_rank={} folded_kernel={} shared_raw_observation_rank={} shared_raw_kernel={} conditioned_kernel={}",
        report.masked_switch_variables_qm31,
        report.masked_switch_observation_rank_qm31,
        report.masked_switch_kernel_qm31,
        report.masked_switch_shared_c2_observation_rank_qm31,
        report.masked_switch_shared_c2_kernel_qm31,
        report.late_switch_conditioned_kernel_qm31,
    );
    println!(
        "switch_q_randomness_rank={} q_coopening_rank={} basis_rank={} basis_fingerprint={:#018x}",
        report.masked_switch_q_randomness_rank_qm31,
        report.masked_switch_q_coopening_rank_qm31,
        report.masked_switch_code_basis_rank_m31,
        report.masked_switch_code_basis_fingerprint,
    );
    println!(
        "switch_size_shared_root_bytes={} standalone_bytes={} frontier_nodes={}",
        report.masked_switch_shared_root_increment_bytes,
        report.masked_switch_standalone_increment_bytes,
        report.masked_switch_standalone_frontier_nodes,
    );
    println!(
        "late_switch_semantic={}->{} contained={} pivots={:?}",
        report.late_switch_conditioned_rank,
        report.late_switch_semantic_augmented_rank,
        report.late_switch_contains_conservative_semantic_superset,
        report.late_switch_semantic_new_pivots_m31
    );
    println!(
        "switch_without_u_rank={} kernel={} u_redundant={}",
        report.masked_switch_without_u_observation_rank_qm31,
        report.masked_switch_without_u_kernel_qm31,
        report.masked_switch_u_observation_rank_redundant
    );
    println!(
        "late_switch_ambient_deficit_m31={}",
        report.late_switch_ambient_deficit_m31
    );
    println!(
        "post_sumcheck_minor={:#018x}",
        report.post_sumcheck_pcs_minor.fingerprint
    );
    println!(
        "switch_observation_minor={:#018x}",
        report.late_switch_observation_minor.fingerprint
    );
    println!(
        "switch_complement_minor={:#018x}",
        report.late_switch_complement_minor.fingerprint
    );
    println!(
        "switch_complement_sources={:?}",
        report.late_switch_complement_minor.source_columns
    );
    println!(
        "switch_complement_rows={:?}",
        report.late_switch_complement_minor.pivot_rows
    );
    println!(
        "switch_observation_sources={:?}",
        report.late_switch_observation_minor.source_columns
    );
    println!(
        "switch_observation_rows={:?}",
        report.late_switch_observation_minor.pivot_rows
    );
    println!("elapsed_millis={}", report.elapsed_millis);
}
