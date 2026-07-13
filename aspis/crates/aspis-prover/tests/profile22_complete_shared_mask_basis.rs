//! Host-only guards for the complete shared-factor full-domain M31 mask grid.

use aspis_core::field::{CM31, M31, QM31};
use aspis_core::state_only_hiding::state_only_mask_tower_basis;
use aspis_core::state_only_prefix::{
    run_atomic_state_only_profile21_transcript_schedule_host_unmined_for_diagnostics_v3,
    StateOnlyProfile21Prefix,
};
use aspis_prover::state_only_hiding_rank::{
    complete_shared_mask_missing_lanes, probe_atomic_state_only_complete_shared_mask_basis_rank,
};
use aspis_prover::HOST_HASH;

const ACTUAL_PROFILE21_PROOF: &[u8] = include_bytes!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../results/stage2/proofs/atomic_state_only_profile21_v3_unmined.bin"
));
const STATEMENT_DIGEST: [u8; 32] = [
    0x52, 0xe9, 0x6f, 0x99, 0x75, 0x6f, 0xe8, 0xfd, 0x2d, 0x8b, 0x7a, 0x70, 0x00, 0x19, 0xb1, 0x43,
    0xd7, 0xeb, 0x54, 0x9a, 0xf1, 0xbf, 0x1a, 0xe9, 0x87, 0xe9, 0x9a, 0x75, 0xca, 0xdc, 0xd4, 0xc9,
];

fn schedule() -> aspis_core::state_only_prefix::StateOnlyTranscriptScheduleResult {
    let (prefix, _) = StateOnlyProfile21Prefix::parse_from_proof(ACTUAL_PROFILE21_PROOF).unwrap();
    run_atomic_state_only_profile21_transcript_schedule_host_unmined_for_diagnostics_v3(
        HOST_HASH,
        &prefix,
        &STATEMENT_DIGEST,
    )
    .unwrap()
    .base
}

fn binomial(n: usize, k: usize) -> M31 {
    if k > n {
        return M31::ZERO;
    }
    let k = k.min(n - k);
    let mut value = M31::ONE;
    for step in 0..k {
        value = value
            .mul(M31((n - step) as u32))
            .mul(M31((step + 1) as u32).inv());
    }
    value
}

fn affine_power_right_inverse(target: &[QM31; 27], offset: QM31, slope: M31) -> [QM31; 27] {
    assert_ne!(slope, M31::ZERO);
    let slope_inverse = slope.inv();
    core::array::from_fn(|degree| {
        (degree..27).fold(QM31::ZERO, |sum, source_degree| {
            let scale = slope_inverse
                .pow(source_degree as u64)
                .mul(binomial(source_degree, degree));
            let offset_power = QM31::ZERO.sub(offset).pow((source_degree - degree) as u64);
            sum.add(target[source_degree].mul_m31(scale).mul(offset_power))
        })
    })
}

fn affine_power_coefficients(coefficients: &[QM31; 27], offset: QM31, slope: M31) -> [QM31; 27] {
    core::array::from_fn(|power| {
        (power..27).fold(QM31::ZERO, |sum, degree| {
            let scale = binomial(degree, power).mul(slope.pow(power as u64));
            sum.add(
                coefficients[degree]
                    .mul(offset.pow((degree - power) as u64))
                    .mul_m31(scale),
            )
        })
    })
}

#[test]
fn complete_shared_grid_order_and_local_right_inverses_are_explicit() {
    let lanes = complete_shared_mask_missing_lanes();
    assert_eq!(lanes.len(), 98);
    assert!(lanes.windows(2).all(|pair| {
        (pair[0].degree, pair[0].tower_rotation) < (pair[1].degree, pair[1].tower_rotation)
    }));

    let existing = [
        (1u8, 0u8),
        (3, 1),
        (5, 2),
        (7, 3),
        (9, 0),
        (11, 1),
        (15, 2),
        (17, 3),
        (19, 0),
        (21, 1),
    ];
    for degree in 0..27u8 {
        for rotation in 0..4u8 {
            let multiplicity = usize::from(existing.contains(&(degree, rotation)))
                + usize::from(
                    lanes
                        .iter()
                        .any(|lane| (lane.degree, lane.tower_rotation) == (degree, rotation)),
                );
            assert_eq!(multiplicity, 1);
        }
    }

    // On sumcheck round r the shared form restricts to C+(3+22r)t.  The
    // slope is nonzero in M31, and the formula above is an explicit inverse
    // from ordinary coefficients to the power basis (C+s t)^d.
    let i = state_only_mask_tower_basis(1);
    let u = state_only_mask_tower_basis(2);
    let offset = QM31::ONE.add(i.mul_m31(M31(7))).add(u.mul_m31(M31(11)));
    let target = core::array::from_fn(|degree| {
        QM31::ONE
            .mul_m31(M31((3 + degree) as u32))
            .add(i.mul_m31(M31((5 + 2 * degree) as u32)))
            .add(u.mul_m31(M31((7 + 3 * degree) as u32)))
    });
    for round in 0..10 {
        let slope = M31((3 + 22 * round) as u32);
        assert_ne!(slope, M31::ZERO);
        let inverse = affine_power_right_inverse(&target, offset, slope);
        assert_eq!(affine_power_coefficients(&inverse, offset, slope), target);
    }

    // The four rotations are the frozen M31 basis of QM31, so the local
    // inverse's arbitrary extension-field coefficients can be serialized as
    // four M31 lanes per degree.
    assert_eq!(state_only_mask_tower_basis(0), QM31::ONE);
    assert_eq!(state_only_mask_tower_basis(1), i);
    assert_eq!(state_only_mask_tower_basis(2), u);
    assert_eq!(state_only_mask_tower_basis(3), i.mul(u));
}

#[test]
fn monic_query_kernel_multiplication_has_a_triangular_high_degree_inverse() {
    // This is the q-uniform local fact: for any monic degree-16 g_q, the
    // map h_<16 -> high_16..31(g_q h) is triangular with diagonal one.
    let mut g = [M31::ZERO; 17];
    for (degree, value) in g[..16].iter_mut().enumerate() {
        *value = M31((19 + 13 * degree) as u32);
    }
    g[16] = M31::ONE;
    let target = core::array::from_fn::<_, 16, _>(|index| M31((101 + 17 * index) as u32));
    let mut h = [M31::ZERO; 16];
    for output_degree in (16..32).rev() {
        let input_degree = output_degree - 16;
        let known = ((input_degree + 1)..16).fold(M31::ZERO, |sum, h_degree| {
            sum.add(h[h_degree].mul(g[output_degree - h_degree]))
        });
        h[input_degree] = target[input_degree].sub(known);
    }
    for output_degree in 16usize..32 {
        let coefficient = (0..16).fold(M31::ZERO, |sum, h_degree| {
            let g_degree = output_degree - h_degree;
            if g_degree <= 16 && h_degree + g_degree == output_degree {
                sum.add(h[h_degree].mul(g[g_degree]))
            } else {
                sum
            }
        });
        assert_eq!(coefficient, target[output_degree - 16]);
    }
}

#[test]
#[ignore = "slow exact three-schedule raw-conditioned sumcheck replay"]
fn complete_shared_grid_is_still_rank_deficient_on_both_distinct_q_controls() {
    let frozen_schedule = schedule();
    let mut queries = frozen_schedule.queries[..frozen_schedule.query_count].to_vec();
    queries.sort_unstable();
    queries.dedup();
    assert_eq!(queries.len(), frozen_schedule.query_count);

    let frozen = probe_atomic_state_only_complete_shared_mask_basis_rank(&frozen_schedule).unwrap();
    assert_eq!(frozen.prefix_masked_sumcheck_ranks_m31, [1080]);
    assert_eq!(frozen.minimum_complete_prefix_lanes, Some(0));

    let i = state_only_mask_tower_basis(1);
    let u = state_only_mask_tower_basis(2);
    let mut nonzero_last = frozen_schedule;
    nonzero_last.prefix.z.fill(QM31::ONE);
    nonzero_last.prefix.z[6] = QM31::ZERO;
    nonzero_last.prefix.z[8] = i;
    nonzero_last.prefix.z[9] = u;
    let nonzero = probe_atomic_state_only_complete_shared_mask_basis_rank(&nonzero_last).unwrap();
    assert_eq!(nonzero.prefix_masked_sumcheck_ranks_m31[0], 790);
    assert_eq!(nonzero.prefix_masked_sumcheck_ranks_m31.last(), Some(&808));
    assert_eq!(nonzero.minimum_complete_prefix_lanes, None);
    assert_eq!(nonzero.processed_missing_lanes, 98);

    let mut affine = nonzero_last;
    let thirty_two = QM31::from_cm31(CM31::from_m31(M31(32)));
    affine.prefix.z[0] = QM31::ZERO.sub(thirty_two.add(i).mul_m31(M31(9).inv()));
    let affine = probe_atomic_state_only_complete_shared_mask_basis_rank(&affine).unwrap();
    assert_eq!(affine.prefix_masked_sumcheck_ranks_m31[0], 916);
    assert_eq!(affine.prefix_masked_sumcheck_ranks_m31.last(), Some(&976));
    assert_eq!(affine.minimum_complete_prefix_lanes, None);
    assert_eq!(affine.processed_missing_lanes, 98);
}
