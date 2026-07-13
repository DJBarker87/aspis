//! Host-only complete shared-factor mask-only rank screen.
//!
//! This module completes the ten production full-domain M31 mask-only lanes
//! to the degree/rotation grid
//!
//! `(L_0^d * beta_r)_(0 <= d <= 26, 0 <= r < 4)`.
//!
//! Missing lanes are inserted in degree-major, rotation-minor order.  The
//! probe stops at the first prefix whose separately raw-conditioned masked
//! sumcheck image has the full legal rank.  It changes no proof wire.

use super::*;

const COMPLETE_SHARED_DEGREES: usize = MASK_SUMCHECK_DEGREE;
const COMPLETE_SHARED_ROTATIONS: usize = 4;
const COMPLETE_SHARED_LANES: usize = COMPLETE_SHARED_DEGREES * COMPLETE_SHARED_ROTATIONS;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CompleteSharedMaskLane {
    pub degree: u8,
    pub tower_rotation: u8,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompleteSharedMaskBasisRankReport {
    pub existing_full_domain_lanes: usize,
    pub complete_full_domain_lanes: usize,
    pub missing_full_domain_lanes: usize,
    pub deterministic_missing_lanes: Vec<CompleteSharedMaskLane>,
    /// Entry zero is the production-width control.  Entry `i` is the rank
    /// after the first `i` missing lanes.  Once the target is reached the
    /// remaining monotone prefixes are not recomputed.
    pub prefix_masked_sumcheck_ranks_m31: Vec<usize>,
    pub masked_sumcheck_target_m31: usize,
    pub minimum_complete_prefix_lanes: Option<usize>,
    pub processed_missing_lanes: usize,
    pub every_processed_extra_raw_rank_m31: usize,
    pub factor_schedule_fingerprint: u64,
    pub c1_leaf_bytes_before: usize,
    pub c1_leaf_delta_bytes_per_lane: usize,
    pub q16_opened_value_delta_bytes_per_lane: usize,
    pub three_terminal_delta_bytes_per_lane: usize,
    pub serialized_opening_delta_bytes_at_minimum: Option<usize>,
    pub generator_width_before: usize,
    pub generator_width_at_minimum: Option<usize>,
    pub elapsed_millis: u128,
}

fn existing_full_domain_lane(degree: usize, rotation: usize) -> bool {
    MASK_ONLY_FACTOR_EXPONENTS
        .iter()
        .copied()
        .enumerate()
        .any(|(column, exponent)| exponent == degree && (column & 3) == rotation)
}

pub fn complete_shared_mask_missing_lanes() -> Vec<CompleteSharedMaskLane> {
    (0..COMPLETE_SHARED_DEGREES)
        .flat_map(|degree| {
            (0..COMPLETE_SHARED_ROTATIONS).filter_map(move |tower_rotation| {
                (!existing_full_domain_lane(degree, tower_rotation)).then_some(
                    CompleteSharedMaskLane {
                        degree: degree as u8,
                        tower_rotation: tower_rotation as u8,
                    },
                )
            })
        })
        .collect()
}

fn factor_schedule_fingerprint(lanes: &[CompleteSharedMaskLane]) -> u64 {
    let mut hash = 0xcbf2_9ce4_8422_2325u64;
    for byte in b"aspis/profile22/complete-shared-mask-grid/v1"
        .iter()
        .copied()
        .chain((lanes.len() as u64).to_le_bytes())
        .chain(
            lanes
                .iter()
                .flat_map(|lane| [lane.degree, lane.tower_rotation]),
        )
    {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
    }
    hash
}

fn shared_power_sumcheck_observations(
    row: usize,
    challenges: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
    lagrange: &[[M31; MASK_SUMCHECK_COEFFICIENTS]; MASK_SUMCHECK_COEFFICIENTS],
    degree: usize,
) -> Vec<QM31> {
    let boolean_point = core::array::from_fn(|coordinate| {
        if row & (1 << (STATE_ONLY_HIDING_SUMCHECK_ROUNDS - 1 - coordinate)) == 0 {
            QM31::ZERO
        } else {
            QM31::ONE
        }
    });
    let mut prefix = [QM31::ZERO; STATE_ONLY_HIDING_SUMCHECK_ROUNDS];
    let mut observations = Vec::with_capacity(STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS);
    observations.push(shared_mask_linear(&boolean_point).pow(degree as u64));
    for round in 0..STATE_ONLY_HIDING_SUMCHECK_ROUNDS {
        let samples = core::array::from_fn(|sample| {
            prefix[round] = QM31::from_cm31(CM31::from_m31(M31(sample as u32)));
            for coordinate in round + 1..STATE_ONLY_HIDING_SUMCHECK_ROUNDS {
                prefix[coordinate] =
                    if row & (1 << (STATE_ONLY_HIDING_SUMCHECK_ROUNDS - 1 - coordinate)) == 0 {
                        QM31::ZERO
                    } else {
                        QM31::ONE
                    };
            }
            eq_weight(&prefix, row).mul(shared_mask_linear(&prefix).pow(degree as u64))
        });
        let polynomial = interpolate(&samples, lagrange);
        observations.push(polynomial[0]);
        observations.extend(polynomial[2..].iter().copied());
        prefix[round] = challenges[round];
    }
    debug_assert_eq!(
        observations.len(),
        STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS
    );
    observations
}

fn shared_power_observations(
    degree: usize,
    schedule: &StateOnlyTranscriptScheduleResult,
    lagrange: &[[M31; MASK_SUMCHECK_COEFFICIENTS]; MASK_SUMCHECK_COEFFICIENTS],
) -> Vec<Vec<QM31>> {
    (0..TRACE_ROWS)
        .map(|row| shared_power_sumcheck_observations(row, &schedule.prefix.z, lagrange, degree))
        .collect()
}

fn insert_semantic_lane(
    rows: &[RowPublicMaps],
    cells: &[usize],
    dependent: usize,
    observations: &[Vec<QM31>],
    scale: QM31,
    sumcheck: &mut ColumnEchelon,
) -> Result<(), StateOnlyHidingRankGateError> {
    let raw_rows = rows[0].layer0_m31.len() + 12;
    let mut raw = CarryEchelon::new(raw_rows);
    let active = atomic_state_only_copy_active_rows_v3();
    for &row in cells {
        if row == dependent {
            continue;
        }
        let subtract = active
            .binary_search(&(row as u16))
            .is_err()
            .then_some(dependent);
        let raw_image = c1_raw_difference(rows, row, subtract);
        let carry = scaled_qm31_difference(
            &observations[row],
            subtract.map(|dependent| observations[dependent].as_slice()),
            scale,
        );
        if let CarryReduction::Kernel(kernel) = raw.reduce_with_pivot(raw_image, carry) {
            sumcheck.insert(kernel);
        }
    }
    if raw.rank != raw_rows {
        return Err(StateOnlyHidingRankGateError::RawC1Rank {
            column: usize::MAX,
            got: raw.rank,
            want: raw_rows,
        });
    }
    Ok(())
}

fn insert_full_domain_m31_lane(
    rows: &[RowPublicMaps],
    active: &[bool; TRACE_ROWS],
    dependent: usize,
    observations: &[Vec<QM31>],
    scale: QM31,
    sumcheck: &mut ColumnEchelon,
) -> Result<usize, StateOnlyHidingRankGateError> {
    let raw_rows = rows[0].layer0_m31.len() + 12;
    let mut raw = CarryEchelon::new(raw_rows);
    for row in 0..TRACE_ROWS {
        if row == dependent {
            continue;
        }
        let subtract = (!active[row]).then_some(dependent);
        let raw_image = c1_raw_difference(rows, row, subtract);
        let carry = scaled_qm31_difference(
            &observations[row],
            subtract.map(|dependent| observations[dependent].as_slice()),
            scale,
        );
        if let CarryReduction::Kernel(kernel) = raw.reduce_with_pivot(raw_image, carry) {
            sumcheck.insert(kernel);
        }
    }
    if raw.rank != raw_rows {
        return Err(StateOnlyHidingRankGateError::RawC1Rank {
            column: usize::MAX,
            got: raw.rank,
            want: raw_rows,
        });
    }
    Ok(raw.rank)
}

fn insert_production_g_lane(
    rows: &[RowPublicMaps],
    active: &[bool; TRACE_ROWS],
    dependent: usize,
    schedule: &StateOnlyTranscriptScheduleResult,
    lagrange: &[[M31; MASK_SUMCHECK_COEFFICIENTS]; MASK_SUMCHECK_COEFFICIENTS],
    sumcheck: &mut ColumnEchelon,
) -> Result<(), StateOnlyHidingRankGateError> {
    let observations = (0..TRACE_ROWS)
        .map(|row| {
            mask_sumcheck_observations(
                row,
                &schedule.prefix.z,
                lagrange,
                MaskFactor::ExplicitG,
                FactorSchedule::FullSharedLinear,
                None,
            )
        })
        .collect::<Vec<_>>();
    let raw_rows = 4 * (rows[0].layer0_m31.len() + 3);
    let mut raw = CarryEchelon::new(raw_rows);
    for coordinate in 0..4 {
        let basis = state_only_mask_tower_basis(coordinate);
        for row in 0..TRACE_ROWS {
            if row == dependent {
                continue;
            }
            let subtract = (!active[row]).then_some(dependent);
            let raw_image = qm31_raw_difference(rows, row, subtract, basis);
            let carry = scaled_qm31_difference(
                &observations[row],
                subtract.map(|dependent| observations[dependent].as_slice()),
                basis,
            );
            if let CarryReduction::Kernel(kernel) = raw.reduce_with_pivot(raw_image, carry) {
                sumcheck.insert(kernel);
            }
        }
    }
    if raw.rank != raw_rows {
        return Err(StateOnlyHidingRankGateError::RawGRank {
            got: raw.rank,
            want: raw_rows,
        });
    }
    Ok(())
}

pub fn probe_atomic_state_only_complete_shared_mask_basis_rank(
    schedule: &StateOnlyTranscriptScheduleResult,
) -> Result<CompleteSharedMaskBasisRankReport, StateOnlyHidingRankGateError> {
    let started = Instant::now();
    if schedule.query_count != 16 {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let domain_log = STATE_ONLY_LOG_ROWS + 9;
    let encoder = CircleEncoder::new_for_domain_log(domain_log);
    // RootMessage avoids constructing any later-fold tail.  Only layer-zero
    // symbols and the three terminal values are consumed below.
    let rows = row_public_maps(
        &encoder,
        domain_log,
        schedule,
        PcsSchedule::RootMessage,
        RankLayout::AtomicV3,
    )?;
    let lagrange = lagrange_basis();
    let mut active = [false; TRACE_ROWS];
    for &row in atomic_state_only_copy_active_rows_v3() {
        active[usize::from(row)] = true;
    }
    let global_dependent = (0..TRACE_ROWS)
        .find(|row| !active[*row])
        .ok_or(StateOnlyHidingRankGateError::Layout)?;
    let mut sumcheck = ColumnEchelon::new(4 * STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS);

    let cells = atomic_state_only_relation_free_mask_cells_v3()
        .map_err(|_| StateOnlyHidingRankGateError::Layout)?;
    let mut cells_by_column = vec![Vec::new(); STATE_ONLY_HIDING_C1_COLUMNS];
    for cell in cells {
        cells_by_column[usize::from(cell.column)].push(usize::from(cell.row));
    }
    for (column, cells) in cells_by_column.iter().enumerate() {
        let dependent = cells
            .iter()
            .copied()
            .filter(|row| !active[*row])
            .last()
            .ok_or(StateOnlyHidingRankGateError::Layout)?;
        let observations =
            shared_power_observations(SEMANTIC_FACTOR_EXPONENTS[column], schedule, &lagrange);
        insert_semantic_lane(
            &rows,
            cells,
            dependent,
            &observations,
            state_only_mask_tower_basis(column & 3),
            &mut sumcheck,
        )?;
    }

    for (column, &degree) in MASK_ONLY_FACTOR_EXPONENTS.iter().enumerate() {
        let observations = shared_power_observations(degree, schedule, &lagrange);
        insert_full_domain_m31_lane(
            &rows,
            &active,
            global_dependent,
            &observations,
            state_only_mask_tower_basis(column & 3),
            &mut sumcheck,
        )?;
    }
    insert_production_g_lane(
        &rows,
        &active,
        global_dependent,
        schedule,
        &lagrange,
        &mut sumcheck,
    )?;

    let missing = complete_shared_mask_missing_lanes();
    if missing.len() + STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS != COMPLETE_SHARED_LANES {
        return Err(StateOnlyHidingRankGateError::Layout);
    }
    let mut prefix_ranks = vec![sumcheck.rank];
    let mut processed = 0usize;
    let mut processed_raw_rank = rows[0].layer0_m31.len() + 12;
    let mut cursor = 0usize;
    while cursor < missing.len() && sumcheck.rank != MASK_SUMCHECK_QUOTIENT_M31 {
        let degree = usize::from(missing[cursor].degree);
        let observations = shared_power_observations(degree, schedule, &lagrange);
        while cursor < missing.len()
            && usize::from(missing[cursor].degree) == degree
            && sumcheck.rank != MASK_SUMCHECK_QUOTIENT_M31
        {
            processed_raw_rank = insert_full_domain_m31_lane(
                &rows,
                &active,
                global_dependent,
                &observations,
                state_only_mask_tower_basis(usize::from(missing[cursor].tower_rotation)),
                &mut sumcheck,
            )?;
            processed += 1;
            cursor += 1;
            prefix_ranks.push(sumcheck.rank);
        }
    }
    if sumcheck.rank > MASK_SUMCHECK_QUOTIENT_M31 {
        return Err(StateOnlyHidingRankGateError::Layout);
    }

    let minimum = prefix_ranks
        .iter()
        .position(|rank| *rank == MASK_SUMCHECK_QUOTIENT_M31);
    let c1_leaf_delta_bytes_per_lane = FIBER_SLOTS * core::mem::size_of::<u32>();
    let q16_opened_value_delta_bytes_per_lane = schedule.query_count * c1_leaf_delta_bytes_per_lane;
    let three_terminal_delta_bytes_per_lane = 3 * 16;
    Ok(CompleteSharedMaskBasisRankReport {
        existing_full_domain_lanes: STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS,
        complete_full_domain_lanes: COMPLETE_SHARED_LANES,
        missing_full_domain_lanes: missing.len(),
        factor_schedule_fingerprint: factor_schedule_fingerprint(&missing),
        deterministic_missing_lanes: missing,
        prefix_masked_sumcheck_ranks_m31: prefix_ranks,
        masked_sumcheck_target_m31: MASK_SUMCHECK_QUOTIENT_M31,
        minimum_complete_prefix_lanes: minimum,
        processed_missing_lanes: processed,
        every_processed_extra_raw_rank_m31: processed_raw_rank,
        c1_leaf_bytes_before: FIBER_SLOTS
            * (STATE_ONLY_HIDING_C1_COLUMNS + STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS)
            * core::mem::size_of::<u32>(),
        c1_leaf_delta_bytes_per_lane,
        q16_opened_value_delta_bytes_per_lane,
        three_terminal_delta_bytes_per_lane,
        serialized_opening_delta_bytes_at_minimum: minimum.map(|lanes| {
            lanes * (q16_opened_value_delta_bytes_per_lane + three_terminal_delta_bytes_per_lane)
        }),
        generator_width_before: STATE_ONLY_HIDING_C1_COLUMNS
            + STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS
            + 2,
        generator_width_at_minimum: minimum.map(|lanes| {
            STATE_ONLY_HIDING_C1_COLUMNS + STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS + 2 + lanes
        }),
        elapsed_millis: started.elapsed().as_millis(),
    })
}
