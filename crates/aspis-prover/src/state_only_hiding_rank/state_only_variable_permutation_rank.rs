//! Exact, production-neutral row-bit permutation screen for the early-p0
//! hiding quotient.
//!
//! For first variable `b`, the physical coefficient coordinates are ordered
//! `pi_b = [b, 0, ..., b-1, b+1, ..., 9]`.  The successor and xor points are
//! conjugated by this permutation.  Applying successor/xor directly to the
//! reordered point would change the statement map and is deliberately not
//! modelled here.

use std::collections::BTreeSet;
use std::time::Instant;

use aspis_core::sumcheck::SUMCHECK_COEFFICIENTS;

use super::*;

const P0_QM31: usize = SUMCHECK_COEFFICIENTS;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AtomicProfile21VariablePermutationP0RankReport {
    pub first_logical_variable: usize,
    pub physical_to_logical_coordinates: [usize; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
    pub conjugation_guard_run: bool,
    pub conjugation_guard_passed: bool,
    pub inactive_low_mask_groups: usize,
    pub baseline_inactive_low_mask_groups: usize,
    pub preserves_grouped_inactive_shape: bool,
    pub raw_c1_rank_m31: usize,
    pub raw_g_rank_m31: usize,
    pub masked_sumcheck_rank_m31: usize,
    pub p0_view_m31: usize,
    pub p0_mask_rank_m31: usize,
    pub p0_semantic_augmented_rank_m31: usize,
    pub p0_legal_sumcheck_augmented_rank_m31: usize,
    pub p0_semantic_new_pivots_m31: Vec<usize>,
    pub p0_legal_sumcheck_new_pivots_m31: Vec<usize>,
    pub p0_contains_conservative_semantic_and_legal_sumcheck: bool,
    pub elapsed_millis: u128,
}

#[derive(Clone, Copy)]
struct BitPermutation {
    physical_to_logical: [usize; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
    logical_to_physical: [usize; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
}

impl BitPermutation {
    fn stable_first(first: usize) -> Option<Self> {
        if first >= STATE_ONLY_HIDING_SUMCHECK_ROUNDS {
            return None;
        }
        let mut physical_to_logical = [0usize; STATE_ONLY_HIDING_SUMCHECK_ROUNDS];
        physical_to_logical[0] = first;
        let mut cursor = 1usize;
        for logical in 0..STATE_ONLY_HIDING_SUMCHECK_ROUNDS {
            if logical != first {
                physical_to_logical[cursor] = logical;
                cursor += 1;
            }
        }
        let mut logical_to_physical = [0usize; STATE_ONLY_HIDING_SUMCHECK_ROUNDS];
        for (physical, logical) in physical_to_logical.iter().copied().enumerate() {
            logical_to_physical[logical] = physical;
        }
        Some(Self {
            physical_to_logical,
            logical_to_physical,
        })
    }

    fn logical_row_to_physical(self, logical_row: usize) -> usize {
        debug_assert!(logical_row < TRACE_ROWS);
        let mut physical_row = 0usize;
        for physical in 0..STATE_ONLY_HIDING_SUMCHECK_ROUNDS {
            let logical = self.physical_to_logical[physical];
            let bit = (logical_row >> (STATE_ONLY_HIDING_SUMCHECK_ROUNDS - 1 - logical)) & 1;
            physical_row |= bit << (STATE_ONLY_HIDING_SUMCHECK_ROUNDS - 1 - physical);
        }
        physical_row
    }

    fn physical_point_to_logical(
        self,
        physical: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
    ) -> [QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS] {
        core::array::from_fn(|logical| physical[self.logical_to_physical[logical]])
    }

    fn logical_point_to_physical(
        self,
        logical: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
    ) -> [QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS] {
        core::array::from_fn(|physical| logical[self.physical_to_logical[physical]])
    }
}

fn permuted_active(permutation: BitPermutation) -> [bool; TRACE_ROWS] {
    let mut active = [false; TRACE_ROWS];
    for &logical in rank_active_rows(RankLayout::AtomicV3) {
        active[permutation.logical_row_to_physical(usize::from(logical))] = true;
    }
    active
}

fn permuted_inactive_masks(permutation: BitPermutation) -> [u16; 64] {
    let logical = rank_inactive_masks(RankLayout::AtomicV3);
    let mut physical = [0u16; 64];
    for logical_row in 0..TRACE_ROWS {
        if ((logical[logical_row >> 4] >> (logical_row & 15)) & 1) == 0 {
            continue;
        }
        let physical_row = permutation.logical_row_to_physical(logical_row);
        physical[physical_row >> 4] |= 1 << (physical_row & 15);
    }
    physical
}

fn low_mask_group_count(masks: &[u16; 64]) -> usize {
    masks.iter().copied().collect::<BTreeSet<_>>().len()
}

fn conjugated_terminal_points(
    schedule: &StateOnlyTranscriptScheduleResult,
    permutation: BitPermutation,
) -> [[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS]; 3] {
    let logical_z = permutation.physical_point_to_logical(&schedule.prefix.z);
    [
        schedule.prefix.z,
        permutation.logical_point_to_physical(&binary_successor_point(&logical_z)),
        permutation.logical_point_to_physical(&xor12_point(&logical_z)),
    ]
}

fn initial_weights_for_points(
    schedule: &StateOnlyTranscriptScheduleResult,
    points: &[[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS]; 3],
    inactive_masks: [u16; 64],
) -> Result<WeightAccumulator, StateOnlyHidingRankGateError> {
    let mut weights = WeightAccumulator::empty(STATE_ONLY_LOG_ROWS);
    let kappa = schedule.prefix.point_scale;
    for (point, scale) in points.iter().zip([QM31::ONE, kappa, kappa.square()]) {
        weights
            .add_multilinear(scale, point.to_vec())
            .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
    }
    weights
        .add_grouped_64x16_binary_masks(inactive_masks)
        .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
    Ok(weights)
}

/// All seven coefficients of the round-zero relation polynomial for every
/// physical unit message.  This is the literal arity-four dual polynomial,
/// not a synthetic projection onto the currently observed coefficient-zero
/// pivot.
fn p0_unit_rows(weights: &WeightAccumulator) -> Vec<[QM31; P0_QM31]> {
    let quarter = M31(4).inv();
    let mut rows = vec![[QM31::ZERO; P0_QM31]; TRACE_ROWS];
    for chunk in 0..TRACE_ROWS / FIBER_SLOTS {
        let base = FIBER_SLOTS * chunk;
        let values = core::array::from_fn::<_, FIBER_SLOTS, _>(|slot| {
            weights.weight_at((base + slot) as u32)
        });
        let dual = [values[0], values[3], values[2], values[1]].map(|value| value.mul_m31(quarter));
        for slot in 0..FIBER_SLOTS {
            for (degree, value) in dual.iter().copied().enumerate() {
                rows[base + slot][slot + degree] = value;
            }
        }
    }
    rows
}

fn deterministic_guard_coefficients() -> Vec<QM31> {
    (0..TRACE_ROWS)
        .map(|row| {
            QM31::from_cm31(CM31::from_m31(M31(
                ((17usize.wrapping_mul(row) + 29) % 2_147_483_647) as u32,
            )))
        })
        .collect()
}

fn dense_conjugation_guard(
    schedule: &StateOnlyTranscriptScheduleResult,
    permutation: BitPermutation,
    points: &[[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS]; 3],
    inactive_masks: [u16; 64],
    structured_weights: &WeightAccumulator,
    p0_rows: &[[QM31; P0_QM31]],
) -> Result<bool, StateOnlyHidingRankGateError> {
    let kappa = schedule.prefix.point_scale;
    let scales = [QM31::ONE, kappa, kappa.square()];
    let dense_weights = (0..TRACE_ROWS)
        .map(|row| {
            let evaluation = points
                .iter()
                .zip(scales)
                .fold(QM31::ZERO, |sum, (point, scale)| {
                    sum.add(scale.mul(eq_weight(point, row)))
                });
            if ((inactive_masks[row >> 4] >> (row & 15)) & 1) != 0 {
                evaluation.add(QM31::ONE)
            } else {
                evaluation
            }
        })
        .collect::<Vec<_>>();
    if dense_weights
        .iter()
        .copied()
        .enumerate()
        .any(|(row, value)| structured_weights.weight_at(row as u32) != value)
    {
        return Ok(false);
    }

    let coefficients = deterministic_guard_coefficients();
    let fast = coefficients.iter().copied().zip(p0_rows).fold(
        [QM31::ZERO; P0_QM31],
        |mut sum, (coefficient, row)| {
            for (target, value) in sum.iter_mut().zip(row) {
                *target = target.add(coefficient.mul(*value));
            }
            sum
        },
    );
    let structured = polynomial_for_extension(&coefficients, structured_weights);
    let mut dense_accumulator = WeightAccumulator::empty(STATE_ONLY_LOG_ROWS);
    dense_accumulator
        .add_dense(dense_weights)
        .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
    let dense = polynomial_for_extension(&coefficients, &dense_accumulator);
    if fast != structured || structured != dense {
        return Ok(false);
    }

    // Independently guard the conjugated statement points.  A logical word
    // reindexed into physical coefficient order must retain all three values.
    let logical_coefficients = deterministic_guard_coefficients();
    let mut physical_coefficients = vec![QM31::ZERO; TRACE_ROWS];
    for (logical_row, value) in logical_coefficients.iter().copied().enumerate() {
        physical_coefficients[permutation.logical_row_to_physical(logical_row)] = value;
    }
    let logical_z = permutation.physical_point_to_logical(&schedule.prefix.z);
    let logical_points = [
        logical_z,
        binary_successor_point(&logical_z),
        xor12_point(&logical_z),
    ];
    for point in 0..3 {
        let logical_value = logical_coefficients
            .iter()
            .copied()
            .enumerate()
            .fold(QM31::ZERO, |sum, (row, value)| {
                sum.add(value.mul(eq_weight(&logical_points[point], row)))
            });
        let physical_value = physical_coefficients
            .iter()
            .copied()
            .enumerate()
            .fold(QM31::ZERO, |sum, (row, value)| {
                sum.add(value.mul(eq_weight(&points[point], row)))
            });
        if logical_value != physical_value {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Cache shared by all ten first-variable screens.  Layer-zero circle
/// openings and masked-sumcheck row maps are independent of the row-bit
/// interpretation; only terminal maps and p0 are rebuilt per permutation.
pub struct AtomicProfile21VariablePermutationP0Probe {
    layer0_rows: Vec<Vec<M31>>,
    semantic_observations: Vec<Vec<Vec<QM31>>>,
    mask_only_observations: Vec<Vec<Vec<QM31>>>,
    g_observations: Vec<Vec<QM31>>,
    baseline_inactive_low_mask_groups: usize,
}

impl AtomicProfile21VariablePermutationP0Probe {
    pub fn new(
        schedule: &StateOnlyTranscriptScheduleResult,
    ) -> Result<Self, StateOnlyHidingRankGateError> {
        if schedule.query_count != 16
            || schedule.prefix.z.len() != STATE_ONLY_HIDING_SUMCHECK_ROUNDS
        {
            return Err(StateOnlyHidingRankGateError::Shape);
        }
        let domain_log = STATE_ONLY_LOG_ROWS + 9;
        let encoder = CircleEncoder::new_for_domain_log(domain_log);
        let indices = derive_circle_line_query_indices_for_count(
            &schedule.queries[..schedule.query_count],
            encoder.codeword_len() / FIBER_SLOTS,
        )
        .map_err(|_| StateOnlyHidingRankGateError::Shape)?;
        let mut layer0_rows = Vec::with_capacity(TRACE_ROWS);
        for row in 0..TRACE_ROWS {
            let mut layer0 = Vec::with_capacity(indices.layer0.len() * FIBER_SLOTS);
            for &query in &indices.layer0 {
                for slot in 0..FIBER_SLOTS {
                    layer0.push(
                        encoder.encode_c1_basis_value(row, FIBER_SLOTS * query as usize + slot)?,
                    );
                }
            }
            layer0_rows.push(layer0);
        }

        let lagrange = lagrange_basis();
        let semantic_observations = (0..STATE_ONLY_HIDING_C1_COLUMNS)
            .map(|column| {
                (0..TRACE_ROWS)
                    .map(|row| {
                        mask_sumcheck_observations(
                            row,
                            &schedule.prefix.z,
                            &lagrange,
                            MaskFactor::Semantic(column),
                            FactorSchedule::FullSharedLinear,
                            None,
                        )
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let mask_only_observations = (0..STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS)
            .map(|column| {
                (0..TRACE_ROWS)
                    .map(|row| {
                        mask_sumcheck_observations(
                            row,
                            &schedule.prefix.z,
                            &lagrange,
                            MaskFactor::MaskOnly(column),
                            FactorSchedule::FullSharedLinear,
                            None,
                        )
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let g_observations = (0..TRACE_ROWS)
            .map(|row| {
                mask_sumcheck_observations(
                    row,
                    &schedule.prefix.z,
                    &lagrange,
                    MaskFactor::ExplicitG,
                    FactorSchedule::FullSharedLinear,
                    None,
                )
            })
            .collect::<Vec<_>>();
        let baseline_inactive_low_mask_groups =
            low_mask_group_count(&rank_inactive_masks(RankLayout::AtomicV3));
        Ok(Self {
            layer0_rows,
            semantic_observations,
            mask_only_observations,
            g_observations,
            baseline_inactive_low_mask_groups,
        })
    }

    pub fn probe_first_variable(
        &self,
        schedule: &StateOnlyTranscriptScheduleResult,
        first_logical_variable: usize,
    ) -> Result<AtomicProfile21VariablePermutationP0RankReport, StateOnlyHidingRankGateError> {
        let started = Instant::now();
        let permutation = BitPermutation::stable_first(first_logical_variable)
            .ok_or(StateOnlyHidingRankGateError::Shape)?;
        let active = permuted_active(permutation);
        let inactive = (0..TRACE_ROWS)
            .filter(|row| !active[*row])
            .collect::<Vec<_>>();
        let global_dependent = inactive[0];
        let inactive_masks = permuted_inactive_masks(permutation);
        let inactive_low_mask_groups = low_mask_group_count(&inactive_masks);
        let points = conjugated_terminal_points(schedule, permutation);
        let weights = initial_weights_for_points(schedule, &points, inactive_masks)?;
        let p0_units = p0_unit_rows(&weights);
        let conjugation_guard_run = first_logical_variable == 0 || first_logical_variable == 7;
        let conjugation_guard_passed = !conjugation_guard_run
            || dense_conjugation_guard(
                schedule,
                permutation,
                &points,
                inactive_masks,
                &weights,
                &p0_units,
            )?;
        if !conjugation_guard_passed {
            return Err(StateOnlyHidingRankGateError::Relation);
        }

        let rows = (0..TRACE_ROWS)
            .map(|row| {
                let pcs_tail = if row == global_dependent {
                    vec![QM31::ZERO; P0_QM31]
                } else if active[row] {
                    p0_units[row].to_vec()
                } else {
                    p0_units[row]
                        .iter()
                        .copied()
                        .zip(p0_units[global_dependent])
                        .map(|(value, dependent)| value.sub(dependent))
                        .collect()
                };
                RowPublicMaps {
                    layer0_m31: self.layer0_rows[row].clone(),
                    terminal: core::array::from_fn(|point| eq_weight(&points[point], row)),
                    pcs_tail,
                }
            })
            .collect::<Vec<_>>();
        let layer0_m31 = rows[0].layer0_m31.len();
        let c1_raw_m31 = layer0_m31 + 12;
        let g_raw_m31 = 4 * (layer0_m31 + 3);
        let h_raw_qm31 = layer0_m31 + 3;
        let p0_view_m31 = 4 * (h_raw_qm31 + P0_QM31);
        let sc_m31 = 4 * STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS;
        let aux_m31 = sc_m31 + p0_view_m31;
        let h_generator_index =
            STATE_ONLY_HIDING_C1_COLUMNS + STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS;
        let g_generator_index = h_generator_index + 1;
        let powers = (0..=g_generator_index)
            .map(|column| gamma_power(schedule.prefix.gamma, column))
            .collect::<Vec<_>>();

        let cells = atomic_state_only_relation_free_mask_cells_v3()
            .map_err(|_| StateOnlyHidingRankGateError::Layout)?;
        let mut cells_by_column = vec![Vec::new(); STATE_ONLY_HIDING_C1_COLUMNS];
        for cell in cells {
            let logical = usize::from(cell.row);
            cells_by_column[usize::from(cell.column)]
                .push(permutation.logical_row_to_physical(logical));
        }

        let mut sumcheck_kernel_images = Vec::new();
        let mut semantic_raw_echelons = Vec::with_capacity(STATE_ONLY_HIDING_C1_COLUMNS);
        let mut raw_c1_rank_m31 = 0usize;
        for (column, cells) in cells_by_column.iter().enumerate() {
            let dependent = cells
                .iter()
                .copied()
                .filter(|row| !active[*row])
                .last()
                .ok_or(StateOnlyHidingRankGateError::Layout)?;
            let observations = &self.semantic_observations[column];
            let mut raw = CarryEchelon::new(c1_raw_m31);
            for &row in cells {
                if row == dependent {
                    continue;
                }
                let subtract = (!active[row]).then_some(dependent);
                let raw_image = c1_raw_difference(&rows, row, subtract);
                let aux = scaled_aux_difference(
                    &rows,
                    row,
                    subtract,
                    observations,
                    QM31::ONE,
                    powers[column],
                    4 * h_raw_qm31,
                    p0_view_m31,
                );
                if let Some(kernel) = raw.reduce(raw_image, aux) {
                    sumcheck_kernel_images.push(kernel);
                }
            }
            if raw.rank != c1_raw_m31 {
                return Err(StateOnlyHidingRankGateError::RawC1Rank {
                    column,
                    got: raw.rank,
                    want: c1_raw_m31,
                });
            }
            raw_c1_rank_m31 += raw.rank;
            semantic_raw_echelons.push(raw);
        }

        for mask_column in 0..STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS {
            let observations = &self.mask_only_observations[mask_column];
            let generator = STATE_ONLY_HIDING_C1_COLUMNS + mask_column;
            let mut raw = CarryEchelon::new(c1_raw_m31);
            for row in 0..TRACE_ROWS {
                if row == global_dependent {
                    continue;
                }
                let subtract = (!active[row]).then_some(global_dependent);
                let raw_image = c1_raw_difference(&rows, row, subtract);
                let aux = scaled_aux_difference(
                    &rows,
                    row,
                    subtract,
                    observations,
                    QM31::ONE,
                    powers[generator],
                    4 * h_raw_qm31,
                    p0_view_m31,
                );
                if let Some(kernel) = raw.reduce(raw_image, aux) {
                    sumcheck_kernel_images.push(kernel);
                }
            }
            if raw.rank != c1_raw_m31 {
                return Err(StateOnlyHidingRankGateError::RawC1Rank {
                    column: generator,
                    got: raw.rank,
                    want: c1_raw_m31,
                });
            }
            raw_c1_rank_m31 += raw.rank;
        }

        let mut g_raw = CarryEchelon::new(g_raw_m31);
        for coordinate in 0..4 {
            let basis = state_only_mask_tower_basis(coordinate);
            for row in 0..TRACE_ROWS {
                if row == global_dependent {
                    continue;
                }
                let subtract = (!active[row]).then_some(global_dependent);
                let raw_image = qm31_raw_difference(&rows, row, subtract, basis);
                let aux = scaled_aux_difference(
                    &rows,
                    row,
                    subtract,
                    &self.g_observations,
                    basis,
                    basis.mul(powers[g_generator_index]),
                    4 * h_raw_qm31,
                    p0_view_m31,
                );
                if let Some(kernel) = g_raw.reduce(raw_image, aux) {
                    sumcheck_kernel_images.push(kernel);
                }
            }
        }
        if g_raw.rank != g_raw_m31 {
            return Err(StateOnlyHidingRankGateError::RawGRank {
                got: g_raw.rank,
                want: g_raw_m31,
            });
        }

        let mut sumcheck = CarryEchelon::new(sc_m31);
        let mut p0_kernel_images = Vec::new();
        for image in sumcheck_kernel_images {
            let (sc, p0) = image.split_at(sc_m31);
            if let Some(kernel) = sumcheck.reduce(sc.to_vec(), p0.to_vec()) {
                p0_kernel_images.push(kernel);
            }
        }
        if sumcheck.rank != MASK_SUMCHECK_QUOTIENT_M31 {
            return Err(StateOnlyHidingRankGateError::MaskedSumcheckRank {
                got: sumcheck.rank,
                want: MASK_SUMCHECK_QUOTIENT_M31,
            });
        }

        let mut p0_rank = ColumnEchelon::new(p0_view_m31);
        for image in p0_kernel_images {
            p0_rank.insert(image);
        }
        let h_scale = powers[h_generator_index];
        for coordinate in 0..4 {
            let basis = state_only_mask_tower_basis(coordinate);
            for &row in &inactive {
                if row != global_dependent {
                    p0_rank.insert(h_pcs_image(
                        &rows,
                        row,
                        global_dependent,
                        basis,
                        h_scale,
                        h_raw_qm31,
                        P0_QM31,
                    ));
                }
            }
        }
        let p0_mask_rank_m31 = p0_rank.rank;

        let mut semantic_augmented = p0_rank.clone();
        let mut compatibility = CarryEchelon::new(sc_m31);
        let mut p0_semantic_new_pivots_m31 = Vec::new();
        for column in 0..STATE_ONLY_HIDING_C1_COLUMNS {
            for logical_row in 1..TRACE_ROWS {
                let row = permutation.logical_row_to_physical(logical_row);
                let raw = c1_raw_difference(&rows, row, None);
                let mut carry = vec![M31::ZERO; aux_m31];
                let pcs = scaled_qm31_difference(&rows[row].pcs_tail, None, powers[column]);
                let pcs_start = sc_m31 + 4 * h_raw_qm31;
                carry[pcs_start..pcs_start + pcs.len()].copy_from_slice(&pcs);
                let post_raw = semantic_raw_echelons[column]
                    .quotient_existing(raw, carry)
                    .ok_or(StateOnlyHidingRankGateError::WitnessRawQuotient {
                        source: column * TRACE_ROWS + logical_row,
                    })?;
                let (sc, p0) = post_raw.split_at(sc_m31);
                let (sc_remainder, mut p0_remainder) =
                    sumcheck.remainder_existing(sc.to_vec(), p0.to_vec());
                let next_pivot = compatibility.rank;
                p0_remainder.extend((0..4).map(|index| {
                    if next_pivot < 4 && index == next_pivot {
                        M31::ONE
                    } else {
                        M31::ZERO
                    }
                }));
                if let CarryReduction::Kernel(mut post_sumcheck) =
                    compatibility.reduce_with_pivot(sc_remainder, p0_remainder)
                {
                    post_sumcheck.truncate(p0_view_m31);
                    if let Some(pivot) = semantic_augmented.insert_with_pivot(post_sumcheck) {
                        p0_semantic_new_pivots_m31.push(pivot);
                    }
                }
            }
        }
        let p0_semantic_augmented_rank_m31 = semantic_augmented.rank;

        let mut legal_augmented = semantic_augmented;
        let mut p0_legal_sumcheck_new_pivots_m31 = Vec::new();
        for sc_row in 4..sc_m31 {
            let mut sc = vec![M31::ZERO; sc_m31];
            sc[sc_row] = M31::ONE;
            let p0 = vec![M31::ZERO; p0_view_m31];
            let (sc_remainder, mut p0_remainder) = sumcheck.remainder_existing(sc, p0);
            p0_remainder.extend([M31::ZERO; 4]);
            if let CarryReduction::Kernel(mut post_sumcheck) =
                compatibility.reduce_with_pivot(sc_remainder, p0_remainder)
            {
                post_sumcheck.truncate(p0_view_m31);
                if let Some(pivot) = legal_augmented.insert_with_pivot(post_sumcheck) {
                    p0_legal_sumcheck_new_pivots_m31.push(pivot);
                }
            }
        }
        let p0_legal_sumcheck_augmented_rank_m31 = legal_augmented.rank;
        Ok(AtomicProfile21VariablePermutationP0RankReport {
            first_logical_variable,
            physical_to_logical_coordinates: permutation.physical_to_logical,
            conjugation_guard_run,
            conjugation_guard_passed,
            inactive_low_mask_groups,
            baseline_inactive_low_mask_groups: self.baseline_inactive_low_mask_groups,
            preserves_grouped_inactive_shape: inactive_low_mask_groups
                == self.baseline_inactive_low_mask_groups,
            raw_c1_rank_m31,
            raw_g_rank_m31: g_raw.rank,
            masked_sumcheck_rank_m31: sumcheck.rank,
            p0_view_m31,
            p0_mask_rank_m31,
            p0_semantic_augmented_rank_m31,
            p0_legal_sumcheck_augmented_rank_m31,
            p0_semantic_new_pivots_m31,
            p0_legal_sumcheck_new_pivots_m31,
            p0_contains_conservative_semantic_and_legal_sumcheck: p0_mask_rank_m31
                == p0_legal_sumcheck_augmented_rank_m31,
            elapsed_millis: started.elapsed().as_millis(),
        })
    }
}
