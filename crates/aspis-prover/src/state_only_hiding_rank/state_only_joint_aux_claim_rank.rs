//! Exact, production-neutral log10/q16 rank gate for a joint auxiliary-tail
//! claim.  Semantic C1 columns and H keep their full three-point openings.
//! The ten mask-only M31 columns and G keep their layer-zero openings plus
//! their individual value at `z`, while their successor/xor values are
//! replaced by one gamma-weighted `A_tail` claim.

use super::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AtomicJointAuxClaimRankReport {
    pub query_count: usize,
    pub tau_coordinates_m31: [u32; 4],
    pub kappa_coordinates_m31: [u32; 4],
    pub delta_group_scale_coordinates_m31: [u32; 4],
    pub c1_raw_m31: usize,
    pub joint_aux_raw_m31: usize,
    pub joint_aux_raw_rank_m31: usize,
    pub masked_sumcheck_rank_m31: usize,
    pub residual_pcs_m31: usize,
    pub pre_helper_pcs_rank_m31: usize,
    pub baseline_pcs_rank_m31: usize,
    pub helper_augmented_rank_m31: usize,
    pub baseline_valid_helper_containment: bool,
    pub semantic_augmented_rank_m31: usize,
    pub semantic_new_pivots_m31: Vec<usize>,
    pub legal_sumcheck_augmented_rank_m31: usize,
    pub legal_sumcheck_new_pivots_m31: Vec<usize>,
    pub contains_conservative_semantic_and_legal_sumcheck: bool,
    pub joint_aux_minor: RankMinorProvenance,
    pub semantic_minor: RankMinorProvenance,
    pub legal_sumcheck_minor: RankMinorProvenance,
    pub elapsed_millis: u128,
}

fn row_pcs_tail_sparse_with_tau(
    encoder: &CircleEncoder,
    domain_log: u32,
    row: usize,
    active: &[bool; TRACE_ROWS],
    inactive_dependent: usize,
    schedule: &StateOnlyTranscriptScheduleResult,
    later_indices: &[Vec<u32>; CANDIDATE_ROUND_COUNT - 1],
    tau: QM31,
) -> Result<Vec<QM31>, StateOnlyHidingRankGateError> {
    if row == inactive_dependent {
        let later = later_indices
            .iter()
            .map(|queries| queries.len() * FIBER_SLOTS)
            .sum::<usize>();
        return Ok(vec![
            QM31::ZERO;
            later
                + CANDIDATE_ROUND_COUNT * CANDIDATE_OOD_SAMPLES
                + CANDIDATE_ROUND_COUNT * 7
                + 4
        ]);
    }
    let dependent = (!active[row]).then_some(inactive_dependent);
    let mut message = vec![QM31::ZERO; TRACE_ROWS];
    message[row] = QM31::ONE;
    if let Some(dependent) = dependent {
        message[dependent] = QM31::ZERO.sub(QM31::ONE);
    }
    let points = [
        schedule.prefix.z,
        binary_successor_point(&schedule.prefix.z),
        xor12_point(&schedule.prefix.z),
    ];
    let kappa = schedule.prefix.point_scale;
    let mut relation = StateOnlyIncrementalRelation::new_with_inactive_masks(
        message,
        &points,
        [tau, kappa, kappa.square()],
        rank_inactive_masks(RankLayout::AtomicV3),
    )?;
    let mut later = Vec::new();
    let mut polynomials = Vec::with_capacity(CANDIDATE_ROUND_COUNT);
    let mut memo = BTreeMap::new();
    for round in 0..CANDIDATE_ROUND_COUNT {
        for sample in 0..CANDIDATE_OOD_SAMPLES {
            if round == 0 {
                let point = schedule.circle_ood_points[sample];
                let value = relation.evaluate_circle_ood(point)?;
                relation.add_circle_ood(point, value, schedule.mu[round][sample])?;
            } else {
                let point = schedule.line_ood_points[round - 1][sample];
                let value = relation.evaluate_line_ood(point)?;
                relation.add_line_ood(point, value, schedule.mu[round][sample])?;
            }
        }
        polynomials.push(relation.polynomial()?);
        relation.fold(schedule.alpha[round])?;
        if round + 1 < CANDIDATE_ROUND_COUNT {
            for &leaf in &later_indices[round] {
                for slot in 0..FIBER_SLOTS {
                    later.push(sparse_folded_row_value(
                        encoder,
                        domain_log,
                        row,
                        dependent,
                        schedule,
                        round + 1,
                        FIBER_SLOTS * leaf as usize + slot,
                        &mut memo,
                    )?);
                }
            }
        }
    }
    let relation = relation.finish()?;
    let mut tail = later;
    for values in relation.ood_values {
        tail.extend_from_slice(&values);
    }
    for polynomial in polynomials {
        tail.extend_from_slice(&polynomial);
    }
    tail.extend_from_slice(&relation.final_coefficients);
    Ok(tail)
}

fn row_public_maps_with_tau(
    encoder: &CircleEncoder,
    domain_log: u32,
    schedule: &StateOnlyTranscriptScheduleResult,
    tau: QM31,
) -> Result<Vec<RowPublicMaps>, StateOnlyHidingRankGateError> {
    if schedule.query_count != 16 || domain_log != STATE_ONLY_LOG_ROWS + 9 {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let indices = derive_circle_line_query_indices_for_count(
        &schedule.queries[..schedule.query_count],
        encoder.codeword_len() / FIBER_SLOTS,
    )
    .map_err(|_| StateOnlyHidingRankGateError::Shape)?;
    let terminal_points = [
        schedule.prefix.z,
        binary_successor_point(&schedule.prefix.z),
        xor12_point(&schedule.prefix.z),
    ];
    let mut active = [false; TRACE_ROWS];
    for row in rank_active_rows(RankLayout::AtomicV3) {
        active[usize::from(row)] = true;
    }
    let inactive_dependent = (0..TRACE_ROWS)
        .find(|row| !active[*row])
        .ok_or(StateOnlyHidingRankGateError::Layout)?;
    let mut rows = Vec::with_capacity(TRACE_ROWS);
    for row in 0..TRACE_ROWS {
        let mut layer0_m31 = Vec::with_capacity(indices.layer0.len() * FIBER_SLOTS);
        for &query in &indices.layer0 {
            for slot in 0..FIBER_SLOTS {
                layer0_m31
                    .push(encoder.encode_c1_basis_value(row, FIBER_SLOTS * query as usize + slot)?);
            }
        }
        rows.push(RowPublicMaps {
            layer0_m31,
            terminal: core::array::from_fn(|point| eq_weight(&terminal_points[point], row)),
            pcs_tail: row_pcs_tail_sparse_with_tau(
                encoder,
                domain_log,
                row,
                &active,
                inactive_dependent,
                schedule,
                &indices.later,
                tau,
            )?,
        });
    }
    Ok(rows)
}

fn terminal_difference(
    rows: &[RowPublicMaps],
    row: usize,
    dependent: Option<usize>,
    point: usize,
) -> QM31 {
    dependent.map_or(rows[row].terminal[point], |dependent| {
        rows[row].terminal[point].sub(rows[dependent].terminal[point])
    })
}

#[allow(clippy::too_many_arguments)]
fn mask_only_joint_raw_image(
    rows: &[RowPublicMaps],
    row: usize,
    dependent: Option<usize>,
    mask_column: usize,
    generator_scale: QM31,
    kappa: QM31,
    mask_block_m31: usize,
    aggregate_offset_m31: usize,
    joint_raw_m31: usize,
) -> Vec<M31> {
    let mut raw = vec![M31::ZERO; joint_raw_m31];
    let start = mask_column * mask_block_m31;
    for (index, value) in rows[row].layer0_m31.iter().copied().enumerate() {
        raw[start + index] = dependent.map_or(value, |dependent| {
            value.sub(rows[dependent].layer0_m31[index])
        });
    }
    let z = terminal_difference(rows, row, dependent, 0);
    raw[start + rows[row].layer0_m31.len()..start + mask_block_m31]
        .copy_from_slice(&qm31_coordinates(z));
    let tail = kappa.mul(terminal_difference(rows, row, dependent, 1)).add(
        kappa
            .square()
            .mul(terminal_difference(rows, row, dependent, 2)),
    );
    raw[aggregate_offset_m31..aggregate_offset_m31 + 4]
        .copy_from_slice(&qm31_coordinates(generator_scale.mul(tail)));
    raw
}

#[allow(clippy::too_many_arguments)]
fn g_joint_raw_image(
    rows: &[RowPublicMaps],
    row: usize,
    dependent: Option<usize>,
    basis: QM31,
    generator_scale: QM31,
    kappa: QM31,
    g_offset_m31: usize,
    aggregate_offset_m31: usize,
    joint_raw_m31: usize,
) -> Vec<M31> {
    let mut raw = vec![M31::ZERO; joint_raw_m31];
    for (index, value) in rows[row].layer0_m31.iter().copied().enumerate() {
        let difference = dependent.map_or(value, |dependent| {
            value.sub(rows[dependent].layer0_m31[index])
        });
        let coordinates = qm31_coordinates(basis.mul_m31(difference));
        let start = g_offset_m31 + 4 * index;
        raw[start..start + 4].copy_from_slice(&coordinates);
    }
    let z = basis.mul(terminal_difference(rows, row, dependent, 0));
    let z_start = g_offset_m31 + 4 * rows[row].layer0_m31.len();
    raw[z_start..z_start + 4].copy_from_slice(&qm31_coordinates(z));
    let tail = kappa.mul(terminal_difference(rows, row, dependent, 1)).add(
        kappa
            .square()
            .mul(terminal_difference(rows, row, dependent, 2)),
    );
    raw[aggregate_offset_m31..aggregate_offset_m31 + 4]
        .copy_from_slice(&qm31_coordinates(generator_scale.mul(basis).mul(tail)));
    raw
}

fn run_joint_aux_claim_rank(
    schedule: &StateOnlyTranscriptScheduleResult,
    tau: QM31,
    delta: QM31,
) -> Result<AtomicJointAuxClaimRankReport, StateOnlyHidingRankGateError> {
    let started = Instant::now();
    if schedule.query_count != 16 || tau == QM31::ZERO || delta == QM31::ZERO {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let domain_log = STATE_ONLY_LOG_ROWS + 9;
    let encoder = CircleEncoder::new_for_domain_log(domain_log);
    let rows = row_public_maps_with_tau(&encoder, domain_log, schedule, tau)?;
    let layer0_m31 = rows[0].layer0_m31.len();
    let pcs_tail_qm31 = rows[0].pcs_tail.len();
    if rows
        .iter()
        .any(|row| row.layer0_m31.len() != layer0_m31 || row.pcs_tail.len() != pcs_tail_qm31)
    {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let c1_raw_m31 = layer0_m31 + 12;
    let h_raw_qm31 = layer0_m31 + 3;
    let residual_pcs_m31 = 4 * (h_raw_qm31 + pcs_tail_qm31);
    let sc_m31 = 4 * STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS;
    let aux_m31 = sc_m31 + residual_pcs_m31;
    let mask_block_m31 = layer0_m31 + 4;
    let mask_blocks_m31 = STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS * mask_block_m31;
    let g_offset_m31 = mask_blocks_m31;
    let g_block_m31 = 4 * (layer0_m31 + 1);
    let aggregate_offset_m31 = g_offset_m31 + g_block_m31;
    let joint_aux_raw_m31 = aggregate_offset_m31 + 4;
    let kappa = schedule.prefix.point_scale;
    let group_scale = delta;
    let lagrange = lagrange_basis();
    let active_rows = rank_active_rows(RankLayout::AtomicV3);
    let mut active = [false; TRACE_ROWS];
    for &row in &active_rows {
        active[usize::from(row)] = true;
    }
    let inactive = (0..TRACE_ROWS)
        .filter(|row| !active[*row])
        .collect::<Vec<_>>();
    let global_dependent = inactive[0];
    let h_generator_index = STATE_ONLY_HIDING_C1_COLUMNS + STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS;
    let g_generator_index = h_generator_index + 1;
    let powers = (0..=g_generator_index)
        .map(|column| gamma_power(schedule.prefix.gamma, column))
        .collect::<Vec<_>>();

    let mut raw_kernel_images = Vec::new();
    let mut semantic_raw_echelons = Vec::with_capacity(STATE_ONLY_HIDING_C1_COLUMNS);
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
        let observations = (0..TRACE_ROWS)
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
            .collect::<Vec<_>>();
        let mut raw = CarryEchelon::new(c1_raw_m31);
        for &row in cells {
            if row == dependent {
                continue;
            }
            let subtract = (!active[row]).then_some(dependent);
            let aux = scaled_aux_difference(
                &rows,
                row,
                subtract,
                &observations,
                QM31::ONE,
                group_scale.mul(powers[column]),
                4 * h_raw_qm31,
                residual_pcs_m31,
            );
            if let Some(kernel) = raw.reduce(c1_raw_difference(&rows, row, subtract), aux) {
                raw_kernel_images.push(kernel);
            }
        }
        if raw.rank != c1_raw_m31 {
            return Err(StateOnlyHidingRankGateError::RawC1Rank {
                column,
                got: raw.rank,
                want: c1_raw_m31,
            });
        }
        semantic_raw_echelons.push(raw);
    }

    let mut joint_raw = CarryEchelon::new(joint_aux_raw_m31);
    let mut joint_sources = Vec::new();
    let mut joint_rows = Vec::new();
    let mut joint_values = Vec::new();
    let mut source_id = 0usize;
    for mask_column in 0..STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS {
        let observations = (0..TRACE_ROWS)
            .map(|row| {
                mask_sumcheck_observations(
                    row,
                    &schedule.prefix.z,
                    &lagrange,
                    MaskFactor::MaskOnly(mask_column),
                    FactorSchedule::FullSharedLinear,
                    None,
                )
            })
            .collect::<Vec<_>>();
        let generator = STATE_ONLY_HIDING_C1_COLUMNS + mask_column;
        for row in 0..TRACE_ROWS {
            if row == global_dependent {
                continue;
            }
            let subtract = (!active[row]).then_some(global_dependent);
            let raw = mask_only_joint_raw_image(
                &rows,
                row,
                subtract,
                mask_column,
                powers[generator],
                kappa,
                mask_block_m31,
                aggregate_offset_m31,
                joint_aux_raw_m31,
            );
            let aux = scaled_aux_difference(
                &rows,
                row,
                subtract,
                &observations,
                QM31::ONE,
                powers[generator],
                4 * h_raw_qm31,
                residual_pcs_m31,
            );
            match joint_raw.reduce_with_pivot(raw, aux) {
                CarryReduction::Pivot { row, value } => {
                    joint_sources.push(source_id);
                    joint_rows.push(row);
                    joint_values.push(value);
                }
                CarryReduction::Kernel(kernel) => raw_kernel_images.push(kernel),
            }
            source_id += 1;
        }
    }
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
    for coordinate in 0..4 {
        let basis = state_only_mask_tower_basis(coordinate);
        for row in 0..TRACE_ROWS {
            if row == global_dependent {
                continue;
            }
            let subtract = (!active[row]).then_some(global_dependent);
            let raw = g_joint_raw_image(
                &rows,
                row,
                subtract,
                basis,
                powers[g_generator_index],
                kappa,
                g_offset_m31,
                aggregate_offset_m31,
                joint_aux_raw_m31,
            );
            let aux = scaled_aux_difference(
                &rows,
                row,
                subtract,
                &g_observations,
                basis,
                basis.mul(powers[g_generator_index]),
                4 * h_raw_qm31,
                residual_pcs_m31,
            );
            match joint_raw.reduce_with_pivot(raw, aux) {
                CarryReduction::Pivot { row, value } => {
                    joint_sources.push(source_id);
                    joint_rows.push(row);
                    joint_values.push(value);
                }
                CarryReduction::Kernel(kernel) => raw_kernel_images.push(kernel),
            }
            source_id += 1;
        }
    }
    let joint_aux_minor = RankMinorProvenance::from_parts(
        "atomic_log10_joint_aux_raw",
        joint_sources,
        joint_rows,
        joint_values,
    );
    if joint_raw.rank != joint_aux_raw_m31 {
        return Err(StateOnlyHidingRankGateError::RawGRank {
            got: joint_raw.rank,
            want: joint_aux_raw_m31,
        });
    }

    let mut sumcheck = CarryEchelon::new(sc_m31);
    let mut pcs_images = Vec::new();
    for image in raw_kernel_images {
        let (sc, pcs) = image.split_at(sc_m31);
        if let Some(kernel) = sumcheck.reduce(sc.to_vec(), pcs.to_vec()) {
            pcs_images.push(kernel);
        }
    }
    if sumcheck.rank != MASK_SUMCHECK_QUOTIENT_M31 {
        return Err(StateOnlyHidingRankGateError::MaskedSumcheckRank {
            got: sumcheck.rank,
            want: MASK_SUMCHECK_QUOTIENT_M31,
        });
    }
    let mut baseline = ColumnEchelon::new(residual_pcs_m31);
    for image in pcs_images {
        baseline.insert(image);
    }
    let pre_helper_pcs_rank_m31 = baseline.rank;
    let h_scale = group_scale.mul(powers[h_generator_index]);
    for coordinate in 0..4 {
        let basis = state_only_mask_tower_basis(coordinate);
        for &row in &inactive {
            if row != global_dependent {
                baseline.insert(h_pcs_image(
                    &rows,
                    row,
                    global_dependent,
                    basis,
                    h_scale,
                    h_raw_qm31,
                    pcs_tail_qm31,
                ));
            }
        }
    }
    let baseline_pcs_rank_m31 = baseline.rank;
    let active_rows = (0..TRACE_ROWS)
        .filter(|row| active[*row])
        .collect::<Vec<_>>();
    let active_dependent = *active_rows
        .last()
        .ok_or(StateOnlyHidingRankGateError::Layout)?;
    let mut helper_augmented = baseline.clone();
    for coordinate in 0..4 {
        let basis = state_only_mask_tower_basis(coordinate);
        for &row in &active_rows[..active_rows.len() - 1] {
            helper_augmented.insert(h_pcs_image(
                &rows,
                row,
                active_dependent,
                basis,
                h_scale,
                h_raw_qm31,
                pcs_tail_qm31,
            ));
        }
    }
    let helper_augmented_rank_m31 = helper_augmented.rank;
    let baseline_valid_helper_containment = helper_augmented_rank_m31 == baseline_pcs_rank_m31;

    let pcs_start = sc_m31 + 4 * h_raw_qm31;
    let mut compatibility = CarryEchelon::new(sc_m31);
    let mut semantic_reference = baseline.clone();
    let mut semantic_images = Vec::new();
    let mut semantic_sources = Vec::new();
    let mut semantic_rows = Vec::new();
    let mut semantic_values = Vec::new();
    for column in 0..STATE_ONLY_HIDING_C1_COLUMNS {
        for row in 1..TRACE_ROWS {
            let source = column * TRACE_ROWS + row;
            let raw = c1_raw_difference(&rows, row, None);
            let mut carry = vec![M31::ZERO; aux_m31];
            let pcs =
                scaled_qm31_difference(&rows[row].pcs_tail, None, group_scale.mul(powers[column]));
            carry[pcs_start..pcs_start + pcs.len()].copy_from_slice(&pcs);
            let post_raw = semantic_raw_echelons[column]
                .quotient_existing(raw, carry)
                .ok_or(StateOnlyHidingRankGateError::WitnessRawQuotient { source })?;
            let (sc, pcs) = post_raw.split_at(sc_m31);
            let (sc_remainder, mut pcs_remainder) =
                sumcheck.remainder_existing(sc.to_vec(), pcs.to_vec());
            let next_pivot = compatibility.rank;
            pcs_remainder.extend((0..4).map(|index| {
                if next_pivot < 4 && index == next_pivot {
                    M31::ONE
                } else {
                    M31::ZERO
                }
            }));
            if let CarryReduction::Kernel(mut post_sumcheck) =
                compatibility.reduce_with_pivot(sc_remainder, pcs_remainder)
            {
                post_sumcheck.truncate(residual_pcs_m31);
                if let Some((pivot, value)) =
                    semantic_reference.insert_with_pivot_value(post_sumcheck.clone())
                {
                    semantic_images.push(post_sumcheck);
                    semantic_sources.push(source);
                    semantic_rows.push(pivot);
                    semantic_values.push(value);
                }
            }
        }
    }
    if compatibility.rank != 4 {
        return Err(StateOnlyHidingRankGateError::Layout);
    }
    let semantic_augmented_rank_m31 = semantic_reference.rank;
    let semantic_minor = RankMinorProvenance::from_parts(
        "atomic_log10_joint_aux_semantic",
        semantic_sources,
        semantic_rows.clone(),
        semantic_values,
    );
    let mut legal_sources = Vec::new();
    let mut legal_rows = Vec::new();
    let mut legal_values = Vec::new();
    for sc_row in 4..sc_m31 {
        let mut sc = vec![M31::ZERO; sc_m31];
        sc[sc_row] = M31::ONE;
        let pcs = vec![M31::ZERO; residual_pcs_m31];
        let (sc_remainder, mut pcs_remainder) = sumcheck.remainder_existing(sc, pcs);
        pcs_remainder.extend([M31::ZERO; 4]);
        if let CarryReduction::Kernel(mut post_sumcheck) =
            compatibility.reduce_with_pivot(sc_remainder, pcs_remainder)
        {
            post_sumcheck.truncate(residual_pcs_m31);
            if let Some((pivot, value)) = semantic_reference.insert_with_pivot_value(post_sumcheck)
            {
                legal_sources.push(sc_row - 4);
                legal_rows.push(pivot);
                legal_values.push(value);
            }
        }
    }
    let legal_sumcheck_augmented_rank_m31 = semantic_reference.rank;
    let legal_sumcheck_minor = RankMinorProvenance::from_parts(
        "atomic_log10_joint_aux_legal_sumcheck",
        legal_sources,
        legal_rows.clone(),
        legal_values,
    );

    Ok(AtomicJointAuxClaimRankReport {
        query_count: schedule.query_count,
        tau_coordinates_m31: qm31_coordinates(tau).map(|coordinate| coordinate.0),
        kappa_coordinates_m31: qm31_coordinates(kappa).map(|coordinate| coordinate.0),
        delta_group_scale_coordinates_m31: qm31_coordinates(group_scale)
            .map(|coordinate| coordinate.0),
        c1_raw_m31,
        joint_aux_raw_m31,
        joint_aux_raw_rank_m31: joint_raw.rank,
        masked_sumcheck_rank_m31: sumcheck.rank,
        residual_pcs_m31,
        pre_helper_pcs_rank_m31,
        baseline_pcs_rank_m31,
        helper_augmented_rank_m31,
        baseline_valid_helper_containment,
        semantic_augmented_rank_m31,
        semantic_new_pivots_m31: semantic_rows,
        legal_sumcheck_augmented_rank_m31,
        legal_sumcheck_new_pivots_m31: legal_rows,
        contains_conservative_semantic_and_legal_sumcheck: baseline_pcs_rank_m31
            == legal_sumcheck_augmented_rank_m31,
        joint_aux_minor,
        semantic_minor,
        legal_sumcheck_minor,
        elapsed_millis: started.elapsed().as_millis(),
    })
}

/// Run the exact q16/log10 no-switch joint-auxiliary claim rank gate. `tau`
/// is supplied explicitly because this diagnostic does not define or promote
/// a new Fiat--Shamir transcript; production must sample it after `A_tail`.
pub fn probe_atomic_state_only_joint_aux_claim_rank(
    schedule: &StateOnlyTranscriptScheduleResult,
    tau: QM31,
    delta: QM31,
) -> Result<AtomicJointAuxClaimRankReport, StateOnlyHidingRankGateError> {
    run_joint_aux_claim_rank(schedule, tau, delta)
}
