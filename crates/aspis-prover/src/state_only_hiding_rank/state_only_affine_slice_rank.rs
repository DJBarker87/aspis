//! Exact, production-neutral affine-slice hiding probe for atomic profile 21.
//!
//! The ten-variable committed words are lifted to eleven variables by
//! duplicating each logical coefficient across an inserted Boolean bit `s`.
//! The existing main `G` lane additionally receives `(s-c) R`, represented by
//! the physical coefficient pair `(-c R, (1-c) R)`.  Every public evaluation
//! and the initial PCS relation uses the affine slice `s=c`; consequently the
//! fresh direction is zero there without a selective or unauthenticated
//! coefficient splice.

use super::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AtomicProfile21AffineSliceVariantReport {
    pub insertion_coordinate: usize,
    /// Tower-basis coordinates `[1, i, u, iu]` of the fixed affine slice.
    pub slice_value_coordinates_m31: [u32; 4],
    /// Compatibility field for the original base-field-only scanner.
    pub slice_value_m31: u32,
    /// Bit `p` is one exactly when the dedicated G terminal opening at
    /// `p = 0:z, 1:successor(z), 2:xor12(z)` is retained in the raw
    /// conditioning block.  C1 and H always retain all three terminals, and
    /// the PCS relation tail is unchanged.
    pub g_retained_terminal_mask: u8,
    /// True for the physically claim-carrying two-row G map
    /// `[G(z), kappa G(successor(z)) + kappa^2 G(xor12(z))]`.
    pub g_uses_z_and_weighted_aggregate: bool,
    pub z_relation_weight_coordinates_m31: [u32; 4],
    /// A single omitted terminal is recoverable from the weighted initial
    /// relation claim exactly when its coefficient is nonzero.  These are
    /// `[1, kappa, kappa^2]` for `[z, successor, xor12]`.
    pub g_single_terminal_reconstructible: [bool; 3],
    pub masked_sumcheck_rank_m31: usize,
    pub g_raw_rank_m31: usize,
    pub affine_g_raw_kernel_m31: usize,
    pub baseline_pcs_rank_m31: usize,
    pub baseline_semantic_augmented_rank_m31: usize,
    pub baseline_semantic_new_pivots_m31: Vec<usize>,
    pub baseline_legal_sumcheck_augmented_rank_m31: usize,
    pub baseline_legal_sumcheck_new_pivots_m31: Vec<usize>,
    pub baseline_contains_conservative_semantic_and_legal_sumcheck: bool,
    pub affine_g_pcs_rank_m31: usize,
    pub affine_g_new_pivots_m31: Vec<usize>,
    pub affine_g_minor: RankMinorProvenance,
    pub semantic_augmented_rank_m31: usize,
    pub semantic_new_pivots_m31: Vec<usize>,
    pub legal_sumcheck_augmented_rank_m31: usize,
    pub legal_sumcheck_new_pivots_m31: Vec<usize>,
    pub contains_conservative_semantic_and_legal_sumcheck: bool,
    pub affine_g_and_h_pcs_rank_m31: usize,
    pub affine_g_and_h_new_pivots_m31: Vec<usize>,
    pub affine_g_and_h_semantic_augmented_rank_m31: usize,
    pub affine_g_and_h_semantic_new_pivots_m31: Vec<usize>,
    pub affine_g_and_h_legal_sumcheck_augmented_rank_m31: usize,
    pub affine_g_and_h_legal_sumcheck_new_pivots_m31: Vec<usize>,
    pub affine_g_and_h_contains_conservative_semantic_and_legal_sumcheck: bool,
    pub affine_h_minor: RankMinorProvenance,
    pub semantic_minor: RankMinorProvenance,
    pub legal_sumcheck_minor: RankMinorProvenance,
    pub elapsed_millis: u128,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AtomicProfile21AffineSliceLiftRankReport {
    pub query_count: usize,
    pub message_log: u32,
    pub codeword_domain_log: u32,
    pub codeword_len: usize,
    pub rate_denominator: usize,
    pub tested: Vec<AtomicProfile21AffineSliceVariantReport>,
    pub first_contained_index: Option<usize>,
    pub elapsed_millis: u128,
}

fn affine_slice_initial_weights(
    schedule: &StateOnlyTranscriptScheduleResult,
    insertion_coordinate: usize,
    c: QM31,
    z_weight: QM31,
) -> Result<WeightAccumulator, StateOnlyHidingRankGateError> {
    let points = [
        extended_point_at(&schedule.prefix.z, insertion_coordinate, c),
        extended_point_at(
            &binary_successor_point(&schedule.prefix.z),
            insertion_coordinate,
            c,
        ),
        extended_point_at(&xor12_point(&schedule.prefix.z), insertion_coordinate, c),
    ];
    let kappa = schedule.prefix.point_scale;
    let mut weights = WeightAccumulator::empty(EXTENDED_LOG_ROWS);
    for (point, scale) in points.into_iter().zip([z_weight, kappa, kappa.square()]) {
        weights
            .add_multilinear(scale, point.to_vec())
            .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
    }

    // The old inactive-row functional is lifted by the evaluation covector
    // of the new bit at c: (1-c,c).  A dense host-only component is exact and
    // avoids pretending this non-Boolean covector is a binary row mask.
    let one_minus_c = QM31::ONE.sub(c);
    let inactive = rank_inactive_masks(RankLayout::AtomicV3);
    let mut dense = vec![QM31::ZERO; EXTENDED_TRACE_ROWS];
    for row in 0..TRACE_ROWS {
        if ((inactive[row >> 4] >> (row & 15)) & 1) == 0 {
            continue;
        }
        let row0 = embed_extended_trace_row(row, insertion_coordinate, 0);
        let row1 = embed_extended_trace_row(row, insertion_coordinate, 1);
        dense[row0] = one_minus_c;
        dense[row1] = c;
    }
    weights
        .add_dense(dense)
        .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
    Ok(weights)
}

fn logical_initial_weights_with_z_weight(
    schedule: &StateOnlyTranscriptScheduleResult,
    z_weight: QM31,
) -> Result<WeightAccumulator, StateOnlyHidingRankGateError> {
    let points = [
        schedule.prefix.z,
        binary_successor_point(&schedule.prefix.z),
        xor12_point(&schedule.prefix.z),
    ];
    let kappa = schedule.prefix.point_scale;
    let mut weights = WeightAccumulator::empty(STATE_ONLY_LOG_ROWS);
    for (point, scale) in points.into_iter().zip([z_weight, kappa, kappa.square()]) {
        weights
            .add_multilinear(scale, point.to_vec())
            .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
    }
    weights
        .add_grouped_64x16_binary_masks(rank_inactive_masks(RankLayout::AtomicV3))
        .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
    Ok(weights)
}

fn affine_slice_row_pcs_tail(
    encoder: &CircleEncoder,
    domain_log: u32,
    row: usize,
    schedule: &StateOnlyTranscriptScheduleResult,
    later_indices: &[Vec<u32>; CANDIDATE_ROUND_COUNT - 1],
    insertion_coordinate: usize,
    c: QM31,
    z_weight: QM31,
) -> Result<Vec<QM31>, StateOnlyHidingRankGateError> {
    let mut coefficients = vec![QM31::ZERO; EXTENDED_TRACE_ROWS];
    coefficients[row] = QM31::ONE;
    let mut weights = affine_slice_initial_weights(schedule, insertion_coordinate, c, z_weight)?;
    let mut running_claim = weights.dot(&coefficients);
    let mut later = Vec::new();
    let mut ood_values = [[QM31::ZERO; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT];
    let mut polynomials = [[QM31::ZERO; 7]; CANDIDATE_ROUND_COUNT];
    let mut memo = BTreeMap::new();

    for round in 0..CANDIDATE_ROUND_COUNT {
        for sample in 0..CANDIDATE_OOD_SAMPLES {
            let mut evaluation = WeightAccumulator::empty(EXTENDED_LOG_ROWS - 2 * round as u32);
            if round == 0 {
                evaluation
                    .add_circle_tensor(QM31::ONE, schedule.circle_ood_points[sample])
                    .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
                weights
                    .add_circle_tensor(
                        schedule.mu[round][sample],
                        schedule.circle_ood_points[sample],
                    )
                    .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
            } else {
                evaluation
                    .add_line_tensor(QM31::ONE, schedule.line_ood_points[round - 1][sample])
                    .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
                weights
                    .add_line_tensor(
                        schedule.mu[round][sample],
                        schedule.line_ood_points[round - 1][sample],
                    )
                    .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
            }
            let value = evaluation.dot(&coefficients);
            ood_values[round][sample] = value;
            running_claim = running_claim.add(schedule.mu[round][sample].mul(value));
        }
        let polynomial = polynomial_for_extension(&coefficients, &weights);
        if boundary_sum(&polynomial) != running_claim {
            return Err(StateOnlyHidingRankGateError::Relation);
        }
        polynomials[round] = polynomial;
        running_claim = evaluate_relation(&polynomial, schedule.alpha[round]);
        weights.fold(schedule.alpha[round]);
        coefficients = fold_adjacent_natural_arity4(&coefficients, schedule.alpha[round]);
        if weights.dot(&coefficients) != running_claim {
            return Err(StateOnlyHidingRankGateError::Relation);
        }
        if round + 1 < CANDIDATE_ROUND_COUNT {
            for &leaf in &later_indices[round] {
                for slot in 0..FIBER_SLOTS {
                    later.push(sparse_extended_folded_row_value(
                        encoder,
                        domain_log,
                        row,
                        schedule,
                        round + 1,
                        FIBER_SLOTS * leaf as usize + slot,
                        &mut memo,
                    )?);
                }
            }
        }
    }

    let mut tail = later;
    for values in ood_values {
        tail.extend_from_slice(&values);
    }
    for polynomial in polynomials {
        tail.extend_from_slice(&polynomial);
    }
    if coefficients.len() != 8 {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    tail.extend_from_slice(&coefficients);
    Ok(tail)
}

fn affine_slice_physical_rows(
    encoder: &CircleEncoder,
    domain_log: u32,
    schedule: &StateOnlyTranscriptScheduleResult,
    insertion_coordinate: usize,
    c: QM31,
    z_weight: QM31,
) -> Result<(Vec<RowPublicMaps>, [Vec<u32>; CANDIDATE_ROUND_COUNT - 1]), StateOnlyHidingRankGateError>
{
    let indices = derive_circle_line_query_indices_for_count(
        &schedule.queries[..schedule.query_count],
        encoder.codeword_len() / FIBER_SLOTS,
    )
    .map_err(|_| StateOnlyHidingRankGateError::Shape)?;
    let terminal_points = [
        extended_point_at(&schedule.prefix.z, insertion_coordinate, c),
        extended_point_at(
            &binary_successor_point(&schedule.prefix.z),
            insertion_coordinate,
            c,
        ),
        extended_point_at(&xor12_point(&schedule.prefix.z), insertion_coordinate, c),
    ];
    let mut rows = Vec::with_capacity(EXTENDED_TRACE_ROWS);
    for row in 0..EXTENDED_TRACE_ROWS {
        let mut layer0_m31 = Vec::with_capacity(indices.layer0.len() * FIBER_SLOTS);
        for &query in &indices.layer0 {
            for slot in 0..FIBER_SLOTS {
                layer0_m31.push(encoder.encode_prefix_basis_value(
                    EXTENDED_LOG_ROWS,
                    row,
                    FIBER_SLOTS * query as usize + slot,
                )?);
            }
        }
        rows.push(RowPublicMaps {
            layer0_m31,
            terminal: core::array::from_fn(|point| eq_weight_slice(&terminal_points[point], row)),
            pcs_tail: affine_slice_row_pcs_tail(
                encoder,
                domain_log,
                row,
                schedule,
                &indices.later,
                insertion_coordinate,
                c,
                z_weight,
            )?,
        });
    }
    Ok((rows, indices.later))
}

fn pair_combination_rows(
    physical: &[RowPublicMaps],
    insertion_coordinate: usize,
    pair: [M31; 2],
) -> Vec<RowPublicMaps> {
    (0..TRACE_ROWS)
        .map(|row| {
            let row0 = embed_extended_trace_row(row, insertion_coordinate, 0);
            let row1 = embed_extended_trace_row(row, insertion_coordinate, 1);
            let mut layer0_m31 = Vec::with_capacity(physical[row0].layer0_m31.len());
            for (&left, &right) in physical[row0]
                .layer0_m31
                .iter()
                .zip(&physical[row1].layer0_m31)
            {
                layer0_m31.push(left.mul(pair[0]).add(right.mul(pair[1])));
            }
            RowPublicMaps {
                layer0_m31,
                terminal: core::array::from_fn(|point| {
                    physical[row0].terminal[point]
                        .mul_m31(pair[0])
                        .add(physical[row1].terminal[point].mul_m31(pair[1]))
                }),
                pcs_tail: physical[row0]
                    .pcs_tail
                    .iter()
                    .zip(&physical[row1].pcs_tail)
                    .map(|(&left, &right)| left.mul_m31(pair[0]).add(right.mul_m31(pair[1])))
                    .collect(),
            }
        })
        .collect()
}

struct Qm31RowPublicMaps {
    layer0: Vec<QM31>,
    terminal: [QM31; 3],
    pcs_tail: Vec<QM31>,
}

#[derive(Clone, Copy)]
enum GRawTerminalConditioning {
    Dedicated(u8),
    ZAndTailAggregate,
}

impl GRawTerminalConditioning {
    fn coordinate_count(self) -> usize {
        match self {
            Self::Dedicated(mask) => (mask & 0b111).count_ones() as usize,
            Self::ZAndTailAggregate => 2,
        }
    }

    fn dedicated_mask(self) -> u8 {
        match self {
            Self::Dedicated(mask) => mask,
            Self::ZAndTailAggregate => 0b001,
        }
    }
}

fn qm31_pair_combination_rows(
    physical: &[RowPublicMaps],
    insertion_coordinate: usize,
    pair: [QM31; 2],
) -> Vec<Qm31RowPublicMaps> {
    (0..TRACE_ROWS)
        .map(|row| {
            let row0 = embed_extended_trace_row(row, insertion_coordinate, 0);
            let row1 = embed_extended_trace_row(row, insertion_coordinate, 1);
            Qm31RowPublicMaps {
                layer0: physical[row0]
                    .layer0_m31
                    .iter()
                    .zip(&physical[row1].layer0_m31)
                    .map(|(&left, &right)| pair[0].mul_m31(left).add(pair[1].mul_m31(right)))
                    .collect(),
                terminal: core::array::from_fn(|point| {
                    pair[0]
                        .mul(physical[row0].terminal[point])
                        .add(pair[1].mul(physical[row1].terminal[point]))
                }),
                pcs_tail: physical[row0]
                    .pcs_tail
                    .iter()
                    .zip(&physical[row1].pcs_tail)
                    .map(|(&left, &right)| pair[0].mul(left).add(pair[1].mul(right)))
                    .collect(),
            }
        })
        .collect()
}

fn qm31_row_raw_image(
    rows: &[Qm31RowPublicMaps],
    row: usize,
    basis: QM31,
    terminal_conditioning: GRawTerminalConditioning,
    kappa: QM31,
) -> Vec<M31> {
    let mut raw =
        Vec::with_capacity(4 * (rows[row].layer0.len() + terminal_conditioning.coordinate_count()));
    for value in &rows[row].layer0 {
        raw.extend_from_slice(&qm31_coordinates(basis.mul(*value)));
    }
    match terminal_conditioning {
        GRawTerminalConditioning::Dedicated(retained_terminal_mask) => {
            for (point, value) in rows[row].terminal.into_iter().enumerate() {
                if (retained_terminal_mask & (1 << point)) != 0 {
                    raw.extend_from_slice(&qm31_coordinates(basis.mul(value)));
                }
            }
        }
        GRawTerminalConditioning::ZAndTailAggregate => {
            let aggregate = kappa
                .mul(rows[row].terminal[1])
                .add(kappa.square().mul(rows[row].terminal[2]));
            raw.extend_from_slice(&qm31_coordinates(basis.mul(rows[row].terminal[0])));
            raw.extend_from_slice(&qm31_coordinates(basis.mul(aggregate)));
        }
    }
    raw
}

fn qm31_raw_difference_retained_terminals(
    rows: &[RowPublicMaps],
    row: usize,
    dependent: Option<usize>,
    basis: QM31,
    terminal_conditioning: GRawTerminalConditioning,
    kappa: QM31,
) -> Vec<M31> {
    let mut raw = Vec::with_capacity(
        4 * (rows[row].layer0_m31.len() + terminal_conditioning.coordinate_count()),
    );
    for (index, value) in rows[row].layer0_m31.iter().copied().enumerate() {
        let value = dependent.map_or(value, |dependent| {
            value.sub(rows[dependent].layer0_m31[index])
        });
        raw.extend_from_slice(&qm31_coordinates(basis.mul_m31(value)));
    }
    let terminal_difference = |point: usize| {
        dependent.map_or(rows[row].terminal[point], |dependent| {
            rows[row].terminal[point].sub(rows[dependent].terminal[point])
        })
    };
    match terminal_conditioning {
        GRawTerminalConditioning::Dedicated(retained_terminal_mask) => {
            for point in 0..3 {
                if (retained_terminal_mask & (1 << point)) == 0 {
                    continue;
                }
                raw.extend_from_slice(&qm31_coordinates(basis.mul(terminal_difference(point))));
            }
        }
        GRawTerminalConditioning::ZAndTailAggregate => {
            let z = terminal_difference(0);
            let aggregate = kappa
                .mul(terminal_difference(1))
                .add(kappa.square().mul(terminal_difference(2)));
            raw.extend_from_slice(&qm31_coordinates(basis.mul(z)));
            raw.extend_from_slice(&qm31_coordinates(basis.mul(aggregate)));
        }
    }
    raw
}

fn qm31_h_pcs_single_image(
    rows: &[Qm31RowPublicMaps],
    row: usize,
    basis: QM31,
    h_scale: QM31,
    h_raw_qm31: usize,
    pcs_tail_qm31: usize,
) -> Vec<M31> {
    let mut image = Vec::with_capacity(4 * (h_raw_qm31 + pcs_tail_qm31));
    for value in &rows[row].layer0 {
        image.extend_from_slice(&qm31_coordinates(basis.mul(*value)));
    }
    for value in rows[row].terminal {
        image.extend_from_slice(&qm31_coordinates(basis.mul(value)));
    }
    image.extend_from_slice(&scaled_qm31_difference(
        &rows[row].pcs_tail,
        None,
        basis.mul(h_scale),
    ));
    image
}

fn affine_g_aux(
    rows: &[Qm31RowPublicMaps],
    row: usize,
    basis: QM31,
    pcs_scale: QM31,
    sc_m31: usize,
    h_raw_qm31: usize,
    joint_pcs_m31: usize,
) -> Vec<M31> {
    let mut aux = vec![M31::ZERO; sc_m31 + joint_pcs_m31];
    let pcs = scaled_qm31_difference(&rows[row].pcs_tail, None, basis.mul(pcs_scale));
    let start = sc_m31 + 4 * h_raw_qm31;
    aux[start..start + pcs.len()].copy_from_slice(&pcs);
    aux
}

fn run_affine_slice_variant(
    schedule: &StateOnlyTranscriptScheduleResult,
    insertion_coordinate: usize,
    c: QM31,
    g_terminal_conditioning: GRawTerminalConditioning,
    z_relation_weight: QM31,
) -> Result<AtomicProfile21AffineSliceVariantReport, StateOnlyHidingRankGateError> {
    let started = Instant::now();
    if g_terminal_conditioning.dedicated_mask() & !0b111 != 0 {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    // Exact claim-preservation guard, independent of the three terminal
    // checks below.  It verifies both halves of the construction against the
    // literal initial relation: duplication reconstructs the old functional,
    // while `(-c,1-c)` lies in its kernel for every logical coefficient.
    let lifted_initial =
        affine_slice_initial_weights(schedule, insertion_coordinate, c, z_relation_weight)?;
    let old_initial = logical_initial_weights_with_z_weight(schedule, z_relation_weight)?;
    for row in 0..TRACE_ROWS {
        let row0 = embed_extended_trace_row(row, insertion_coordinate, 0);
        let row1 = embed_extended_trace_row(row, insertion_coordinate, 1);
        let weight0 = lifted_initial.weight_at(row0 as u32);
        let weight1 = lifted_initial.weight_at(row1 as u32);
        if weight0.add(weight1) != old_initial.weight_at(row as u32)
            || weight0
                .mul(QM31::ZERO.sub(c))
                .add(weight1.mul(QM31::ONE.sub(c)))
                != QM31::ZERO
        {
            return Err(StateOnlyHidingRankGateError::Layout);
        }
    }
    let domain_log = STATE_ONLY_LOG_ROWS + 9;
    let encoder = CircleEncoder::new_for_domain_log(domain_log);
    let (physical, later_indices) = affine_slice_physical_rows(
        &encoder,
        domain_log,
        schedule,
        insertion_coordinate,
        c,
        z_relation_weight,
    )?;
    let independent = pair_combination_rows(&physical, insertion_coordinate, [M31::ONE, M31::ONE]);
    let affine = qm31_pair_combination_rows(
        &physical,
        insertion_coordinate,
        [QM31::ZERO.sub(c), QM31::ONE.sub(c)],
    );

    // The affine pair must vanish at all three literal s=c terminals.  This
    // assertion catches both bit-order mistakes and accidental use of the
    // physical 11-bit row as a logical 10-bit sumcheck row.
    if affine
        .iter()
        .flat_map(|row| row.terminal)
        .any(|value| value != QM31::ZERO)
    {
        return Err(StateOnlyHidingRankGateError::Layout);
    }

    let layer0_m31 = independent[0].layer0_m31.len();
    let c1_raw_m31 = layer0_m31 + 12;
    let g_raw_m31 = 4 * (layer0_m31 + g_terminal_conditioning.coordinate_count());
    let pcs_tail_qm31 = independent[0].pcs_tail.len();
    if independent
        .iter()
        .any(|row| row.layer0_m31.len() != layer0_m31 || row.pcs_tail.len() != pcs_tail_qm31)
        || affine
            .iter()
            .any(|row| row.layer0.len() != layer0_m31 || row.pcs_tail.len() != pcs_tail_qm31)
    {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let later_opened_symbols = later_indices
        .iter()
        .map(|indices| FIBER_SLOTS * indices.len())
        .sum::<usize>();
    let expected_tail = later_opened_symbols
        + CANDIDATE_ROUND_COUNT * CANDIDATE_OOD_SAMPLES
        + CANDIDATE_ROUND_COUNT * 7
        + 8;
    if pcs_tail_qm31 != expected_tail {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let h_raw_qm31 = layer0_m31 + 3;
    let joint_pcs_m31 = 4 * (h_raw_qm31 + pcs_tail_qm31);
    let sc_m31 = 4 * STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS;
    let aux_m31 = sc_m31 + joint_pcs_m31;
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

    let mut base_sumcheck_kernel_images = Vec::new();
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
                &independent,
                row,
                subtract,
                &observations,
                QM31::ONE,
                powers[column],
                4 * h_raw_qm31,
                joint_pcs_m31,
            );
            if let Some(kernel) = raw.reduce(c1_raw_difference(&independent, row, subtract), aux) {
                base_sumcheck_kernel_images.push(kernel);
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
        let mut raw = CarryEchelon::new(c1_raw_m31);
        for row in 0..TRACE_ROWS {
            if row == global_dependent {
                continue;
            }
            let subtract = (!active[row]).then_some(global_dependent);
            let aux = scaled_aux_difference(
                &independent,
                row,
                subtract,
                &observations,
                QM31::ONE,
                powers[generator],
                4 * h_raw_qm31,
                joint_pcs_m31,
            );
            if let Some(kernel) = raw.reduce(c1_raw_difference(&independent, row, subtract), aux) {
                base_sumcheck_kernel_images.push(kernel);
            }
        }
        if raw.rank != c1_raw_m31 {
            return Err(StateOnlyHidingRankGateError::RawC1Rank {
                column: generator,
                got: raw.rank,
                want: c1_raw_m31,
            });
        }
    }

    let base_g_observations = (0..TRACE_ROWS)
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
    let mut g_raw = CarryEchelon::new(g_raw_m31);
    for coordinate in 0..4 {
        let basis = state_only_mask_tower_basis(coordinate);
        for row in 0..TRACE_ROWS {
            if row == global_dependent {
                continue;
            }
            let subtract = (!active[row]).then_some(global_dependent);
            let aux = scaled_aux_difference(
                &independent,
                row,
                subtract,
                &base_g_observations,
                basis,
                basis.mul(powers[g_generator_index]),
                4 * h_raw_qm31,
                joint_pcs_m31,
            );
            if let Some(kernel) = g_raw.reduce(
                qm31_raw_difference_retained_terminals(
                    &independent,
                    row,
                    subtract,
                    basis,
                    g_terminal_conditioning,
                    schedule.prefix.point_scale,
                ),
                aux,
            ) {
                base_sumcheck_kernel_images.push(kernel);
            }
        }
    }
    if g_raw.rank != g_raw_m31 {
        return Err(StateOnlyHidingRankGateError::RawGRank {
            got: g_raw.rank,
            want: g_raw_m31,
        });
    }

    // Insert the literal `(s-c)R` directions only after freezing the base G
    // raw quotient, so their carried kernels are an exact incremental block.
    let mut affine_g_sumcheck_kernel_images = Vec::new();
    let mut affine_g_raw_kernel_m31 = 0usize;
    for coordinate in 0..4 {
        let basis = state_only_mask_tower_basis(coordinate);
        for row in 0..TRACE_ROWS {
            let aux = affine_g_aux(
                &affine,
                row,
                basis,
                powers[g_generator_index],
                sc_m31,
                h_raw_qm31,
                joint_pcs_m31,
            );
            if let Some(kernel) = g_raw.reduce(
                qm31_row_raw_image(
                    &affine,
                    row,
                    basis,
                    g_terminal_conditioning,
                    schedule.prefix.point_scale,
                ),
                aux,
            ) {
                affine_g_raw_kernel_m31 += 1;
                affine_g_sumcheck_kernel_images.push((4 * row + coordinate, kernel));
            }
        }
    }

    let mut sumcheck = CarryEchelon::new(sc_m31);
    let mut base_pcs_kernel_images = Vec::new();
    for image in base_sumcheck_kernel_images {
        let (sc, pcs) = image.split_at(sc_m31);
        if let Some(kernel) = sumcheck.reduce(sc.to_vec(), pcs.to_vec()) {
            base_pcs_kernel_images.push(kernel);
        }
    }
    if sumcheck.rank != MASK_SUMCHECK_QUOTIENT_M31 {
        return Err(StateOnlyHidingRankGateError::MaskedSumcheckRank {
            got: sumcheck.rank,
            want: MASK_SUMCHECK_QUOTIENT_M31,
        });
    }
    let mut affine_g_pcs_images = Vec::new();
    for (source, image) in affine_g_sumcheck_kernel_images {
        let (sc, pcs) = image.split_at(sc_m31);
        let quotient = sumcheck
            .quotient_existing(sc.to_vec(), pcs.to_vec())
            .ok_or(StateOnlyHidingRankGateError::Layout)?;
        affine_g_pcs_images.push((source, quotient));
    }

    let mut baseline = ColumnEchelon::new(joint_pcs_m31);
    for image in base_pcs_kernel_images {
        baseline.insert(image);
    }
    let h_scale = powers[h_generator_index];
    for coordinate in 0..4 {
        let basis = state_only_mask_tower_basis(coordinate);
        for &row in &inactive {
            if row != global_dependent {
                baseline.insert(h_pcs_image(
                    &independent,
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

    let mut affine_g_selected = baseline.clone();
    let mut affine_g_sources = Vec::new();
    let mut affine_g_rows = Vec::new();
    let mut affine_g_values = Vec::new();
    for (source, image) in &affine_g_pcs_images {
        if let Some((pivot, value)) = affine_g_selected.insert_with_pivot_value(image.clone()) {
            affine_g_sources.push(*source);
            affine_g_rows.push(pivot);
            affine_g_values.push(value);
        }
    }
    let affine_g_pcs_rank_m31 = affine_g_selected.rank;
    let affine_g_minor = RankMinorProvenance::from_parts(
        "atomic_profile21_affine_slice_g",
        affine_g_sources,
        affine_g_rows.clone(),
        affine_g_values,
    );

    // Conservative same-statement audit, with every semantic direction
    // duplicated across s.  Sumcheck directions remain indexed by the old
    // logical 10-bit row and are never indexed by the embedded physical row.
    let mut compatibility = CarryEchelon::new(sc_m31);
    let mut semantic_images = Vec::new();
    let mut semantic_sources = Vec::new();
    let mut semantic_rows = Vec::new();
    let mut semantic_values = Vec::new();
    let pcs_start = sc_m31 + 4 * h_raw_qm31;
    let mut semantic_reference = baseline.clone();
    for column in 0..STATE_ONLY_HIDING_C1_COLUMNS {
        for row in 1..TRACE_ROWS {
            let source_id = column * TRACE_ROWS + row;
            let raw = c1_raw_difference(&independent, row, None);
            let mut carry = vec![M31::ZERO; aux_m31];
            let pcs = scaled_qm31_difference(&independent[row].pcs_tail, None, powers[column]);
            carry[pcs_start..pcs_start + pcs.len()].copy_from_slice(&pcs);
            let post_raw = semantic_raw_echelons[column]
                .quotient_existing(raw, carry)
                .ok_or(StateOnlyHidingRankGateError::WitnessRawQuotient { source: source_id })?;
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
                post_sumcheck.truncate(joint_pcs_m31);
                if let Some((pivot, value)) =
                    semantic_reference.insert_with_pivot_value(post_sumcheck.clone())
                {
                    semantic_images.push(post_sumcheck);
                    semantic_sources.push(source_id);
                    semantic_rows.push(pivot);
                    semantic_values.push(value);
                }
            }
        }
    }
    if compatibility.rank != 4 {
        return Err(StateOnlyHidingRankGateError::Layout);
    }
    let baseline_semantic_augmented_rank_m31 = semantic_reference.rank;
    let baseline_semantic_new_pivots_m31 = semantic_rows.clone();
    let semantic_minor = RankMinorProvenance::from_parts(
        "atomic_profile21_affine_slice_semantic",
        semantic_sources,
        semantic_rows,
        semantic_values,
    );

    let mut legal_images = Vec::new();
    let mut legal_sources = Vec::new();
    let mut legal_rows = Vec::new();
    let mut legal_values = Vec::new();
    for sc_row in 4..sc_m31 {
        let mut sc = vec![M31::ZERO; sc_m31];
        sc[sc_row] = M31::ONE;
        let pcs = vec![M31::ZERO; joint_pcs_m31];
        let (sc_remainder, mut pcs_remainder) = sumcheck.remainder_existing(sc, pcs);
        pcs_remainder.extend([M31::ZERO; 4]);
        if let CarryReduction::Kernel(mut post_sumcheck) =
            compatibility.reduce_with_pivot(sc_remainder, pcs_remainder)
        {
            post_sumcheck.truncate(joint_pcs_m31);
            if let Some((pivot, value)) =
                semantic_reference.insert_with_pivot_value(post_sumcheck.clone())
            {
                legal_images.push(post_sumcheck);
                legal_sources.push(sc_row - 4);
                legal_rows.push(pivot);
                legal_values.push(value);
            }
        }
    }
    let baseline_legal_sumcheck_augmented_rank_m31 = semantic_reference.rank;
    let baseline_legal_sumcheck_new_pivots_m31 = legal_rows.clone();
    let legal_sumcheck_minor = RankMinorProvenance::from_parts(
        "atomic_profile21_affine_slice_legal_sumcheck",
        legal_sources,
        legal_rows,
        legal_values,
    );
    let mut g_semantic = affine_g_selected.clone();
    let mut semantic_new_pivots_m31 = Vec::new();
    for image in &semantic_images {
        if let Some(pivot) = g_semantic.insert_with_pivot(image.clone()) {
            semantic_new_pivots_m31.push(pivot);
        }
    }
    let semantic_augmented_rank_m31 = g_semantic.rank;
    let mut legal_sumcheck_new_pivots_m31 = Vec::new();
    for image in &legal_images {
        if let Some(pivot) = g_semantic.insert_with_pivot(image.clone()) {
            legal_sumcheck_new_pivots_m31.push(pivot);
        }
    }
    let legal_sumcheck_augmented_rank_m31 = g_semantic.rank;

    // Cheap companion diagnostic: add an independent affine-slice R in H,
    // including its literal raw H openings and the identical PCS tail.
    let mut affine_g_and_h = affine_g_selected;
    let mut affine_h_sources = Vec::new();
    let mut affine_h_rows = Vec::new();
    let mut affine_h_values = Vec::new();
    for coordinate in 0..4 {
        let basis = state_only_mask_tower_basis(coordinate);
        for row in 0..TRACE_ROWS {
            let image =
                qm31_h_pcs_single_image(&affine, row, basis, h_scale, h_raw_qm31, pcs_tail_qm31);
            if let Some((pivot, value)) = affine_g_and_h.insert_with_pivot_value(image) {
                affine_h_sources.push(4 * row + coordinate);
                affine_h_rows.push(pivot);
                affine_h_values.push(value);
            }
        }
    }
    let affine_g_and_h_pcs_rank_m31 = affine_g_and_h.rank;
    let affine_h_minor = RankMinorProvenance::from_parts(
        "atomic_profile21_affine_slice_h",
        affine_h_sources,
        affine_h_rows.clone(),
        affine_h_values,
    );
    let mut gh_semantic = affine_g_and_h;
    let mut gh_semantic_pivots = Vec::new();
    for image in &semantic_images {
        if let Some(pivot) = gh_semantic.insert_with_pivot(image.clone()) {
            gh_semantic_pivots.push(pivot);
        }
    }
    let gh_semantic_rank = gh_semantic.rank;
    let mut gh_legal_pivots = Vec::new();
    for image in &legal_images {
        if let Some(pivot) = gh_semantic.insert_with_pivot(image.clone()) {
            gh_legal_pivots.push(pivot);
        }
    }
    let gh_legal_rank = gh_semantic.rank;

    Ok(AtomicProfile21AffineSliceVariantReport {
        insertion_coordinate,
        slice_value_coordinates_m31: qm31_coordinates(c).map(|coordinate| coordinate.0),
        slice_value_m31: c.c0.a.0,
        g_retained_terminal_mask: g_terminal_conditioning.dedicated_mask(),
        g_uses_z_and_weighted_aggregate: matches!(
            g_terminal_conditioning,
            GRawTerminalConditioning::ZAndTailAggregate
        ),
        z_relation_weight_coordinates_m31: qm31_coordinates(z_relation_weight)
            .map(|coordinate| coordinate.0),
        g_single_terminal_reconstructible: [
            true,
            schedule.prefix.point_scale != QM31::ZERO,
            schedule.prefix.point_scale.square() != QM31::ZERO,
        ],
        masked_sumcheck_rank_m31: sumcheck.rank,
        g_raw_rank_m31: g_raw.rank,
        affine_g_raw_kernel_m31,
        baseline_pcs_rank_m31,
        baseline_semantic_augmented_rank_m31,
        baseline_semantic_new_pivots_m31,
        baseline_legal_sumcheck_augmented_rank_m31,
        baseline_legal_sumcheck_new_pivots_m31,
        baseline_contains_conservative_semantic_and_legal_sumcheck: baseline_pcs_rank_m31
            == baseline_legal_sumcheck_augmented_rank_m31,
        affine_g_pcs_rank_m31,
        affine_g_new_pivots_m31: affine_g_rows,
        affine_g_minor,
        semantic_augmented_rank_m31,
        semantic_new_pivots_m31,
        legal_sumcheck_augmented_rank_m31,
        legal_sumcheck_new_pivots_m31,
        contains_conservative_semantic_and_legal_sumcheck: affine_g_pcs_rank_m31
            == legal_sumcheck_augmented_rank_m31,
        affine_g_and_h_pcs_rank_m31,
        affine_g_and_h_new_pivots_m31: affine_h_rows,
        affine_g_and_h_semantic_augmented_rank_m31: gh_semantic_rank,
        affine_g_and_h_semantic_new_pivots_m31: gh_semantic_pivots,
        affine_g_and_h_legal_sumcheck_augmented_rank_m31: gh_legal_rank,
        affine_g_and_h_legal_sumcheck_new_pivots_m31: gh_legal_pivots,
        affine_g_and_h_contains_conservative_semantic_and_legal_sumcheck:
            affine_g_and_h_pcs_rank_m31 == gh_legal_rank,
        affine_h_minor,
        semantic_minor,
        legal_sumcheck_minor,
        elapsed_millis: started.elapsed().as_millis(),
    })
}

/// One checkpointable coordinate of the exact affine-slice scan.
pub fn probe_atomic_state_only_profile21_affine_slice_lift_rank_variant(
    schedule: &StateOnlyProfile21TranscriptScheduleResult,
    insertion_coordinate: usize,
    slice_value: M31,
) -> Result<AtomicProfile21AffineSliceVariantReport, StateOnlyHidingRankGateError> {
    if schedule.base.query_count != 16 || insertion_coordinate > STATE_ONLY_HIDING_SUMCHECK_ROUNDS {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    run_affine_slice_variant(
        &schedule.base,
        insertion_coordinate,
        QM31::from_cm31(CM31::from_m31(slice_value)),
        GRawTerminalConditioning::Dedicated(0b111),
        QM31::ONE,
    )
}

/// One checkpointable fixed slice over the full challenge field.  In
/// particular this admits a tower-basis value outside M31.
pub fn probe_atomic_state_only_profile21_affine_extension_slice_lift_rank_variant(
    schedule: &StateOnlyProfile21TranscriptScheduleResult,
    insertion_coordinate: usize,
    slice_value: QM31,
) -> Result<AtomicProfile21AffineSliceVariantReport, StateOnlyHidingRankGateError> {
    if !matches!(schedule.base.query_count, 16 | 18)
        || insertion_coordinate > STATE_ONLY_HIDING_SUMCHECK_ROUNDS
    {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    run_affine_slice_variant(
        &schedule.base,
        insertion_coordinate,
        slice_value,
        GRawTerminalConditioning::Dedicated(0b111),
        QM31::ONE,
    )
}

/// Production-neutral claim-elision rank variant.  Only the selected G raw
/// terminal coordinates are conditioned on; C1/H raw views and the complete
/// PCS relation tail remain byte-for-byte represented in the linear map.
///
/// Rank containment is only a necessary privacy diagnostic.  In particular,
/// omitting more than one terminal is not justified by the single weighted
/// initial-relation claim and must not be treated as a sound protocol change.
pub fn probe_atomic_state_only_profile21_affine_g_claim_elision_rank_variant(
    schedule: &StateOnlyProfile21TranscriptScheduleResult,
    insertion_coordinate: usize,
    slice_value: QM31,
    g_retained_terminal_mask: u8,
) -> Result<AtomicProfile21AffineSliceVariantReport, StateOnlyHidingRankGateError> {
    if !matches!(schedule.base.query_count, 16 | 18)
        || insertion_coordinate > STATE_ONLY_HIDING_SUMCHECK_ROUNDS
        || g_retained_terminal_mask & !0b111 != 0
    {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    run_affine_slice_variant(
        &schedule.base,
        insertion_coordinate,
        slice_value,
        GRawTerminalConditioning::Dedicated(g_retained_terminal_mask),
        QM31::ONE,
    )
}

/// Exact rank image of the physically claim-carrying G map: retain `G(z)`
/// for terminal verification and replace the successor/xor pair by the
/// weighted tail claim
/// `A_tail = kappa G(successor(z)) + kappa^2 G(xor12(z))`.
/// The PCS relation must use the independently sampled `tau` as the `G(z)`
/// coefficient. C1/H keep all three terminal coordinates.
pub fn probe_atomic_state_only_profile21_affine_g_z_aggregate_claim_rank_variant(
    schedule: &StateOnlyProfile21TranscriptScheduleResult,
    insertion_coordinate: usize,
    slice_value: QM31,
    tau: QM31,
) -> Result<AtomicProfile21AffineSliceVariantReport, StateOnlyHidingRankGateError> {
    if !matches!(schedule.base.query_count, 16 | 18)
        || insertion_coordinate > STATE_ONLY_HIDING_SUMCHECK_ROUNDS
    {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    run_affine_slice_variant(
        &schedule.base,
        insertion_coordinate,
        slice_value,
        GRawTerminalConditioning::ZAndTailAggregate,
        tau,
    )
}

/// Scan the requested fixed non-Boolean slices, stopping at the first exact
/// semantic+legal-sumcheck containment result.  The scan is diagnostic only;
/// no production prover or verifier accepts a new layout based on this rank.
pub fn probe_atomic_state_only_profile21_affine_slice_lift_rank(
    schedule: &StateOnlyProfile21TranscriptScheduleResult,
) -> Result<AtomicProfile21AffineSliceLiftRankReport, StateOnlyHidingRankGateError> {
    let started = Instant::now();
    let schedule = &schedule.base;
    if schedule.query_count != 16 || schedule.prefix.z.len() != STATE_ONLY_HIDING_SUMCHECK_ROUNDS {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let mut tested = Vec::new();
    let mut first_contained_index = None;
    'slice: for c in [M31(2), M31(3), M31(5), M31(7)] {
        for chunk_start in (0..=STATE_ONLY_HIDING_SUMCHECK_ROUNDS).step_by(4) {
            let chunk_end = (chunk_start + 4).min(STATE_ONLY_HIDING_SUMCHECK_ROUNDS + 1);
            let variants = std::thread::scope(|scope| {
                let handles = (chunk_start..chunk_end)
                    .map(|insertion_coordinate| {
                        scope.spawn(move || {
                            run_affine_slice_variant(
                                schedule,
                                insertion_coordinate,
                                QM31::from_cm31(CM31::from_m31(c)),
                                GRawTerminalConditioning::Dedicated(0b111),
                                QM31::ONE,
                            )
                        })
                    })
                    .collect::<Vec<_>>();
                handles
                    .into_iter()
                    .map(|handle| {
                        handle
                            .join()
                            .map_err(|_| StateOnlyHidingRankGateError::Layout)?
                    })
                    .collect::<Result<Vec<_>, _>>()
            })?;
            let mut chunk_contained = false;
            for variant in variants {
                let contained = variant.contains_conservative_semantic_and_legal_sumcheck
                    || variant.affine_g_and_h_contains_conservative_semantic_and_legal_sumcheck;
                tested.push(variant);
                if contained && first_contained_index.is_none() {
                    first_contained_index = Some(tested.len() - 1);
                    chunk_contained = true;
                }
            }
            if chunk_contained {
                break 'slice;
            }
        }
    }
    let domain_log = STATE_ONLY_LOG_ROWS + 9;
    let codeword_len = CircleEncoder::new_for_domain_log(domain_log).codeword_len();
    Ok(AtomicProfile21AffineSliceLiftRankReport {
        query_count: schedule.query_count,
        message_log: EXTENDED_LOG_ROWS,
        codeword_domain_log: domain_log,
        codeword_len,
        rate_denominator: codeword_len / EXTENDED_TRACE_ROWS,
        tested,
        first_contained_index,
        elapsed_millis: started.elapsed().as_millis(),
    })
}
