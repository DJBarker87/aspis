//! Exact, production-neutral two-variable restriction-kernel rank probe.
//!
//! Every ten-variable word is lifted to twelve variables by duplicating it
//! across the two new most-significant Boolean coordinates `(s,t)`.  Public
//! evaluation is restricted to `(s,t)=(c,d)`.  A promotable construction must
//! take `c,d` in M31: otherwise a malicious M31 physical word can restrict to
//! an extension-valued logical trace unless a separate subcode check is added.
//! Extension-valued slices are therefore diagnostic only.  The existing `G` oracle gets
//! three independent full-QM31 masks
//!
//! ```text
//! (s-c) R1 + (t-d) R2 + (s-c)(t-d) R3.
//! ```
//!
//! The masks vanish identically on the statement slice.  This file only
//! measures the exact linear transcript image; it does not alter the prover,
//! verifier, transcript, or accepted proof format.

use super::*;

const TWO_VARIABLE_LOG_ROWS: u32 = STATE_ONLY_LOG_ROWS + 2;
const TWO_VARIABLE_TRACE_ROWS: usize = 1 << TWO_VARIABLE_LOG_ROWS;
const TWO_VARIABLE_FINAL_COEFFICIENTS: usize =
    TWO_VARIABLE_TRACE_ROWS / FIBER_SLOTS.pow(CANDIDATE_ROUND_COUNT as u32);
const RESTRICTION_KERNEL_MASKS: usize = 3;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AtomicProfile21TwoVariableSliceLiftRankReport {
    pub query_count: usize,
    pub message_log: u32,
    pub codeword_domain_log: u32,
    pub codeword_len: usize,
    pub rate_denominator: usize,
    pub final_coefficients_qm31: usize,
    pub slice_c_coordinates_m31: [u32; 4],
    pub slice_d_coordinates_m31: [u32; 4],
    pub initial_restriction_guard: bool,
    pub terminal_zero_guard: bool,
    pub sparse_dense_differential_guard: bool,
    pub sparse_dense_differential_rows: Vec<usize>,
    pub masked_sumcheck_rank_m31: usize,
    pub g_raw_rank_m31: usize,
    pub restriction_raw_kernel_m31: [usize; RESTRICTION_KERNEL_MASKS],
    pub baseline_pcs_rank_m31: usize,
    pub restriction_incremental_pcs_rank_m31: [usize; RESTRICTION_KERNEL_MASKS],
    pub restriction_incremental_new_pivots_m31: [Vec<usize>; RESTRICTION_KERNEL_MASKS],
    pub restriction_pcs_rank_m31: usize,
    pub semantic_augmented_rank_m31: usize,
    pub semantic_new_pivots_m31: Vec<usize>,
    pub legal_sumcheck_augmented_rank_m31: usize,
    pub legal_sumcheck_new_pivots_m31: Vec<usize>,
    pub contains_conservative_semantic_and_legal_sumcheck: bool,
    pub restriction_minor: RankMinorProvenance,
    pub semantic_minor: RankMinorProvenance,
    pub legal_sumcheck_minor: RankMinorProvenance,
    pub elapsed_millis: u128,
}

#[derive(Clone)]
struct Qm31RowPublicMaps {
    layer0: Vec<QM31>,
    terminal: [QM31; 3],
    pcs_tail: Vec<QM31>,
}

impl Qm31RowPublicMaps {
    fn zero(layer0: usize, pcs_tail: usize) -> Self {
        Self {
            layer0: vec![QM31::ZERO; layer0],
            terminal: [QM31::ZERO; 3],
            pcs_tail: vec![QM31::ZERO; pcs_tail],
        }
    }

    fn add_scaled_physical(&mut self, physical: &RowPublicMaps, scale: QM31) {
        for (output, &value) in self.layer0.iter_mut().zip(&physical.layer0_m31) {
            *output = output.add(scale.mul_m31(value));
        }
        for (output, &value) in self.terminal.iter_mut().zip(&physical.terminal) {
            *output = output.add(scale.mul(value));
        }
        for (output, &value) in self.pcs_tail.iter_mut().zip(&physical.pcs_tail) {
            *output = output.add(scale.mul(value));
        }
    }
}

struct SparseRelationSchedule {
    before_round: Vec<Vec<QM31>>,
    polynomial_weights: Vec<Vec<QM31>>,
    evaluations: Vec<[Vec<QM31>; CANDIDATE_OOD_SAMPLES]>,
    final_weights: Vec<QM31>,
}

fn two_variable_point(
    point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
    c: QM31,
    d: QM31,
) -> [QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS + 2] {
    core::array::from_fn(|coordinate| match coordinate {
        0 => c,
        1 => d,
        _ => point[coordinate - 2],
    })
}

#[inline]
fn physical_row(logical_row: usize, s: usize, t: usize) -> usize {
    debug_assert!(logical_row < TRACE_ROWS && s <= 1 && t <= 1);
    (s << (STATE_ONLY_HIDING_SUMCHECK_ROUNDS + 1))
        | (t << STATE_ONLY_HIDING_SUMCHECK_ROUNDS)
        | logical_row
}

#[inline]
fn slice_bit_weight(bit: usize, value: QM31) -> QM31 {
    if bit == 0 {
        QM31::ONE.sub(value)
    } else {
        value
    }
}

#[inline]
fn restriction_factor(bit: usize, value: QM31) -> QM31 {
    if bit == 0 {
        QM31::ZERO.sub(value)
    } else {
        QM31::ONE.sub(value)
    }
}

fn two_variable_initial_weights(
    schedule: &StateOnlyTranscriptScheduleResult,
    c: QM31,
    d: QM31,
) -> Result<WeightAccumulator, StateOnlyHidingRankGateError> {
    let points = [
        two_variable_point(&schedule.prefix.z, c, d),
        two_variable_point(&binary_successor_point(&schedule.prefix.z), c, d),
        two_variable_point(&xor12_point(&schedule.prefix.z), c, d),
    ];
    let kappa = schedule.prefix.point_scale;
    let mut weights = WeightAccumulator::empty(TWO_VARIABLE_LOG_ROWS);
    for (point, scale) in points.into_iter().zip([QM31::ONE, kappa, kappa.square()]) {
        weights
            .add_multilinear(scale, point.to_vec())
            .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
    }

    let inactive = rank_inactive_masks(RankLayout::AtomicV3);
    let mut dense = vec![QM31::ZERO; TWO_VARIABLE_TRACE_ROWS];
    for logical_row in 0..TRACE_ROWS {
        if ((inactive[logical_row >> 4] >> (logical_row & 15)) & 1) == 0 {
            continue;
        }
        for s in 0..2 {
            for t in 0..2 {
                dense[physical_row(logical_row, s, t)] =
                    slice_bit_weight(s, c).mul(slice_bit_weight(t, d));
            }
        }
    }
    weights
        .add_dense(dense)
        .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
    Ok(weights)
}

fn materialize_weights(weights: &WeightAccumulator, len: usize) -> Vec<QM31> {
    (0..len)
        .map(|index| weights.weight_at(index as u32))
        .collect()
}

fn build_sparse_relation_schedule(
    schedule: &StateOnlyTranscriptScheduleResult,
    c: QM31,
    d: QM31,
) -> Result<SparseRelationSchedule, StateOnlyHidingRankGateError> {
    let mut weights = two_variable_initial_weights(schedule, c, d)?;
    let mut before_round = Vec::with_capacity(CANDIDATE_ROUND_COUNT);
    let mut polynomial_weights = Vec::with_capacity(CANDIDATE_ROUND_COUNT);
    let mut evaluations = Vec::with_capacity(CANDIDATE_ROUND_COUNT);
    let mut len = TWO_VARIABLE_TRACE_ROWS;

    for round in 0..CANDIDATE_ROUND_COUNT {
        before_round.push(materialize_weights(&weights, len));
        let round_evaluations = core::array::from_fn(|sample| {
            let mut evaluation = WeightAccumulator::empty(TWO_VARIABLE_LOG_ROWS - 2 * round as u32);
            let added = if round == 0 {
                evaluation.add_circle_tensor(QM31::ONE, schedule.circle_ood_points[sample])
            } else {
                evaluation.add_line_tensor(QM31::ONE, schedule.line_ood_points[round - 1][sample])
            };
            added.expect("two-variable OOD tensor has the exact round length");
            materialize_weights(&evaluation, len)
        });
        for sample in 0..CANDIDATE_OOD_SAMPLES {
            if round == 0 {
                weights
                    .add_circle_tensor(
                        schedule.mu[round][sample],
                        schedule.circle_ood_points[sample],
                    )
                    .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
            } else {
                weights
                    .add_line_tensor(
                        schedule.mu[round][sample],
                        schedule.line_ood_points[round - 1][sample],
                    )
                    .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
            }
        }
        evaluations.push(round_evaluations);
        polynomial_weights.push(materialize_weights(&weights, len));
        weights.fold(schedule.alpha[round]);
        len /= FIBER_SLOTS;
    }
    let final_weights = materialize_weights(&weights, len);
    if len != TWO_VARIABLE_FINAL_COEFFICIENTS {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    Ok(SparseRelationSchedule {
        before_round,
        polynomial_weights,
        evaluations,
        final_weights,
    })
}

fn sparse_two_variable_folded_row_value(
    encoder: &CircleEncoder,
    domain_log: u32,
    row: usize,
    schedule: &StateOnlyTranscriptScheduleResult,
    layer: usize,
    index: usize,
    memo: &mut BTreeMap<(usize, usize), QM31>,
) -> Result<QM31, StateOnlyHidingRankGateError> {
    if let Some(value) = memo.get(&(layer, index)) {
        return Ok(*value);
    }
    let value = if layer == 0 {
        QM31::from_cm31(CM31::from_m31(encoder.encode_prefix_basis_value(
            TWO_VARIABLE_LOG_ROWS,
            row,
            index,
        )?))
    } else {
        let mut values = [QM31::ZERO; FIBER_SLOTS];
        for (slot, value) in values.iter_mut().enumerate() {
            *value = sparse_two_variable_folded_row_value(
                encoder,
                domain_log,
                row,
                schedule,
                layer - 1,
                FIBER_SLOTS * index + slot,
                memo,
            )?;
        }
        if layer == 1 {
            aspis_core::circle_fri::normalized_circle_to_line_arity4_at_fiber_for_domain_log(
                values,
                schedule.alpha[0],
                domain_log,
                index,
            )
            .map_err(|_| StateOnlyHidingRankGateError::Encoding)?
        } else {
            normalized_line_arity4_at_fiber_for_domain_log(
                values,
                schedule.alpha[layer - 1],
                domain_log,
                (layer - 1) as u8,
                index,
            )
            .map_err(|_| StateOnlyHidingRankGateError::Encoding)?
        }
    };
    memo.insert((layer, index), value);
    Ok(value)
}

fn sparse_basis_polynomial(scale: QM31, index: usize, weights: &[QM31]) -> [QM31; 7] {
    let slot = index & (FIBER_SLOTS - 1);
    let base = index - slot;
    let dual = [
        weights[base],
        weights[base + 3],
        weights[base + 2],
        weights[base + 1],
    ];
    let mut polynomial = [QM31::ZERO; 7];
    for (degree, weight) in dual.into_iter().enumerate() {
        polynomial[slot + degree] = scale.mul(weight).half().half();
    }
    polynomial
}

fn sparse_basis_fold(scale: QM31, index: usize, alpha: QM31) -> QM31 {
    let alpha2 = alpha.square();
    let alpha3 = alpha2.mul(alpha);
    // This is the primal coefficient fold.  The dual weight accumulator and
    // the relation polynomial carry the 1/4 normalization; coefficients use
    // `[1, alpha, alpha^2, alpha^3]` with no division.
    scale.mul([QM31::ONE, alpha, alpha2, alpha3][index & (FIBER_SLOTS - 1)])
}

fn two_variable_row_pcs_tail(
    encoder: &CircleEncoder,
    domain_log: u32,
    row: usize,
    schedule: &StateOnlyTranscriptScheduleResult,
    later_indices: &[Vec<u32>; CANDIDATE_ROUND_COUNT - 1],
    relation: &SparseRelationSchedule,
) -> Result<Vec<QM31>, StateOnlyHidingRankGateError> {
    let mut index = row;
    let mut scale = QM31::ONE;
    let mut running_claim = relation.before_round[0][index];
    let mut later = Vec::new();
    let mut ood_values = [[QM31::ZERO; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT];
    let mut polynomials = [[QM31::ZERO; 7]; CANDIDATE_ROUND_COUNT];
    let mut memo = BTreeMap::new();

    for round in 0..CANDIDATE_ROUND_COUNT {
        if scale.mul(relation.before_round[round][index]) != running_claim {
            return Err(StateOnlyHidingRankGateError::Relation);
        }
        for sample in 0..CANDIDATE_OOD_SAMPLES {
            let value = scale.mul(relation.evaluations[round][sample][index]);
            ood_values[round][sample] = value;
            running_claim = running_claim.add(schedule.mu[round][sample].mul(value));
        }
        let polynomial = sparse_basis_polynomial(scale, index, &relation.polynomial_weights[round]);
        if boundary_sum(&polynomial) != running_claim {
            return Err(StateOnlyHidingRankGateError::Relation);
        }
        polynomials[round] = polynomial;
        running_claim = evaluate_relation(&polynomial, schedule.alpha[round]);
        scale = sparse_basis_fold(scale, index, schedule.alpha[round]);
        index /= FIBER_SLOTS;

        if round + 1 < CANDIDATE_ROUND_COUNT {
            if scale.mul(relation.before_round[round + 1][index]) != running_claim {
                return Err(StateOnlyHidingRankGateError::Relation);
            }
            for &leaf in &later_indices[round] {
                for slot in 0..FIBER_SLOTS {
                    later.push(sparse_two_variable_folded_row_value(
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
    if scale.mul(relation.final_weights[index]) != running_claim {
        return Err(StateOnlyHidingRankGateError::Relation);
    }

    let mut tail = later;
    for values in ood_values {
        tail.extend_from_slice(&values);
    }
    for polynomial in polynomials {
        tail.extend_from_slice(&polynomial);
    }
    let mut final_coefficients = vec![QM31::ZERO; TWO_VARIABLE_FINAL_COEFFICIENTS];
    final_coefficients[index] = scale;
    tail.extend_from_slice(&final_coefficients);
    Ok(tail)
}

fn physical_basis_public_maps(
    encoder: &CircleEncoder,
    domain_log: u32,
    row: usize,
    schedule: &StateOnlyTranscriptScheduleResult,
    indices: &aspis_core::circle_line_merkle::CircleLineQueryIndices,
    terminal_points: &[[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS + 2]; 3],
    relation: &SparseRelationSchedule,
) -> Result<RowPublicMaps, StateOnlyHidingRankGateError> {
    let mut layer0_m31 = Vec::with_capacity(indices.layer0.len() * FIBER_SLOTS);
    for &query in &indices.layer0 {
        for slot in 0..FIBER_SLOTS {
            layer0_m31.push(encoder.encode_prefix_basis_value(
                TWO_VARIABLE_LOG_ROWS,
                row,
                FIBER_SLOTS * query as usize + slot,
            )?);
        }
    }
    Ok(RowPublicMaps {
        layer0_m31,
        terminal: core::array::from_fn(|point| eq_weight_slice(&terminal_points[point], row)),
        pcs_tail: two_variable_row_pcs_tail(
            encoder,
            domain_log,
            row,
            schedule,
            &indices.later,
            relation,
        )?,
    })
}

fn dense_physical_basis_public_maps(
    encoder: &CircleEncoder,
    domain_log: u32,
    row: usize,
    schedule: &StateOnlyTranscriptScheduleResult,
    indices: &aspis_core::circle_line_merkle::CircleLineQueryIndices,
    terminal_points: &[[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS + 2]; 3],
    c: QM31,
    d: QM31,
) -> Result<RowPublicMaps, StateOnlyHidingRankGateError> {
    let mut coefficients = vec![QM31::ZERO; TWO_VARIABLE_TRACE_ROWS];
    coefficients[row] = QM31::ONE;
    let mut codeword = encoder.encode_c2_message_prefix(&coefficients)?;
    let mut layer0_m31 = Vec::with_capacity(indices.layer0.len() * FIBER_SLOTS);
    for &query in &indices.layer0 {
        let start = FIBER_SLOTS * query as usize;
        for &value in &codeword[start..start + FIBER_SLOTS] {
            if value.c0.b != M31::ZERO || value.c1 != CM31::ZERO {
                return Err(StateOnlyHidingRankGateError::Encoding);
            }
            layer0_m31.push(value.c0.a);
        }
    }

    let mut weights = two_variable_initial_weights(schedule, c, d)?;
    let mut running_claim = weights.dot(&coefficients);
    let mut later = Vec::new();
    let mut ood_values = [[QM31::ZERO; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT];
    let mut polynomials = [[QM31::ZERO; 7]; CANDIDATE_ROUND_COUNT];
    for round in 0..CANDIDATE_ROUND_COUNT {
        for sample in 0..CANDIDATE_OOD_SAMPLES {
            let mut evaluation = WeightAccumulator::empty(TWO_VARIABLE_LOG_ROWS - 2 * round as u32);
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
        codeword = fold_candidate_codeword_round_for_domain_log(
            &codeword,
            schedule.alpha[round],
            round,
            domain_log,
        )?;
        if round + 1 < CANDIDATE_ROUND_COUNT {
            for &leaf in &indices.later[round] {
                let start = FIBER_SLOTS * leaf as usize;
                later.extend_from_slice(&codeword[start..start + FIBER_SLOTS]);
            }
        }
    }
    if coefficients.len() != TWO_VARIABLE_FINAL_COEFFICIENTS {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let mut pcs_tail = later;
    for values in ood_values {
        pcs_tail.extend_from_slice(&values);
    }
    for polynomial in polynomials {
        pcs_tail.extend_from_slice(&polynomial);
    }
    pcs_tail.extend_from_slice(&coefficients);
    Ok(RowPublicMaps {
        layer0_m31,
        terminal: core::array::from_fn(|point| eq_weight_slice(&terminal_points[point], row)),
        pcs_tail,
    })
}

fn sparse_dense_differential_guard(
    encoder: &CircleEncoder,
    domain_log: u32,
    schedule: &StateOnlyTranscriptScheduleResult,
    indices: &aspis_core::circle_line_merkle::CircleLineQueryIndices,
    terminal_points: &[[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS + 2]; 3],
    relation: &SparseRelationSchedule,
    c: QM31,
    d: QM31,
) -> Result<Vec<usize>, StateOnlyHidingRankGateError> {
    // Both endpoints plus logical rows `85 = 1111_base4` and
    // `170 = 2222_base4` in every physical `(s,t)` slice exercise all four
    // primal coefficient slots at every one of the four folds.
    let rows = vec![
        0, 85, 170, 1023, 1024, 1109, 1194, 2047, 2048, 2133, 2218, 3071, 3072, 3157, 3242, 4095,
    ];
    for &row in &rows {
        let sparse = physical_basis_public_maps(
            encoder,
            domain_log,
            row,
            schedule,
            indices,
            terminal_points,
            relation,
        )?;
        let dense = dense_physical_basis_public_maps(
            encoder,
            domain_log,
            row,
            schedule,
            indices,
            terminal_points,
            c,
            d,
        )?;
        if sparse.layer0_m31 != dense.layer0_m31
            || sparse.terminal != dense.terminal
            || sparse.pcs_tail != dense.pcs_tail
        {
            return Err(StateOnlyHidingRankGateError::Layout);
        }
    }
    Ok(rows)
}

fn two_variable_logical_maps(
    encoder: &CircleEncoder,
    domain_log: u32,
    schedule: &StateOnlyTranscriptScheduleResult,
    c: QM31,
    d: QM31,
) -> Result<
    (
        Vec<RowPublicMaps>,
        [Vec<Qm31RowPublicMaps>; RESTRICTION_KERNEL_MASKS],
        [Vec<u32>; CANDIDATE_ROUND_COUNT - 1],
    ),
    StateOnlyHidingRankGateError,
> {
    let indices = derive_circle_line_query_indices_for_count(
        &schedule.queries[..schedule.query_count],
        encoder.codeword_len() / FIBER_SLOTS,
    )
    .map_err(|_| StateOnlyHidingRankGateError::Shape)?;
    let terminal_points = [
        two_variable_point(&schedule.prefix.z, c, d),
        two_variable_point(&binary_successor_point(&schedule.prefix.z), c, d),
        two_variable_point(&xor12_point(&schedule.prefix.z), c, d),
    ];
    let relation = build_sparse_relation_schedule(schedule, c, d)?;
    let _differential_rows = sparse_dense_differential_guard(
        encoder,
        domain_log,
        schedule,
        &indices,
        &terminal_points,
        &relation,
        c,
        d,
    )?;
    let layer0 = indices.layer0.len() * FIBER_SLOTS;
    let later_opened_symbols = indices
        .later
        .iter()
        .map(|round| round.len() * FIBER_SLOTS)
        .sum::<usize>();
    let pcs_tail = later_opened_symbols
        + CANDIDATE_ROUND_COUNT * CANDIDATE_OOD_SAMPLES
        + CANDIDATE_ROUND_COUNT * 7
        + TWO_VARIABLE_FINAL_COEFFICIENTS;
    let mut independent = Vec::with_capacity(TRACE_ROWS);
    let mut kernels: [Vec<Qm31RowPublicMaps>; RESTRICTION_KERNEL_MASKS] =
        core::array::from_fn(|_| Vec::with_capacity(TRACE_ROWS));

    for logical_row in 0..TRACE_ROWS {
        let mut base = RowPublicMaps {
            layer0_m31: vec![M31::ZERO; layer0],
            terminal: [QM31::ZERO; 3],
            pcs_tail: vec![QM31::ZERO; pcs_tail],
        };
        let mut mask_rows: [Qm31RowPublicMaps; RESTRICTION_KERNEL_MASKS] =
            core::array::from_fn(|_| Qm31RowPublicMaps::zero(layer0, pcs_tail));
        for s in 0..2 {
            for t in 0..2 {
                let physical = physical_basis_public_maps(
                    encoder,
                    domain_log,
                    physical_row(logical_row, s, t),
                    schedule,
                    &indices,
                    &terminal_points,
                    &relation,
                )?;
                for (output, &value) in base.layer0_m31.iter_mut().zip(&physical.layer0_m31) {
                    *output = output.add(value);
                }
                for (output, &value) in base.terminal.iter_mut().zip(&physical.terminal) {
                    *output = output.add(value);
                }
                for (output, &value) in base.pcs_tail.iter_mut().zip(&physical.pcs_tail) {
                    *output = output.add(value);
                }
                let s_factor = restriction_factor(s, c);
                let t_factor = restriction_factor(t, d);
                mask_rows[0].add_scaled_physical(&physical, s_factor);
                mask_rows[1].add_scaled_physical(&physical, t_factor);
                mask_rows[2].add_scaled_physical(&physical, s_factor.mul(t_factor));
            }
        }
        independent.push(base);
        for (destination, row) in kernels.iter_mut().zip(mask_rows) {
            destination.push(row);
        }
    }
    Ok((independent, kernels, indices.later))
}

fn qm31_kernel_raw_image(rows: &[Qm31RowPublicMaps], row: usize, basis: QM31) -> Vec<M31> {
    let mut raw = Vec::with_capacity(4 * (rows[row].layer0.len() + 3));
    for value in &rows[row].layer0 {
        raw.extend_from_slice(&qm31_coordinates(basis.mul(*value)));
    }
    for value in rows[row].terminal {
        raw.extend_from_slice(&qm31_coordinates(basis.mul(value)));
    }
    raw
}

fn qm31_kernel_aux(
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

/// Run the exact rank gate for two inserted MSB coordinates.  The currently
/// frozen fixture supplies q16.  q20 is accepted as well so a sampler-derived
/// diagnostic schedule can be replayed without changing this linear map.
pub fn probe_atomic_state_only_profile21_two_variable_slice_lift_rank(
    schedule: &StateOnlyProfile21TranscriptScheduleResult,
    c: QM31,
    d: QM31,
) -> Result<AtomicProfile21TwoVariableSliceLiftRankReport, StateOnlyHidingRankGateError> {
    let started = Instant::now();
    let schedule = &schedule.base;
    if !matches!(schedule.query_count, 16 | 20)
        || schedule.prefix.z.len() != STATE_ONLY_HIDING_SUMCHECK_ROUNDS
    {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let domain_log = STATE_ONLY_LOG_ROWS + 9;
    let encoder = CircleEncoder::new_for_domain_log(domain_log);

    // Exact restriction guard against the literal ten-variable initial
    // relation.  All three fresh directions must lie in its kernel, row by
    // row, before any rank result is considered.
    let lifted_initial = two_variable_initial_weights(schedule, c, d)?;
    let old_initial = initial_relation_weights(schedule, RankLayout::AtomicV3)?;
    for logical_row in 0..TRACE_ROWS {
        let mut base = QM31::ZERO;
        let mut fresh = [QM31::ZERO; RESTRICTION_KERNEL_MASKS];
        for s in 0..2 {
            for t in 0..2 {
                let weight = lifted_initial.weight_at(physical_row(logical_row, s, t) as u32);
                let s_factor = restriction_factor(s, c);
                let t_factor = restriction_factor(t, d);
                base = base.add(weight);
                fresh[0] = fresh[0].add(weight.mul(s_factor));
                fresh[1] = fresh[1].add(weight.mul(t_factor));
                fresh[2] = fresh[2].add(weight.mul(s_factor.mul(t_factor)));
            }
        }
        if base != old_initial.weight_at(logical_row as u32)
            || fresh.into_iter().any(|value| value != QM31::ZERO)
        {
            return Err(StateOnlyHidingRankGateError::Layout);
        }
    }

    let (independent, kernels, later_indices) =
        two_variable_logical_maps(&encoder, domain_log, schedule, c, d)?;
    if kernels
        .iter()
        .flat_map(|rows| rows.iter())
        .flat_map(|row| row.terminal)
        .any(|value| value != QM31::ZERO)
    {
        return Err(StateOnlyHidingRankGateError::Layout);
    }

    let layer0_m31 = independent[0].layer0_m31.len();
    let c1_raw_m31 = layer0_m31 + 12;
    let g_raw_m31 = 4 * (layer0_m31 + 3);
    let pcs_tail_qm31 = independent[0].pcs_tail.len();
    let later_opened_symbols = later_indices
        .iter()
        .map(|indices| FIBER_SLOTS * indices.len())
        .sum::<usize>();
    let expected_tail = later_opened_symbols
        + CANDIDATE_ROUND_COUNT * CANDIDATE_OOD_SAMPLES
        + CANDIDATE_ROUND_COUNT * 7
        + TWO_VARIABLE_FINAL_COEFFICIENTS;
    if independent
        .iter()
        .any(|row| row.layer0_m31.len() != layer0_m31 || row.pcs_tail.len() != pcs_tail_qm31)
        || kernels
            .iter()
            .flat_map(|rows| rows.iter())
            .any(|row| row.layer0.len() != layer0_m31 || row.pcs_tail.len() != pcs_tail_qm31)
        || pcs_tail_qm31 != expected_tail
    {
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
            if let Some(kernel) =
                g_raw.reduce(qm31_raw_difference(&independent, row, subtract, basis), aux)
            {
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

    // Condition the three literal restriction-kernel masks on the already
    // complete raw-G and masked-sumcheck views, then insert only their exact
    // PCS quotient images.  This streaming form avoids retaining ~12k large
    // intermediate carry vectors.
    let mut selected = baseline.clone();
    let mut raw_kernel_counts = [0usize; RESTRICTION_KERNEL_MASKS];
    let mut incremental_ranks = [baseline_pcs_rank_m31; RESTRICTION_KERNEL_MASKS];
    let mut incremental_pivots: [Vec<usize>; RESTRICTION_KERNEL_MASKS] =
        core::array::from_fn(|_| Vec::new());
    let mut restriction_sources = Vec::new();
    let mut restriction_rows = Vec::new();
    let mut restriction_values = Vec::new();
    for mask in 0..RESTRICTION_KERNEL_MASKS {
        // Quotienting against frozen echelons is read-only and dominates the
        // host diagnostic.  Compute the four tower coordinates in parallel,
        // then insert in stable coordinate/row order so rank provenance is
        // deterministic.
        let coordinate_images = std::thread::scope(|scope| {
            let handles = (0..4)
                .map(|coordinate| {
                    let rows = &kernels[mask];
                    let g_raw = &g_raw;
                    let sumcheck = &sumcheck;
                    let pcs_scale = powers[g_generator_index];
                    scope.spawn(move || {
                        let basis = state_only_mask_tower_basis(coordinate);
                        let mut images = Vec::with_capacity(TRACE_ROWS);
                        for row in 0..TRACE_ROWS {
                            let source = mask * 4 * TRACE_ROWS + 4 * row + coordinate;
                            let aux = qm31_kernel_aux(
                                rows,
                                row,
                                basis,
                                pcs_scale,
                                sc_m31,
                                h_raw_qm31,
                                joint_pcs_m31,
                            );
                            let raw_kernel = g_raw
                                .quotient_existing(qm31_kernel_raw_image(rows, row, basis), aux)
                                .ok_or(StateOnlyHidingRankGateError::Layout)?;
                            let (sc, pcs) = raw_kernel.split_at(sc_m31);
                            let pcs = sumcheck
                                .quotient_existing(sc.to_vec(), pcs.to_vec())
                                .ok_or(StateOnlyHidingRankGateError::Layout)?;
                            images.push((source, pcs));
                        }
                        Ok::<_, StateOnlyHidingRankGateError>(images)
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
        for images in coordinate_images {
            raw_kernel_counts[mask] += images.len();
            for (source, pcs) in images {
                if let Some((pivot, value)) = selected.insert_with_pivot_value(pcs) {
                    incremental_pivots[mask].push(pivot);
                    restriction_sources.push(source);
                    restriction_rows.push(pivot);
                    restriction_values.push(value);
                }
            }
        }
        incremental_ranks[mask] = selected.rank;
    }
    let restriction_pcs_rank_m31 = selected.rank;
    let restriction_minor = RankMinorProvenance::from_parts(
        "atomic_profile21_two_variable_restriction_kernel",
        restriction_sources,
        restriction_rows,
        restriction_values,
    );

    // Conservative semantic and legal-sumcheck closure is the same exact
    // quotient construction as the one-variable gate.  Semantic rows remain
    // ten-bit logical rows; no physical twelve-bit index enters sumcheck.
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
    let semantic_minor = RankMinorProvenance::from_parts(
        "atomic_profile21_two_variable_semantic",
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
    let legal_sumcheck_minor = RankMinorProvenance::from_parts(
        "atomic_profile21_two_variable_legal_sumcheck",
        legal_sources,
        legal_rows,
        legal_values,
    );

    let mut augmented = selected;
    let mut semantic_new_pivots_m31 = Vec::new();
    for image in &semantic_images {
        if let Some(pivot) = augmented.insert_with_pivot(image.clone()) {
            semantic_new_pivots_m31.push(pivot);
        }
    }
    let semantic_augmented_rank_m31 = augmented.rank;
    let mut legal_sumcheck_new_pivots_m31 = Vec::new();
    for image in &legal_images {
        if let Some(pivot) = augmented.insert_with_pivot(image.clone()) {
            legal_sumcheck_new_pivots_m31.push(pivot);
        }
    }
    let legal_sumcheck_augmented_rank_m31 = augmented.rank;

    let codeword_len = encoder.codeword_len();
    Ok(AtomicProfile21TwoVariableSliceLiftRankReport {
        query_count: schedule.query_count,
        message_log: TWO_VARIABLE_LOG_ROWS,
        codeword_domain_log: domain_log,
        codeword_len,
        rate_denominator: codeword_len / TWO_VARIABLE_TRACE_ROWS,
        final_coefficients_qm31: TWO_VARIABLE_FINAL_COEFFICIENTS,
        slice_c_coordinates_m31: qm31_coordinates(c).map(|coordinate| coordinate.0),
        slice_d_coordinates_m31: qm31_coordinates(d).map(|coordinate| coordinate.0),
        initial_restriction_guard: true,
        terminal_zero_guard: true,
        sparse_dense_differential_guard: true,
        sparse_dense_differential_rows: vec![
            0, 85, 170, 1023, 1024, 1109, 1194, 2047, 2048, 2133, 2218, 3071, 3072, 3157, 3242,
            4095,
        ],
        masked_sumcheck_rank_m31: sumcheck.rank,
        g_raw_rank_m31: g_raw.rank,
        restriction_raw_kernel_m31: raw_kernel_counts,
        baseline_pcs_rank_m31,
        restriction_incremental_pcs_rank_m31: incremental_ranks,
        restriction_incremental_new_pivots_m31: incremental_pivots,
        restriction_pcs_rank_m31,
        semantic_augmented_rank_m31,
        semantic_new_pivots_m31,
        legal_sumcheck_augmented_rank_m31,
        legal_sumcheck_new_pivots_m31,
        contains_conservative_semantic_and_legal_sumcheck: restriction_pcs_rank_m31
            == legal_sumcheck_augmented_rank_m31,
        restriction_minor,
        semantic_minor,
        legal_sumcheck_minor,
        elapsed_millis: started.elapsed().as_millis(),
    })
}
