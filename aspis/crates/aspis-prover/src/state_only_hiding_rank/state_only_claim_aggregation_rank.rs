//! Exact log10/profile-21 rank probe for compact terminal claims.
//!
//! This module changes no production wire.  It models the physically
//! implementable split
//!
//! * semantic columns `S = 0..16`: all three terminal claims are public;
//! * unused-tail columns `U = 16..28`: only the `z` claim is public;
//! * one public aggregate
//!   `A = kappa U_gamma(succ(z)) + kappa^2 U_gamma(xor12(z))`.
//!
//! After `A` is absorbed, fresh separators `tau, delta` define the one PCS
//! word `F* = delta S_gamma + U_gamma`.  Its relation weights are
//! `[tau, kappa, kappa^2]`.  The resulting initial claim is exactly
//!
//! `delta*tau S_z + delta(kappa S_s + kappa^2 S_x) + tau U_z + A`.
//!
//! The rank map below includes the literal shared `A` row.  In particular it
//! does not pretend that every unused-tail column owns a separate aggregate.

use super::*;

const SEMANTIC_COLUMNS: usize = STATE_ONLY_HIDING_C1_COLUMNS;
const MASK_ONLY_COLUMNS: usize = STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS;
const UNUSED_COLUMNS: usize = MASK_ONLY_COLUMNS + 2;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AtomicProfile21CompactClaimRankReport {
    pub query_count: usize,
    pub message_log: u32,
    pub codeword_domain_log: u32,
    pub rate_denominator: usize,
    pub semantic_terminal_claims_qm31: usize,
    pub unused_z_claims_qm31: usize,
    pub shared_tail_claims_qm31: usize,
    pub old_claims_qm31: usize,
    pub compact_claims_qm31: usize,
    pub saved_claims_qm31: usize,
    pub saved_claim_bytes: usize,
    pub tau_coordinates_m31: [u32; 4],
    pub delta_coordinates_m31: [u32; 4],
    pub full_domain_pad_probe: bool,
    pub pad_constant_one_sumcheck_factor: bool,
    pub pad_source_basis_m31: usize,
    pub pad_joint_raw_kernel_m31: usize,
    pub shared_unused_raw_rows_m31: usize,
    pub shared_unused_raw_rank_m31: usize,
    pub shared_unused_raw_kernel_m31: usize,
    pub masked_sumcheck_rank_m31: usize,
    pub baseline_pcs_rank_m31: usize,
    pub helper_augmented_rank_m31: usize,
    pub helper_new_pivots_m31: Vec<usize>,
    pub semantic_augmented_rank_m31: usize,
    pub semantic_new_pivots_m31: Vec<usize>,
    pub legal_sumcheck_augmented_rank_m31: usize,
    pub legal_sumcheck_new_pivots_m31: Vec<usize>,
    pub contains_helper_semantic_and_legal_sumcheck: bool,
    pub bound_root0_switch_probe: bool,
    pub bound_root0_switch_coefficient_functional_mode: bool,
    pub bound_root0_switch_lean_x_only_mode: bool,
    pub bound_root0_switch_coefficient_index: usize,
    pub bound_root0_switch_message_qm31: usize,
    pub bound_root0_switch_randomness_qm31: usize,
    pub bound_root0_switch_dimension_qm31: usize,
    pub bound_root0_switch_variables_qm31: usize,
    pub bound_root0_switch_epsilon_coordinates_m31: [u32; 4],
    pub bound_root0_switch_code_basis_rank_qm31: usize,
    pub bound_root0_switch_code_basis_fingerprint: u64,
    pub bound_root0_switch_multiplier_degree: usize,
    pub bound_root0_switch_multiplier_fingerprint: u64,
    pub bound_root0_switch_product_dimension_qm31: usize,
    pub bound_root0_switch_product_max_root_slot: usize,
    pub bound_root0_switch_product_basis_fingerprint: u64,
    pub bound_root0_switch_pointwise_product_identity: bool,
    pub bound_root0_switch_fold_product_identity: bool,
    pub bound_root0_switch_folded_opening_rank_qm31: usize,
    pub bound_root0_switch_raw_opening_rank_qm31: usize,
    pub bound_root0_switch_raw_contains_folded_openings: bool,
    pub bound_root0_switch_u_plus_folded_rank_qm31: usize,
    pub bound_root0_switch_u_plus_folded_target_rank_qm31: usize,
    pub bound_root0_switch_u_plus_raw_rank_qm31: usize,
    pub bound_root0_switch_u_plus_raw_target_rank_qm31: usize,
    pub bound_root0_switch_conditioned_kernel_qm31: usize,
    pub bound_root0_switch_gamma_exponent: usize,
    pub bound_root0_switch_exact_full_tail: bool,
    pub bound_root0_switch_sparse_dense_tail_parity: bool,
    pub bound_root0_switch_pcs_augmented_rank_m31: usize,
    pub bound_root0_switch_new_pivots_m31: Vec<usize>,
    pub bound_root0_switch_pivots_later_m31: usize,
    pub bound_root0_switch_pivots_ood_m31: usize,
    pub bound_root0_switch_pivots_relation_m31: usize,
    pub bound_root0_switch_pivots_final_m31: usize,
    pub bound_root0_switch_contains_semantic_and_legal_sumcheck: bool,
    pub helper_minor: RankMinorProvenance,
    pub bound_root0_switch_minor: RankMinorProvenance,
    pub semantic_minor: RankMinorProvenance,
    pub legal_sumcheck_minor: RankMinorProvenance,
    pub elapsed_millis: u128,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CompactBoundRoot0SwitchShape {
    /// `M = span{x,1}`, `R = (x^2+1) P_<16`, total dimension 18.
    D18M2,
    /// `M = span{x,1,x^18}`, `R = (x^2+1) P_<16`, total dimension 19.
    D19M3,
    /// Ideal physically bound high-carry View: X/F are degree-`<19`
    /// natural-coefficient words and only `coeff_18(X)` enters root-zero row
    /// 72. This rank mode assumes a source-PCS coefficient-functional proof;
    /// q openings plus the coefficient lemma alone are not such a proof.
    D19Coefficient18,
    /// Lean-only maximal source `X in P_<255`. For an affine multiplier,
    /// `pX in P_<256` occupies root-zero slots through row 1020 while the
    /// verifier wire remains only raw q openings plus one target scalar.
    D255Natural,
    /// Lean-only maximal unmultiplied source `X in P_<256`. This is the
    /// cheapest maximal-kernel control: no affine multiplication is needed.
    D256Natural,
}

/// Public multiplier for a physically committed `p(t)X` root-zero lane.
/// Coefficients are ordinary-monomial coefficients in low-to-high order and
/// deliberately remain in QM31: projecting them to M31 would erase the tower
/// mixing which extension-affine candidates are intended to test.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompactRoot0Multiplier {
    pub ordinary_coefficients: Vec<QM31>,
}

impl CompactRoot0Multiplier {
    pub fn identity() -> Self {
        Self {
            ordinary_coefficients: vec![QM31::ONE],
        }
    }

    /// `p(t)=t-zeta`, where `zeta` is fixed before the challenge that samples
    /// the main PCS batching scalar.
    pub fn fixed_affine(zeta: QM31) -> Self {
        Self {
            ordinary_coefficients: vec![zeta.neg(), QM31::ONE],
        }
    }

    pub fn monomial(degree: usize) -> Self {
        let mut ordinary_coefficients = vec![QM31::ZERO; degree + 1];
        ordinary_coefficients[degree] = QM31::ONE;
        Self {
            ordinary_coefficients,
        }
    }

    pub fn x2_plus_one_power(power: usize) -> Self {
        let mut coefficients = vec![QM31::ONE];
        for _ in 0..power {
            let mut next = vec![QM31::ZERO; coefficients.len() + 2];
            for (degree, coefficient) in coefficients.into_iter().enumerate() {
                next[degree] = next[degree].add(coefficient);
                next[degree + 2] = next[degree + 2].add(coefficient);
            }
            coefficients = next;
        }
        Self {
            ordinary_coefficients: coefficients,
        }
    }

    fn degree(&self) -> Result<usize, StateOnlyHidingRankGateError> {
        let degree = self
            .ordinary_coefficients
            .iter()
            .rposition(|coefficient| *coefficient != QM31::ZERO)
            .ok_or(StateOnlyHidingRankGateError::Shape)?;
        if degree > 16 || degree + 1 != self.ordinary_coefficients.len() {
            return Err(StateOnlyHidingRankGateError::Shape);
        }
        Ok(degree)
    }
}

impl CompactBoundRoot0SwitchShape {
    fn message_degrees(self) -> &'static [usize] {
        match self {
            Self::D18M2 => &[1, 0],
            Self::D19M3 => &[1, 0, 18],
            Self::D19Coefficient18 => &[],
            Self::D255Natural => &[],
            Self::D256Natural => &[],
        }
    }
}

fn compact_initial_weights(
    schedule: &StateOnlyTranscriptScheduleResult,
    tau: QM31,
) -> Result<WeightAccumulator, StateOnlyHidingRankGateError> {
    let points = [
        schedule.prefix.z,
        binary_successor_point(&schedule.prefix.z),
        xor12_point(&schedule.prefix.z),
    ];
    let kappa = schedule.prefix.point_scale;
    let mut weights = WeightAccumulator::empty(STATE_ONLY_LOG_ROWS);
    for (point, scale) in points.into_iter().zip([tau, kappa, kappa.square()]) {
        weights
            .add_multilinear(scale, point.to_vec())
            .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
    }
    weights
        .add_grouped_64x16_binary_masks(rank_inactive_masks(RankLayout::AtomicV3))
        .map_err(|_| StateOnlyHidingRankGateError::Relation)?;
    Ok(weights)
}

fn compact_row_pcs_tail_sparse(
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
    let mut coefficients = vec![QM31::ZERO; TRACE_ROWS];
    coefficients[row] = QM31::ONE;
    if let Some(dependent) = dependent {
        coefficients[dependent] = QM31::ZERO.sub(QM31::ONE);
    }
    let mut weights = compact_initial_weights(schedule, tau)?;
    let mut running_claim = weights.dot(&coefficients);
    let mut later = Vec::new();
    let mut ood_values = [[QM31::ZERO; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT];
    let mut polynomials = [[QM31::ZERO; 7]; CANDIDATE_ROUND_COUNT];
    let mut memo = BTreeMap::new();

    for round in 0..CANDIDATE_ROUND_COUNT {
        for sample in 0..CANDIDATE_OOD_SAMPLES {
            let mut evaluation =
                WeightAccumulator::empty(STATE_ONLY_LOG_ROWS.saturating_sub(2 * round as u32));
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
    if coefficients.len() != 4 {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let mut tail = later;
    for values in ood_values {
        tail.extend_from_slice(&values);
    }
    for polynomial in polynomials {
        tail.extend_from_slice(&polynomial);
    }
    tail.extend_from_slice(&coefficients);
    Ok(tail)
}

fn compact_row_public_maps(
    encoder: &CircleEncoder,
    domain_log: u32,
    schedule: &StateOnlyTranscriptScheduleResult,
    tau: QM31,
) -> Result<Vec<RowPublicMaps>, StateOnlyHidingRankGateError> {
    let indices = derive_circle_line_query_indices_for_count(
        &schedule.queries[..schedule.query_count],
        encoder.codeword_len() / FIBER_SLOTS,
    )
    .map_err(|_| StateOnlyHidingRankGateError::Shape)?;
    let points = [
        schedule.prefix.z,
        binary_successor_point(&schedule.prefix.z),
        xor12_point(&schedule.prefix.z),
    ];
    let mut active = [false; TRACE_ROWS];
    for &row in rank_active_rows(RankLayout::AtomicV3) {
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
            terminal: core::array::from_fn(|point| eq_weight(&points[point], row)),
            pcs_tail: compact_row_pcs_tail_sparse(
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

#[derive(Clone, Copy)]
struct CompactRawLayout {
    layer0_m31: usize,
    mask_block_m31: usize,
    g_block_m31: usize,
    h_block_m31: usize,
    g_start: usize,
    h_start: usize,
    pad_start: usize,
    pad_block_m31: usize,
    aggregate_start: usize,
    total_m31: usize,
}

impl CompactRawLayout {
    fn new(layer0_m31: usize, include_pad: bool) -> Self {
        let mask_block_m31 = layer0_m31 + 4;
        let g_block_m31 = 4 * (layer0_m31 + 1);
        let h_block_m31 = g_block_m31;
        let g_start = MASK_ONLY_COLUMNS * mask_block_m31;
        let h_start = g_start + g_block_m31;
        let pad_start = h_start + h_block_m31;
        let pad_block_m31 = usize::from(include_pad) * 4 * (layer0_m31 + 1);
        let aggregate_start = pad_start + pad_block_m31;
        Self {
            layer0_m31,
            mask_block_m31,
            g_block_m31,
            h_block_m31,
            g_start,
            h_start,
            pad_start,
            pad_block_m31,
            aggregate_start,
            total_m31: aggregate_start + 4,
        }
    }
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

fn compact_mask_raw(
    rows: &[RowPublicMaps],
    row: usize,
    dependent: Option<usize>,
    mask_column: usize,
    gamma_scale: QM31,
    kappa: QM31,
    layout: CompactRawLayout,
) -> Vec<M31> {
    let mut raw = vec![M31::ZERO; layout.total_m31];
    let start = mask_column * layout.mask_block_m31;
    for (index, &value) in rows[row].layer0_m31.iter().enumerate() {
        raw[start + index] = dependent.map_or(value, |dependent| {
            value.sub(rows[dependent].layer0_m31[index])
        });
    }
    let z = qm31_coordinates(terminal_difference(rows, row, dependent, 0));
    raw[start + layout.layer0_m31..start + layout.mask_block_m31].copy_from_slice(&z);
    let tail = kappa.mul(terminal_difference(rows, row, dependent, 1)).add(
        kappa
            .square()
            .mul(terminal_difference(rows, row, dependent, 2)),
    );
    raw[layout.aggregate_start..].copy_from_slice(&qm31_coordinates(gamma_scale.mul(tail)));
    raw
}

fn compact_qm31_raw(
    rows: &[RowPublicMaps],
    row: usize,
    dependent: Option<usize>,
    basis: QM31,
    gamma_scale: QM31,
    kappa: QM31,
    start: usize,
    layout: CompactRawLayout,
) -> Vec<M31> {
    let mut raw = vec![M31::ZERO; layout.total_m31];
    for (index, &value) in rows[row].layer0_m31.iter().enumerate() {
        let value = dependent.map_or(value, |dependent| {
            value.sub(rows[dependent].layer0_m31[index])
        });
        let coordinates = qm31_coordinates(basis.mul_m31(value));
        raw[start + 4 * index..start + 4 * index + 4].copy_from_slice(&coordinates);
    }
    let z = basis.mul(terminal_difference(rows, row, dependent, 0));
    let z_start = start + 4 * layout.layer0_m31;
    raw[z_start..z_start + 4].copy_from_slice(&qm31_coordinates(z));
    let tail = kappa.mul(terminal_difference(rows, row, dependent, 1)).add(
        kappa
            .square()
            .mul(terminal_difference(rows, row, dependent, 2)),
    );
    raw[layout.aggregate_start..]
        .copy_from_slice(&qm31_coordinates(gamma_scale.mul(basis).mul(tail)));
    raw
}

fn compact_pad_raw(
    rows: &[RowPublicMaps],
    row: usize,
    dependent: Option<usize>,
    basis: QM31,
    gamma_scale: QM31,
    kappa: QM31,
    layout: CompactRawLayout,
) -> Vec<M31> {
    debug_assert_eq!(layout.pad_block_m31, 4 * (layout.layer0_m31 + 1));
    let mut raw = vec![M31::ZERO; layout.total_m31];
    for (index, &value) in rows[row].layer0_m31.iter().enumerate() {
        let value = dependent.map_or(value, |dependent| {
            value.sub(rows[dependent].layer0_m31[index])
        });
        let start = layout.pad_start + 4 * index;
        raw[start..start + 4].copy_from_slice(&qm31_coordinates(basis.mul_m31(value)));
    }
    let z = basis.mul(terminal_difference(rows, row, dependent, 0));
    let z_start = layout.pad_start + 4 * layout.layer0_m31;
    raw[z_start..z_start + 4].copy_from_slice(&qm31_coordinates(z));
    let tail = kappa.mul(terminal_difference(rows, row, dependent, 1)).add(
        kappa
            .square()
            .mul(terminal_difference(rows, row, dependent, 2)),
    );
    raw[layout.aggregate_start..]
        .copy_from_slice(&qm31_coordinates(gamma_scale.mul(basis).mul(tail)));
    raw
}

fn carry_image(
    rows: &[RowPublicMaps],
    row: usize,
    dependent: Option<usize>,
    observations: Option<&[Vec<QM31>]>,
    sumcheck_scale: QM31,
    pcs_scale: QM31,
    sc_m31: usize,
    pcs_m31: usize,
) -> Vec<M31> {
    let mut carry = vec![M31::ZERO; sc_m31 + pcs_m31];
    if let Some(observations) = observations {
        let sc = scaled_qm31_difference(
            &observations[row],
            dependent.map(|dependent| observations[dependent].as_slice()),
            sumcheck_scale,
        );
        carry[..sc_m31].copy_from_slice(&sc);
    }
    let pcs = scaled_qm31_difference(
        &rows[row].pcs_tail,
        dependent.map(|dependent| rows[dependent].pcs_tail.as_slice()),
        pcs_scale,
    );
    carry[sc_m31..].copy_from_slice(&pcs);
    carry
}

#[derive(Clone)]
struct BoundRoot0SwitchResult {
    conditioned: ColumnEchelon,
    message_qm31: usize,
    randomness_qm31: usize,
    dimension_qm31: usize,
    variables_qm31: usize,
    epsilon_coordinates_m31: [u32; 4],
    code_basis_rank_qm31: usize,
    code_basis_fingerprint: u64,
    lean_x_only_mode: bool,
    multiplier_degree: usize,
    multiplier_fingerprint: u64,
    product_dimension_qm31: usize,
    product_max_root_slot: usize,
    product_basis_fingerprint: u64,
    pointwise_product_identity: bool,
    fold_product_identity: bool,
    folded_opening_rank_qm31: usize,
    raw_opening_rank_qm31: usize,
    raw_contains_folded_openings: bool,
    u_plus_folded_rank_qm31: usize,
    u_plus_folded_target_rank_qm31: usize,
    u_plus_raw_rank_qm31: usize,
    u_plus_raw_target_rank_qm31: usize,
    conditioned_kernel_qm31: usize,
    gamma_exponent: usize,
    new_pivots_m31: Vec<usize>,
    pivots_later_m31: usize,
    pivots_ood_m31: usize,
    pivots_relation_m31: usize,
    pivots_final_m31: usize,
    sparse_dense_tail_parity: bool,
    coefficient_functional_mode: bool,
    coefficient_index: usize,
    minor: RankMinorProvenance,
}

#[derive(Clone)]
struct CompactBoundRoot0SwitchRequest {
    shape: CompactBoundRoot0SwitchShape,
    epsilon: QM31,
    multiplier: CompactRoot0Multiplier,
    lean_x_only_mode: bool,
}

/// Complete unbalanced root-zero PCS image under the compact claim's literal
/// `[tau,kappa,kappa^2]` relation. This is deliberately separate from the
/// legacy `raw_root0_row_pcs_tail_sparse`, whose z coefficient is one.
fn compact_raw_root0_row_pcs_tail_sparse(
    encoder: &CircleEncoder,
    domain_log: u32,
    row: usize,
    schedule: &StateOnlyTranscriptScheduleResult,
    later_indices: &[Vec<u32>; CANDIDATE_ROUND_COUNT - 1],
    tau: QM31,
) -> Result<Vec<QM31>, StateOnlyHidingRankGateError> {
    if row >= TRACE_ROWS {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let mut coefficients = vec![QM31::ZERO; TRACE_ROWS];
    coefficients[row] = QM31::ONE;
    let mut weights = compact_initial_weights(schedule, tau)?;
    let mut later = Vec::new();
    let mut ood_values = [[QM31::ZERO; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT];
    let mut polynomials = [[QM31::ZERO; 7]; CANDIDATE_ROUND_COUNT];
    let mut memo = BTreeMap::new();

    for round in 0..CANDIDATE_ROUND_COUNT {
        for sample in 0..CANDIDATE_OOD_SAMPLES {
            let mut evaluation =
                WeightAccumulator::empty(STATE_ONLY_LOG_ROWS.saturating_sub(2 * round as u32));
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
            ood_values[round][sample] = evaluation.dot(&coefficients);
        }
        let polynomial = polynomial_for_extension(&coefficients, &weights);
        if boundary_sum(&polynomial) != weights.dot(&coefficients) {
            return Err(StateOnlyHidingRankGateError::Relation);
        }
        polynomials[round] = polynomial;
        weights.fold(schedule.alpha[round]);
        coefficients = fold_adjacent_natural_arity4(&coefficients, schedule.alpha[round]);
        if round + 1 < CANDIDATE_ROUND_COUNT {
            for &leaf in &later_indices[round] {
                for slot in 0..FIBER_SLOTS {
                    later.push(sparse_folded_row_value(
                        encoder,
                        domain_log,
                        row,
                        None,
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
    tail.extend_from_slice(&coefficients);
    Ok(tail)
}

/// Independent full-codeword reference for the compact unbalanced root-zero
/// row. It uses `StateOnlyIncrementalRelation` rather than the sparse row
/// evaluator and manual weight folding above.
fn compact_raw_root0_row_pcs_tail_dense(
    encoder: &CircleEncoder,
    domain_log: u32,
    row: usize,
    schedule: &StateOnlyTranscriptScheduleResult,
    later_indices: &[Vec<u32>; CANDIDATE_ROUND_COUNT - 1],
    tau: QM31,
) -> Result<Vec<QM31>, StateOnlyHidingRankGateError> {
    if row >= TRACE_ROWS {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let mut message = vec![QM31::ZERO; TRACE_ROWS];
    message[row] = QM31::ONE;
    let mut base = vec![M31::ZERO; TRACE_ROWS];
    base[row] = M31::ONE;
    let encoded = encoder.encode_c1_message(&base)?;
    let mut codeword = encoded
        .into_iter()
        .map(|value| QM31::from_cm31(CM31::from_m31(value)))
        .collect::<Vec<_>>();
    let points = [
        schedule.prefix.z,
        binary_successor_point(&schedule.prefix.z),
        xor12_point(&schedule.prefix.z),
    ];
    let kappa = schedule.prefix.point_scale;
    let inactive_masks = rank_inactive_masks(RankLayout::AtomicV3);
    let inactive_claim = if inactive_masks[row >> 4] & (1 << (row & 15)) == 0 {
        QM31::ZERO
    } else {
        QM31::ONE
    };
    let mut relation = StateOnlyIncrementalRelation::new_with_inactive_masks_and_claim(
        message,
        &points,
        [tau, kappa, kappa.square()],
        inactive_masks,
        inactive_claim,
    )?;
    let mut later = Vec::new();
    let mut polynomials = Vec::with_capacity(CANDIDATE_ROUND_COUNT);
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
        codeword = fold_candidate_codeword_round_for_domain_log(
            &codeword,
            schedule.alpha[round],
            round,
            domain_log,
        )?;
        if round + 1 < CANDIDATE_ROUND_COUNT {
            for &query in &later_indices[round] {
                let start = FIBER_SLOTS * query as usize;
                later.extend_from_slice(&codeword[start..start + FIBER_SLOTS]);
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

fn combine_natural_qm31_columns_with_qm31_coefficients(
    natural_columns: &[Vec<QM31>],
    coefficients: &[QM31],
) -> Result<Vec<QM31>, StateOnlyHidingRankGateError> {
    let rows = natural_columns
        .first()
        .map(Vec::len)
        .ok_or(StateOnlyHidingRankGateError::Shape)?;
    if coefficients.len() != natural_columns.len()
        || natural_columns.iter().any(|column| column.len() != rows)
    {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let mut combined = vec![QM31::ZERO; rows];
    for (column, &scale) in natural_columns.iter().zip(coefficients) {
        if scale == QM31::ZERO {
            continue;
        }
        for (output, &value) in combined.iter_mut().zip(column) {
            *output = output.add(value.mul(scale));
        }
    }
    Ok(combined)
}

fn qm31_matrix_fingerprint(block: &str, columns: &[Vec<QM31>]) -> u64 {
    let mut hash = 0xcbf2_9ce4_8422_2325u64;
    let mut absorb = |bytes: &[u8]| {
        for &byte in bytes {
            hash ^= u64::from(byte);
            hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
        }
    };
    absorb(b"aspis/profile21/qm31-matrix/v1");
    absorb(&(block.len() as u64).to_le_bytes());
    absorb(block.as_bytes());
    absorb(&(columns.len() as u64).to_le_bytes());
    for column in columns {
        absorb(&(column.len() as u64).to_le_bytes());
        for value in column {
            for coordinate in qm31_coordinates(*value) {
                absorb(&coordinate.0.to_le_bytes());
            }
        }
    }
    hash
}

fn multiply_natural_basis_by_qm31_ordinary_multiplier(
    code_basis: &[Vec<M31>],
    source_dimension: usize,
    multiplier: &CompactRoot0Multiplier,
) -> Result<Vec<Vec<QM31>>, StateOnlyHidingRankGateError> {
    let multiplier_degree = multiplier.degree()?;
    let product_dimension = source_dimension + multiplier_degree;
    if product_dimension > TRACE_ROWS / FIBER_SLOTS
        || code_basis
            .iter()
            .any(|column| column.len() != source_dimension)
    {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let natural_ordinary = natural_line_basis_polynomials(source_dimension);
    let monomial_to_natural = ordinary_monomials_in_natural_line_basis(product_dimension);
    code_basis
        .iter()
        .map(|source_natural| {
            let mut source_ordinary = vec![M31::ZERO; source_dimension];
            for (natural, &scale) in source_natural.iter().enumerate() {
                if scale == M31::ZERO {
                    continue;
                }
                for (degree, &coefficient) in natural_ordinary[natural].iter().enumerate() {
                    source_ordinary[degree] = source_ordinary[degree].add(scale.mul(coefficient));
                }
            }
            let mut product_ordinary = vec![QM31::ZERO; product_dimension];
            for (source_degree, &source_coefficient) in source_ordinary.iter().enumerate() {
                if source_coefficient == M31::ZERO {
                    continue;
                }
                for (multiplier_degree, &multiplier_coefficient) in
                    multiplier.ordinary_coefficients.iter().enumerate()
                {
                    product_ordinary[source_degree + multiplier_degree] = product_ordinary
                        [source_degree + multiplier_degree]
                        .add(multiplier_coefficient.mul_m31(source_coefficient));
                }
            }
            let mut product_natural = vec![QM31::ZERO; product_dimension];
            for (degree, coefficient) in product_ordinary.into_iter().enumerate() {
                if coefficient == QM31::ZERO {
                    continue;
                }
                for (output, &basis) in product_natural.iter_mut().zip(&monomial_to_natural[degree])
                {
                    *output = output.add(coefficient.mul_m31(basis));
                }
            }
            Ok(product_natural)
        })
        .collect()
}

fn evaluate_qm31_ordinary_polynomial(coefficients: &[QM31], point: M31) -> QM31 {
    coefficients
        .iter()
        .rev()
        .copied()
        .fold(QM31::ZERO, |value, coefficient| {
            value.mul_m31(point).add(coefficient)
        })
}

fn apply_compact_bound_root0_switch(
    encoder: &CircleEncoder,
    domain_log: u32,
    schedule: &StateOnlyTranscriptScheduleResult,
    tau: QM31,
    epsilon: QM31,
    shape: CompactBoundRoot0SwitchShape,
    multiplier: &CompactRoot0Multiplier,
    lean_x_only_mode: bool,
    baseline: &ColumnEchelon,
    pcs_tail_qm31: usize,
) -> Result<BoundRoot0SwitchResult, StateOnlyHidingRankGateError> {
    let coefficient_functional_mode = shape == CompactBoundRoot0SwitchShape::D19Coefficient18;
    let maximal_natural_mode = shape == CompactBoundRoot0SwitchShape::D255Natural;
    let maximal_identity_natural_mode = shape == CompactBoundRoot0SwitchShape::D256Natural;
    let multiplier_degree = multiplier.degree()?;
    if coefficient_functional_mode && multiplier_degree != 0 {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let coefficient_index = usize::from(coefficient_functional_mode) * 18;
    let message_degrees = shape.message_degrees();
    let (message, randomness, dimension) = if maximal_identity_natural_mode {
        (256, 0, 256)
    } else if maximal_natural_mode {
        (255, 0, 255)
    } else if coefficient_functional_mode {
        (19, 0, 19)
    } else {
        (message_degrees.len(), 16, message_degrees.len() + 16)
    };
    let variables = if lean_x_only_mode {
        dimension
    } else {
        2 * dimension
    };
    if (dimension != 18 && dimension != 19 && dimension != 255 && dimension != 256)
        || ((maximal_natural_mode || maximal_identity_natural_mode) && !lean_x_only_mode)
        || (maximal_identity_natural_mode && multiplier_degree != 0)
    {
        return Err(StateOnlyHidingRankGateError::Shape);
    }

    // Full-X modes use M={x,1[,x^18]} and R=(x^2+1)P_<16. The
    // coefficient-functional mode instead uses the literal natural basis of
    // P_<19, so logical coordinate 18 is exactly the row-72 carry scalar.
    let conversion = ordinary_monomials_in_natural_line_basis(dimension);
    let code_basis =
        if coefficient_functional_mode || maximal_natural_mode || maximal_identity_natural_mode {
            (0..dimension)
                .map(|coordinate| {
                    let mut column = vec![M31::ZERO; dimension];
                    column[coordinate] = M31::ONE;
                    column
                })
                .collect::<Vec<_>>()
        } else {
            let mut basis = message_degrees
                .iter()
                .map(|&degree| conversion[degree].clone())
                .collect::<Vec<_>>();
            for degree in 0..randomness {
                basis.push(
                    conversion[degree]
                        .iter()
                        .copied()
                        .zip(conversion[degree + 2].iter().copied())
                        .map(|(low, high)| low.add(high))
                        .collect(),
                );
            }
            basis
        };
    let mut code_basis_rank = ColumnEchelon::new(dimension);
    for column in &code_basis {
        code_basis_rank.insert(column.clone());
    }
    if code_basis.len() != dimension || code_basis_rank.rank != dimension {
        return Err(StateOnlyHidingRankGateError::Layout);
    }
    let code_basis_fingerprint = m31_matrix_fingerprint(
        match shape {
            CompactBoundRoot0SwitchShape::D18M2 => "compact_root0_d18_x_1_x2p1_p16",
            CompactBoundRoot0SwitchShape::D19M3 => "compact_root0_d19_x_1_x18_x2p1_p16",
            CompactBoundRoot0SwitchShape::D19Coefficient18 => {
                "compact_root0_d19_natural_coefficient18"
            }
            CompactBoundRoot0SwitchShape::D255Natural => "compact_root0_d255_natural",
            CompactBoundRoot0SwitchShape::D256Natural => "compact_root0_d256_natural",
        },
        &code_basis,
    );
    let product_dimension = dimension + multiplier_degree;
    let product_max_root_slot = FIBER_SLOTS * (product_dimension - 1);
    if product_max_root_slot >= TRACE_ROWS {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let product_basis =
        multiply_natural_basis_by_qm31_ordinary_multiplier(&code_basis, dimension, multiplier)?;
    let multiplier_fingerprint = qm31_matrix_fingerprint(
        "compact_root0_ordinary_multiplier",
        std::slice::from_ref(&multiplier.ordinary_coefficients),
    );
    let product_basis_fingerprint =
        qm31_matrix_fingerprint("compact_root0_product_natural_basis", &product_basis);

    let queries = &schedule.queries[..schedule.query_count];
    let natural_folded = (0..dimension)
        .map(|coefficient| {
            first_later_coefficient_query_values(
                encoder,
                domain_log,
                coefficient,
                schedule,
                queries,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    let folded = code_basis
        .iter()
        .map(|coefficients| combine_natural_qm31_columns(&natural_folded, coefficients))
        .collect::<Result<Vec<_>, _>>()?;
    let natural_raw = (0..dimension)
        .map(|coefficient| first_layer0_coefficient_query_fibers(encoder, coefficient, queries))
        .collect::<Result<Vec<_>, _>>()?;
    let raw = code_basis
        .iter()
        .map(|coefficients| combine_natural_qm31_columns(&natural_raw, coefficients))
        .collect::<Result<Vec<_>, _>>()?;
    let product_natural_folded = (0..product_dimension)
        .map(|coefficient| {
            first_later_coefficient_query_values(
                encoder,
                domain_log,
                coefficient,
                schedule,
                queries,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    let product_folded = product_basis
        .iter()
        .map(|coefficients| {
            combine_natural_qm31_columns_with_qm31_coefficients(
                &product_natural_folded,
                coefficients,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    let product_natural_raw = (0..product_dimension)
        .map(|coefficient| first_layer0_coefficient_query_fibers(encoder, coefficient, queries))
        .collect::<Result<Vec<_>, _>>()?;
    let product_raw = product_basis
        .iter()
        .map(|coefficients| {
            combine_natural_qm31_columns_with_qm31_coefficients(&product_natural_raw, coefficients)
        })
        .collect::<Result<Vec<_>, _>>()?;

    // Differentially pin the raw four-symbol C2 view to the normalized
    // post-alpha scalar shorthand.  The raw view remains the decisive one.
    for logical in 0..dimension {
        for (query_ordinal, &query) in queries.iter().enumerate() {
            let start = FIBER_SLOTS * query_ordinal;
            let fiber: [QM31; FIBER_SLOTS] = raw[logical][start..start + FIBER_SLOTS]
                .try_into()
                .map_err(|_| StateOnlyHidingRankGateError::Shape)?;
            let folded_raw =
                aspis_core::circle_fri::normalized_circle_to_line_arity4_at_fiber_for_domain_log(
                    fiber,
                    schedule.alpha[0],
                    domain_log,
                    query as usize,
                )
                .map_err(|_| StateOnlyHidingRankGateError::Encoding)?;
            if folded_raw != folded[logical][query_ordinal] {
                return Err(StateOnlyHidingRankGateError::Layout);
            }
            let product_fiber: [QM31; FIBER_SLOTS] = product_raw[logical]
                [start..start + FIBER_SLOTS]
                .try_into()
                .map_err(|_| StateOnlyHidingRankGateError::Shape)?;
            let x = line_domain_x_for_circle(domain_log, 1, query as usize)
                .map_err(|_| StateOnlyHidingRankGateError::Encoding)?;
            let point_multiplier =
                evaluate_qm31_ordinary_polynomial(&multiplier.ordinary_coefficients, x);
            // Multiplication must be a Hamming isometry on the full physical
            // query surface. Extension-affine fixed roots satisfy this
            // unconditionally because every x is in M31.
            if point_multiplier == QM31::ZERO {
                return Err(StateOnlyHidingRankGateError::Layout);
            }
            for slot in 0..FIBER_SLOTS {
                if product_fiber[slot] != point_multiplier.mul(fiber[slot]) {
                    return Err(StateOnlyHidingRankGateError::Layout);
                }
            }
            let folded_product_raw =
                aspis_core::circle_fri::normalized_circle_to_line_arity4_at_fiber_for_domain_log(
                    product_fiber,
                    schedule.alpha[0],
                    domain_log,
                    query as usize,
                )
                .map_err(|_| StateOnlyHidingRankGateError::Encoding)?;
            if folded_product_raw != product_folded[logical][query_ordinal]
                || product_folded[logical][query_ordinal]
                    != point_multiplier.mul(folded[logical][query_ordinal])
            {
                return Err(StateOnlyHidingRankGateError::Layout);
            }
        }
    }
    let folded_opening_rank_qm31 = qm31_column_rank(&folded, schedule.query_count);
    let raw_rows = FIBER_SLOTS * schedule.query_count;
    let raw_opening_rank_qm31 = qm31_column_rank(&raw, raw_rows);
    let raw_plus_folded = raw
        .iter()
        .zip(&folded)
        .map(|(raw, folded)| {
            let mut union = raw.clone();
            union.extend_from_slice(folded);
            union
        })
        .collect::<Vec<_>>();
    let raw_contains_folded_openings =
        qm31_column_rank(&raw_plus_folded, raw_rows + schedule.query_count)
            == raw_opening_rank_qm31;
    if !raw_contains_folded_openings {
        return Err(StateOnlyHidingRankGateError::Layout);
    }

    // The exact root-zero relation covector for X. F is source-only. This
    // target is already fixed when X enters the main gamma lane and is
    // therefore a conditioning row, not a free cancellation scalar.
    let relation_weights = compact_initial_weights(schedule, tau)?;
    let x_target = product_basis
        .iter()
        .map(|column| {
            column
                .iter()
                .copied()
                .enumerate()
                .filter(|(_, coefficient)| *coefficient != QM31::ZERO)
                .fold(QM31::ZERO, |sum, (natural, coefficient)| {
                    sum.add(
                        relation_weights
                            .weight_at((FIBER_SLOTS * natural) as u32)
                            .mul(coefficient),
                    )
                })
        })
        .collect::<Vec<_>>();

    if epsilon == QM31::ZERO {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let build_full_source_view = |openings: &[Vec<QM31>], include_target: bool| {
        let opening_rows = openings[0].len();
        (0..2 * dimension)
            .map(|variable| {
                let fresh = variable >= dimension;
                let coordinate = variable % dimension;
                let mut column =
                    vec![QM31::ZERO; dimension + 2 * opening_rows + usize::from(include_target)];
                let u_scale = if fresh { QM31::ONE } else { epsilon };
                for (natural, &coefficient) in code_basis[coordinate].iter().enumerate() {
                    column[natural] = u_scale.mul_m31(coefficient);
                }
                let opening_start = dimension + usize::from(fresh) * opening_rows;
                column[opening_start..opening_start + opening_rows]
                    .copy_from_slice(&openings[coordinate]);
                if include_target && !fresh {
                    *column.last_mut().expect("target row") = x_target[coordinate];
                }
                column
            })
            .collect::<Vec<_>>()
    };
    let build_lean_x_view = |openings: &[Vec<QM31>], include_target: bool| {
        let opening_rows = openings[0].len();
        (0..dimension)
            .map(|coordinate| {
                let mut column = Vec::with_capacity(opening_rows + usize::from(include_target));
                column.extend_from_slice(&openings[coordinate]);
                if include_target {
                    column.push(x_target[coordinate]);
                }
                column
            })
            .collect::<Vec<_>>()
    };
    let include_target = !coefficient_functional_mode;
    let (folded_view, folded_target_view, raw_view, raw_target_view) = if lean_x_only_mode {
        (
            build_lean_x_view(&folded, false),
            build_lean_x_view(&folded, include_target),
            build_lean_x_view(&raw, false),
            build_lean_x_view(&raw, include_target),
        )
    } else {
        (
            build_full_source_view(&folded, false),
            build_full_source_view(&folded, include_target),
            build_full_source_view(&raw, false),
            build_full_source_view(&raw, include_target),
        )
    };
    let folded_view_rows = if lean_x_only_mode {
        schedule.query_count
    } else {
        dimension + 2 * schedule.query_count
    };
    let raw_view_rows = if lean_x_only_mode {
        raw_rows
    } else {
        dimension + 2 * raw_rows
    };
    let u_plus_folded_rank_qm31 = qm31_column_rank(&folded_view, folded_view_rows);
    let u_plus_folded_target_rank_qm31 = qm31_column_rank(
        &folded_target_view,
        folded_view_rows + usize::from(include_target),
    );
    let u_plus_raw_rank_qm31 = qm31_column_rank(&raw_view, raw_view_rows);
    let raw_target_rows = raw_view_rows + usize::from(include_target);
    let u_plus_raw_target_rank_qm31 = qm31_column_rank(&raw_target_view, raw_target_rows);
    let conditioned_kernel_qm31 = variables.saturating_sub(u_plus_raw_target_rank_qm31);

    let indices =
        derive_circle_line_query_indices_for_count(queries, encoder.codeword_len() / FIBER_SLOTS)
            .map_err(|_| StateOnlyHidingRankGateError::Shape)?;
    let natural_tails = (0..product_dimension)
        .map(|natural| {
            let sparse = compact_raw_root0_row_pcs_tail_sparse(
                encoder,
                domain_log,
                FIBER_SLOTS * natural,
                schedule,
                &indices.later,
                tau,
            )?;
            let dense = compact_raw_root0_row_pcs_tail_dense(
                encoder,
                domain_log,
                FIBER_SLOTS * natural,
                schedule,
                &indices.later,
                tau,
            )?;
            if sparse != dense {
                return Err(StateOnlyHidingRankGateError::Encoding);
            }
            Ok(sparse)
        })
        .collect::<Result<Vec<_>, StateOnlyHidingRankGateError>>()?;
    if natural_tails.iter().any(|tail| tail.len() != pcs_tail_qm31) {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let code_tails = if coefficient_functional_mode {
        (0..dimension)
            .map(|logical| {
                if logical == coefficient_index {
                    natural_tails[coefficient_index].clone()
                } else {
                    vec![QM31::ZERO; pcs_tail_qm31]
                }
            })
            .collect::<Vec<_>>()
    } else {
        product_basis
            .iter()
            .map(|coefficients| {
                combine_natural_qm31_columns_with_qm31_coefficients(&natural_tails, coefficients)
            })
            .collect::<Result<Vec<_>, _>>()?
    };
    let gamma_exponent = if lean_x_only_mode {
        0
    } else {
        SEMANTIC_COLUMNS + MASK_ONLY_COLUMNS + 2
    };
    // In lean mode pX is an outer third PCS group, so its literal coefficient
    // is epsilon. The legacy full X/F/U source diagnostic retains its old
    // placement as gamma lane 28 and its U=F+epsilon X disclosure.
    let gamma_scale = if lean_x_only_mode {
        epsilon
    } else {
        epsilon.mul(gamma_power(schedule.prefix.gamma, gamma_exponent))
    };

    let mut quotient = CarryEchelon::new(4 * raw_target_rows);
    let mut conditioned = baseline.clone();
    let mut minor_sources = Vec::new();
    let mut minor_rows = Vec::new();
    let mut minor_values = Vec::new();
    let mut new_pivots_m31 = Vec::new();
    let mut pivots_later_m31 = 0usize;
    let mut pivots_ood_m31 = 0usize;
    let mut pivots_relation_m31 = 0usize;
    let mut pivots_final_m31 = 0usize;
    for variable in 0..variables {
        for tower_coordinate in 0..4 {
            let basis = state_only_mask_tower_basis(tower_coordinate);
            let mut observation = Vec::with_capacity(4 * raw_target_rows);
            append_qm31_coordinates(
                &mut observation,
                raw_target_view[variable]
                    .iter()
                    .copied()
                    .map(|value| value.mul(basis)),
            );
            let carry = if variable < dimension {
                scaled_qm31_difference(&code_tails[variable], None, gamma_scale.mul(basis))
            } else {
                vec![M31::ZERO; 4 * pcs_tail_qm31]
            };
            let source = 4 * variable + tower_coordinate;
            match quotient.reduce_with_pivot(observation, carry) {
                CarryReduction::Pivot { .. } => {}
                CarryReduction::Kernel(carry) => {
                    if let Some((pivot, value)) = conditioned.insert_with_pivot_value(carry) {
                        minor_sources.push(source);
                        minor_rows.push(pivot);
                        minor_values.push(value);
                        new_pivots_m31.push(pivot);
                        let later_m31 = 4 * (pcs_tail_qm31 - 40);
                        if pivot < later_m31 {
                            pivots_later_m31 += 1;
                        } else if pivot < later_m31 + 4 * 8 {
                            pivots_ood_m31 += 1;
                        } else if pivot < later_m31 + 4 * (8 + 28) {
                            pivots_relation_m31 += 1;
                        } else {
                            pivots_final_m31 += 1;
                        }
                    }
                }
            }
        }
    }
    if quotient.rank != 4 * u_plus_raw_target_rank_qm31 {
        return Err(StateOnlyHidingRankGateError::Layout);
    }
    let minor = RankMinorProvenance::from_parts(
        match (shape, lean_x_only_mode, multiplier_degree) {
            (CompactBoundRoot0SwitchShape::D18M2, _, _) => "compact_bound_root0_d18_switch",
            (CompactBoundRoot0SwitchShape::D19M3, true, 1) => {
                "compact_bound_root0_d19_affine_lean_x_only"
            }
            (CompactBoundRoot0SwitchShape::D19M3, false, 1) => {
                "compact_bound_root0_d19_affine_full_source"
            }
            (CompactBoundRoot0SwitchShape::D19M3, _, _) => "compact_bound_root0_d19_switch",
            (CompactBoundRoot0SwitchShape::D19Coefficient18, _, _) => {
                "compact_bound_root0_d19_coefficient18"
            }
            (CompactBoundRoot0SwitchShape::D255Natural, true, 1) => {
                "compact_bound_root0_d255_affine_lean_x_only"
            }
            (CompactBoundRoot0SwitchShape::D255Natural, _, _) => {
                "compact_bound_root0_d255_lean_x_only"
            }
            (CompactBoundRoot0SwitchShape::D256Natural, true, 0) => {
                "compact_bound_root0_d256_identity_lean_x_only"
            }
            (CompactBoundRoot0SwitchShape::D256Natural, _, _) => {
                "compact_bound_root0_d256_lean_x_only"
            }
        },
        minor_sources,
        minor_rows,
        minor_values,
    );

    Ok(BoundRoot0SwitchResult {
        conditioned,
        message_qm31: message,
        randomness_qm31: randomness,
        dimension_qm31: dimension,
        variables_qm31: variables,
        epsilon_coordinates_m31: qm31_coordinates(epsilon).map(|coordinate| coordinate.0),
        code_basis_rank_qm31: code_basis_rank.rank,
        code_basis_fingerprint,
        lean_x_only_mode,
        multiplier_degree,
        multiplier_fingerprint,
        product_dimension_qm31: product_dimension,
        product_max_root_slot,
        product_basis_fingerprint,
        pointwise_product_identity: true,
        fold_product_identity: true,
        folded_opening_rank_qm31,
        raw_opening_rank_qm31,
        raw_contains_folded_openings,
        u_plus_folded_rank_qm31,
        u_plus_folded_target_rank_qm31,
        u_plus_raw_rank_qm31,
        u_plus_raw_target_rank_qm31,
        conditioned_kernel_qm31,
        gamma_exponent,
        new_pivots_m31,
        pivots_later_m31,
        pivots_ood_m31,
        pivots_relation_m31,
        pivots_final_m31,
        sparse_dense_tail_parity: true,
        coefficient_functional_mode,
        coefficient_index,
        minor,
    })
}

/// Exact complete-view rank of the compact-claim construction at one actual
/// base transcript schedule and supplied post-aggregate separators
/// `(tau, delta)`. This function does not authorize a wire change.
fn run_atomic_state_only_compact_claim_rank(
    schedule: &StateOnlyTranscriptScheduleResult,
    tau: QM31,
    delta: QM31,
    include_pad: bool,
    pad_constant_one_sumcheck_factor: bool,
    bound_root0_switch: Option<CompactBoundRoot0SwitchRequest>,
) -> Result<AtomicProfile21CompactClaimRankReport, StateOnlyHidingRankGateError> {
    let started = Instant::now();
    if schedule.query_count != 16
        || schedule.prefix.z.len() != STATE_ONLY_HIDING_SUMCHECK_ROUNDS
        || tau == QM31::ZERO
        || delta == QM31::ZERO
    {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let domain_log = STATE_ONLY_LOG_ROWS + 9;
    let encoder = CircleEncoder::new_for_domain_log(domain_log);
    let rows = compact_row_public_maps(&encoder, domain_log, schedule, tau)?;
    let layer0_m31 = rows[0].layer0_m31.len();
    let c1_raw_m31 = layer0_m31 + 12;
    let raw_layout = CompactRawLayout::new(layer0_m31, include_pad);
    if raw_layout.g_block_m31 != raw_layout.h_block_m31 {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let pcs_tail_qm31 = rows[0].pcs_tail.len();
    let pcs_m31 = 4 * pcs_tail_qm31;
    let sc_m31 = 4 * STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS;
    let lagrange = lagrange_basis();
    let active_rows = rank_active_rows(RankLayout::AtomicV3);
    let mut active = [false; TRACE_ROWS];
    for &row in active_rows {
        active[usize::from(row)] = true;
    }
    let inactive = (0..TRACE_ROWS)
        .filter(|row| !active[*row])
        .collect::<Vec<_>>();
    let global_dependent = inactive[0];
    let h_generator_index = SEMANTIC_COLUMNS + MASK_ONLY_COLUMNS;
    let g_generator_index = h_generator_index + 1;
    let pad_generator_index = g_generator_index + 1;
    let powers = (0..=g_generator_index + usize::from(include_pad))
        .map(|column| gamma_power(schedule.prefix.gamma, column))
        .collect::<Vec<_>>();
    let semantic_scale = delta;
    let kappa = schedule.prefix.point_scale;

    let mut kernel_images = Vec::new();
    let mut semantic_raw_echelons = Vec::with_capacity(SEMANTIC_COLUMNS);
    let cells = atomic_state_only_relation_free_mask_cells_v3()
        .map_err(|_| StateOnlyHidingRankGateError::Layout)?;
    let mut cells_by_column = vec![Vec::new(); SEMANTIC_COLUMNS];
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
            let carry = carry_image(
                &rows,
                row,
                subtract,
                Some(&observations),
                QM31::ONE,
                semantic_scale.mul(powers[column]),
                sc_m31,
                pcs_m31,
            );
            if let Some(kernel) = raw.reduce(c1_raw_difference(&rows, row, subtract), carry) {
                kernel_images.push(kernel);
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

    // All U sources share the four M31 coordinates of A_tail, so this must be
    // one raw quotient. Per-column raw echelons would silently model twelve
    // separate aggregates and overstate privacy.
    let mut unused_raw = CarryEchelon::new(raw_layout.total_m31);
    let mut unused_source_count = 0usize;
    for mask_column in 0..MASK_ONLY_COLUMNS {
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
        let generator = SEMANTIC_COLUMNS + mask_column;
        for row in 0..TRACE_ROWS {
            if row == global_dependent {
                continue;
            }
            let subtract = (!active[row]).then_some(global_dependent);
            let raw = compact_mask_raw(
                &rows,
                row,
                subtract,
                mask_column,
                powers[generator],
                kappa,
                raw_layout,
            );
            let carry = carry_image(
                &rows,
                row,
                subtract,
                Some(&observations),
                QM31::ONE,
                powers[generator],
                sc_m31,
                pcs_m31,
            );
            unused_source_count += 1;
            if let Some(kernel) = unused_raw.reduce(raw, carry) {
                kernel_images.push(kernel);
            }
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
            let raw = compact_qm31_raw(
                &rows,
                row,
                subtract,
                basis,
                powers[g_generator_index],
                kappa,
                raw_layout.g_start,
                raw_layout,
            );
            let carry = carry_image(
                &rows,
                row,
                subtract,
                Some(&g_observations),
                basis,
                powers[g_generator_index].mul(basis),
                sc_m31,
                pcs_m31,
            );
            unused_source_count += 1;
            if let Some(kernel) = unused_raw.reduce(raw, carry) {
                kernel_images.push(kernel);
            }
        }
    }

    let h_scale = powers[h_generator_index];
    for coordinate in 0..4 {
        let basis = state_only_mask_tower_basis(coordinate);
        for &row in &inactive {
            if row == global_dependent {
                continue;
            }
            let raw = compact_qm31_raw(
                &rows,
                row,
                Some(global_dependent),
                basis,
                h_scale,
                kappa,
                raw_layout.h_start,
                raw_layout,
            );
            let carry = carry_image(
                &rows,
                row,
                Some(global_dependent),
                None,
                QM31::ZERO,
                h_scale.mul(basis),
                sc_m31,
                pcs_m31,
            );
            unused_source_count += 1;
            if let Some(kernel) = unused_raw.reduce(raw, carry) {
                kernel_images.push(kernel);
            }
        }
    }
    let mut pad_source_basis_m31 = 0usize;
    let mut pad_joint_raw_kernel_m31 = 0usize;
    if include_pad {
        // Semantic(0) under FullSharedLinear is exactly the constant-one
        // factor.  The pad therefore participates in the literal masked
        // sumcheck while preserving the degree-27 wire shape.
        let pad_observations = pad_constant_one_sumcheck_factor.then(|| {
            (0..TRACE_ROWS)
                .map(|row| {
                    mask_sumcheck_observations(
                        row,
                        &schedule.prefix.z,
                        &lagrange,
                        MaskFactor::Semantic(0),
                        FactorSchedule::FullSharedLinear,
                        None,
                    )
                })
                .collect::<Vec<_>>()
        });
        let pad_scale = powers[pad_generator_index];
        for coordinate in 0..4 {
            let basis = state_only_mask_tower_basis(coordinate);
            for row in 0..TRACE_ROWS {
                if row == global_dependent {
                    continue;
                }
                let subtract = (!active[row]).then_some(global_dependent);
                let raw =
                    compact_pad_raw(&rows, row, subtract, basis, pad_scale, kappa, raw_layout);
                let carry = carry_image(
                    &rows,
                    row,
                    subtract,
                    pad_observations.as_deref(),
                    if pad_constant_one_sumcheck_factor {
                        basis
                    } else {
                        QM31::ZERO
                    },
                    pad_scale.mul(basis),
                    sc_m31,
                    pcs_m31,
                );
                unused_source_count += 1;
                pad_source_basis_m31 += 1;
                if let Some(kernel) = unused_raw.reduce(raw, carry) {
                    pad_joint_raw_kernel_m31 += 1;
                    kernel_images.push(kernel);
                }
            }
        }
    }
    let shared_unused_raw_rank_m31 = unused_raw.rank;
    let shared_unused_raw_kernel_m31 = unused_source_count - unused_raw.rank;

    let mut sumcheck = CarryEchelon::new(sc_m31);
    let mut pcs_images = Vec::new();
    for image in kernel_images {
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
    let mut pcs = ColumnEchelon::new(pcs_m31);
    for image in pcs_images {
        pcs.insert(image);
    }
    let baseline_pcs_rank_m31 = pcs.rank;

    // H depends on the witness on copy-active rows.  Inactive H masks are in
    // the selected source above; every active zero-sum H difference must be
    // contained after quotienting the same shared raw/A block.
    let active_rows = (0..TRACE_ROWS)
        .filter(|row| active[*row])
        .collect::<Vec<_>>();
    let active_dependent = *active_rows
        .last()
        .ok_or(StateOnlyHidingRankGateError::Layout)?;
    let mut helper_augmented = pcs.clone();
    let mut helper_sources = Vec::new();
    let mut helper_rows = Vec::new();
    let mut helper_values = Vec::new();
    for coordinate in 0..4 {
        let basis = state_only_mask_tower_basis(coordinate);
        for &row in &active_rows[..active_rows.len() - 1] {
            let raw = compact_qm31_raw(
                &rows,
                row,
                Some(active_dependent),
                basis,
                h_scale,
                kappa,
                raw_layout.h_start,
                raw_layout,
            );
            let carry = carry_image(
                &rows,
                row,
                Some(active_dependent),
                None,
                QM31::ZERO,
                h_scale.mul(basis),
                sc_m31,
                pcs_m31,
            );
            let post_raw = unused_raw.quotient_existing(raw, carry).ok_or(
                StateOnlyHidingRankGateError::HelperContainment {
                    before: baseline_pcs_rank_m31,
                    after: baseline_pcs_rank_m31 + 1,
                },
            )?;
            let (sc, pcs_tail) = post_raw.split_at(sc_m31);
            let post_sumcheck = sumcheck
                .quotient_existing(sc.to_vec(), pcs_tail.to_vec())
                .ok_or(StateOnlyHidingRankGateError::HelperContainment {
                    before: baseline_pcs_rank_m31,
                    after: baseline_pcs_rank_m31 + 1,
                })?;
            if let Some((pivot, value)) = helper_augmented.insert_with_pivot_value(post_sumcheck) {
                helper_sources.push(4 * row + coordinate);
                helper_rows.push(pivot);
                helper_values.push(value);
            }
        }
    }
    let helper_augmented_rank_m31 = helper_augmented.rank;
    let helper_minor = RankMinorProvenance::from_parts(
        "atomic_profile21_compact_claim_helper",
        helper_sources,
        helper_rows.clone(),
        helper_values,
    );

    let bound_root0_switch = bound_root0_switch
        .map(|request| {
            apply_compact_bound_root0_switch(
                &encoder,
                domain_log,
                schedule,
                tau,
                request.epsilon,
                request.shape,
                &request.multiplier,
                request.lean_x_only_mode,
                &helper_augmented,
                pcs_tail_qm31,
            )
        })
        .transpose()?;
    let bound_root0_switch_pcs_augmented_rank_m31 = bound_root0_switch
        .as_ref()
        .map_or(helper_augmented_rank_m31, |switch| switch.conditioned.rank);

    // Conservative same-statement semantic audit, identical to the selected
    // profile-21 audit except for delta in every semantic PCS coefficient.
    let mut compatibility = CarryEchelon::new(sc_m31);
    let mut semantic_augmented = bound_root0_switch
        .as_ref()
        .map(|switch| switch.conditioned.clone())
        .unwrap_or(helper_augmented);
    let mut semantic_sources = Vec::new();
    let mut semantic_rows = Vec::new();
    let mut semantic_values = Vec::new();
    for column in 0..SEMANTIC_COLUMNS {
        for row in 1..TRACE_ROWS {
            let source = column * TRACE_ROWS + row;
            let raw = c1_raw_difference(&rows, row, None);
            let carry = carry_image(
                &rows,
                row,
                None,
                None,
                QM31::ZERO,
                semantic_scale.mul(powers[column]),
                sc_m31,
                pcs_m31,
            );
            let post_raw = semantic_raw_echelons[column]
                .quotient_existing(raw, carry)
                .ok_or(StateOnlyHidingRankGateError::WitnessRawQuotient { source })?;
            let (sc, pcs_tail) = post_raw.split_at(sc_m31);
            let (sc_remainder, mut pcs_remainder) =
                sumcheck.remainder_existing(sc.to_vec(), pcs_tail.to_vec());
            let next_pivot = compatibility.rank;
            pcs_remainder.extend((0..4).map(|index| {
                if next_pivot < 4 && index == next_pivot {
                    M31::ONE
                } else {
                    M31::ZERO
                }
            }));
            if let CarryReduction::Kernel(mut image) =
                compatibility.reduce_with_pivot(sc_remainder, pcs_remainder)
            {
                image.truncate(pcs_m31);
                if let Some((pivot, value)) = semantic_augmented.insert_with_pivot_value(image) {
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
    let semantic_augmented_rank_m31 = semantic_augmented.rank;
    let semantic_minor = RankMinorProvenance::from_parts(
        "atomic_profile21_compact_claim_semantic",
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
        let pcs_zero = vec![M31::ZERO; pcs_m31];
        let (sc_remainder, mut pcs_remainder) = sumcheck.remainder_existing(sc, pcs_zero);
        pcs_remainder.extend([M31::ZERO; 4]);
        if let CarryReduction::Kernel(mut image) =
            compatibility.reduce_with_pivot(sc_remainder, pcs_remainder)
        {
            image.truncate(pcs_m31);
            if let Some((pivot, value)) = semantic_augmented.insert_with_pivot_value(image) {
                legal_sources.push(sc_row - 4);
                legal_rows.push(pivot);
                legal_values.push(value);
            }
        }
    }
    let legal_sumcheck_augmented_rank_m31 = semantic_augmented.rank;
    let legal_sumcheck_minor = RankMinorProvenance::from_parts(
        "atomic_profile21_compact_claim_legal_sumcheck",
        legal_sources,
        legal_rows.clone(),
        legal_values,
    );

    let old_claims_qm31 = 3 * (SEMANTIC_COLUMNS + UNUSED_COLUMNS);
    let compact_claims_qm31 = 3 * SEMANTIC_COLUMNS + UNUSED_COLUMNS + usize::from(include_pad) + 1;
    Ok(AtomicProfile21CompactClaimRankReport {
        query_count: schedule.query_count,
        message_log: STATE_ONLY_LOG_ROWS,
        codeword_domain_log: domain_log,
        rate_denominator: 1usize << (domain_log - STATE_ONLY_LOG_ROWS),
        semantic_terminal_claims_qm31: 3 * SEMANTIC_COLUMNS,
        unused_z_claims_qm31: UNUSED_COLUMNS + usize::from(include_pad),
        shared_tail_claims_qm31: 1,
        old_claims_qm31,
        compact_claims_qm31,
        saved_claims_qm31: old_claims_qm31 - compact_claims_qm31,
        saved_claim_bytes: 16 * (old_claims_qm31 - compact_claims_qm31),
        tau_coordinates_m31: qm31_coordinates(tau).map(|coordinate| coordinate.0),
        delta_coordinates_m31: qm31_coordinates(delta).map(|coordinate| coordinate.0),
        full_domain_pad_probe: include_pad,
        pad_constant_one_sumcheck_factor,
        pad_source_basis_m31,
        pad_joint_raw_kernel_m31,
        shared_unused_raw_rows_m31: raw_layout.total_m31,
        shared_unused_raw_rank_m31,
        shared_unused_raw_kernel_m31,
        masked_sumcheck_rank_m31: sumcheck.rank,
        baseline_pcs_rank_m31,
        helper_augmented_rank_m31,
        helper_new_pivots_m31: helper_rows,
        semantic_augmented_rank_m31,
        semantic_new_pivots_m31: semantic_rows,
        legal_sumcheck_augmented_rank_m31,
        legal_sumcheck_new_pivots_m31: legal_rows,
        contains_helper_semantic_and_legal_sumcheck: baseline_pcs_rank_m31
            == legal_sumcheck_augmented_rank_m31,
        bound_root0_switch_probe: bound_root0_switch.is_some(),
        bound_root0_switch_coefficient_functional_mode: bound_root0_switch
            .as_ref()
            .is_some_and(|switch| switch.coefficient_functional_mode),
        bound_root0_switch_lean_x_only_mode: bound_root0_switch
            .as_ref()
            .is_some_and(|switch| switch.lean_x_only_mode),
        bound_root0_switch_coefficient_index: bound_root0_switch
            .as_ref()
            .map_or(0, |switch| switch.coefficient_index),
        bound_root0_switch_message_qm31: bound_root0_switch
            .as_ref()
            .map_or(0, |switch| switch.message_qm31),
        bound_root0_switch_randomness_qm31: bound_root0_switch
            .as_ref()
            .map_or(0, |switch| switch.randomness_qm31),
        bound_root0_switch_dimension_qm31: bound_root0_switch
            .as_ref()
            .map_or(0, |switch| switch.dimension_qm31),
        bound_root0_switch_variables_qm31: bound_root0_switch
            .as_ref()
            .map_or(0, |switch| switch.variables_qm31),
        bound_root0_switch_epsilon_coordinates_m31: bound_root0_switch
            .as_ref()
            .map_or([0; 4], |switch| switch.epsilon_coordinates_m31),
        bound_root0_switch_code_basis_rank_qm31: bound_root0_switch
            .as_ref()
            .map_or(0, |switch| switch.code_basis_rank_qm31),
        bound_root0_switch_code_basis_fingerprint: bound_root0_switch
            .as_ref()
            .map_or(0, |switch| switch.code_basis_fingerprint),
        bound_root0_switch_multiplier_degree: bound_root0_switch
            .as_ref()
            .map_or(0, |switch| switch.multiplier_degree),
        bound_root0_switch_multiplier_fingerprint: bound_root0_switch
            .as_ref()
            .map_or(0, |switch| switch.multiplier_fingerprint),
        bound_root0_switch_product_dimension_qm31: bound_root0_switch
            .as_ref()
            .map_or(0, |switch| switch.product_dimension_qm31),
        bound_root0_switch_product_max_root_slot: bound_root0_switch
            .as_ref()
            .map_or(0, |switch| switch.product_max_root_slot),
        bound_root0_switch_product_basis_fingerprint: bound_root0_switch
            .as_ref()
            .map_or(0, |switch| switch.product_basis_fingerprint),
        bound_root0_switch_pointwise_product_identity: bound_root0_switch
            .as_ref()
            .is_some_and(|switch| switch.pointwise_product_identity),
        bound_root0_switch_fold_product_identity: bound_root0_switch
            .as_ref()
            .is_some_and(|switch| switch.fold_product_identity),
        bound_root0_switch_folded_opening_rank_qm31: bound_root0_switch
            .as_ref()
            .map_or(0, |switch| switch.folded_opening_rank_qm31),
        bound_root0_switch_raw_opening_rank_qm31: bound_root0_switch
            .as_ref()
            .map_or(0, |switch| switch.raw_opening_rank_qm31),
        bound_root0_switch_raw_contains_folded_openings: bound_root0_switch
            .as_ref()
            .is_some_and(|switch| switch.raw_contains_folded_openings),
        bound_root0_switch_u_plus_folded_rank_qm31: bound_root0_switch
            .as_ref()
            .map_or(0, |switch| switch.u_plus_folded_rank_qm31),
        bound_root0_switch_u_plus_folded_target_rank_qm31: bound_root0_switch
            .as_ref()
            .map_or(0, |switch| switch.u_plus_folded_target_rank_qm31),
        bound_root0_switch_u_plus_raw_rank_qm31: bound_root0_switch
            .as_ref()
            .map_or(0, |switch| switch.u_plus_raw_rank_qm31),
        bound_root0_switch_u_plus_raw_target_rank_qm31: bound_root0_switch
            .as_ref()
            .map_or(0, |switch| switch.u_plus_raw_target_rank_qm31),
        bound_root0_switch_conditioned_kernel_qm31: bound_root0_switch
            .as_ref()
            .map_or(0, |switch| switch.conditioned_kernel_qm31),
        bound_root0_switch_gamma_exponent: bound_root0_switch
            .as_ref()
            .map_or(0, |switch| switch.gamma_exponent),
        bound_root0_switch_exact_full_tail: bound_root0_switch.is_some(),
        bound_root0_switch_sparse_dense_tail_parity: bound_root0_switch
            .as_ref()
            .is_some_and(|switch| switch.sparse_dense_tail_parity),
        bound_root0_switch_pcs_augmented_rank_m31,
        bound_root0_switch_new_pivots_m31: bound_root0_switch
            .as_ref()
            .map_or_else(Vec::new, |switch| switch.new_pivots_m31.clone()),
        bound_root0_switch_pivots_later_m31: bound_root0_switch
            .as_ref()
            .map_or(0, |switch| switch.pivots_later_m31),
        bound_root0_switch_pivots_ood_m31: bound_root0_switch
            .as_ref()
            .map_or(0, |switch| switch.pivots_ood_m31),
        bound_root0_switch_pivots_relation_m31: bound_root0_switch
            .as_ref()
            .map_or(0, |switch| switch.pivots_relation_m31),
        bound_root0_switch_pivots_final_m31: bound_root0_switch
            .as_ref()
            .map_or(0, |switch| switch.pivots_final_m31),
        bound_root0_switch_contains_semantic_and_legal_sumcheck: bound_root0_switch.is_some()
            && bound_root0_switch_pcs_augmented_rank_m31 == legal_sumcheck_augmented_rank_m31,
        helper_minor,
        bound_root0_switch_minor: bound_root0_switch.map_or_else(
            || RankMinorProvenance::empty("compact_bound_root0_switch"),
            |switch| switch.minor,
        ),
        semantic_minor,
        legal_sumcheck_minor,
        elapsed_millis: started.elapsed().as_millis(),
    })
}

pub fn probe_atomic_state_only_compact_claim_rank(
    schedule: &StateOnlyTranscriptScheduleResult,
    tau: QM31,
    delta: QM31,
) -> Result<AtomicProfile21CompactClaimRankReport, StateOnlyHidingRankGateError> {
    run_atomic_state_only_compact_claim_rank(schedule, tau, delta, false, false, None)
}

/// Compact-claim gate plus one fresh full-domain QM31 pad at gamma exponent
/// 28. The pad uses the constant-one masked-sumcheck factor, exposes layer0
/// and `P(z)`, and contributes its successor/xor evaluations only through the
/// shared `A_tail` claim.
pub fn probe_atomic_state_only_compact_claim_rank_with_constant_pad(
    schedule: &StateOnlyTranscriptScheduleResult,
    tau: QM31,
    delta: QM31,
) -> Result<AtomicProfile21CompactClaimRankReport, StateOnlyHidingRankGateError> {
    run_atomic_state_only_compact_claim_rank(schedule, tau, delta, true, true, None)
}

/// Same compact full-domain pad, but with zero masked-sumcheck carry. This is
/// kept as a distinct diagnostic and must not be confused with the
/// constant-one-factor construction.
pub fn probe_atomic_state_only_compact_claim_rank_with_zero_factor_pad(
    schedule: &StateOnlyTranscriptScheduleResult,
    tau: QM31,
    delta: QM31,
) -> Result<AtomicProfile21CompactClaimRankReport, StateOnlyHidingRankGateError> {
    run_atomic_state_only_compact_claim_rank(schedule, tau, delta, true, false, None)
}

/// Compact-claim baseline plus an exact physically bound root-zero X/F
/// source switch. Both source words expose all four authenticated C2 symbols
/// at every production query. X alone enters the main root-zero gamma lane at
/// exponent 28 and carries its complete p0/later/OOD/relation/final image.
pub fn probe_atomic_state_only_compact_claim_bound_root0_switch_rank(
    schedule: &StateOnlyTranscriptScheduleResult,
    tau: QM31,
    delta: QM31,
    epsilon: QM31,
    shape: CompactBoundRoot0SwitchShape,
) -> Result<AtomicProfile21CompactClaimRankReport, StateOnlyHidingRankGateError> {
    run_atomic_state_only_compact_claim_rank(
        schedule,
        tau,
        delta,
        false,
        false,
        Some(CompactBoundRoot0SwitchRequest {
            shape,
            epsilon,
            multiplier: CompactRoot0Multiplier::identity(),
            lean_x_only_mode: false,
        }),
    )
}

/// Exact physical `p(t)X` carry with the existing X/F/U source disclosure.
/// `tX=L_tau(pX)` is conditioned before the fresh `epsilon` separator.
pub fn probe_atomic_state_only_compact_claim_bound_root0_multiplier_rank(
    schedule: &StateOnlyTranscriptScheduleResult,
    tau: QM31,
    delta: QM31,
    epsilon: QM31,
    shape: CompactBoundRoot0SwitchShape,
    multiplier: CompactRoot0Multiplier,
) -> Result<AtomicProfile21CompactClaimRankReport, StateOnlyHidingRankGateError> {
    run_atomic_state_only_compact_claim_rank(
        schedule,
        tau,
        delta,
        false,
        false,
        Some(CompactBoundRoot0SwitchRequest {
            shape,
            epsilon,
            multiplier,
            lean_x_only_mode: false,
        }),
    )
}

/// Decisive lean ablation: X is committed before the challenges; after tau,
/// only `tX=L_tau(pX)` is disclosed. Raw query openings authenticate X and
/// the main PCS carries `epsilon*pX`. No F/U/V/source-CA view is modeled.
pub fn probe_atomic_state_only_compact_claim_bound_root0_multiplier_lean_rank(
    schedule: &StateOnlyTranscriptScheduleResult,
    tau: QM31,
    delta: QM31,
    epsilon: QM31,
    shape: CompactBoundRoot0SwitchShape,
    multiplier: CompactRoot0Multiplier,
) -> Result<AtomicProfile21CompactClaimRankReport, StateOnlyHidingRankGateError> {
    run_atomic_state_only_compact_claim_rank(
        schedule,
        tau,
        delta,
        false,
        false,
        Some(CompactBoundRoot0SwitchRequest {
            shape,
            epsilon,
            multiplier,
            lean_x_only_mode: true,
        }),
    )
}

/// Compatibility wrapper for the earlier one-separator diagnostic. New work
/// must call [`probe_atomic_state_only_compact_claim_rank`] with independently
/// sampled nonzero `tau` and `delta`.
pub fn probe_atomic_state_only_profile21_compact_claim_rank(
    schedule: &StateOnlyProfile21TranscriptScheduleResult,
    tau: QM31,
) -> Result<AtomicProfile21CompactClaimRankReport, StateOnlyHidingRankGateError> {
    probe_atomic_state_only_compact_claim_rank(&schedule.base, tau, tau.square())
}
