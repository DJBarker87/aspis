//! Exact affine conditioning for the reduced, bound natural-B18 switch.
//!
//! The authenticated source code is
//!
//! `V = span{B_18} (+) (x^2+1) P_<16`,
//!
//! in the natural line basis.  X and F are opened through the full four-slot
//! shared-C2 fibers, while `U = F + delta X` is disclosed in this same
//! 17-coordinate basis.  Only the B18 coordinate carries into the old PCS
//! view.  This is a host-only rank object and changes no production wire.

use super::*;

pub(super) struct ReducedNatural18SwitchConditioning {
    pub observation_rank_qm31: usize,
    pub conditioned_pcs: ColumnEchelon,
}

#[allow(clippy::too_many_arguments)]
pub(super) fn condition_reduced_natural18_shared_c2_pcs(
    encoder: &CircleEncoder,
    domain_log: u32,
    schedule: &StateOnlyTranscriptScheduleResult,
    delta: QM31,
    rows: &[RowPublicMaps],
    h_raw_qm31: usize,
    pcs_tail_qm31: usize,
    baseline_pcs: &ColumnEchelon,
) -> Result<ReducedNatural18SwitchConditioning, StateOnlyHidingRankGateError> {
    const RANDOMNESS: usize = 16;
    const DIMENSION: usize = 17;
    const NATURAL_DIMENSION: usize = 19;
    const HIGH: usize = 18;
    if schedule.query_count != RANDOMNESS
        || domain_log != STATE_ONLY_LOG_ROWS + 9
        || delta == QM31::ZERO
        || rows.len() != TRACE_ROWS
    {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let queries = &schedule.queries[..schedule.query_count];
    let certificate = profile21_high_switch_carry_certificate(queries)?;
    if certificate.evaluation_plus_leading_rank_qm31 != 17 {
        return Err(StateOnlyHidingRankGateError::Layout);
    }

    let conversion = ordinary_monomials_in_natural_line_basis(NATURAL_DIMENSION);
    let mut code_basis = Vec::with_capacity(DIMENSION);
    let mut b18 = vec![M31::ZERO; NATURAL_DIMENSION];
    b18[HIGH] = M31::ONE;
    code_basis.push(b18);
    for degree in 0..RANDOMNESS {
        code_basis.push(
            conversion[degree]
                .iter()
                .copied()
                .zip(conversion[degree + 2].iter().copied())
                .map(|(low, high)| low.add(high))
                .collect(),
        );
    }
    let mut basis_rank = ColumnEchelon::new(NATURAL_DIMENSION);
    for column in &code_basis {
        basis_rank.insert(column.clone());
    }
    if basis_rank.rank != DIMENSION {
        return Err(StateOnlyHidingRankGateError::Layout);
    }

    let raw_natural = (0..NATURAL_DIMENSION)
        .map(|coefficient| first_layer0_coefficient_query_fibers(encoder, coefficient, queries))
        .collect::<Result<Vec<_>, _>>()?;
    let raw_code = code_basis
        .iter()
        .map(|coefficients| combine_natural_qm31_columns(&raw_natural, coefficients))
        .collect::<Result<Vec<_>, _>>()?;
    if qm31_column_rank(&raw_code, FIBER_SLOTS * RANDOMNESS) != RANDOMNESS {
        return Err(StateOnlyHidingRankGateError::Layout);
    }

    // Column order is X[0..17], F[0..17].  The independently public block is
    // U[17], raw-X[64], raw-F[64].  Keeping both raw blocks in the matrix pins
    // the exact shared-leaf byte View; their linear dependence through U is
    // discovered by elimination rather than pre-deleted.
    let observation_qm31 = DIMENSION + 2 * FIBER_SLOTS * RANDOMNESS;
    let columns = (0..2 * DIMENSION)
        .map(|variable| {
            let is_f = variable >= DIMENSION;
            let coordinate = variable % DIMENSION;
            let mut column = vec![QM31::ZERO; observation_qm31];
            column[coordinate] = if is_f { QM31::ONE } else { delta };
            let raw_start = DIMENSION + usize::from(is_f) * FIBER_SLOTS * RANDOMNESS;
            column[raw_start..raw_start + FIBER_SLOTS * RANDOMNESS]
                .copy_from_slice(&raw_code[coordinate]);
            column
        })
        .collect::<Vec<_>>();
    let observation_rank_qm31 = qm31_column_rank(&columns, observation_qm31);
    if observation_rank_qm31 != DIMENSION + RANDOMNESS {
        return Err(StateOnlyHidingRankGateError::Layout);
    }

    let mut observation = CarryEchelon::new(4 * observation_qm31);
    let mut conditioned_pcs = baseline_pcs.clone();
    for variable in 0..2 * DIMENSION {
        for tower_coordinate in 0..4 {
            let basis = state_only_mask_tower_basis(tower_coordinate);
            let mut public = Vec::with_capacity(4 * observation_qm31);
            append_qm31_coordinates(
                &mut public,
                columns[variable]
                    .iter()
                    .copied()
                    .map(|value| value.mul(basis)),
            );
            let carry = if variable == 0 {
                combined_pcs_image(rows, FIBER_SLOTS * HIGH, basis, h_raw_qm31, pcs_tail_qm31)
            } else {
                vec![M31::ZERO; 4 * (h_raw_qm31 + pcs_tail_qm31)]
            };
            if let CarryReduction::Kernel(kernel) = observation.reduce_with_pivot(public, carry) {
                conditioned_pcs.insert(kernel);
            }
        }
    }
    if observation.rank != 4 * observation_rank_qm31 {
        return Err(StateOnlyHidingRankGateError::Layout);
    }

    Ok(ReducedNatural18SwitchConditioning {
        observation_rank_qm31,
        conditioned_pcs,
    })
}
