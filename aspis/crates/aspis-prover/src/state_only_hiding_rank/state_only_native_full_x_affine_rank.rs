//! Production-neutral affine conditioning for one native full root-zero X lane.
//!
//! This helper deliberately models the literal public X block before its PCS
//! image is admitted into a hiding rank:
//!
//! - all four authenticated layer-zero symbols for each selected query; and
//! - the complete three-point-plus-inactive relation target `tX`.
//!
//! The three X point evaluations are inputs to `tX`, but are not separately
//! serialized by the minimal wire.  `expose_point_evaluations` exists only to
//! compare the strictly wider diagnostic wire which does serialize them.
//!
//! The returned echelon is therefore the image of `epsilon * P(X)` restricted
//! to the kernel of every independently visible X field.  It is a host rank
//! diagnostic only; it does not alter a proof or verifier wire.

use super::*;

pub(super) struct NativeFullXAffineConditioning {
    pub observation_rank_qm31: usize,
    pub conditioned_pcs: ColumnEchelon,
}

#[allow(clippy::too_many_arguments)]
pub(super) fn condition_native_full_x_affine_pcs(
    schedule: &StateOnlyTranscriptScheduleResult,
    layout: RankLayout,
    rows: &[RowPublicMaps],
    full_tails: &[Vec<QM31>],
    epsilon: QM31,
    h_raw_qm31: usize,
    baseline_pcs: &ColumnEchelon,
    expose_target: bool,
    expose_point_evaluations: bool,
) -> Result<NativeFullXAffineConditioning, StateOnlyHidingRankGateError> {
    if epsilon == QM31::ZERO
        || rows.len() != TRACE_ROWS
        || full_tails.len() != TRACE_ROWS
        || rows
            .iter()
            .any(|row| row.layer0_m31.len() != FIBER_SLOTS * schedule.query_count)
    {
        return Err(StateOnlyHidingRankGateError::Shape);
    }

    let relation_weights = initial_relation_weights(schedule, layout)?;
    let inactive_masks = rank_inactive_masks(layout);
    let kappa = schedule.prefix.point_scale;

    // R_q(X) and tX are the minimal public fields. The tX identity is
    // independently reconstructed rather than trusting the
    // accumulated relation covector: this catches omission or inversion of an
    // inactive row in the diagnostic itself.  The optional three point rows
    // are a labelled conservative comparison, not part of the selected wire.
    let observation_qm31 = FIBER_SLOTS * schedule.query_count
        + usize::from(expose_target)
        + 3 * usize::from(expose_point_evaluations);
    let observation_columns = (0..TRACE_ROWS)
        .map(|row| {
            let inactive = if inactive_masks[row >> 4] & (1 << (row & 15)) == 0 {
                QM31::ZERO
            } else {
                QM31::ONE
            };
            let independently_reconstructed_target = rows[row].terminal[0]
                .add(kappa.mul(rows[row].terminal[1]))
                .add(kappa.square().mul(rows[row].terminal[2]))
                .add(inactive);
            let target = relation_weights.weight_at(row as u32);
            if independently_reconstructed_target != target {
                return Err(StateOnlyHidingRankGateError::Relation);
            }

            let mut column = rows[row]
                .layer0_m31
                .iter()
                .copied()
                .map(|value| QM31::from_cm31(CM31::from_m31(value)))
                .collect::<Vec<_>>();
            if expose_point_evaluations {
                column.extend(rows[row].terminal);
            }
            if expose_target {
                column.push(target);
            }
            Ok(column)
        })
        .collect::<Result<Vec<_>, StateOnlyHidingRankGateError>>()?;

    let observation_rank_qm31 = qm31_column_rank(&observation_columns, observation_qm31);
    if observation_rank_qm31 != observation_qm31 {
        return Err(StateOnlyHidingRankGateError::Layout);
    }

    let mut observation = CarryEchelon::new(4 * observation_qm31);
    let mut conditioned_pcs = baseline_pcs.clone();
    for message_row in 0..TRACE_ROWS {
        for tower_coordinate in 0..4 {
            let basis = state_only_mask_tower_basis(tower_coordinate);
            let mut public = Vec::with_capacity(4 * observation_qm31);
            append_qm31_coordinates(
                &mut public,
                observation_columns[message_row]
                    .iter()
                    .copied()
                    .map(|value| value.mul(basis)),
            );
            let pcs =
                first_later_pcs_image(&full_tails[message_row], epsilon.mul(basis), h_raw_qm31);
            if let CarryReduction::Kernel(kernel) = observation.reduce_with_pivot(public, pcs) {
                conditioned_pcs.insert(kernel);
            }
        }
    }
    if observation.rank != 4 * observation_rank_qm31 {
        return Err(StateOnlyHidingRankGateError::Layout);
    }

    Ok(NativeFullXAffineConditioning {
        observation_rank_qm31,
        conditioned_pcs,
    })
}
