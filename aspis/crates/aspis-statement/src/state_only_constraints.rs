//! Complete host-side degree-27 state-only constraint and hiding terminal.
//!
//! The 94 base-coefficient semantic residual polynomials are injectively
//! packed into 24 QM31 lanes, the LogUp copy lane remains separate, and the
//! four Poseidon lanes lead the frozen 29-lane theta registry.

use aspis_core::field::{PreparedQm31Multiplier, QM31};
use aspis_core::state_only_hiding::state_only_mask_value;
use aspis_core::statement_sumcheck::PaymentConstraintChallenges;

use crate::constraints_v4::multilinear_evaluate_qm31;
use crate::state_only_poseidon::{
    evaluate_state_only_poseidon_oracle, StateOnlyPoseidonSelectors,
    STATE_ONLY_POSEIDON_PACKED_LANES,
};
use crate::state_only_semantic::{
    evaluate_state_only_semantic_oracle, state_only_semantic_openings_at_point,
    StateOnlySemanticError, StateOnlySemanticOpenings, STATE_ONLY_PACKED_BASE_LANE_COUNT,
    STATE_ONLY_RANDOMIZED_SEMANTIC_LANE_COUNT,
};
use crate::state_only_trace::StateOnlyTraceFoundation;
use crate::SpendPublic;

pub const STATE_ONLY_RANDOMIZED_CONSTRAINT_LANES: usize =
    STATE_ONLY_POSEIDON_PACKED_LANES + STATE_ONLY_RANDOMIZED_SEMANTIC_LANE_COUNT;
const _: () = assert!(STATE_ONLY_RANDOMIZED_CONSTRAINT_LANES == 29);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StateOnlyPointOpenings {
    pub semantic: StateOnlySemanticOpenings,
    pub g_z: QM31,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StateOnlyConstraintError {
    Shape,
    Semantic(StateOnlySemanticError),
}

impl From<StateOnlySemanticError> for StateOnlyConstraintError {
    fn from(error: StateOnlySemanticError) -> Self {
        Self::Semantic(error)
    }
}

pub fn state_only_point_openings(
    trace: &StateOnlyTraceFoundation,
    h1: &[QM31],
    g: &[QM31],
    point: &[QM31; 10],
) -> Result<StateOnlyPointOpenings, StateOnlyConstraintError> {
    let semantic = state_only_semantic_openings_at_point(trace, h1, point)
        .ok_or(StateOnlyConstraintError::Shape)?;
    let g_z = multilinear_evaluate_qm31(g, point).ok_or(StateOnlyConstraintError::Shape)?;
    Ok(StateOnlyPointOpenings { semantic, g_z })
}

/// `sum_i lane_i * theta^i`, with Poseidon lanes first, then the 24 packed
/// semantic lanes, then the copy-LogUp lane.
pub fn evaluate_state_only_constraint_point(
    public: &SpendPublic,
    openings: &StateOnlyPointOpenings,
    point: &[QM31; 10],
    lambda: QM31,
    chi: QM31,
    theta: QM31,
) -> Result<QM31, StateOnlyConstraintError> {
    let poseidon = evaluate_state_only_poseidon_oracle(
        &openings.semantic.c1,
        &StateOnlyPoseidonSelectors::at_point(point),
    );
    let semantic =
        evaluate_state_only_semantic_oracle(public, &openings.semantic, point, lambda, chi)?;
    let packed = semantic.packed_base_lanes();
    let prepared_theta = PreparedQm31Multiplier::new(theta);
    let mut accumulator = QM31::ZERO;
    for lane in poseidon
        .into_iter()
        .chain(packed)
        .chain(core::iter::once(semantic.copy))
        .rev()
    {
        accumulator = prepared_theta.mul(accumulator).add(lane);
    }
    debug_assert_eq!(STATE_ONLY_PACKED_BASE_LANE_COUNT, 24);
    Ok(accumulator)
}

fn equality_value(left: &[QM31; 10], right: &[QM31; 10]) -> QM31 {
    left.iter().zip(right).fold(QM31::ONE, |product, (a, b)| {
        product.mul(a.mul(*b).add(QM31::ONE.sub(*a).mul(QM31::ONE.sub(*b))))
    })
}

pub fn state_only_unmasked_terminal_value(
    public: &SpendPublic,
    openings: &StateOnlyPointOpenings,
    point: &[QM31; 10],
    batching: &PaymentConstraintChallenges,
    lambda: QM31,
    chi: QM31,
) -> Result<QM31, StateOnlyConstraintError> {
    let composition =
        evaluate_state_only_constraint_point(public, openings, point, lambda, chi, batching.theta)?;
    Ok(equality_value(&batching.zerocheck_point, point)
        .mul(composition)
        .add(batching.mu.mul(openings.semantic.h1_z)))
}

/// Bound terminal for the one-G plus C1-padding construction:
/// `H(z) + eta * (eq(r,z) C(z) + mu h1(z))`.
pub fn state_only_masked_terminal_value(
    public: &SpendPublic,
    openings: &StateOnlyPointOpenings,
    point: &[QM31; 10],
    batching: &PaymentConstraintChallenges,
    lambda: QM31,
    chi: QM31,
    eta: QM31,
) -> Result<QM31, StateOnlyConstraintError> {
    let original =
        state_only_unmasked_terminal_value(public, openings, point, batching, lambda, chi)?;
    let mask = state_only_mask_value(&openings.semantic.c1.z, openings.g_z, point);
    Ok(mask.add(eta.mul(original)))
}
