#![no_std]

use aspis_core::circle_fri::normalized_circle_to_line_arity4_prepared_polynomial_refs;
use aspis_core::circle_query::{
    check_fixed_line_transition_prepared_polynomial_powers,
    check_fixed_terminal_transition_prepared_polynomial_refs, CircleQueryError,
};
use aspis_core::field::{M31, PreparedQm31Multiplier, QM31};

pub fn square(input: QM31) -> QM31 {
    input.square()
}

pub fn mul(left: QM31, right: QM31) -> QM31 {
    left.mul(right)
}

pub fn prepare(input: QM31) -> PreparedQm31Multiplier {
    PreparedQm31Multiplier::new(input)
}

pub fn circle(
    values: &[QM31; 4],
    alpha_powers: &[PreparedQm31Multiplier; 3],
    inv_2x: M31,
    inv_2y: M31,
) -> QM31 {
    normalized_circle_to_line_arity4_prepared_polynomial_refs(
        values,
        alpha_powers,
        inv_2x,
        inv_2y,
    )
}

pub fn line(
    incoming_leaf: &[u8],
    outgoing_leaf: &[u8],
    incoming_leaf_index: usize,
    layer: u8,
    inverses: [M31; 3],
    alpha_powers: &[PreparedQm31Multiplier; 3],
) -> Result<(), CircleQueryError> {
    check_fixed_line_transition_prepared_polynomial_powers(
        incoming_leaf,
        outgoing_leaf,
        incoming_leaf_index,
        layer,
        inverses,
        alpha_powers,
    )
}

pub fn terminal(
    incoming_leaf: &[u8],
    final_natural: &[QM31; 4],
    final_index: usize,
    inverses: [M31; 3],
    final_x: M31,
    alpha_powers: &[PreparedQm31Multiplier; 3],
) -> Result<(), CircleQueryError> {
    check_fixed_terminal_transition_prepared_polynomial_refs(
        incoming_leaf,
        final_natural,
        final_index,
        inverses,
        final_x,
        alpha_powers,
    )
}
