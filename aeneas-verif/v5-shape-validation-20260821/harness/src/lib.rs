#![no_std]

use aspis_core::circle_pcs_shape::{CirclePcsShape, CirclePcsShapeError};

/// Narrow extraction root for the production shape validator used by the V5
/// FRI consumer.  The wrapper adds no behavior.
pub fn validate_shape(input: CirclePcsShape) -> Result<CirclePcsShape, CirclePcsShapeError> {
    input.validate()
}

#[cfg(kani)]
mod proofs {
    use super::*;

    /// The production validator has many rejecting branches, but its only
    /// successful return is the shape passed by value into the function.
    #[kani::proof]
    #[kani::unwind(7)]
    fn production_validation_success_returns_input() {
        let input = CirclePcsShape {
            trace_log_size: kani::any(),
            domain_log_size: kani::any(),
            query_count: kani::any(),
            opening_points: kani::any(),
            c1_columns: kani::any(),
            c2_columns: kani::any(),
            c1_layer0_tag: kani::any(),
            c2_layer0_tag: kani::any(),
            later_layer_tags: [kani::any(), kani::any(), kani::any()],
        };
        if let Ok(output) = validate_shape(input) {
            assert_eq!(output, input);
        }
    }
}
