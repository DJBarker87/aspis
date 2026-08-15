#![allow(dead_code)]

// Compile the unchanged production relation checker in a Solana-free crate.
// Charon therefore starts from the repository source itself without pulling
// in the program entrypoint or Solana runtime dependencies.
#[path = "../../../../programs/aspis-verifier/src/v5_relation_stress.rs"]
pub mod relation_stress;

use aspis_core::field::QM31;
use aspis_core::sumcheck::{SumcheckPolynomial, WeightAccumulator};

// These wrappers are extraction roots only. Their bodies call the unchanged
// production helpers, so the generated definitions retain the real method
// bodies instead of a copied or simplified verifier.
pub fn extract_boundary_sum(polynomial: &SumcheckPolynomial) -> QM31 {
    aspis_core::sumcheck::boundary_sum(polynomial)
}

pub fn extract_evaluate(polynomial: &SumcheckPolynomial, alpha: QM31) -> QM31 {
    aspis_core::sumcheck::evaluate(polynomial, alpha)
}

pub fn extract_weight_fold(mut weights: WeightAccumulator, alpha: QM31) -> WeightAccumulator {
    weights.fold(alpha);
    weights
}

pub fn extract_weight_dot(weights: &WeightAccumulator, values: &[QM31; 4]) -> QM31 {
    weights.dot(values)
}
