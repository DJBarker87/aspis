//! Interleaved linear-relation sumcheck for the arity-4 coefficient fold.
//!
//! For each four-coefficient chunk, let
//! `A(X) = a0 + a1 X + a2 X^2 + a3 X^3`. The PCS fold stores `A(alpha)`.
//! Given linear weights `(b0..b3)`, define the dual polynomial
//! `B(X) = (b0 + b3 X + b2 X^2 + b1 X^3) / 4`. Summing `A(X)B(X)` over the
//! four fourth roots of unity returns `sum_t a_t b_t`; evaluating it at the
//! transcript challenge returns the same relation on the folded vector.
//! Thus one degree-6 polynomial per committed layer carries an arbitrary
//! batched linear claim down to the explicit final coefficients.

use alloc::vec::Vec;

use crate::field::{M31_QUARTER, QM31};
use crate::verify::EvaluationClaim;

pub const SUMCHECK_COEFFICIENTS: usize = 7;
pub const SUMCHECK_BYTES: usize = SUMCHECK_COEFFICIENTS * 16;
pub type SumcheckPolynomial = [QM31; SUMCHECK_COEFFICIENTS];

#[derive(Clone, Debug)]
enum WeightComponent {
    /// scale * base^index (univariate evaluation at `base`).
    Geometric { scale: QM31, base: QM31 },
    /// scale * eq(point, index_bits), with big-endian coordinate order.
    Multilinear { scale: QM31, point: Vec<QM31> },
}

/// Compact sum of structured linear forms. It avoids materializing a full
/// QM31 weight vector in the SBF verifier (which would exceed the heap for
/// the lr14 diagnostic).
#[derive(Clone, Debug)]
pub struct WeightAccumulator {
    log_len: u32,
    components: Vec<WeightComponent>,
}

impl WeightAccumulator {
    pub fn empty(log_len: u32) -> Self {
        Self {
            log_len,
            components: Vec::new(),
        }
    }

    pub fn from_claim(log_len: u32, claim: Option<&EvaluationClaim>) -> Self {
        let mut out = Self::empty(log_len);
        if let Some(claim) = claim {
            debug_assert_eq!(claim.z.len(), log_len as usize);
            out.components.push(WeightComponent::Multilinear {
                scale: QM31::ONE,
                point: claim.z.clone(),
            });
        }
        out
    }

    /// Add `scale * [1, base, base^2, ...]`, the coefficient-linear form for
    /// a univariate evaluation at `base`.
    pub fn add_geometric(&mut self, scale: QM31, base: QM31) {
        self.components
            .push(WeightComponent::Geometric { scale, base });
    }

    pub fn weight_at(&self, index: u32) -> QM31 {
        debug_assert!(index < (1u32 << self.log_len));
        let mut total = QM31::ZERO;
        for component in &self.components {
            let value = match component {
                WeightComponent::Geometric { scale, base } => scale.mul(base.pow(index as u64)),
                WeightComponent::Multilinear { scale, point } => {
                    let mut value = *scale;
                    for (coordinate, z) in point.iter().enumerate() {
                        let bit = (index >> (point.len() - 1 - coordinate)) & 1;
                        value = if bit == 0 {
                            value.mul(QM31::ONE.sub(*z))
                        } else {
                            value.mul(*z)
                        };
                    }
                    value
                }
            };
            total = total.add(value);
        }
        total
    }

    /// Apply the dual of the arity-4 monomial coefficient fold.
    pub fn fold(&mut self, alpha: QM31) {
        debug_assert!(self.log_len >= 2);
        let alpha2 = alpha.square();
        let alpha3 = alpha2.mul(alpha);
        for component in &mut self.components {
            match component {
                WeightComponent::Geometric { scale, base } => {
                    let base2 = base.square();
                    let base3 = base2.mul(*base);
                    let factor = QM31::ONE
                        .add(alpha3.mul(*base))
                        .add(alpha2.mul(base2))
                        .add(alpha.mul(base3))
                        .mul_m31(M31_QUARTER);
                    *scale = scale.mul(factor);
                    *base = base2.square();
                }
                WeightComponent::Multilinear { scale, point } => {
                    let split = point.len() - 2;
                    let z0 = point[split];
                    let z1 = point[split + 1];
                    let one_minus_z0 = QM31::ONE.sub(z0);
                    let one_minus_z1 = QM31::ONE.sub(z1);
                    let b0 = one_minus_z0.mul(one_minus_z1);
                    let b1 = one_minus_z0.mul(z1);
                    let b2 = z0.mul(one_minus_z1);
                    let b3 = z0.mul(z1);
                    let factor = b0
                        .add(alpha3.mul(b1))
                        .add(alpha2.mul(b2))
                        .add(alpha.mul(b3))
                        .mul_m31(M31_QUARTER);
                    *scale = scale.mul(factor);
                    point.truncate(split);
                }
            }
        }
        self.log_len -= 2;
    }

    pub fn dot(&self, values: &[QM31]) -> QM31 {
        debug_assert_eq!(values.len(), 1usize << self.log_len);
        values
            .iter()
            .enumerate()
            .fold(QM31::ZERO, |sum, (index, value)| {
                sum.add(value.mul(self.weight_at(index as u32)))
            })
    }
}

fn accumulate_chunk(output: &mut SumcheckPolynomial, values: [QM31; 4], weights: [QM31; 4]) {
    // B coefficients are [b0, b3, b2, b1] / 4.
    let dual = [weights[0], weights[3], weights[2], weights[1]];
    for (a_degree, value) in values.iter().enumerate() {
        for (b_degree, weight) in dual.iter().enumerate() {
            output[a_degree + b_degree] =
                output[a_degree + b_degree].add(value.mul(*weight).mul_m31(M31_QUARTER));
        }
    }
}

pub fn polynomial_for_base(
    coefficients: &[crate::field::M31],
    weights: &WeightAccumulator,
) -> SumcheckPolynomial {
    debug_assert_eq!(coefficients.len(), 1usize << weights.log_len);
    let mut output = [QM31::ZERO; SUMCHECK_COEFFICIENTS];
    for (chunk_index, chunk) in coefficients.chunks_exact(4).enumerate() {
        let base = (chunk_index * 4) as u32;
        accumulate_chunk(
            &mut output,
            [
                QM31::from_cm31(crate::field::CM31::from_m31(chunk[0])),
                QM31::from_cm31(crate::field::CM31::from_m31(chunk[1])),
                QM31::from_cm31(crate::field::CM31::from_m31(chunk[2])),
                QM31::from_cm31(crate::field::CM31::from_m31(chunk[3])),
            ],
            [
                weights.weight_at(base),
                weights.weight_at(base + 1),
                weights.weight_at(base + 2),
                weights.weight_at(base + 3),
            ],
        );
    }
    output
}

pub fn polynomial_for_extension(
    coefficients: &[QM31],
    weights: &WeightAccumulator,
) -> SumcheckPolynomial {
    debug_assert_eq!(coefficients.len(), 1usize << weights.log_len);
    let mut output = [QM31::ZERO; SUMCHECK_COEFFICIENTS];
    for (chunk_index, chunk) in coefficients.chunks_exact(4).enumerate() {
        let base = (chunk_index * 4) as u32;
        accumulate_chunk(
            &mut output,
            [chunk[0], chunk[1], chunk[2], chunk[3]],
            [
                weights.weight_at(base),
                weights.weight_at(base + 1),
                weights.weight_at(base + 2),
                weights.weight_at(base + 3),
            ],
        );
    }
    output
}

/// Sum over the four fourth roots of unity. For degree <= 6, only
/// coefficients 0 and 4 survive the root-of-unity filter.
pub fn boundary_sum(polynomial: &SumcheckPolynomial) -> QM31 {
    polynomial[0]
        .add(polynomial[4])
        .mul_m31(crate::field::M31(4))
}

pub fn evaluate(polynomial: &SumcheckPolynomial, point: QM31) -> QM31 {
    polynomial
        .iter()
        .rev()
        .fold(QM31::ZERO, |acc, coefficient| {
            acc.mul(point).add(*coefficient)
        })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::{CM31, M31};
    use alloc::vec;

    fn q(value: u32) -> QM31 {
        QM31::from_cm31(CM31::from_m31(M31(value)))
    }

    fn fold_values(values: &[QM31], alpha: QM31) -> Vec<QM31> {
        let alpha2 = alpha.mul(alpha);
        let alpha3 = alpha2.mul(alpha);
        values
            .chunks_exact(4)
            .map(|chunk| {
                chunk[0]
                    .add(alpha.mul(chunk[1]))
                    .add(alpha2.mul(chunk[2]))
                    .add(alpha3.mul(chunk[3]))
            })
            .collect()
    }

    #[test]
    fn boundary_and_fold_invariants_hold_for_mixed_weights() {
        let values = (1..=16).map(q).collect::<Vec<_>>();
        let claim = EvaluationClaim {
            z: vec![q(2), q(3), q(4), q(5)],
            v: QM31::ZERO,
        };
        let mut weights = WeightAccumulator::from_claim(4, Some(&claim));
        weights.add_geometric(q(7), q(9));

        let polynomial = polynomial_for_extension(&values, &weights);
        assert_eq!(boundary_sum(&polynomial), weights.dot(&values));

        let alpha = q(11);
        let folded = fold_values(&values, alpha);
        weights.fold(alpha);
        assert_eq!(evaluate(&polynomial, alpha), weights.dot(&folded));

        let polynomial = polynomial_for_extension(&folded, &weights);
        assert_eq!(boundary_sum(&polynomial), weights.dot(&folded));
        let alpha = q(13);
        let folded = fold_values(&folded, alpha);
        weights.fold(alpha);
        assert_eq!(evaluate(&polynomial, alpha), weights.dot(&folded));
    }
}
