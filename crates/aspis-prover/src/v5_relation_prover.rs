//! Four-claim incremental relation for the V5 PCS.
//!
//! The ordinary three MLE claims, the carried atomic-v3 copy-inactive claim and
//! the structured Component-B terminal covector are all reduced against the
//! same gamma-combined nineteen-lane message.  The prover then follows the
//! production four-round OOD/sumcheck/fold order.  This module deliberately
//! owns no transcript or wire: callers must absorb every value before drawing
//! its dependent challenge.

use aspis_core::circle::SecureCirclePoint;
use aspis_core::circle_fri::FIXED_TRACE_LOG_SIZE;
use aspis_core::circle_prefix::{
    CANDIDATE_FINAL_POLY_LEN, CANDIDATE_OOD_SAMPLES, CANDIDATE_ROUND_COUNT,
};
use aspis_core::field::{M31_QUARTER, QM31};
use aspis_core::sumcheck::{
    boundary_sum, evaluate, SumcheckPolynomial, TensorWeightError, WeightAccumulator,
};

use crate::circle_candidate::{fold_adjacent_natural_arity4, TRACE_LEN};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum V5RelationProverError {
    MessageLength { expected: usize, actual: usize },
    CovectorLength { expected: usize, actual: usize },
    InactiveClaimMismatch,
    Weight(TensorWeightError),
    RoundOrder,
    OodOrder,
    BoundaryMismatch,
    FoldMismatch,
    Incomplete,
}

impl From<TensorWeightError> for V5RelationProverError {
    fn from(error: TensorWeightError) -> Self {
        Self::Weight(error)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct V5RelationTrace {
    pub point_claims: [QM31; 3],
    pub terminal_claim: QM31,
    pub ood_values: [[QM31; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT],
    pub sumchecks: [SumcheckPolynomial; CANDIDATE_ROUND_COUNT],
    pub running_claims: [QM31; CANDIDATE_ROUND_COUNT + 1],
    pub final_coefficients: [QM31; CANDIDATE_FINAL_POLY_LEN],
}

pub struct V5IncrementalRelation {
    coefficients: Vec<QM31>,
    weights: WeightAccumulator,
    point_claims: [QM31; 3],
    terminal_claim: QM31,
    ood_values: [[QM31; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT],
    sumchecks: [SumcheckPolynomial; CANDIDATE_ROUND_COUNT],
    running_claims: [QM31; CANDIDATE_ROUND_COUNT + 1],
    running_claim: QM31,
    round: usize,
    samples: usize,
}

fn add_relation_point_claim(
    coefficients: &[QM31],
    weights: &mut WeightAccumulator,
    point: &[QM31],
    point_scale: QM31,
    running_claim: QM31,
) -> Result<(QM31, QM31), V5RelationProverError> {
    let mut evaluation = WeightAccumulator::empty(FIXED_TRACE_LOG_SIZE);
    evaluation.add_multilinear(QM31::ONE, point.to_vec())?;
    let point_claim = evaluation.dot(coefficients);
    weights.add_multilinear(point_scale, point.to_vec())?;
    Ok((point_claim, running_claim.add(point_scale.mul(point_claim))))
}

fn add_initial_point_claims(
    coefficients: &[QM31],
    points: &[[QM31; FIXED_TRACE_LOG_SIZE as usize]; 3],
    point_scales: [QM31; 3],
    inactive_claim: QM31,
) -> Result<(WeightAccumulator, [QM31; 3], QM31), V5RelationProverError> {
    let mut weights = WeightAccumulator::empty(FIXED_TRACE_LOG_SIZE);
    let mut point_claims = [QM31::ZERO; 3];
    let mut running_claim = inactive_claim;
    (point_claims[0], running_claim) = add_relation_point_claim(
        coefficients,
        &mut weights,
        &points[0],
        point_scales[0],
        running_claim,
    )?;
    (point_claims[1], running_claim) = add_relation_point_claim(
        coefficients,
        &mut weights,
        &points[1],
        point_scales[1],
        running_claim,
    )?;
    (point_claims[2], running_claim) = add_relation_point_claim(
        coefficients,
        &mut weights,
        &points[2],
        point_scales[2],
        running_claim,
    )?;
    Ok((weights, point_claims, running_claim))
}

fn add_terminal_claim(
    coefficients: &[QM31],
    weights: &mut WeightAccumulator,
    terminal_covector: &[QM31],
    terminal_scale: QM31,
    running_claim: QM31,
) -> Result<(QM31, QM31), V5RelationProverError> {
    let mut scaled_covector = Vec::with_capacity(terminal_covector.len());
    let mut terminal_claim = QM31::ZERO;
    let mut row = 0usize;
    while row < terminal_covector.len() {
        let weight = terminal_covector[row];
        scaled_covector.push(terminal_scale.mul(weight));
        terminal_claim = terminal_claim.add(weight.mul(coefficients[row]));
        row += 1;
    }
    weights.add_dense(scaled_covector)?;
    Ok((
        terminal_claim,
        running_claim.add(terminal_scale.mul(terminal_claim)),
    ))
}

impl V5IncrementalRelation {
    fn materialize_weights(weights: &WeightAccumulator, len: usize) -> Vec<QM31> {
        let mut table = Vec::with_capacity(len);
        let mut index = 0usize;
        while index < len {
            table.push(weights.weight_at(index as u32));
            index += 1;
        }
        table
    }

    fn materialized_dot(coefficients: &[QM31], table: &[QM31]) -> QM31 {
        debug_assert_eq!(coefficients.len(), table.len());
        let mut total = QM31::ZERO;
        let mut index = 0usize;
        while index < coefficients.len() {
            total = total.add(coefficients[index].mul(table[index]));
            index += 1;
        }
        total
    }

    fn materialized_polynomial(coefficients: &[QM31], table: &[QM31]) -> SumcheckPolynomial {
        debug_assert_eq!(coefficients.len(), table.len());
        debug_assert_eq!(coefficients.len() & 3, 0);
        let mut output = [QM31::ZERO; 7];
        let mut base = 0usize;
        while base < coefficients.len() {
            let dual = [
                table[base],
                table[base + 3],
                table[base + 2],
                table[base + 1],
            ];
            let mut a_degree = 0usize;
            while a_degree < 4 {
                let mut b_degree = 0usize;
                while b_degree < 4 {
                    output[a_degree + b_degree] = output[a_degree + b_degree].add(
                        coefficients[base + a_degree]
                            .mul(dual[b_degree])
                            .mul_m31(M31_QUARTER),
                    );
                    b_degree += 1;
                }
                a_degree += 1;
            }
            base += 4;
        }
        output
    }

    #[allow(clippy::too_many_arguments)]
    pub fn new(
        coefficients: Vec<QM31>,
        points: &[[QM31; FIXED_TRACE_LOG_SIZE as usize]; 3],
        point_scales: [QM31; 3],
        inactive_masks: [u16; 64],
        inactive_claim: QM31,
        terminal_covector: &[QM31],
        terminal_scale: QM31,
    ) -> Result<Self, V5RelationProverError> {
        if coefficients.len() != TRACE_LEN {
            return Err(V5RelationProverError::MessageLength {
                expected: TRACE_LEN,
                actual: coefficients.len(),
            });
        }
        if terminal_covector.len() != TRACE_LEN {
            return Err(V5RelationProverError::CovectorLength {
                expected: TRACE_LEN,
                actual: terminal_covector.len(),
            });
        }
        let mut actual_inactive_claim = QM31::ZERO;
        let mut row = 0usize;
        while row < coefficients.len() {
            if inactive_masks[row >> 4] & (1 << (row & 15)) != 0 {
                actual_inactive_claim = actual_inactive_claim.add(coefficients[row]);
            }
            row += 1;
        }
        if actual_inactive_claim != inactive_claim {
            return Err(V5RelationProverError::InactiveClaimMismatch);
        }

        let (mut weights, point_claims, running_claim) =
            add_initial_point_claims(&coefficients, points, point_scales, inactive_claim)?;
        weights.add_grouped_64x16_binary_masks_deferred(inactive_masks)?;
        let (terminal_claim, running_claim) = add_terminal_claim(
            &coefficients,
            &mut weights,
            terminal_covector,
            terminal_scale,
            running_claim,
        )?;
        let mut running_claims = [QM31::ZERO; CANDIDATE_ROUND_COUNT + 1];
        running_claims[0] = running_claim;

        Ok(Self {
            coefficients,
            weights,
            point_claims,
            terminal_claim,
            ood_values: [[QM31::ZERO; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT],
            sumchecks: [[QM31::ZERO; 7]; CANDIDATE_ROUND_COUNT],
            running_claims,
            running_claim,
            round: 0,
            samples: 0,
        })
    }

    pub fn evaluate_circle_ood(
        &self,
        point: SecureCirclePoint,
    ) -> Result<QM31, V5RelationProverError> {
        let (value, _) = self.evaluate_circle_ood_with_table(point)?;
        Ok(value)
    }

    pub fn evaluate_circle_ood_with_table(
        &self,
        point: SecureCirclePoint,
    ) -> Result<(QM31, Vec<QM31>), V5RelationProverError> {
        if self.round != 0 || self.samples >= CANDIDATE_OOD_SAMPLES {
            return Err(V5RelationProverError::OodOrder);
        }
        let mut evaluation = WeightAccumulator::empty(FIXED_TRACE_LOG_SIZE);
        evaluation.add_circle_tensor(QM31::ONE, point)?;
        let table = Self::materialize_weights(&evaluation, self.coefficients.len());
        Ok((Self::materialized_dot(&self.coefficients, &table), table))
    }

    pub fn add_circle_ood(
        &mut self,
        point: SecureCirclePoint,
        value: QM31,
        mix: QM31,
    ) -> Result<(), V5RelationProverError> {
        if self.round != 0 || self.samples >= CANDIDATE_OOD_SAMPLES {
            return Err(V5RelationProverError::OodOrder);
        }
        self.weights.add_circle_tensor(mix, point)?;
        self.ood_values[0][self.samples] = value;
        self.running_claim = self.running_claim.add(mix.mul(value));
        self.samples += 1;
        Ok(())
    }

    pub fn evaluate_line_ood(&self, point: QM31) -> Result<QM31, V5RelationProverError> {
        let (value, _) = self.evaluate_line_ood_with_table(point)?;
        Ok(value)
    }

    pub fn evaluate_line_ood_with_table(
        &self,
        point: QM31,
    ) -> Result<(QM31, Vec<QM31>), V5RelationProverError> {
        if self.round == 0
            || self.round >= CANDIDATE_ROUND_COUNT
            || self.samples >= CANDIDATE_OOD_SAMPLES
        {
            return Err(V5RelationProverError::OodOrder);
        }
        let mut evaluation = WeightAccumulator::empty(FIXED_TRACE_LOG_SIZE - 2 * self.round as u32);
        evaluation.add_line_tensor(QM31::ONE, point)?;
        let table = Self::materialize_weights(&evaluation, self.coefficients.len());
        Ok((Self::materialized_dot(&self.coefficients, &table), table))
    }

    pub fn add_line_ood(
        &mut self,
        point: QM31,
        value: QM31,
        mix: QM31,
    ) -> Result<(), V5RelationProverError> {
        if self.round == 0
            || self.round >= CANDIDATE_ROUND_COUNT
            || self.samples >= CANDIDATE_OOD_SAMPLES
        {
            return Err(V5RelationProverError::OodOrder);
        }
        self.weights.add_line_tensor(mix, point)?;
        self.ood_values[self.round][self.samples] = value;
        self.running_claim = self.running_claim.add(mix.mul(value));
        self.samples += 1;
        Ok(())
    }

    pub fn polynomial(&mut self) -> Result<SumcheckPolynomial, V5RelationProverError> {
        let (polynomial, _) = self.polynomial_with_table()?;
        Ok(polynomial)
    }

    pub fn polynomial_with_table(
        &mut self,
    ) -> Result<(SumcheckPolynomial, Vec<QM31>), V5RelationProverError> {
        if self.round >= CANDIDATE_ROUND_COUNT || self.samples != CANDIDATE_OOD_SAMPLES {
            return Err(V5RelationProverError::RoundOrder);
        }
        let table = Self::materialize_weights(&self.weights, self.coefficients.len());
        let polynomial = Self::materialized_polynomial(&self.coefficients, &table);
        if boundary_sum(&polynomial) != self.running_claim {
            return Err(V5RelationProverError::BoundaryMismatch);
        }
        self.sumchecks[self.round] = polynomial;
        Ok((polynomial, table))
    }

    pub fn fold(&mut self, alpha: QM31) -> Result<(), V5RelationProverError> {
        if self.round >= CANDIDATE_ROUND_COUNT || self.samples != CANDIDATE_OOD_SAMPLES {
            return Err(V5RelationProverError::RoundOrder);
        }
        self.running_claim = evaluate(&self.sumchecks[self.round], alpha);
        self.running_claims[self.round + 1] = self.running_claim;
        self.weights.fold_deferred_relation_arity4(alpha);
        self.coefficients = fold_adjacent_natural_arity4(&self.coefficients, alpha);
        if self.weights.dot(&self.coefficients) != self.running_claim {
            return Err(V5RelationProverError::FoldMismatch);
        }
        self.round += 1;
        self.samples = 0;
        Ok(())
    }

    pub fn finish(self) -> Result<V5RelationTrace, V5RelationProverError> {
        if self.round != CANDIDATE_ROUND_COUNT
            || self.samples != 0
            || self.coefficients.len() != CANDIDATE_FINAL_POLY_LEN
        {
            return Err(V5RelationProverError::Incomplete);
        }
        let final_coefficients: [QM31; CANDIDATE_FINAL_POLY_LEN] = self
            .coefficients
            .as_slice()
            .try_into()
            .map_err(|_| V5RelationProverError::Incomplete)?;
        if self.weights.dot(&final_coefficients) != self.running_claim {
            return Err(V5RelationProverError::FoldMismatch);
        }
        Ok(V5RelationTrace {
            point_claims: self.point_claims,
            terminal_claim: self.terminal_claim,
            ood_values: self.ood_values,
            sumchecks: self.sumchecks,
            running_claims: self.running_claims,
            final_coefficients,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_core::field::{CM31, M31};

    fn q(value: u32) -> QM31 {
        QM31::from_cm31(CM31::from_m31(M31(value)))
    }

    #[test]
    fn materialized_relation_arithmetic_matches_accumulator() {
        for log_len in [10u32, 8, 6, 4] {
            let len = 1usize << log_len;
            let values = (0..len).map(|i| q(i as u32 + 3)).collect::<Vec<_>>();
            let mut weights = WeightAccumulator::empty(log_len);
            weights
                .add_multilinear(q(7), (0..log_len).map(|i| q(i + 11)).collect())
                .unwrap();
            let table = V5IncrementalRelation::materialize_weights(&weights, len);
            assert_eq!(
                V5IncrementalRelation::materialized_dot(&values, &table),
                weights.dot(&values)
            );
            assert_eq!(
                V5IncrementalRelation::materialized_polynomial(&values, &table),
                aspis_core::sumcheck::polynomial_for_extension(&values, &weights)
            );
        }
    }

    #[test]
    fn honest_four_claim_relation_reaches_its_final_dot() {
        let coefficients = (0..TRACE_LEN).map(|row| q(row as u32 + 1)).collect();
        let points = [
            core::array::from_fn(|i| q(i as u32 + 2)),
            core::array::from_fn(|i| q(i as u32 + 17)),
            core::array::from_fn(|i| q(i as u32 + 37)),
        ];
        let covector = (0..TRACE_LEN)
            .map(|row| if row & 7 == 0 { q(3) } else { QM31::ZERO })
            .collect::<Vec<_>>();
        let mut relation = V5IncrementalRelation::new(
            coefficients,
            &points,
            [QM31::ONE, q(5), q(25)],
            [0u16; 64],
            QM31::ZERO,
            &covector,
            q(125),
        )
        .unwrap();
        for round in 0..CANDIDATE_ROUND_COUNT {
            for sample in 0..CANDIDATE_OOD_SAMPLES {
                if round == 0 {
                    let point = SecureCirclePoint {
                        x: if sample == 0 { QM31::ONE } else { QM31::ZERO },
                        y: if sample == 0 { QM31::ZERO } else { QM31::ONE },
                    };
                    let value = relation.evaluate_circle_ood(point).unwrap();
                    relation
                        .add_circle_ood(point, value, q(7 + sample as u32))
                        .unwrap();
                } else {
                    let point = q(11 + (2 * round + sample) as u32);
                    let value = relation.evaluate_line_ood(point).unwrap();
                    relation
                        .add_line_ood(point, value, q(19 + sample as u32))
                        .unwrap();
                }
            }
            relation.polynomial().unwrap();
            relation.fold(q(29 + round as u32)).unwrap();
        }
        let trace = relation.finish().unwrap();
        assert_eq!(trace.final_coefficients.len(), CANDIDATE_FINAL_POLY_LEN);
        assert_eq!(trace.running_claims.len(), CANDIDATE_ROUND_COUNT + 1);
    }
}
