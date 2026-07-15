//! Sequential three-point OOD/fold relation for the state-only profile.

use aspis_core::circle::SecureCirclePoint;
use aspis_core::circle_fri::FIXED_TRACE_LOG_SIZE;
use aspis_core::circle_prefix::{
    CANDIDATE_FINAL_POLY_LEN, CANDIDATE_OOD_SAMPLES, CANDIDATE_ROUND_COUNT,
};
use aspis_core::field::QM31;
use aspis_core::state_only_masked_switch_basis::{
    masked_switch_logical_to_natural, MASKED_SWITCH_UNIVERSAL_DIMENSION,
};
use aspis_core::sumcheck::{
    boundary_sum, evaluate, polynomial_for_extension, SumcheckPolynomial, WeightAccumulator,
};
use aspis_statement::state_only_copy_inactive_row_masks_v4;
#[cfg(test)]
use aspis_statement::{state_only_copy_active_rows_v4, state_only_copy_inactive_indicator_v4};

use crate::circle_candidate::CandidatePrefixBuildError;
use crate::circle_candidate::{fold_adjacent_natural_arity4, TRACE_LEN};

pub const STATE_ONLY_RELATION_POINT_COUNT: usize = 3;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StateOnlyCircleRelationTrace {
    pub point_claims: [QM31; STATE_ONLY_RELATION_POINT_COUNT],
    pub ood_values: [[QM31; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT],
    pub boundary_claims: [QM31; CANDIDATE_ROUND_COUNT],
    pub sumchecks: [SumcheckPolynomial; CANDIDATE_ROUND_COUNT],
    pub running_claims: [QM31; CANDIDATE_ROUND_COUNT + 1],
    pub final_coefficients: [QM31; CANDIDATE_FINAL_POLY_LEN],
    pub terminal_claim: QM31,
}

pub struct StateOnlyIncrementalRelation {
    coefficients: Vec<QM31>,
    weights: WeightAccumulator,
    point_claims: [QM31; STATE_ONLY_RELATION_POINT_COUNT],
    ood_values: [[QM31; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT],
    boundary_claims: [QM31; CANDIDATE_ROUND_COUNT],
    sumchecks: [SumcheckPolynomial; CANDIDATE_ROUND_COUNT],
    running_claims: [QM31; CANDIDATE_ROUND_COUNT + 1],
    running_claim: QM31,
    round: usize,
    samples: usize,
}

fn volatile_clear_qm31(values: &mut [QM31]) {
    for value in values {
        // SAFETY: relation storage is uniquely borrowed during drop.
        unsafe { core::ptr::write_volatile(value, QM31::ZERO) };
    }
    core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
}

impl Drop for StateOnlyIncrementalRelation {
    fn drop(&mut self) {
        volatile_clear_qm31(&mut self.coefficients);
        volatile_clear_qm31(&mut self.point_claims);
        for values in &mut self.ood_values {
            volatile_clear_qm31(values);
        }
        volatile_clear_qm31(&mut self.boundary_claims);
        for polynomial in &mut self.sumchecks {
            volatile_clear_qm31(polynomial);
        }
        volatile_clear_qm31(&mut self.running_claims);
        volatile_clear_qm31(core::slice::from_mut(&mut self.running_claim));
        self.round = 0;
        self.samples = 0;
    }
}

impl StateOnlyIncrementalRelation {
    pub fn new(
        coefficients: Vec<QM31>,
        points: &[[QM31; FIXED_TRACE_LOG_SIZE as usize]; STATE_ONLY_RELATION_POINT_COUNT],
        point_scales: [QM31; STATE_ONLY_RELATION_POINT_COUNT],
    ) -> Result<Self, CandidatePrefixBuildError> {
        Self::new_with_inactive_masks(
            coefficients,
            points,
            point_scales,
            state_only_copy_inactive_row_masks_v4(),
        )
    }

    pub fn new_with_inactive_masks(
        coefficients: Vec<QM31>,
        points: &[[QM31; FIXED_TRACE_LOG_SIZE as usize]; STATE_ONLY_RELATION_POINT_COUNT],
        point_scales: [QM31; STATE_ONLY_RELATION_POINT_COUNT],
        inactive_masks: [u16; 64],
    ) -> Result<Self, CandidatePrefixBuildError> {
        Self::new_with_inactive_masks_and_claim(
            coefficients,
            points,
            point_scales,
            inactive_masks,
            QM31::ZERO,
        )
    }

    /// Construct the same relation with an explicitly carried copy-inactive
    /// target. Production trace masks use target zero; physically bound
    /// unbalanced auxiliary words instead serialize this target before their
    /// PCS group separator is sampled.
    pub fn new_with_inactive_masks_and_claim(
        coefficients: Vec<QM31>,
        points: &[[QM31; FIXED_TRACE_LOG_SIZE as usize]; STATE_ONLY_RELATION_POINT_COUNT],
        point_scales: [QM31; STATE_ONLY_RELATION_POINT_COUNT],
        inactive_masks: [u16; 64],
        inactive_claim: QM31,
    ) -> Result<Self, CandidatePrefixBuildError> {
        if coefficients.len() != TRACE_LEN {
            return Err(CandidatePrefixBuildError::Consistency(
                "state-only combined message has the wrong length",
            ));
        }
        let actual_inactive_claim =
            coefficients
                .iter()
                .copied()
                .enumerate()
                .fold(QM31::ZERO, |sum, (row, value)| {
                    if inactive_masks[row >> 4] & (1 << (row & 15)) == 0 {
                        sum
                    } else {
                        sum.add(value)
                    }
                });
        if actual_inactive_claim != inactive_claim {
            return Err(CandidatePrefixBuildError::Consistency(
                "state-only combined copy-inactive claim mismatches its carried target",
            ));
        }
        let mut weights = WeightAccumulator::empty(FIXED_TRACE_LOG_SIZE);
        let mut point_claims = [QM31::ZERO; STATE_ONLY_RELATION_POINT_COUNT];
        let mut running_claim = inactive_claim;
        for index in 0..STATE_ONLY_RELATION_POINT_COUNT {
            let mut evaluation = WeightAccumulator::empty(FIXED_TRACE_LOG_SIZE);
            evaluation.add_multilinear(QM31::ONE, points[index].to_vec())?;
            point_claims[index] = evaluation.dot(&coefficients);
            weights.add_multilinear(point_scales[index], points[index].to_vec())?;
            running_claim = running_claim.add(point_scales[index].mul(point_claims[index]));
        }
        weights.add_grouped_64x16_binary_masks(inactive_masks)?;
        let mut running_claims = [QM31::ZERO; CANDIDATE_ROUND_COUNT + 1];
        running_claims[0] = running_claim;
        Ok(Self {
            coefficients,
            weights,
            point_claims,
            ood_values: [[QM31::ZERO; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT],
            boundary_claims: [QM31::ZERO; CANDIDATE_ROUND_COUNT],
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
    ) -> Result<QM31, CandidatePrefixBuildError> {
        if self.round != 0 || self.samples >= CANDIDATE_OOD_SAMPLES {
            return Err(CandidatePrefixBuildError::Consistency(
                "state-only circle OOD requested out of order",
            ));
        }
        let mut evaluation = WeightAccumulator::empty(FIXED_TRACE_LOG_SIZE);
        evaluation.add_circle_tensor(QM31::ONE, point)?;
        Ok(evaluation.dot(&self.coefficients))
    }

    pub fn add_circle_ood(
        &mut self,
        point: SecureCirclePoint,
        value: QM31,
        mix: QM31,
    ) -> Result<(), CandidatePrefixBuildError> {
        self.weights.add_circle_tensor(mix, point)?;
        self.ood_values[0][self.samples] = value;
        self.running_claim = self.running_claim.add(mix.mul(value));
        self.samples += 1;
        Ok(())
    }

    pub fn evaluate_line_ood(&self, x: QM31) -> Result<QM31, CandidatePrefixBuildError> {
        if self.round == 0
            || self.round >= CANDIDATE_ROUND_COUNT
            || self.samples >= CANDIDATE_OOD_SAMPLES
        {
            return Err(CandidatePrefixBuildError::Consistency(
                "state-only line OOD requested out of order",
            ));
        }
        let mut evaluation = WeightAccumulator::empty(FIXED_TRACE_LOG_SIZE - 2 * self.round as u32);
        evaluation.add_line_tensor(QM31::ONE, x)?;
        Ok(evaluation.dot(&self.coefficients))
    }

    pub fn add_line_ood(
        &mut self,
        x: QM31,
        value: QM31,
        mix: QM31,
    ) -> Result<(), CandidatePrefixBuildError> {
        self.weights.add_line_tensor(mix, x)?;
        self.ood_values[self.round][self.samples] = value;
        self.running_claim = self.running_claim.add(mix.mul(value));
        self.samples += 1;
        Ok(())
    }

    pub fn polynomial(&mut self) -> Result<SumcheckPolynomial, CandidatePrefixBuildError> {
        if self.samples != CANDIDATE_OOD_SAMPLES {
            return Err(CandidatePrefixBuildError::Consistency(
                "state-only relation sumcheck built before both OOD samples",
            ));
        }
        let polynomial = polynomial_for_extension(&self.coefficients, &self.weights);
        if boundary_sum(&polynomial) != self.running_claim {
            return Err(CandidatePrefixBuildError::Consistency(
                "state-only relation boundary mismatch",
            ));
        }
        self.boundary_claims[self.round] = self.running_claim;
        self.sumchecks[self.round] = polynomial;
        Ok(polynomial)
    }

    pub fn fold(&mut self, alpha: QM31) -> Result<(), CandidatePrefixBuildError> {
        if self.samples != CANDIDATE_OOD_SAMPLES || self.round >= CANDIDATE_ROUND_COUNT {
            return Err(CandidatePrefixBuildError::Consistency(
                "state-only relation fold requested out of order",
            ));
        }
        self.running_claim = evaluate(&self.sumchecks[self.round], alpha);
        self.running_claims[self.round + 1] = self.running_claim;
        self.weights.fold(alpha);
        self.coefficients = fold_adjacent_natural_arity4(&self.coefficients, alpha);
        if self.weights.dot(&self.coefficients) != self.running_claim {
            return Err(CandidatePrefixBuildError::Consistency(
                "state-only folded relation dot mismatch",
            ));
        }
        self.round += 1;
        self.samples = 0;
        Ok(())
    }

    /// Exact profile-21 seam immediately after the circle-to-line fold.
    /// Injects the disclosed natural U polynomial into the committed root-one
    /// word and returns its complete folded-relation target, including all
    /// sixteen randomness coordinates.
    pub fn inject_profile21_first_later_u(
        &mut self,
        logical_u: &[QM31; MASKED_SWITCH_UNIVERSAL_DIMENSION],
    ) -> Result<QM31, CandidatePrefixBuildError> {
        if self.round != 1 || self.samples != 0 || self.coefficients.len() != TRACE_LEN / 4 {
            return Err(CandidatePrefixBuildError::Consistency(
                "profile21 U injection requested outside the first later seam",
            ));
        }
        let natural_u = masked_switch_logical_to_natural(logical_u);
        let target = natural_u
            .iter()
            .copied()
            .enumerate()
            .fold(QM31::ZERO, |sum, (index, value)| {
                sum.add(self.weights.weight_at(index as u32).mul(value))
            });
        for (coefficient, value) in self.coefficients.iter_mut().zip(natural_u) {
            *coefficient = coefficient.add(value);
        }
        self.running_claim = self.running_claim.add(target);
        self.running_claims[self.round] = self.running_claim;
        if self.weights.dot(&self.coefficients) != self.running_claim {
            return Err(CandidatePrefixBuildError::Consistency(
                "profile21 U injection changed the folded relation target",
            ));
        }
        Ok(target)
    }

    /// Evaluate the complete post-alpha relation target of one logical source
    /// word without mutating the relation. This is used before delta to bind
    /// the two scalar claims `tX` and `muF`.
    pub fn profile21_first_later_full_target(
        &self,
        logical: &[QM31; MASKED_SWITCH_UNIVERSAL_DIMENSION],
    ) -> Result<QM31, CandidatePrefixBuildError> {
        if self.round != 1 || self.samples != 0 || self.coefficients.len() != TRACE_LEN / 4 {
            return Err(CandidatePrefixBuildError::Consistency(
                "profile21 full target requested outside the first later seam",
            ));
        }
        Ok(masked_switch_logical_to_natural(logical)
            .iter()
            .copied()
            .enumerate()
            .fold(QM31::ZERO, |sum, (index, value)| {
                sum.add(self.weights.weight_at(index as u32).mul(value))
            }))
    }

    pub fn finish(self) -> Result<StateOnlyCircleRelationTrace, CandidatePrefixBuildError> {
        if self.round != CANDIDATE_ROUND_COUNT
            || self.coefficients.len() != CANDIDATE_FINAL_POLY_LEN
        {
            return Err(CandidatePrefixBuildError::Consistency(
                "state-only relation did not reach terminal",
            ));
        }
        let final_coefficients: [QM31; CANDIDATE_FINAL_POLY_LEN] =
            self.coefficients.as_slice().try_into().map_err(|_| {
                CandidatePrefixBuildError::Consistency("terminal conversion failed")
            })?;
        let terminal_claim = self.weights.dot(&final_coefficients);
        if terminal_claim != self.running_claim {
            return Err(CandidatePrefixBuildError::Consistency(
                "state-only terminal relation dot mismatch",
            ));
        }
        Ok(StateOnlyCircleRelationTrace {
            point_claims: self.point_claims,
            ood_values: self.ood_values,
            boundary_claims: self.boundary_claims,
            sumchecks: self.sumchecks,
            running_claims: self.running_claims,
            final_coefficients,
            terminal_claim,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_core::field::{CM31, M31};

    fn q(seed: u32) -> QM31 {
        QM31 {
            c0: CM31::new(M31(seed), M31(seed + 1)),
            c1: CM31::new(M31(seed + 2), M31(seed + 3)),
        }
    }

    #[test]
    fn copy_inactive_registry_is_a_mandatory_zero_claim() {
        let points = [[QM31::ZERO; FIXED_TRACE_LOG_SIZE as usize]; STATE_ONLY_RELATION_POINT_COUNT];
        let scales = [QM31::ONE; STATE_ONLY_RELATION_POINT_COUNT];
        let mut balanced = vec![QM31::ZERO; TRACE_LEN];
        let inactive_indicator = state_only_copy_inactive_indicator_v4();
        let mut inactive_rows = inactive_indicator
            .iter()
            .enumerate()
            .filter_map(|(row, weight)| (*weight == QM31::ONE).then_some(row));
        let first_inactive = inactive_rows.next().unwrap();
        let second_inactive = inactive_rows.next().unwrap();
        balanced[first_inactive] = QM31::ONE;
        balanced[second_inactive] = QM31::ZERO.sub(QM31::ONE);
        assert!(StateOnlyIncrementalRelation::new(balanced, &points, scales).is_ok());

        let mut unbalanced = vec![QM31::ZERO; TRACE_LEN];
        unbalanced[first_inactive] = QM31::ONE;
        assert!(matches!(
            StateOnlyIncrementalRelation::new(unbalanced, &points, scales),
            Err(CandidatePrefixBuildError::Consistency(
                "state-only combined copy-inactive claim mismatches its carried target"
            ))
        ));

        // A malicious active-row discrepancy cannot be hidden by an equal
        // and opposite inactive helper value. The global helper sum would
        // still be zero, but the exact generated inactive-row claim rejects
        // it.
        let mut cancelled = vec![QM31::ZERO; TRACE_LEN];
        let active = usize::from(state_only_copy_active_rows_v4()[0]);
        let inactive_prefix = inactive_indicator
            .iter()
            .position(|weight| *weight == QM31::ONE)
            .unwrap();
        cancelled[active] = QM31::ONE;
        cancelled[inactive_prefix] = QM31::ZERO.sub(QM31::ONE);
        assert_eq!(
            cancelled.iter().copied().fold(QM31::ZERO, QM31::add),
            QM31::ZERO
        );
        assert!(matches!(
            StateOnlyIncrementalRelation::new(cancelled, &points, scales),
            Err(CandidatePrefixBuildError::Consistency(
                "state-only combined copy-inactive claim mismatches its carried target"
            ))
        ));
    }

    #[test]
    fn profile21_prover_injection_matches_full_relation_target_and_finishes() {
        let points: [[QM31; FIXED_TRACE_LOG_SIZE as usize]; STATE_ONLY_RELATION_POINT_COUNT] =
            core::array::from_fn(|point| {
                core::array::from_fn(|coordinate| q(101 + 41 * point as u32 + coordinate as u32))
            });
        let scales = [QM31::ONE, q(401), q(401).square()];
        let inactive_masks =
            aspis_statement::atomic_state_only_terminal::atomic_state_only_copy_inactive_row_masks_v3();
        let mut relation = StateOnlyIncrementalRelation::new_with_inactive_masks(
            vec![QM31::ZERO; TRACE_LEN],
            &points,
            scales,
            inactive_masks,
        )
        .unwrap();

        let circle_points = [
            SecureCirclePoint {
                x: q(701),
                y: q(709),
            },
            SecureCirclePoint {
                x: q(719),
                y: q(727),
            },
        ];
        let circle_mixes = [q(733), q(739)];
        for sample in 0..CANDIDATE_OOD_SAMPLES {
            let value = relation.evaluate_circle_ood(circle_points[sample]).unwrap();
            relation
                .add_circle_ood(circle_points[sample], value, circle_mixes[sample])
                .unwrap();
        }
        relation.polynomial().unwrap();
        let alpha0 = q(751);
        relation.fold(alpha0).unwrap();

        let logical_u = core::array::from_fn(|index| q(809 + 11 * index as u32));
        let precomputed_target = relation
            .profile21_first_later_full_target(&logical_u)
            .unwrap();
        let injected_target = relation.inject_profile21_first_later_u(&logical_u).unwrap();
        assert_eq!(injected_target, precomputed_target);

        // Independent verifier construction: deferred masks, same exact OOD
        // components, then the circle-to-line fold.
        let mut verifier_weights = WeightAccumulator::empty(FIXED_TRACE_LOG_SIZE);
        for point in 0..STATE_ONLY_RELATION_POINT_COUNT {
            verifier_weights
                .add_multilinear(scales[point], points[point].to_vec())
                .unwrap();
        }
        verifier_weights
            .add_grouped_64x16_binary_masks_deferred(inactive_masks)
            .unwrap();
        for sample in 0..CANDIDATE_OOD_SAMPLES {
            verifier_weights
                .add_circle_tensor(circle_mixes[sample], circle_points[sample])
                .unwrap();
        }
        verifier_weights.fold(alpha0);
        let natural_u = masked_switch_logical_to_natural(&logical_u);
        assert_eq!(
            injected_target,
            natural_u
                .iter()
                .copied()
                .enumerate()
                .fold(QM31::ZERO, |sum, (index, value)| {
                    sum.add(verifier_weights.weight_at(index as u32).mul(value))
                })
        );

        // The injected full natural polynomial survives every remaining
        // prover fold and reaches the exact terminal dot relation.
        for round in 1..CANDIDATE_ROUND_COUNT {
            for sample in 0..CANDIDATE_OOD_SAMPLES {
                let x = q(1_301 + 31 * round as u32 + sample as u32);
                let mix = q(1_701 + 37 * round as u32 + sample as u32);
                let value = relation.evaluate_line_ood(x).unwrap();
                relation.add_line_ood(x, value, mix).unwrap();
            }
            relation.polynomial().unwrap();
            relation.fold(q(2_003 + 43 * round as u32)).unwrap();
        }
        relation.finish().unwrap();
    }
}
