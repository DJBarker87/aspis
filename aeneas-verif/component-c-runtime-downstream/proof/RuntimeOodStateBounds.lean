import RuntimeOodWithTableArithmetic

set_option autoImplicit false

open Aeneas Aeneas.Std Result

namespace aspis_prover.ComponentCRuntimeOodStateBounds

open aspis_prover

abbrev RawQM31 := aspis_core.field.QM31
abbrev RuntimeRelation :=
  v5_mask.relation_prover.V5IncrementalRelation

theorem generated_circle_ood_success_state_bounds
    (relation : RuntimeRelation)
    (point : aspis_core.circle.SecureCirclePoint)
    (value : RawQM31) (table : alloc.vec.Vec RawQM31)
    (hrun :
      v5_mask.relation_prover.V5IncrementalRelation.evaluate_circle_ood_with_table
          relation point = ok (core.result.Result.Ok (value, table))) :
    relation.round = 0#usize ∧ relation.samples.val < 2 := by
  unfold
    v5_mask.relation_prover.V5IncrementalRelation.evaluate_circle_ood_with_table
    at hrun
  by_cases hround : relation.round != 0#usize
  · simp [hround] at hrun
  · have hroundEq : relation.round = 0#usize := by
      by_contra hne
      apply hround
      simpa [hne]
    by_cases hsamples :
        relation.samples >= aspis_core.circle_prefix.CANDIDATE_OOD_SAMPLES
    · simp [hround, hsamples] at hrun
    · refine ⟨hroundEq, ?_⟩
      simp only [aspis_core.circle_prefix.CANDIDATE_OOD_SAMPLES] at hsamples
      scalar_tac

theorem generated_line_ood_success_state_bounds
    (relation : RuntimeRelation) (point value : RawQM31)
    (table : alloc.vec.Vec RawQM31)
    (hrun :
      v5_mask.relation_prover.V5IncrementalRelation.evaluate_line_ood_with_table
          relation point = ok (core.result.Result.Ok (value, table))) :
    relation.round ≠ 0#usize ∧ relation.round.val < 4 ∧
      relation.samples.val < 2 := by
  unfold
    v5_mask.relation_prover.V5IncrementalRelation.evaluate_line_ood_with_table
    at hrun
  by_cases hzero : relation.round = 0#usize
  · simp [hzero] at hrun
  · by_cases hround :
        relation.round >= aspis_core.circle_prefix.CANDIDATE_ROUND_COUNT
    · simp [hzero, hround] at hrun
    · by_cases hsamples :
          relation.samples >= aspis_core.circle_prefix.CANDIDATE_OOD_SAMPLES
      · simp [hzero, hround, hsamples] at hrun
      · refine ⟨hzero, ?_, ?_⟩
        · simp only [aspis_core.circle_prefix.CANDIDATE_ROUND_COUNT] at hround
          scalar_tac
        · simp only [aspis_core.circle_prefix.CANDIDATE_OOD_SAMPLES]
            at hsamples
          scalar_tac

#print axioms generated_circle_ood_success_state_bounds
#print axioms generated_line_ood_success_state_bounds

end aspis_prover.ComponentCRuntimeOodStateBounds
