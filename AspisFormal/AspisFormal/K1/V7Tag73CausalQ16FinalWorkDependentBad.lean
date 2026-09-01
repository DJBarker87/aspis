import AspisFormal.K1.V7Tag73CausalQ16FinalWorkProbability

/-!
# Final-work-dependent q16 bad sets

The final 34-bit work answer is exposed before the q16 forest.  Therefore the
semantic q16 consistency set may causally depend on that already-exposed work
answer without weakening either factor in the joint probability bound.  This
module proves the exact finite product statement rather than requiring the bad
set to be fixed before the work answer is sampled.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73CausalQ16FinalWorkDependentBad

open MeasureTheory
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CausalQ16FinalWorkProbability
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73FinalWorkDigestProbability
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73Q16CompactScheduleCount
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisK1.V7Tag73Q16RawENNRealProbability
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73Q16SuccessfulForestBridge
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

local instance finalWork34AcceptedDecidable (work : Digest256) :
    Decidable (FinalWork34Accepted work) :=
  Classical.propDecidable _

/-- The successful joint event when the q16 consistency set is allowed to
depend on the already-exposed final-work answer. -/
def finalWorkQ16SuccessfulDependentBadEvent
    (bad : Digest256 → Finset (Fin 262144)) :
    Set (Digest256 × SuccessfulQ16Coordinates) :=
  {coordinates |
    FinalWork34Accepted coordinates.1 ∧
      coordinates.2 ∈ q16SuccessfulCoordinatesBadEvent (bad coordinates.1)}

theorem product_slice_final_work_q16_dependent_bad
    (bad : Digest256 → Finset (Fin 262144)) (work : Digest256) :
    productEventFstSlice
        (finalWorkQ16SuccessfulDependentBadEvent bad) work =
      if FinalWork34Accepted work then
        q16SuccessfulCoordinatesBadEvent (bad work)
      else ∅ := by
  ext coordinates
  by_cases accepted : FinalWork34Accepted work <;>
    simp [productEventFstSlice,
      finalWorkQ16SuccessfulDependentBadEvent, accepted]

/-- Conditioning on the work answer does not cost the 34-bit work factor:
every accepted work-answer slice has the same q16 cap, while every rejected
slice is empty. -/
theorem uniform_final_work_q16_dependent_bad_probability_le_semantic
    [Nonempty SuccessfulQ16Coordinates]
    (bad : Digest256 → Finset (Fin 262144))
    (badCard : ∀ work, (bad work).card ≤ 9557)
    (reference : AdmittedResult SemanticCap203Admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        reference.1)) :
    (PMF.uniformOfFintype
      (Digest256 × SuccessfulQ16Coordinates)).toOuterMeasure
        (finalWorkQ16SuccessfulDependentBadEvent bad) ≤
      ((1 : ENNReal) / (2 : ENNReal) ^ 34) *
        ((Nat.choose 9557 16 : ENNReal) /
          (semanticCompactFavourable : ENNReal)) := by
  let bound : ENNReal :=
    (Nat.choose 9557 16 : ENNReal) /
      (semanticCompactFavourable : ENNReal)
  let sample : FirstAdmittedSample q16CandidateOutput
      SemanticCap203Admitted 64 := ⟨reference, Classical.choice traceExists⟩
  letI : Nonempty (FirstAdmittedSample q16CandidateOutput
      SemanticCap203Admitted 64) := ⟨sample⟩
  rw [uniform_product_event_probability_eq_weighted_slices]
  calc
    (∑' work : Digest256,
        (PMF.uniformOfFintype Digest256) work *
          (PMF.uniformOfFintype SuccessfulQ16Coordinates).toOuterMeasure
            (productEventFstSlice
              (finalWorkQ16SuccessfulDependentBadEvent bad) work)) ≤
        ∑' work : Digest256,
          (PMF.uniformOfFintype Digest256) work *
            (if FinalWork34Accepted work then bound else 0) := by
      exact ENNReal.tsum_le_tsum fun work => by
        apply mul_le_mul_left'
        rw [product_slice_final_work_q16_dependent_bad]
        by_cases accepted : FinalWork34Accepted work
        · simp only [accepted, if_true]
          exact q16_successful_coordinates_bad_measure_le_semantic_choose
            (bad work) (badCard work) reference traceExists
        · simp [accepted]
    _ = (∑' work : Digest256,
          finalWork34AcceptedEvent.indicator
            (fun work => (PMF.uniformOfFintype Digest256) work) work) *
          bound := by
      rw [← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro work
      by_cases accepted : FinalWork34Accepted work <;>
        simp [finalWork34AcceptedEvent, accepted]
    _ = (PMF.uniformOfFintype Digest256).toOuterMeasure
          finalWork34AcceptedEvent * bound := by
      rw [PMF.toOuterMeasure_apply]
    _ = ((1 : ENNReal) / (2 : ENNReal) ^ 34) *
          ((Nat.choose 9557 16 : ENNReal) /
            (semanticCompactFavourable : ENNReal)) := by
      rw [uniform_final_work_34_probability_exact]

/-! ## Conditioning an arbitrary causal tape factorisation -/

/-- Every residual context may select a different family of q16 bad sets,
and within that context the family may additionally depend on the exposed
final-work answer. -/
theorem uniform_tape_dependent_final_work_answer_q16_probability_le
    {Tape Residual : Type}
    [Fintype Tape] [Nonempty Tape]
    [Fintype Residual] [Nonempty Residual]
    (coordinates : Equiv Tape
      (Residual × (Digest256 × Q16CandidateDigestForest)))
    (bad : Residual → Digest256 → Finset (Fin 262144))
    (badCard : ∀ residual work, (bad residual work).card ≤ 9557)
    (reference : AdmittedResult SemanticCap203Admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        reference.1))
    (event : Set Tape)
    (covered : event ⊆ coordinates ⁻¹'
      dependentSuccessfulSubtypeEvent finalWorkQ16TotalSucceeds
        (fun residual => successfulFinalWorkQ16TotalEquiv ⁻¹'
          finalWorkQ16SuccessfulDependentBadEvent (bad residual))) :
    (PMF.uniformOfFintype Tape).toOuterMeasure event ≤
      ((1 : ENNReal) / (2 : ENNReal) ^ 34) *
        ((Nat.choose 9557 16 : ENNReal) /
          (semanticCompactFavourable : ENNReal)) := by
  classical
  let sample : FirstAdmittedSample q16CandidateOutput
      SemanticCap203Admitted 64 := ⟨reference, Classical.choice traceExists⟩
  letI : Nonempty (FirstAdmittedSample q16CandidateOutput
      SemanticCap203Admitted 64) := ⟨sample⟩
  let successfulCoordinates : SuccessfulQ16Coordinates :=
    (Classical.choice inferInstance, sample)
  letI : Nonempty SuccessfulQ16Coordinates := ⟨successfulCoordinates⟩
  letI : Nonempty SuccessfulFinalWorkQ16Total :=
    ⟨successfulFinalWorkQ16TotalEquiv.symm
      (Classical.choice inferInstance, successfulCoordinates)⟩
  apply uniform_tape_dependent_successful_event_probability_le
    finalWorkQ16TotalSucceeds coordinates successfulFinalWorkQ16TotalEquiv
    (fun residual =>
      finalWorkQ16SuccessfulDependentBadEvent (bad residual))
    (((1 : ENNReal) / (2 : ENNReal) ^ 34) *
      ((Nat.choose 9557 16 : ENNReal) /
        (semanticCompactFavourable : ENNReal)))
  · intro residual
    exact uniform_final_work_q16_dependent_bad_probability_le_semantic
      (bad residual) (badCard residual) reference traceExists
  · exact covered

/-- Hidden-tape averaging of the exact 513-slot compiler router with a q16
bad family that may depend on the routed final-work answer. -/
theorem exact_compiler_causal_final_work_answer_q16_event_probability_le
    {HiddenTape : Type} [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    (parameters : ExactCompilerResourceParameters)
    (router : HiddenTape →
      ExactCompilerCausalFinalWorkQ16Router parameters)
    (bad : HiddenTape → ExactCompilerFinalWorkQ16Residual parameters →
      Digest256 → Finset (Fin 262144))
    (badCard : ∀ hidden residual work,
      (bad hidden residual work).card ≤ 9557)
    (reference : AdmittedResult SemanticCap203Admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        reference.1))
    (event : Set (ExactCompilerSample HiddenTape parameters))
    (covered : ∀ hidden, jointEventSlice event hidden ⊆
      exactCompilerCausalFinalWorkQ16Coordinates parameters (router hidden) ⁻¹'
        dependentSuccessfulSubtypeEvent finalWorkQ16TotalSucceeds
          (fun residual => successfulFinalWorkQ16TotalEquiv ⁻¹'
            finalWorkQ16SuccessfulDependentBadEvent
              (bad hidden residual))) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure event ≤
      ((1 : ENNReal) / (2 : ENNReal) ^ 34) *
        ((Nat.choose 9557 16 : ENNReal) /
          (semanticCompactFavourable : ENNReal)) := by
  apply joint_event_probability_le_of_every_slice_le
  intro hidden
  exact uniform_tape_dependent_final_work_answer_q16_probability_le
    (exactCompilerCausalFinalWorkQ16Coordinates parameters (router hidden))
    (bad hidden) (badCard hidden) reference traceExists
    (jointEventSlice event hidden) (covered hidden)

#print axioms product_slice_final_work_q16_dependent_bad
#print axioms
  uniform_final_work_q16_dependent_bad_probability_le_semantic
#print axioms
  uniform_tape_dependent_final_work_answer_q16_probability_le
#print axioms
  exact_compiler_causal_final_work_answer_q16_event_probability_le

end

end AspisK1.V7Tag73CausalQ16FinalWorkDependentBad
