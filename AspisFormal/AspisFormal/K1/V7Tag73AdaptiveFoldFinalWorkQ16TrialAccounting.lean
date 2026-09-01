import AspisFormal.K1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates

/-!
# Two positioned work-trial accounting

The source bridge may need one precommitted exposure index for the fold-work
answer and another for the final-work/q16 anchor.  This module performs the
finite unions in transcript order: the 34-bit final-work factor pays only for
the inner anchor inventory, and the earlier 31-bit fold-work factor pays only
for the outer alpha-boundary inventory.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73AdaptiveFoldFinalWorkQ16TrialAccounting

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73CausalAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisK1.V7Tag73Q16RawENNRealProbability
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73Q16SuccessfulForestBridge
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Generic finite work-qualified union, used once at 34 bits and once at 31
bits.  Keeping the base error explicit preserves the earlier work factor
through the inner union. -/
theorem finite_work_trial_union_probability_le_base
    {Sample Trial : Type} [Fintype Trial]
    (law : PMF Sample) (bits : Nat) (base : ENNReal)
    (event : Trial → Set Sample)
    (perTrial : ∀ trial,
      law.toOuterMeasure (event trial) ≤ base / (2 : ENNReal) ^ bits)
    (trialCap : Fintype.card Trial ≤ 2 ^ bits) :
    law.toOuterMeasure (⋃ trial, event trial) ≤ base := by
  calc
    law.toOuterMeasure (⋃ trial, event trial) ≤
        ∑ trial : Trial, law.toOuterMeasure (event trial) := by
      exact measure_iUnion_fintype_le law.toOuterMeasure event
    _ ≤ ∑ _trial : Trial, base / (2 : ENNReal) ^ bits := by
      exact Finset.sum_le_sum fun trial _member => perTrial trial
    _ = (Fintype.card Trial : ENNReal) *
        (base / (2 : ENNReal) ^ bits) := by simp
    _ = ((Fintype.card Trial : ENNReal) * base) /
        (2 : ENNReal) ^ bits := by
      simp only [div_eq_mul_inv, mul_assoc]
    _ ≤ base := by
      rw [ENNReal.div_le_iff (by simp) (by simp)]
      have castTrialCap : (Fintype.card Trial : ENNReal) ≤
          (2 : ENNReal) ^ bits := by
        exact_mod_cast trialCap
      calc
        (Fintype.card Trial : ENNReal) * base ≤
            (2 : ENNReal) ^ bits * base :=
          mul_le_mul_right' castTrialCap base
        _ = base * (2 : ENNReal) ^ bits := by ac_rfl

/-- Probability-ready family indexed separately by the first exposure of the
fold answer and the first exposure of the final-work/q16 anchor. -/
structure ExactCompilerCausalFoldAlphaFinalWorkAnswerQ16Trials
    {HiddenTape FoldTrial FinalTrial : Type}
    [Fintype HiddenTape] [Fintype FoldTrial] [Fintype FinalTrial]
    (parameters : ExactCompilerResourceParameters) where
  event : FoldTrial → FinalTrial →
    Set (ExactCompilerSample HiddenTape parameters)
  router : FoldTrial → FinalTrial → HiddenTape →
    ExactCompilerCausalFoldAlphaFinalWorkQ16Router parameters
  bad : FoldTrial → FinalTrial → HiddenTape →
    ExactCompilerFoldAlphaFinalWorkQ16Residual parameters →
      AlphaZeroDigestBlocks → Digest256 → Digest256 →
        Finset (Fin 262144)
  badCard : ∀ foldTrial finalTrial hidden residual alpha fold work,
    (bad foldTrial finalTrial hidden residual alpha fold work).card ≤ 9557
  reference : AdmittedResult SemanticCap203Admitted
  traceExists : Nonempty
    (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
      reference.1)
  covered : ∀ foldTrial finalTrial hidden,
    jointEventSlice (event foldTrial finalTrial) hidden ⊆
      exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters
          (router foldTrial finalTrial hidden) ⁻¹'
        dependentSuccessfulSubtypeEvent foldFinalWorkQ16TotalSucceeds
          (fun context => successfulFoldFinalWorkQ16TotalEquiv ⁻¹'
            foldFinalWorkQ16SuccessfulBadEvent
              (fun fold work =>
                bad foldTrial finalTrial hidden context.1 context.2 fold work))

theorem
    ExactCompilerCausalFoldAlphaFinalWorkAnswerQ16Trials.event_probability_le_product
    {HiddenTape FoldTrial FinalTrial : Type}
    [Fintype HiddenTape] [Fintype FoldTrial] [Fintype FinalTrial]
    {hiddenLaw : PMF HiddenTape}
    {parameters : ExactCompilerResourceParameters}
    (trials : ExactCompilerCausalFoldAlphaFinalWorkAnswerQ16Trials
      (HiddenTape := HiddenTape) (FoldTrial := FoldTrial)
      (FinalTrial := FinalTrial) parameters)
    (foldTrial : FoldTrial) (finalTrial : FinalTrial) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (trials.event foldTrial finalTrial) ≤
      (q16SemanticOneForestRawError / (2 : ENNReal) ^ 31) /
        (2 : ENNReal) ^ 34 := by
  have bound :=
    exact_compiler_causal_fold_alpha_final_work_answer_q16_event_probability_le
      hiddenLaw parameters (trials.router foldTrial finalTrial)
      (trials.bad foldTrial finalTrial)
      (trials.badCard foldTrial finalTrial) trials.reference trials.traceExists
      (trials.event foldTrial finalTrial)
      (trials.covered foldTrial finalTrial)
  change
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (trials.event foldTrial finalTrial) ≤
      ((1 : ENNReal) / (2 : ENNReal) ^ 31) *
        (((1 : ENNReal) / (2 : ENNReal) ^ 34) *
          q16SemanticOneForestRawError) at bound
  calc
    _ ≤ ((1 : ENNReal) / (2 : ENNReal) ^ 31) *
        (((1 : ENNReal) / (2 : ENNReal) ^ 34) *
          q16SemanticOneForestRawError) := bound
    _ = (q16SemanticOneForestRawError / (2 : ENNReal) ^ 31) /
        (2 : ENNReal) ^ 34 := by
      simp only [div_eq_mul_inv, one_mul]
      ac_rfl

/-- The final-work inventory is paid only by the 34-bit positioned digest. -/
theorem
    ExactCompilerCausalFoldAlphaFinalWorkAnswerQ16Trials.inner_union_probability_le
    {HiddenTape FoldTrial FinalTrial : Type}
    [Fintype HiddenTape] [Fintype FoldTrial] [Fintype FinalTrial]
    {hiddenLaw : PMF HiddenTape}
    {parameters : ExactCompilerResourceParameters}
    (trials : ExactCompilerCausalFoldAlphaFinalWorkAnswerQ16Trials
      (HiddenTape := HiddenTape) (FoldTrial := FoldTrial)
      (FinalTrial := FinalTrial) parameters)
    (finalTrialCap : Fintype.card FinalTrial ≤ 2 ^ 34)
    (foldTrial : FoldTrial) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (⋃ finalTrial, trials.event foldTrial finalTrial) ≤
      q16SemanticOneForestRawError / (2 : ENNReal) ^ 31 := by
  exact finite_work_trial_union_probability_le_base
    (exactCompilerJointLaw hiddenLaw parameters) 34
    (q16SemanticOneForestRawError / (2 : ENNReal) ^ 31)
    (trials.event foldTrial) (trials.event_probability_le_product foldTrial)
    finalTrialCap

/-- The outer alpha-boundary inventory is paid only by the earlier 31-bit
fold-work digest.  The conclusion is the original raw one-forest q16 error. -/
theorem
    ExactCompilerCausalFoldAlphaFinalWorkAnswerQ16Trials.failure_union_probability_le_one_forest
    {HiddenTape FoldTrial FinalTrial : Type}
    [Fintype HiddenTape] [Fintype FoldTrial] [Fintype FinalTrial]
    {hiddenLaw : PMF HiddenTape}
    {parameters : ExactCompilerResourceParameters}
    (trials : ExactCompilerCausalFoldAlphaFinalWorkAnswerQ16Trials
      (HiddenTape := HiddenTape) (FoldTrial := FoldTrial)
      (FinalTrial := FinalTrial) parameters)
    (foldTrialCap : Fintype.card FoldTrial ≤ 2 ^ 31)
    (finalTrialCap : Fintype.card FinalTrial ≤ 2 ^ 34) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (⋃ foldTrial, ⋃ finalTrial, trials.event foldTrial finalTrial) ≤
      q16SemanticOneForestRawError := by
  exact finite_work_trial_union_probability_le_base
    (exactCompilerJointLaw hiddenLaw parameters) 31
    q16SemanticOneForestRawError
    (fun foldTrial => ⋃ finalTrial, trials.event foldTrial finalTrial)
    (trials.inner_union_probability_le finalTrialCap) foldTrialCap

end


#print axioms finite_work_trial_union_probability_le_base
#print axioms ExactCompilerCausalFoldAlphaFinalWorkAnswerQ16Trials
#print axioms
  ExactCompilerCausalFoldAlphaFinalWorkAnswerQ16Trials.event_probability_le_product
#print axioms
  ExactCompilerCausalFoldAlphaFinalWorkAnswerQ16Trials.inner_union_probability_le
#print axioms
  ExactCompilerCausalFoldAlphaFinalWorkAnswerQ16Trials.failure_union_probability_le_one_forest

end AspisK1.V7Tag73AdaptiveFoldFinalWorkQ16TrialAccounting
