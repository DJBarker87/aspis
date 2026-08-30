import AspisFormal.K1.V7Tag73CausalQ16FinalWorkProbability

/-!
# Adaptive Tag-73 q16 trial accounting

The semantic q16 theorem gives the exact recurrence-denominator bound for one
causally routed digest forest; the generated release certificate separately
identifies that denominator with `exactQ16IdealRawError`.  A general
random-oracle adversary, however,
may construct several work-qualified transcript prefixes and retain a proof
using a later forest.  The raw input bytes of a cached squeeze do not identify
that eventual choice before its answer is exposed, so silently treating the
selected forest as one pre-answer router is not sound.

This module gives the exact finite replacement.  Every genuine transcript
trial supplies its own causal router and the existing tight forest bound.
An adaptively selected failure must be covered by the finite union of those
trials, and therefore costs at most the number of trials times the one-forest
error.  The final theorem proves the raw one-forest bound when at most `2^34`
trials each satisfy the still-explicit joint q16/final-work product bound.

No trial cover is assumed here.  The production/source bridge must enumerate
the actual work-qualified q16 transcript attempts and prove that the accepted
one is among them.  This module prevents that remaining obligation from being
hidden inside a false one-router independence premise.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73AdaptiveQ16TrialAccounting

open MeasureTheory
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73CausalQ16FinalWorkProbability
open AspisK1.V7Tag73CausalQ16ProbabilityBridge
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73Q16CompactScheduleCount
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisK1.V7Tag73Q16SuccessfulForestBridge
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- A finite inventory of genuine q16 transcript trials.  Every trial is
individually causal: its bad set may depend on the hidden adversary tape and
all residual non-q16 answers, but not on the forest answers assigned by its
router. -/
structure ExactCompilerCausalQ16Trials
    {HiddenTape Trial : Type}
    [Fintype HiddenTape] [Fintype Trial]
    (parameters : ExactCompilerResourceParameters) where
  event : Trial → Set (ExactCompilerSample HiddenTape parameters)
  router : Trial → HiddenTape → ExactCompilerCausalQ16Router parameters
  bad : Trial → HiddenTape → ExactCompilerQ16Residual parameters →
    Finset (Fin 262144)
  badCard : ∀ trial hidden residual,
    (bad trial hidden residual).card ≤ 9557
  reference : AdmittedResult SemanticCap203Admitted
  traceExists : Nonempty
    (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
      reference.1)
  covered : ∀ trial hidden, jointEventSlice (event trial) hidden ⊆
    exactCompilerCausalQ16Coordinates parameters (router trial hidden) ⁻¹'
      dependentSuccessfulSubtypeEvent q16DigestForestSucceeds
        (fun residual => successfulQ16DigestForestEquiv ⁻¹'
          q16SuccessfulCoordinatesBadEvent (bad trial hidden residual))

/-- One causally routed q16 forest, before the separate release-denominator
certificate rewrites the semantic recurrence to its frozen decimal. -/
def q16SemanticOneForestRawError : ENNReal :=
  (Nat.choose 9557 16 : ENNReal) /
    (semanticCompactFavourable : ENNReal)

/-- The literal finite union of all causally routed q16 trial failures. -/
def ExactCompilerCausalQ16Trials.failureUnion
    {HiddenTape Trial : Type}
    [Fintype HiddenTape] [Fintype Trial]
    {parameters : ExactCompilerResourceParameters}
    (trials : ExactCompilerCausalQ16Trials
      (HiddenTape := HiddenTape) (Trial := Trial) parameters) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  ⋃ trial, trials.event trial

/-- Each trial inherits the already-proved exact one-forest semantic bound. -/
theorem ExactCompilerCausalQ16Trials.event_probability_le_semantic
    {HiddenTape Trial : Type}
    [Fintype HiddenTape] [Fintype Trial]
    {hiddenLaw : PMF HiddenTape}
    {parameters : ExactCompilerResourceParameters}
    (trials : ExactCompilerCausalQ16Trials
      (HiddenTape := HiddenTape) (Trial := Trial) parameters)
    (trial : Trial) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (trials.event trial) ≤
      q16SemanticOneForestRawError := by
  exact exact_compiler_causal_q16_event_probability_le_semantic
    hiddenLaw parameters (trials.router trial) (trials.bad trial)
      (trials.badCard trial) trials.reference trials.traceExists
      (trials.event trial) (trials.covered trial)

/-- Adaptive selection among finitely many honest causal trials costs exactly
the ordinary finite-union factor.  No independence between trials is used. -/
theorem ExactCompilerCausalQ16Trials.failure_union_probability_le
    {HiddenTape Trial : Type}
    [Fintype HiddenTape] [Fintype Trial]
    {hiddenLaw : PMF HiddenTape}
    {parameters : ExactCompilerResourceParameters}
    (trials : ExactCompilerCausalQ16Trials
      (HiddenTape := HiddenTape) (Trial := Trial) parameters) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        trials.failureUnion ≤
      (Fintype.card Trial : ENNReal) *
        q16SemanticOneForestRawError := by
  calc
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        trials.failureUnion ≤
      ∑ trial : Trial,
        (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (trials.event trial) := by
            exact measure_iUnion_fintype_le
              (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
              trials.event
    _ ≤ ∑ _trial : Trial, q16SemanticOneForestRawError := by
      exact Finset.sum_le_sum fun trial _member =>
        trials.event_probability_le_semantic trial
    _ = (Fintype.card Trial : ENNReal) *
        q16SemanticOneForestRawError := by
      simp

/-- Any deployed failure event covered by the genuine trial inventory gets
the same exact finite-union bound.  Constructing `covered` is the remaining
production trace/source obligation; it is not a field of the one-trial q16
probability theorem. -/
theorem ExactCompilerCausalQ16Trials.covered_failure_probability_le
    {HiddenTape Trial : Type}
    [Fintype HiddenTape] [Fintype Trial]
    {hiddenLaw : PMF HiddenTape}
    {parameters : ExactCompilerResourceParameters}
    (trials : ExactCompilerCausalQ16Trials
      (HiddenTape := HiddenTape) (Trial := Trial) parameters)
    (failure : Set (ExactCompilerSample HiddenTape parameters))
    (covered : failure ⊆ trials.failureUnion) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure failure ≤
      (Fintype.card Trial : ENNReal) *
        q16SemanticOneForestRawError := by
  exact (measure_mono covered).trans trials.failure_union_probability_le

/-- Raw q16 error for an explicit number of adaptively selectable trials. -/
def adaptiveQ16SemanticTrialRawError (trialCount : Nat) : ENNReal :=
  (trialCount : ENNReal) * q16SemanticOneForestRawError

theorem adaptive_q16_trial_raw_error_zero :
    adaptiveQ16SemanticTrialRawError 0 = 0 := by
  simp [adaptiveQ16SemanticTrialRawError]

theorem adaptive_q16_trial_raw_error_one :
    adaptiveQ16SemanticTrialRawError 1 =
      q16SemanticOneForestRawError := by
  simp [adaptiveQ16SemanticTrialRawError]

/-- Exact raw (not reporting-normalized) accounting for work-qualified trial
selection.  If every causal trial jointly pays its independent 34-bit final
work factor and there are at most `2^34` trials, their finite union is still
bounded by the one-forest q16 error.  The explicit `perTrial` premise is the
remaining causal work/q16 product theorem; it is not inferred from the q16
router alone. -/
theorem work_qualified_q16_trial_union_probability_le_one_forest
    {Sample Trial : Type} [Fintype Trial]
    (law : PMF Sample)
    (event : Trial → Set Sample)
    (perTrial : ∀ trial,
      law.toOuterMeasure (event trial) ≤
        q16SemanticOneForestRawError / (2 : ENNReal) ^ 34)
    (trialCap : Fintype.card Trial ≤ 2 ^ 34) :
    law.toOuterMeasure (⋃ trial, event trial) ≤
      q16SemanticOneForestRawError := by
  calc
    law.toOuterMeasure (⋃ trial, event trial) ≤
        ∑ trial : Trial, law.toOuterMeasure (event trial) := by
      exact measure_iUnion_fintype_le law.toOuterMeasure event
    _ ≤ ∑ _trial : Trial,
        q16SemanticOneForestRawError / (2 : ENNReal) ^ 34 := by
      exact Finset.sum_le_sum fun trial _member => perTrial trial
    _ = (Fintype.card Trial : ENNReal) *
        (q16SemanticOneForestRawError / (2 : ENNReal) ^ 34) := by
      simp
    _ = ((Fintype.card Trial : ENNReal) *
        q16SemanticOneForestRawError) / (2 : ENNReal) ^ 34 := by
      simp only [div_eq_mul_inv, mul_assoc]
    _ ≤ q16SemanticOneForestRawError := by
      rw [ENNReal.div_le_iff (by norm_num) (by norm_num)]
      have castTrialCap : (Fintype.card Trial : ENNReal) ≤
          (2 : ENNReal) ^ 34 := by
        exact_mod_cast trialCap
      calc
        (Fintype.card Trial : ENNReal) * q16SemanticOneForestRawError ≤
            (2 : ENNReal) ^ 34 * q16SemanticOneForestRawError :=
          mul_le_mul_left castTrialCap q16SemanticOneForestRawError
        _ = q16SemanticOneForestRawError * (2 : ENNReal) ^ 34 := by
          ac_rfl

/-! ## Exact compiler instantiation of the joint work/q16 product -/

/-- A finite inventory whose individual events carry the complete 513-slot
causal certificate: one literal final-work digest plus every q16 digest
block.  The source layer still has to construct these routers and the final
cover; the probability product itself is no longer a premise. -/
structure ExactCompilerCausalFinalWorkQ16Trials
    {HiddenTape Trial : Type}
    [Fintype HiddenTape] [Fintype Trial]
    (parameters : ExactCompilerResourceParameters) where
  event : Trial → Set (ExactCompilerSample HiddenTape parameters)
  router : Trial → HiddenTape →
    ExactCompilerCausalFinalWorkQ16Router parameters
  bad : Trial → HiddenTape →
    ExactCompilerFinalWorkQ16Residual parameters → Finset (Fin 262144)
  badCard : ∀ trial hidden residual,
    (bad trial hidden residual).card ≤ 9557
  reference : AdmittedResult SemanticCap203Admitted
  traceExists : Nonempty
    (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
      reference.1)
  covered : ∀ trial hidden, jointEventSlice (event trial) hidden ⊆
    exactCompilerCausalFinalWorkQ16Coordinates parameters
        (router trial hidden) ⁻¹'
      dependentSuccessfulSubtypeEvent finalWorkQ16TotalSucceeds
        (fun residual => successfulFinalWorkQ16TotalEquiv ⁻¹'
          finalWorkQ16SuccessfulBadEvent (bad trial hidden residual))

theorem ExactCompilerCausalFinalWorkQ16Trials.event_probability_le_product
    {HiddenTape Trial : Type}
    [Fintype HiddenTape] [Fintype Trial]
    {hiddenLaw : PMF HiddenTape}
    {parameters : ExactCompilerResourceParameters}
    (trials : ExactCompilerCausalFinalWorkQ16Trials
      (HiddenTape := HiddenTape) (Trial := Trial) parameters)
    (trial : Trial) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (trials.event trial) ≤
      q16SemanticOneForestRawError / (2 : ENNReal) ^ 34 := by
  have productBound :=
    exact_compiler_causal_final_work_q16_event_probability_le_semantic
      hiddenLaw parameters (trials.router trial) (trials.bad trial)
      (trials.badCard trial) trials.reference trials.traceExists
      (trials.event trial) (trials.covered trial)
  change
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (trials.event trial) ≤
      ((1 : ENNReal) / (2 : ENNReal) ^ 34) *
        q16SemanticOneForestRawError at productBound
  calc
    _ ≤ ((1 : ENNReal) / (2 : ENNReal) ^ 34) *
          q16SemanticOneForestRawError := productBound
    _ = q16SemanticOneForestRawError / (2 : ENNReal) ^ 34 := by
      rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
      simp

/-- The exact 513-slot product cancels the finite adaptive trial union up to
the deployed `2^34` final-work trial cap.  The conclusion is the original
raw one-forest q16 error; no work-normalized reporting convention appears. -/
theorem ExactCompilerCausalFinalWorkQ16Trials.failure_union_probability_le_one_forest
    {HiddenTape Trial : Type}
    [Fintype HiddenTape] [Fintype Trial]
    {hiddenLaw : PMF HiddenTape}
    {parameters : ExactCompilerResourceParameters}
    (trials : ExactCompilerCausalFinalWorkQ16Trials
      (HiddenTape := HiddenTape) (Trial := Trial) parameters)
    (trialCap : Fintype.card Trial ≤ 2 ^ 34) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (⋃ trial, trials.event trial) ≤ q16SemanticOneForestRawError := by
  exact work_qualified_q16_trial_union_probability_le_one_forest
    (exactCompilerJointLaw hiddenLaw parameters) trials.event
    trials.event_probability_le_product trialCap

end

#print axioms ExactCompilerCausalQ16Trials.event_probability_le_semantic
#print axioms ExactCompilerCausalQ16Trials.failure_union_probability_le
#print axioms ExactCompilerCausalQ16Trials.covered_failure_probability_le
#print axioms work_qualified_q16_trial_union_probability_le_one_forest
#print axioms ExactCompilerCausalFinalWorkQ16Trials.event_probability_le_product
#print axioms ExactCompilerCausalFinalWorkQ16Trials.failure_union_probability_le_one_forest

end AspisK1.V7Tag73AdaptiveQ16TrialAccounting
