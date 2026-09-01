import AspisFormal.K1.V7Tag73CausalQ16FinalWorkDependentBad
import AspisFormal.K1.V7Tag73ExactFixedCleanQ16ResidualFactorization

/-!
# Clean fixed K1.3 factorisation conditional on the final-work answer

The deployed 34-bit final-work answer is available before q16 begins.  The
q16 consistency set may therefore depend on that answer.  This file weakens
the old residual-fibre invariant in exactly that causal direction and routes
the clean fixed K1.3 event through the unchanged `2^-34 * epsilon_q16` bound.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

namespace AspisK1.V7Tag73ExactFixedCleanWorkDependentQ16Factorization

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73CausalQ16FinalWorkDependentBad
open AspisK1.V7Tag73CausalQ16FinalWorkProbability
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactFixedCleanQ16ResidualFactorization
open AspisK1.V7Tag73ExactFixedInstanceEvent
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkDigestProbability
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73OperationalQ16ForestHandoff
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisK1.V7Tag73Q16RawENNRealProbability
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73Q16SuccessfulForestBridge
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact
open AspisV5WithoutReplacementQuerySoundness

noncomputable section

/-! ## Generic exposure-trial package -/

structure ExactCompilerCausalFinalWorkAnswerQ16Trials
    {HiddenTape Trial : Type}
    [Fintype HiddenTape] [Fintype Trial]
    (parameters : ExactCompilerResourceParameters) where
  event : Trial → Set (ExactCompilerSample HiddenTape parameters)
  router : Trial → HiddenTape →
    ExactCompilerCausalFinalWorkQ16Router parameters
  bad : Trial → HiddenTape → ExactCompilerFinalWorkQ16Residual parameters →
    Digest256 → Finset (Fin 262144)
  badCard : ∀ trial hidden residual work,
    (bad trial hidden residual work).card ≤ 9557
  reference : AdmittedResult SemanticCap203Admitted
  traceExists : Nonempty
    (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
      reference.1)
  covered : ∀ trial hidden, jointEventSlice (event trial) hidden ⊆
    exactCompilerCausalFinalWorkQ16Coordinates parameters
        (router trial hidden) ⁻¹'
      dependentSuccessfulSubtypeEvent finalWorkQ16TotalSucceeds
        (fun residual => successfulFinalWorkQ16TotalEquiv ⁻¹'
          finalWorkQ16SuccessfulDependentBadEvent
            (bad trial hidden residual))

theorem ExactCompilerCausalFinalWorkAnswerQ16Trials.event_probability_le_product
    {HiddenTape Trial : Type}
    [Fintype HiddenTape] [Fintype Trial]
    {hiddenLaw : PMF HiddenTape}
    {parameters : ExactCompilerResourceParameters}
    (trials : ExactCompilerCausalFinalWorkAnswerQ16Trials
      (HiddenTape := HiddenTape) (Trial := Trial) parameters)
    (trial : Trial) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (trials.event trial) ≤
      q16SemanticOneForestRawError / (2 : ENNReal) ^ 34 := by
  have bound :=
    exact_compiler_causal_final_work_answer_q16_event_probability_le
      hiddenLaw parameters (trials.router trial) (trials.bad trial)
      (trials.badCard trial) trials.reference trials.traceExists
      (trials.event trial) (trials.covered trial)
  change
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (trials.event trial) ≤
      ((1 : ENNReal) / (2 : ENNReal) ^ 34) *
        q16SemanticOneForestRawError at bound
  calc
    _ ≤ ((1 : ENNReal) / (2 : ENNReal) ^ 34) *
          q16SemanticOneForestRawError := bound
    _ = q16SemanticOneForestRawError / (2 : ENNReal) ^ 34 := by
      rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
      simp

theorem ExactCompilerCausalFinalWorkAnswerQ16Trials.failure_union_probability_le
    {HiddenTape Trial : Type}
    [Fintype HiddenTape] [Fintype Trial]
    {hiddenLaw : PMF HiddenTape}
    {parameters : ExactCompilerResourceParameters}
    (trials : ExactCompilerCausalFinalWorkAnswerQ16Trials
      (HiddenTape := HiddenTape) (Trial := Trial) parameters) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (⋃ trial, trials.event trial) ≤
      ((Fintype.card Trial : ENNReal) * q16SemanticOneForestRawError) /
        (2 : ENNReal) ^ 34 := by
  exact work_qualified_q16_trial_union_probability_le_card_mul
    (exactCompilerJointLaw hiddenLaw parameters) trials.event
    trials.event_probability_le_product

theorem ExactCompilerCausalFinalWorkAnswerQ16Trials.failure_union_probability_le_one_forest
    {HiddenTape Trial : Type}
    [Fintype HiddenTape] [Fintype Trial]
    {hiddenLaw : PMF HiddenTape}
    {parameters : ExactCompilerResourceParameters}
    (trials : ExactCompilerCausalFinalWorkAnswerQ16Trials
      (HiddenTape := HiddenTape) (Trial := Trial) parameters)
    (trialCap : Fintype.card Trial ≤ 2 ^ 34) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (⋃ trial, trials.event trial) ≤ q16SemanticOneForestRawError := by
  exact work_qualified_q16_trial_union_probability_le_one_forest
    (exactCompilerJointLaw hiddenLaw parameters) trials.event
    trials.event_probability_le_product trialCap

/-! ## Clean fixed-root instantiation -/

/-- Bad sets need agree only after both the residual tape and the already
exposed final-work answer have been fixed. -/
def ExactFixedCleanK13ResidualWorkInvariant
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) : Prop :=
  ∀ (trial : ExactCompilerExposureTrial parameters) (hidden : HiddenTape)
      (left right : FreshAnswerTape Digest256
        (exactCompilerTargetCaps parameters).length),
    (hidden, left) ∈ exactFixedCleanK13JointTrialEvent transitionFuel
        configuration projection fixedInstance decoder trial →
    (hidden, right) ∈ exactFixedCleanK13JointTrialEvent transitionFuel
        configuration projection fixedInstance decoder trial →
    (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, left)).1 =
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, right)).1 →
    (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, left)).2.1 =
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, right)).2.1 →
    exactFixedK13PointwiseBad transitionFuel configuration projection
        fixedInstance decoder trial (hidden, left) =
      exactFixedK13PointwiseBad transitionFuel configuration projection
        fixedInstance decoder trial (hidden, right)

def exactFixedCleanK13ResidualWorkFibreNonempty
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (trial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (residual : ExactCompilerFinalWorkQ16Residual parameters)
    (work : Digest256) : Prop :=
  ∃ tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length,
    (hidden, tape) ∈ exactFixedCleanK13JointTrialEvent transitionFuel
        configuration projection fixedInstance decoder trial ∧
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, tape)).1 = residual ∧
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, tape)).2.1 = work

noncomputable def exactFixedCleanK13ResidualWorkBad
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (trial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (residual : ExactCompilerFinalWorkQ16Residual parameters)
    (work : Digest256) : Finset (Fin 262144) := by
  classical
  exact if inhabitedFibre : exactFixedCleanK13ResidualWorkFibreNonempty
        transitionFuel configuration projection fixedInstance decoder trial
        hidden residual work then
      exactFixedK13PointwiseBad transitionFuel configuration projection
        fixedInstance decoder trial (hidden, Classical.choose inhabitedFibre)
    else ∅

theorem exact_fixed_clean_k13_residual_work_bad_card
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (trial : ExactCompilerExposureTrial parameters) (hidden : HiddenTape)
    (residual : ExactCompilerFinalWorkQ16Residual parameters)
    (work : Digest256) :
    (exactFixedCleanK13ResidualWorkBad transitionFuel configuration projection
      fixedInstance decoder trial hidden residual work).card ≤ 9557 := by
  classical
  by_cases inhabitedFibre : exactFixedCleanK13ResidualWorkFibreNonempty
      transitionFuel configuration projection fixedInstance decoder trial
      hidden residual work
  · simpa [exactFixedCleanK13ResidualWorkBad, inhabitedFibre] using
      exact_fixed_k13_pointwise_bad_card
        (configuration := configuration) (projection := projection)
        (fixedInstance := fixedInstance) (decoder := decoder) trial
        (hidden, Classical.choose inhabitedFibre)
  · simp [exactFixedCleanK13ResidualWorkBad, inhabitedFibre]

theorem exact_fixed_clean_k13_residual_work_bad_eq_pointwise
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (invariant : ExactFixedCleanK13ResidualWorkInvariant transitionFuel
      configuration projection fixedInstance decoder)
    (trial : ExactCompilerExposureTrial parameters) (hidden : HiddenTape)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (member : (hidden, tape) ∈ exactFixedCleanK13JointTrialEvent
      transitionFuel configuration projection fixedInstance decoder trial) :
    exactFixedCleanK13ResidualWorkBad transitionFuel configuration projection
        fixedInstance decoder trial hidden
          (exactFixedK13TrialCoordinates transitionFuel configuration trial
            (hidden, tape)).1
          (exactFixedK13TrialCoordinates transitionFuel configuration trial
            (hidden, tape)).2.1 =
      exactFixedK13PointwiseBad transitionFuel configuration projection
        fixedInstance decoder trial (hidden, tape) := by
  classical
  let residual := (exactFixedK13TrialCoordinates transitionFuel configuration
    trial (hidden, tape)).1
  let work := (exactFixedK13TrialCoordinates transitionFuel configuration
    trial (hidden, tape)).2.1
  have inhabitedFibre : exactFixedCleanK13ResidualWorkFibreNonempty
      transitionFuel configuration projection fixedInstance decoder trial
      hidden residual work := ⟨tape, member, rfl, rfl⟩
  let representative := Classical.choose inhabitedFibre
  have representativeFacts := Classical.choose_spec inhabitedFibre
  have sameBad := invariant trial hidden representative tape
    representativeFacts.1 member representativeFacts.2.1
      representativeFacts.2.2
  simpa [exactFixedCleanK13ResidualWorkBad, inhabitedFibre, residual, work,
    representative] using sameBad

noncomputable def exactFixedCleanK13WorkDependentExposureTrials
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (invariant : ExactFixedCleanK13ResidualWorkInvariant transitionFuel
      configuration projection fixedInstance decoder)
    (reference : AdmittedResult SemanticCap203Admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        reference.1)) :
    ExactCompilerCausalFinalWorkAnswerQ16Trials
      (HiddenTape := HiddenTape)
      (Trial := ExactCompilerExposureTrial parameters) parameters where
  event := exactFixedCleanK13JointTrialEvent transitionFuel configuration
    projection fixedInstance decoder
  router := fun trial hidden =>
    exactCompilerExposureTrialDagRouter parameters transitionFuel trial
      (exactPlainRomCursor configuration hidden).erase
  bad := exactFixedCleanK13ResidualWorkBad transitionFuel configuration
    projection fixedInstance decoder
  badCard := exact_fixed_clean_k13_residual_work_bad_card
    (configuration := configuration) (projection := projection)
    (fixedInstance := fixedInstance) (decoder := decoder)
  reference := reference
  traceExists := traceExists
  covered := by
    intro trial hidden tape member
    change exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, tape) ∈
      dependentSuccessfulSubtypeEvent finalWorkQ16TotalSucceeds
        (fun residual => successfulFinalWorkQ16TotalEquiv ⁻¹'
          finalWorkQ16SuccessfulDependentBadEvent
            (exactFixedCleanK13ResidualWorkBad transitionFuel configuration
              projection fixedInstance decoder trial hidden residual))
    let witness := Classical.choice member.1
    have canonicalEq := exact_fixed_clean_k13_residual_work_bad_eq_pointwise
      invariant trial hidden tape member
    have pointwiseEq :
        exactFixedK13PointwiseBad transitionFuel configuration projection
            fixedInstance decoder trial (hidden, tape) = witness.bad := by
      simpa [witness] using
        (exact_fixed_k13_pointwise_bad_eq_choice
          (configuration := configuration) (projection := projection)
          (fixedInstance := fixedInstance) (decoder := decoder) trial
          (hidden, tape) member.1)
    have badEq :
        exactFixedCleanK13ResidualWorkBad transitionFuel configuration
            projection fixedInstance decoder trial hidden
              (exactFixedK13TrialCoordinates transitionFuel configuration trial
                (hidden, tape)).1
              (exactFixedK13TrialCoordinates transitionFuel configuration trial
                (hidden, tape)).2.1 = witness.bad :=
      canonicalEq.trans pointwiseEq
    rcases witness.coordinate with ⟨success, badMember⟩
    refine ⟨success, ?_⟩
    change successfulFinalWorkQ16TotalEquiv
        ⟨(exactFixedK13TrialCoordinates transitionFuel configuration trial
          (hidden, tape)).2, success⟩ ∈
      finalWorkQ16SuccessfulDependentBadEvent
        (exactFixedCleanK13ResidualWorkBad transitionFuel configuration
          projection fixedInstance decoder trial hidden
            (exactFixedK13TrialCoordinates transitionFuel configuration trial
              (hidden, tape)).1)
    change FinalWork34Accepted
          (successfulFinalWorkQ16TotalEquiv
            ⟨(exactFixedK13TrialCoordinates transitionFuel configuration trial
              (hidden, tape)).2, success⟩).1 ∧
        (successfulFinalWorkQ16TotalEquiv
            ⟨(exactFixedK13TrialCoordinates transitionFuel configuration trial
              (hidden, tape)).2, success⟩).2 ∈
          q16SuccessfulCoordinatesBadEvent
            (exactFixedCleanK13ResidualWorkBad transitionFuel configuration
              projection fixedInstance decoder trial hidden
                (exactFixedK13TrialCoordinates transitionFuel configuration
                  trial (hidden, tape)).1
                (exactFixedK13TrialCoordinates transitionFuel configuration
                  trial (hidden, tape)).2.1)
    rw [badEq]
    exact badMember

theorem exact_fixed_clean_work_dependent_k13_query_probability_le_one_forest
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (source : ExactFixedK13ParsedSourceProvider transitionFuel configuration
      projection fixedInstance)
    (frontierExact : ∀
      (sample : ExactCompilerSample HiddenTape parameters)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (schedule : QuerySchedule),
      (exactOperationalTape input).frontierNodes schedule =
        semanticFrontierNodes schedule.positions)
    (invariant : ExactFixedCleanK13ResidualWorkInvariant transitionFuel
      configuration projection fixedInstance decoder)
    (reference : AdmittedResult SemanticCap203Admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        reference.1))
    (exposureCap : unifiedFull256ExposureCap parameters ≤ 2 ^ 34) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
            projection fixedInstance ∩
          exactTag73K13QueryEvent transitionFuel configuration projection
            fixedInstance decoder) ≤ q16SemanticOneForestRawError := by
  let trials := exactFixedCleanK13WorkDependentExposureTrials transitionFuel
    configuration projection fixedInstance decoder invariant reference
      traceExists
  calc
    _ ≤ (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (⋃ trial, trials.event trial) := by
      apply measure_mono
      exact exact_fixed_clean_k13_query_event_subset_trial_union transitionRoom
        programmedCover source frontierExact
    _ ≤ q16SemanticOneForestRawError :=
      trials.failure_union_probability_le_one_forest (by
        simpa [ExactCompilerExposureTrial] using exposureCap)

#print axioms
  ExactCompilerCausalFinalWorkAnswerQ16Trials.event_probability_le_product
#print axioms ExactFixedCleanK13ResidualWorkInvariant
#print axioms exact_fixed_clean_k13_residual_work_bad_card
#print axioms exact_fixed_clean_k13_residual_work_bad_eq_pointwise
#print axioms exactFixedCleanK13WorkDependentExposureTrials
#print axioms
  exact_fixed_clean_work_dependent_k13_query_probability_le_one_forest

end

end AspisK1.V7Tag73ExactFixedCleanWorkDependentQ16Factorization
