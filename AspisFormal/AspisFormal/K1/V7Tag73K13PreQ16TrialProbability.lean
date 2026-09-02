import AspisFormal.K1.V7Tag73K13PreQ16JointEventHandoff
import AspisFormal.K1.V7Tag73ExactFixedCleanWorkDependentQ16Factorization

/-!
# Probability wrapper for corrected pre-q16 K1.3 trials

This is the finite-measure wrapper for the corrected event.  The canonical
bad set is chosen within a fibre after fixing the hidden tape, final-work
residual and already exposed final-work answer.  The sole protocol-specific
noninterference endpoint is stated explicitly below; the generic 34-bit work
and first-cap-203 q16 calculation is reused unchanged.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

namespace AspisK1.V7Tag73K13PreQ16TrialProbability

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73CausalQ16FinalWorkDependentBad
open AspisK1.V7Tag73CausalQ16FinalWorkProbability
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactFixedCleanWorkDependentQ16Factorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkDigestProbability
open AspisK1.V7Tag73K13PreQ16JointEventHandoff
open AspisK1.V7Tag73OperationalSemanticReplay
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

/-- The actual bad set carried by one corrected trial member, or empty off the
event. -/
noncomputable def exactPreQ16K13PointwiseBad
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (trial : ExactCompilerExposureTrial parameters)
    (sample : ExactCompilerSample HiddenTape parameters) :
    Finset (Fin 262144) := by
  classical
  exact if member : Nonempty (ExactPreQ16K13JointTrialWitness transitionFuel
      configuration projection fixedInstance decoder sample trial) then
    (Classical.choice member).bad
  else ∅

theorem exact_preQ16_k13_pointwise_bad_card
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (trial : ExactCompilerExposureTrial parameters)
    (sample : ExactCompilerSample HiddenTape parameters) :
    (exactPreQ16K13PointwiseBad transitionFuel configuration projection
      fixedInstance decoder trial sample).card ≤ 9557 := by
  classical
  by_cases member : Nonempty (ExactPreQ16K13JointTrialWitness transitionFuel
      configuration projection fixedInstance decoder sample trial)
  · simpa [exactPreQ16K13PointwiseBad, member] using
      (Classical.choice member).badCard
  · simp [exactPreQ16K13PointwiseBad, member]

/-- Exact remaining causal endpoint: inside one final-work residual/answer
fibre, two corrected accepted trials choose the same pre-q16 bad set. -/
def ExactPreQ16K13ResidualWorkInvariant
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
    (hidden, left) ∈ exactPreQ16K13JointTrialEvent transitionFuel
        configuration projection fixedInstance decoder trial →
    (hidden, right) ∈ exactPreQ16K13JointTrialEvent transitionFuel
        configuration projection fixedInstance decoder trial →
    (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, left)).1 =
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, right)).1 →
    (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, left)).2.1 =
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, right)).2.1 →
    exactPreQ16K13PointwiseBad transitionFuel configuration projection
        fixedInstance decoder trial (hidden, left) =
      exactPreQ16K13PointwiseBad transitionFuel configuration projection
        fixedInstance decoder trial (hidden, right)

def exactPreQ16K13ResidualWorkFibreNonempty
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (trial : ExactCompilerExposureTrial parameters) (hidden : HiddenTape)
    (residual : ExactCompilerFinalWorkQ16Residual parameters)
    (work : Digest256) : Prop :=
  ∃ tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length,
    (hidden, tape) ∈ exactPreQ16K13JointTrialEvent transitionFuel
        configuration projection fixedInstance decoder trial ∧
    (exactFixedK13TrialCoordinates transitionFuel configuration trial
      (hidden, tape)).1 = residual ∧
    (exactFixedK13TrialCoordinates transitionFuel configuration trial
      (hidden, tape)).2.1 = work

noncomputable def exactPreQ16K13ResidualWorkBad
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (trial : ExactCompilerExposureTrial parameters) (hidden : HiddenTape)
    (residual : ExactCompilerFinalWorkQ16Residual parameters)
    (work : Digest256) : Finset (Fin 262144) := by
  classical
  exact if inhabited : exactPreQ16K13ResidualWorkFibreNonempty transitionFuel
      configuration projection fixedInstance decoder trial hidden residual work
    then exactPreQ16K13PointwiseBad transitionFuel configuration projection
      fixedInstance decoder trial (hidden, Classical.choose inhabited)
    else ∅

theorem exact_preQ16_k13_residual_work_bad_card
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
    (exactPreQ16K13ResidualWorkBad transitionFuel configuration projection
      fixedInstance decoder trial hidden residual work).card ≤ 9557 := by
  classical
  by_cases inhabited : exactPreQ16K13ResidualWorkFibreNonempty transitionFuel
      configuration projection fixedInstance decoder trial hidden residual work
  · simpa [exactPreQ16K13ResidualWorkBad, inhabited] using
      exact_preQ16_k13_pointwise_bad_card
        (configuration := configuration) (projection := projection)
        (fixedInstance := fixedInstance) (decoder := decoder) trial
        (hidden, Classical.choose inhabited)
  · simp [exactPreQ16K13ResidualWorkBad, inhabited]

theorem exact_preQ16_k13_residual_work_bad_eq_pointwise
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (invariant : ExactPreQ16K13ResidualWorkInvariant transitionFuel
      configuration projection fixedInstance decoder)
    (trial : ExactCompilerExposureTrial parameters) (hidden : HiddenTape)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (member : (hidden, tape) ∈ exactPreQ16K13JointTrialEvent transitionFuel
      configuration projection fixedInstance decoder trial) :
    exactPreQ16K13ResidualWorkBad transitionFuel configuration projection
        fixedInstance decoder trial hidden
          (exactFixedK13TrialCoordinates transitionFuel configuration trial
            (hidden, tape)).1
          (exactFixedK13TrialCoordinates transitionFuel configuration trial
            (hidden, tape)).2.1 =
      exactPreQ16K13PointwiseBad transitionFuel configuration projection
        fixedInstance decoder trial (hidden, tape) := by
  classical
  let residual := (exactFixedK13TrialCoordinates transitionFuel configuration
    trial (hidden, tape)).1
  let work := (exactFixedK13TrialCoordinates transitionFuel configuration trial
    (hidden, tape)).2.1
  have inhabited : exactPreQ16K13ResidualWorkFibreNonempty transitionFuel
      configuration projection fixedInstance decoder trial hidden residual work :=
    ⟨tape, member, rfl, rfl⟩
  let representative := Classical.choose inhabited
  have facts := Classical.choose_spec inhabited
  have sameBad := invariant trial hidden representative tape facts.1 member
    facts.2.1 facts.2.2
  simpa [exactPreQ16K13ResidualWorkBad, inhabited, residual, work,
    representative] using sameBad

noncomputable def exactPreQ16K13WorkDependentTrials
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (invariant : ExactPreQ16K13ResidualWorkInvariant transitionFuel
      configuration projection fixedInstance decoder)
    (reference : AdmittedResult SemanticCap203Admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        reference.1)) :
    ExactCompilerCausalFinalWorkAnswerQ16Trials
      (HiddenTape := HiddenTape)
      (Trial := ExactCompilerExposureTrial parameters) parameters where
  event := exactPreQ16K13JointTrialEvent transitionFuel configuration
    projection fixedInstance decoder
  router := fun trial hidden => exactCompilerExposureTrialDagRouter parameters
    transitionFuel trial (exactPlainRomCursor configuration hidden).erase
  bad := exactPreQ16K13ResidualWorkBad transitionFuel configuration projection
    fixedInstance decoder
  badCard := exact_preQ16_k13_residual_work_bad_card
    (configuration := configuration) (projection := projection)
    (fixedInstance := fixedInstance) (decoder := decoder)
  reference := reference
  traceExists := traceExists
  covered := by
    intro trial hidden tape member
    have member' : Nonempty (ExactPreQ16K13JointTrialWitness transitionFuel
        configuration projection fixedInstance decoder (hidden, tape) trial) :=
      member
    let witness := Classical.choice member'
    have canonicalEq := exact_preQ16_k13_residual_work_bad_eq_pointwise
      invariant trial hidden tape member
    have pointwiseEq : exactPreQ16K13PointwiseBad transitionFuel configuration
        projection fixedInstance decoder trial (hidden, tape) = witness.bad := by
      rw [exactPreQ16K13PointwiseBad, dif_pos member']
    have badEq := canonicalEq.trans pointwiseEq
    rcases witness.coordinate with ⟨success, badMember⟩
    refine ⟨success, ?_⟩
    change successfulFinalWorkQ16TotalEquiv
        ⟨(exactFixedK13TrialCoordinates transitionFuel configuration trial
          (hidden, tape)).2, success⟩ ∈
      finalWorkQ16SuccessfulDependentBadEvent
        (exactPreQ16K13ResidualWorkBad transitionFuel configuration projection
          fixedInstance decoder trial hidden
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
            (exactPreQ16K13ResidualWorkBad transitionFuel configuration
              projection fixedInstance decoder trial hidden
                (exactFixedK13TrialCoordinates transitionFuel configuration
                  trial (hidden, tape)).1
                (exactFixedK13TrialCoordinates transitionFuel configuration
                  trial (hidden, tape)).2.1)
    rw [badEq]
    exact badMember

theorem exact_preQ16_k13_trial_union_probability_le_one_forest
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
    (invariant : ExactPreQ16K13ResidualWorkInvariant transitionFuel
      configuration projection fixedInstance decoder)
    (reference : AdmittedResult SemanticCap203Admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        reference.1))
    (exposureCap : unifiedFull256ExposureCap parameters ≤ 2 ^ 34) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (⋃ trial : ExactCompilerExposureTrial parameters,
          exactPreQ16K13JointTrialEvent transitionFuel configuration projection
            fixedInstance decoder trial) ≤ q16SemanticOneForestRawError := by
  let trials := exactPreQ16K13WorkDependentTrials transitionFuel configuration
    projection fixedInstance decoder invariant reference traceExists
  exact trials.failure_union_probability_le_one_forest (by
    simpa [ExactCompilerExposureTrial] using exposureCap)

#print axioms exact_preQ16_k13_pointwise_bad_card
#print axioms ExactPreQ16K13ResidualWorkInvariant
#print axioms exact_preQ16_k13_residual_work_bad_card
#print axioms exact_preQ16_k13_residual_work_bad_eq_pointwise
#print axioms exactPreQ16K13WorkDependentTrials
#print axioms exact_preQ16_k13_trial_union_probability_le_one_forest

end

end AspisK1.V7Tag73K13PreQ16TrialProbability
