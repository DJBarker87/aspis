import AspisFormal.K1.V7Tag73ExactFixedQ16ResidualFactorization
import AspisFormal.K1.V7Tag73ExactFixedInstanceEvent

/-!
# Clean-event residual factorization for fixed Tag-73 K1.3 q16

K1.6 consumes K1.2--K1.5 only on the literal fixed-instance legal same-tape
event.  The causal SHA target event is disjoint from this event and is bounded
separately by the exact compiler coefficient.  This module therefore repeats
the finite q16 fibre construction on exactly that clean domain.

The construction does not assume target cleanliness.  It retains cleanliness
as proof-relevant membership in every fibre, so the remaining source theorem
is the honest one: pointwise bad sets must agree only between two accepted,
target-clean members with the same hidden tape and residual coordinate.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

namespace AspisK1.V7Tag73ExactFixedCleanQ16ResidualFactorization

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73CausalQ16FinalWorkProbability
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactFixedInstanceEvent
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactFixedQ16ResidualFactorization
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkDigestProbability
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73OperationalQ16ForestHandoff
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact
open AspisV5WithoutReplacementQuerySoundness

noncomputable section

/-- One chronological K1.3 trial restricted to the exact fixed clean event. -/
def exactFixedCleanK13JointTrialEvent
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (trial : ExactCompilerExposureTrial parameters) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  exactFixedK13JointTrialEvent transitionFuel configuration projection
      fixedInstance decoder trial ∩
    exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration projection
      fixedInstance

/-- Exact noninterference obligation on the domain actually consumed by
K1.6.  No target-hit comparison is requested. -/
def ExactFixedCleanK13ResidualInvariant
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
    exactFixedK13PointwiseBad transitionFuel configuration projection
        fixedInstance decoder trial (hidden, left) =
      exactFixedK13PointwiseBad transitionFuel configuration projection
        fixedInstance decoder trial (hidden, right)

/-- The previous global invariant remains a sufficient, stronger endpoint. -/
theorem exact_fixed_clean_k13_residual_invariant_of_global
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (invariant : ExactFixedK13ResidualInvariant transitionFuel configuration
      projection fixedInstance decoder) :
    ExactFixedCleanK13ResidualInvariant transitionFuel configuration projection
      fixedInstance decoder := by
  intro trial hidden left right leftMember rightMember residualExact
  exact invariant trial hidden left right leftMember.1 rightMember.1 residualExact

/-- A clean residual fibre is inhabited by a genuine clean trial member. -/
def exactFixedCleanK13ResidualFibreNonempty
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
    (residual : ExactCompilerFinalWorkQ16Residual parameters) : Prop :=
  ∃ tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length,
    (hidden, tape) ∈ exactFixedCleanK13JointTrialEvent transitionFuel
        configuration projection fixedInstance decoder trial ∧
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, tape)).1 = residual

/-- Canonical bad set chosen only from the clean residual fibre. -/
noncomputable def exactFixedCleanK13ResidualBad
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
    (residual : ExactCompilerFinalWorkQ16Residual parameters) :
    Finset (Fin 262144) := by
  classical
  exact if inhabitedFibre : exactFixedCleanK13ResidualFibreNonempty
        transitionFuel configuration projection fixedInstance decoder trial
        hidden residual then
      exactFixedK13PointwiseBad transitionFuel configuration projection
        fixedInstance decoder trial (hidden, Classical.choose inhabitedFibre)
    else
      ∅

theorem exact_fixed_clean_k13_residual_bad_card
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (trial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (residual : ExactCompilerFinalWorkQ16Residual parameters) :
    (exactFixedCleanK13ResidualBad transitionFuel configuration projection
      fixedInstance decoder trial hidden residual).card ≤ 9557 := by
  classical
  by_cases inhabitedFibre : exactFixedCleanK13ResidualFibreNonempty
      transitionFuel configuration projection fixedInstance decoder trial
      hidden residual
  · simpa [exactFixedCleanK13ResidualBad, inhabitedFibre] using
      exact_fixed_k13_pointwise_bad_card
        (configuration := configuration) (projection := projection)
        (fixedInstance := fixedInstance) (decoder := decoder) trial
        (hidden, Classical.choose inhabitedFibre)
  · simp [exactFixedCleanK13ResidualBad, inhabitedFibre]

theorem exact_fixed_clean_k13_residual_bad_eq_pointwise
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (invariant : ExactFixedCleanK13ResidualInvariant transitionFuel configuration
      projection fixedInstance decoder)
    (trial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (member : (hidden, tape) ∈ exactFixedCleanK13JointTrialEvent transitionFuel
      configuration projection fixedInstance decoder trial) :
    exactFixedCleanK13ResidualBad transitionFuel configuration projection
        fixedInstance decoder trial hidden
          (exactFixedK13TrialCoordinates transitionFuel configuration trial
            (hidden, tape)).1 =
      exactFixedK13PointwiseBad transitionFuel configuration projection
        fixedInstance decoder trial (hidden, tape) := by
  classical
  let residual := (exactFixedK13TrialCoordinates transitionFuel configuration
    trial (hidden, tape)).1
  have inhabitedFibre : exactFixedCleanK13ResidualFibreNonempty transitionFuel
      configuration projection fixedInstance decoder trial hidden residual :=
    ⟨tape, member, rfl⟩
  let representative := Classical.choose inhabitedFibre
  have representativeFacts := Classical.choose_spec inhabitedFibre
  have sameResidual :
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, representative)).1 =
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, tape)).1 := representativeFacts.2
  have sameBad := invariant trial hidden representative tape
    representativeFacts.1 member sameResidual
  simpa [exactFixedCleanK13ResidualBad, inhabitedFibre, residual,
    representative] using sameBad

/-- Exact exposure-indexed q16 trials on clean members only. -/
noncomputable def exactFixedCleanK13ExposureTrials
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (invariant : ExactFixedCleanK13ResidualInvariant transitionFuel configuration
      projection fixedInstance decoder)
    (reference : AdmittedResult SemanticCap203Admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        reference.1)) :
    ExactCompilerExposureIndexedFinalWorkQ16Trials
      (HiddenTape := HiddenTape) parameters where
  event := exactFixedCleanK13JointTrialEvent transitionFuel configuration
    projection fixedInstance decoder
  router := fun trial hidden =>
    exactCompilerExposureTrialDagRouter parameters transitionFuel trial
      (exactPlainRomCursor configuration hidden).erase
  bad := exactFixedCleanK13ResidualBad transitionFuel configuration projection
    fixedInstance decoder
  badCard := exact_fixed_clean_k13_residual_bad_card
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
          finalWorkQ16SuccessfulBadEvent
            (exactFixedCleanK13ResidualBad transitionFuel configuration
              projection fixedInstance decoder trial hidden residual))
    let witness := Classical.choice member.1
    have residualEq := exact_fixed_clean_k13_residual_bad_eq_pointwise invariant
      trial hidden tape member
    have pointwiseEq :
        exactFixedK13PointwiseBad transitionFuel configuration projection
            fixedInstance decoder trial (hidden, tape) = witness.bad := by
      simpa [witness] using
        (exact_fixed_k13_pointwise_bad_eq_choice
          (configuration := configuration) (projection := projection)
          (fixedInstance := fixedInstance) (decoder := decoder) trial
          (hidden, tape) member.1)
    have badEq :
        exactFixedCleanK13ResidualBad transitionFuel configuration projection
            fixedInstance decoder trial hidden
              (exactFixedK13TrialCoordinates transitionFuel configuration trial
                (hidden, tape)).1 = witness.bad :=
      residualEq.trans pointwiseEq
    rcases witness.coordinate with ⟨success, badMember⟩
    refine ⟨success, ?_⟩
    change successfulFinalWorkQ16TotalEquiv
        ⟨(exactFixedK13TrialCoordinates transitionFuel configuration trial
          (hidden, tape)).2, success⟩ ∈
      finalWorkQ16SuccessfulBadEvent
        (exactFixedCleanK13ResidualBad transitionFuel configuration projection
          fixedInstance decoder trial hidden
            (exactFixedK13TrialCoordinates transitionFuel configuration trial
              (hidden, tape)).1)
    rw [badEq]
    exact badMember

/-- Clean q16 failures are covered by the union of clean chronological
trials. -/
theorem exact_fixed_clean_k13_query_event_subset_trial_union
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
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
        semanticFrontierNodes schedule.positions) :
    (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration projection
        fixedInstance ∩
      exactTag73K13QueryEvent transitionFuel configuration projection
        fixedInstance decoder) ⊆
      ⋃ trial : ExactCompilerExposureTrial parameters,
        exactFixedCleanK13JointTrialEvent transitionFuel configuration projection
          fixedInstance decoder trial := by
  intro sample member
  obtain ⟨trial, trialMember⟩ :=
    exact_fixed_k13_query_failure_has_joint_trial_witness transitionRoom
      programmedCover source (frontierExact sample) member.2
  exact Set.mem_iUnion.mpr ⟨trial, trialMember, member.1⟩

/-- Exact raw clean-event K1.3 q16 bound with the chronological exposure
factor retained. -/
theorem exact_fixed_clean_k13_query_probability_le_exposure_mul
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
    (invariant : ExactFixedCleanK13ResidualInvariant transitionFuel configuration
      projection fixedInstance decoder)
    (reference : AdmittedResult SemanticCap203Admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        reference.1)) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
            projection fixedInstance ∩
          exactTag73K13QueryEvent transitionFuel configuration projection
            fixedInstance decoder) ≤
      ((unifiedFull256ExposureCap parameters : ENNReal) *
        q16SemanticOneForestRawError) / (2 : ENNReal) ^ 34 := by
  let trials := exactFixedCleanK13ExposureTrials transitionFuel configuration
    projection fixedInstance decoder invariant reference traceExists
  calc
    _ ≤ (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (⋃ trial, trials.event trial) := by
      apply measure_mono
      exact exact_fixed_clean_k13_query_event_subset_trial_union transitionRoom
        programmedCover source frontierExact
    _ ≤ ((unifiedFull256ExposureCap parameters : ENNReal) *
          q16SemanticOneForestRawError) / (2 : ENNReal) ^ 34 :=
      trials.failure_union_probability_le_exposure_mul

/-- Release form for the clean q16 event. -/
theorem exact_fixed_clean_k13_query_probability_le_one_forest
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
    (invariant : ExactFixedCleanK13ResidualInvariant transitionFuel configuration
      projection fixedInstance decoder)
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
  let trials := exactFixedCleanK13ExposureTrials transitionFuel configuration
    projection fixedInstance decoder invariant reference traceExists
  calc
    _ ≤ (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (⋃ trial, trials.event trial) := by
      apply measure_mono
      exact exact_fixed_clean_k13_query_event_subset_trial_union transitionRoom
        programmedCover source frontierExact
    _ ≤ q16SemanticOneForestRawError :=
      trials.failure_union_probability_le_one_forest exposureCap

#print axioms exact_fixed_clean_k13_residual_invariant_of_global
#print axioms exact_fixed_clean_k13_residual_bad_card
#print axioms exact_fixed_clean_k13_residual_bad_eq_pointwise
#print axioms exactFixedCleanK13ExposureTrials
#print axioms exact_fixed_clean_k13_query_event_subset_trial_union
#print axioms exact_fixed_clean_k13_query_probability_le_exposure_mul
#print axioms exact_fixed_clean_k13_query_probability_le_one_forest

end

end AspisK1.V7Tag73ExactFixedCleanQ16ResidualFactorization
