import AspisFormal.K1.V7Tag73ExactPairTrialProbabilityClosure
import AspisFormal.K1.V7Tag73K13PreQ16JointEventHandoff

/-!
# Corrected pre-q16 two-trial K1.3 probability wrapper

This module combines the fold-armed alpha/final-work/q16 coordinate system
with the corrected pre-q16 K1.3 bad set.  In particular, the bad set is fixed
after conditioning on the four alpha blocks and both positioned work answers,
but before exposing the q16 forest.  It therefore neither assumes the false
q16-only alpha invariant nor reintroduces the old completed-transcript
circularity.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace AspisK1.V7Tag73K13CorrectedPairTrialProbability

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AdaptiveFoldFinalWorkQ16TrialAccounting
open AspisK1.V7Tag73CausalAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedInstanceEvent
open AspisK1.V7Tag73ExactFoldAlphaQ16OperationalRealization
open AspisK1.V7Tag73ExactFoldArmedQ16Routing
open AspisK1.V7Tag73ExactPairTrialProbabilityClosure
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkDigestProbability
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73K13PreQ16JointEventHandoff
open AspisK1.V7Tag73OperationalQ16ForestHandoff
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

/-- One corrected K1.3 failure indexed by its literal fold-work and
final-work exposure trials. -/
structure ExactPreQ16CleanK13PairTrialWitness
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (sample : ExactCompilerSample HiddenTape parameters)
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters) : Type where
  joint : ExactPreQ16K13JointTrialWitness transitionFuel configuration
    projection fixedInstance decoder sample finalTrial
  legal : sample ∈ exactFixedPlainRomLegalSameTapeEvent transitionFuel
    configuration projection fixedInstance
  foldExact : (exactAcceptedFoldTrial joint.input).trial = foldTrial

def exactPreQ16CleanK13PairTrialEvent
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | Nonempty (ExactPreQ16CleanK13PairTrialWitness transitionFuel
    configuration projection fixedInstance decoder sample foldTrial finalTrial)}

/-- The corrected pointwise bad set, totalized by the empty set off-event. -/
noncomputable def exactPreQ16CleanK13PairPointwiseBad
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (sample : ExactCompilerSample HiddenTape parameters) : Finset (Fin 262144) := by
  classical
  exact if member : Nonempty (ExactPreQ16CleanK13PairTrialWitness
      transitionFuel configuration projection fixedInstance decoder sample
        foldTrial finalTrial) then
    (Classical.choice member).joint.bad
  else ∅

theorem exact_preQ16_clean_k13_pair_pointwise_bad_card
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (sample : ExactCompilerSample HiddenTape parameters) :
    (exactPreQ16CleanK13PairPointwiseBad transitionFuel configuration projection
      fixedInstance decoder foldTrial finalTrial sample).card ≤ 9557 := by
  classical
  by_cases member : Nonempty (ExactPreQ16CleanK13PairTrialWitness
      transitionFuel configuration projection fixedInstance decoder sample
        foldTrial finalTrial)
  · simpa [exactPreQ16CleanK13PairPointwiseBad, member] using
      (Classical.choice member).joint.badCard
  · simp [exactPreQ16CleanK13PairPointwiseBad, member]

/-- The sole protocol-specific endpoint required by the generic probability
theorem.  The conditioning context includes all four alpha blocks and both
positioned work answers, but excludes every q16 answer. -/
def ExactPreQ16CleanK13PairCoordinateInvariant
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) : Prop :=
  ∀ (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
      (hidden : HiddenTape)
      (left right : FreshAnswerTape Digest256
        (exactCompilerTargetCaps parameters).length),
    (hidden, left) ∈ exactPreQ16CleanK13PairTrialEvent transitionFuel
      configuration projection fixedInstance decoder foldTrial finalTrial →
    (hidden, right) ∈ exactPreQ16CleanK13PairTrialEvent transitionFuel
      configuration projection fixedInstance decoder foldTrial finalTrial →
    let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
      transitionFuel foldTrial.val finalTrial.val
      (exactPlainRomCursor configuration hidden).erase
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        left).1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        right).1 →
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        left).2.1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        right).2.1 →
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        left).2.2.1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        right).2.2.1 →
    exactPreQ16CleanK13PairPointwiseBad transitionFuel configuration projection
        fixedInstance decoder foldTrial finalTrial (hidden, left) =
      exactPreQ16CleanK13PairPointwiseBad transitionFuel configuration projection
        fixedInstance decoder foldTrial finalTrial (hidden, right)

def exactPreQ16CleanK13PairFibreNonempty
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (context : ExactCompilerFoldAlphaFinalWorkQ16Residual parameters ×
      AlphaZeroDigestBlocks)
    (fold work : Digest256) : Prop :=
  let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
    transitionFuel foldTrial.val finalTrial.val
    (exactPlainRomCursor configuration hidden).erase
  ∃ tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length,
    (hidden, tape) ∈ exactPreQ16CleanK13PairTrialEvent transitionFuel
      configuration projection fixedInstance decoder foldTrial finalTrial ∧
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
      tape).1 = context ∧
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
      tape).2.1 = fold ∧
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
      tape).2.2.1 = work

noncomputable def exactPreQ16CleanK13PairFibreBad
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (context : ExactCompilerFoldAlphaFinalWorkQ16Residual parameters ×
      AlphaZeroDigestBlocks)
    (fold work : Digest256) : Finset (Fin 262144) := by
  classical
  exact if inhabited : exactPreQ16CleanK13PairFibreNonempty transitionFuel
      configuration projection fixedInstance decoder foldTrial finalTrial hidden
        context fold work then
    exactPreQ16CleanK13PairPointwiseBad transitionFuel configuration projection
      fixedInstance decoder foldTrial finalTrial
        (hidden, Classical.choose inhabited)
  else ∅

theorem exact_preQ16_clean_k13_pair_fibre_bad_card
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (context : ExactCompilerFoldAlphaFinalWorkQ16Residual parameters ×
      AlphaZeroDigestBlocks)
    (fold work : Digest256) :
    (exactPreQ16CleanK13PairFibreBad transitionFuel configuration projection
      fixedInstance decoder foldTrial finalTrial hidden context fold work).card ≤
        9557 := by
  classical
  by_cases inhabited : exactPreQ16CleanK13PairFibreNonempty transitionFuel
      configuration projection fixedInstance decoder foldTrial finalTrial hidden
        context fold work
  · simpa [exactPreQ16CleanK13PairFibreBad, inhabited] using
      exact_preQ16_clean_k13_pair_pointwise_bad_card
        (configuration := configuration) (projection := projection)
        (fixedInstance := fixedInstance) (decoder := decoder) foldTrial
        finalTrial (hidden, Classical.choose inhabited)
  · simp [exactPreQ16CleanK13PairFibreBad, inhabited]

theorem exact_preQ16_clean_k13_pair_fibre_bad_eq_pointwise
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (invariant : ExactPreQ16CleanK13PairCoordinateInvariant transitionFuel
      configuration projection fixedInstance decoder)
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (member : (hidden, tape) ∈ exactPreQ16CleanK13PairTrialEvent transitionFuel
      configuration projection fixedInstance decoder foldTrial finalTrial) :
    let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
      transitionFuel foldTrial.val finalTrial.val
      (exactPlainRomCursor configuration hidden).erase
    exactPreQ16CleanK13PairFibreBad transitionFuel configuration projection
        fixedInstance decoder foldTrial finalTrial hidden
          (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
            tape).1
          (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
            tape).2.1
          (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
            tape).2.2.1 =
      exactPreQ16CleanK13PairPointwiseBad transitionFuel configuration projection
        fixedInstance decoder foldTrial finalTrial (hidden, tape) := by
  classical
  let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
    transitionFuel foldTrial.val finalTrial.val
    (exactPlainRomCursor configuration hidden).erase
  let coordinates := exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates
    parameters router tape
  have inhabited : exactPreQ16CleanK13PairFibreNonempty transitionFuel
      configuration projection fixedInstance decoder foldTrial finalTrial hidden
        coordinates.1 coordinates.2.1 coordinates.2.2.1 :=
    ⟨tape, member, rfl, rfl, rfl⟩
  let representative := Classical.choose inhabited
  have facts := Classical.choose_spec inhabited
  have sameBad := invariant foldTrial finalTrial hidden representative tape
    facts.1 member facts.2.1 facts.2.2.1 facts.2.2.2
  simpa [exactPreQ16CleanK13PairFibreBad, inhabited, router, coordinates,
    representative] using sameBad

noncomputable def exactPreQ16CleanK13PairExposureTrials
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (frontierExact : ∀
      (sample : ExactCompilerSample HiddenTape parameters)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (schedule : QuerySchedule),
      (exactOperationalTape input).frontierNodes schedule =
        semanticFrontierNodes schedule.positions)
    (invariant : ExactPreQ16CleanK13PairCoordinateInvariant transitionFuel
      configuration projection fixedInstance decoder)
    (reference : AdmittedResult SemanticCap203Admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        reference.1)) :
    ExactCompilerExposurePairIndexedFoldAlphaFinalWorkQ16Trials
      (HiddenTape := HiddenTape) parameters where
  event := exactPreQ16CleanK13PairTrialEvent transitionFuel configuration
    projection fixedInstance decoder
  router := fun foldTrial finalTrial hidden =>
    exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters transitionFuel
      foldTrial.val finalTrial.val
      (exactPlainRomCursor configuration hidden).erase
  bad := fun foldTrial finalTrial hidden residual alpha fold work =>
    exactPreQ16CleanK13PairFibreBad transitionFuel configuration projection
      fixedInstance decoder foldTrial finalTrial hidden (residual, alpha) fold work
  badCard := fun foldTrial finalTrial hidden residual alpha fold work =>
    exact_preQ16_clean_k13_pair_fibre_bad_card
      (configuration := configuration) (projection := projection)
      (fixedInstance := fixedInstance) (decoder := decoder) foldTrial finalTrial
      hidden (residual, alpha) fold work
  reference := reference
  traceExists := traceExists
  covered := by
    intro foldTrial finalTrial hidden tape member
    change Nonempty (ExactPreQ16CleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, tape) foldTrial
        finalTrial) at member
    let witness := Classical.choice member
    let realization := Classical.choice
      (exact_compiler_accepted_fold_armed_q16_operational_realization
        transitionRoom programmedCover witness.joint.input
          (frontierExact (hidden, tape) witness.joint.input))
    have finalExact : realization.anchor.source.finalTrial = finalTrial := by
      rw [realization.anchor.sourceExact]
      exact (exact_fixed_k13_actual_trial_eq_accepted_installation transitionRoom
        witness.joint.input finalTrial witness.joint.actualTrial).symm
    let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
      transitionFuel foldTrial.val finalTrial.val
      (exactPlainRomCursor configuration hidden).erase
    have routerExact : realization.anchor.router = router := by
      rw [realization.anchor.routerExact, realization.anchor.foldExact,
        finalExact, witness.foldExact]
    let coordinates := exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates
      parameters router tape
    have q16Success : q16DigestForestSucceeds
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters
          realization.anchor.router tape).2.2.2 := by
      simpa using operational_realization_implies_q16_digest_forest_succeeds
        realization.forestRealized
    have pointwiseExact : exactPreQ16CleanK13PairPointwiseBad transitionFuel
        configuration projection fixedInstance decoder foldTrial finalTrial
          (hidden, tape) = witness.joint.bad := by
      simp [exactPreQ16CleanK13PairPointwiseBad, member, witness]
    have fibreExact := exact_preQ16_clean_k13_pair_fibre_bad_eq_pointwise
      invariant foldTrial finalTrial hidden tape member
    have badExact : exactPreQ16CleanK13PairFibreBad transitionFuel configuration
        projection fixedInstance decoder foldTrial finalTrial hidden
          coordinates.1 coordinates.2.1 coordinates.2.2.1 =
        witness.joint.bad := by
      simpa [router, coordinates] using fibreExact.trans pointwiseExact
    have allBad : AllInBad witness.joint.bad
        (semanticScheduleOfOperational
          (exactOperationalTape witness.joint.input).search.selectedSchedule) := by
      exact witness.joint.allBad
    have q16Bad := operational_all_in_bad_implies_successful_coordinate_bad
      realization.forestRealized witness.joint.bad allBad
    have badExactAnchor : exactPreQ16CleanK13PairFibreBad transitionFuel
        configuration projection fixedInstance decoder foldTrial finalTrial
        hidden
          (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters
            realization.anchor.router tape).1
          (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters
            realization.anchor.router tape).2.1
          (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters
            realization.anchor.router tape).2.2.1 = witness.joint.bad := by
      rw [routerExact]
      exact badExact
    simp only [Set.mem_preimage]
    change (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters
      router tape) ∈ dependentSuccessfulSubtypeEvent _ _
    rw [← routerExact]
    refine ⟨q16Success, ?_⟩
    change FoldWork31Accepted _ ∧ FinalWork34Accepted _ ∧ _
    refine ⟨realization.anchor.foldCoordinate ▸
      realization.anchor.fold.accepted,
      realization.anchor.workCoordinate ▸
        realization.anchor.source.workAccepted, ?_⟩
    change successfulQ16DigestForestEquiv
        ⟨(exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters
          realization.anchor.router tape).2.2.2, q16Success⟩ ∈
      q16SuccessfulCoordinatesBadEvent
        (exactPreQ16CleanK13PairFibreBad transitionFuel configuration projection
          fixedInstance decoder foldTrial finalTrial hidden
          (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters
            realization.anchor.router tape).1
          (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters
            realization.anchor.router tape).2.1
          (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters
            realization.anchor.router tape).2.2.1)
    rw [badExactAnchor]
    exact q16Bad

theorem exact_preQ16_clean_pair_trial_union_probability_le_one_forest
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
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (frontierExact : ∀
      (sample : ExactCompilerSample HiddenTape parameters)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (schedule : QuerySchedule),
      (exactOperationalTape input).frontierNodes schedule =
        semanticFrontierNodes schedule.positions)
    (invariant : ExactPreQ16CleanK13PairCoordinateInvariant transitionFuel
      configuration projection fixedInstance decoder)
    (reference : AdmittedResult SemanticCap203Admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        reference.1))
    (foldExposureCap : unifiedFull256ExposureCap parameters ≤ 2 ^ 31)
    (finalExposureCap : unifiedFull256ExposureCap parameters ≤ 2 ^ 34) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (⋃ foldTrial, ⋃ finalTrial,
          exactPreQ16CleanK13PairTrialEvent transitionFuel configuration
            projection fixedInstance decoder foldTrial finalTrial) ≤
      q16SemanticOneForestRawError := by
  let trials := exactPreQ16CleanK13PairExposureTrials transitionFuel
    configuration projection fixedInstance decoder transitionRoom
      programmedCover frontierExact invariant reference traceExists
  exact trials.failure_union_probability_le_one_forest foldExposureCap
    finalExposureCap

#print axioms ExactPreQ16CleanK13PairTrialWitness
#print axioms exact_preQ16_clean_k13_pair_pointwise_bad_card
#print axioms ExactPreQ16CleanK13PairCoordinateInvariant
#print axioms exact_preQ16_clean_k13_pair_fibre_bad_card
#print axioms exact_preQ16_clean_k13_pair_fibre_bad_eq_pointwise
#print axioms exactPreQ16CleanK13PairExposureTrials
#print axioms exact_preQ16_clean_pair_trial_union_probability_le_one_forest

end

end AspisK1.V7Tag73K13CorrectedPairTrialProbability
