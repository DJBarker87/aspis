import AspisFormal.K1.V7Tag73K13PreQ16RootInvariant
import AspisFormal.K1.V7Tag73ExactAlphaZeroRootOrder

/-!
# Alpha terminal invariance for the corrected pre-q16 K1.3 fibre

The selected q16 answer is removed from the causal residual.  This leaf first
shows that the accepted alpha-zero chains nevertheless reach the same digest.
It uses the common retained `final256` creation record and the accepted
final-nonce record; no SHA injectivity or role classifier is assumed.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace AspisK1.V7Tag73K13PreQ16AlphaInvariant

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactAdversaryAnchorSelectedInputInvariant
open AspisK1.V7Tag73ExactAlphaZeroActualTrialPrefinal
open AspisK1.V7Tag73ExactAlphaZeroRootOrder
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactFixedQ16VerifierAnchorInvariant
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRootCausalChain
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K13PreQ16JointEventHandoff
open AspisK1.V7Tag73K13PreQ16RootInvariant
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Equal corrected residuals fix the transcript digest reached immediately
after the accepted alpha-zero challenge. -/
theorem exact_preQ16_k13_alpha_terminal_digest_eq
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (trial : ExactCompilerExposureTrial parameters) (hidden : HiddenTape)
    (left right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (leftWitness : ExactPreQ16K13JointTrialWitness transitionFuel configuration
      projection fixedInstance decoder (hidden, left) trial)
    (rightWitness : ExactPreQ16K13JointTrialWitness transitionFuel configuration
      projection fixedInstance decoder (hidden, right) trial)
    (residualExact :
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, left)).1 =
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, right)).1) :
    ∃ leftAfterAlpha rightAfterAlpha : EvalState,
      leftAfterAlpha.digest = rightAfterAlpha.digest := by
  classical
  obtain ⟨leftCanonicalBefore, rightCanonicalBefore, commonDigest,
      leftCanonicalActor, rightCanonicalActor, canonicalInputExact,
      leftCanonicalLookup, rightCanonicalLookup, leftCanonicalMember,
      rightCanonicalMember, leftCommonPrefix, rightCommonPrefix⟩ :=
    exact_preQ16_k13_common_final256_record transitionRoom programmedCover
      trial hidden left right leftWitness rightWitness residualExact
  obtain ⟨_leftProducer, leftFinal256Input, _leftBeforeAlpha,
      leftAfterAlpha, _leftAfterBlocks, leftAfterFinal256, _leftOutputs,
      _leftAdvances, _leftValue, _leftWorkAnswer, leftQ16Base,
      _leftProducerLookup, _leftProducerBoundary, _leftOrdered,
      _leftOutputsLength, _leftOutputsPositive, _leftAdvancesLength,
      _leftTerminalExact, _leftAfterAlphaExact, leftFinal256InputExact,
      leftFinal256Lookup, _leftWorkLookup, _leftWorkAccepted,
      leftFinalNonceLookup, leftQ16BaseExact, _leftAcceptedParameter,
      _leftDecode, _leftOperational⟩ :=
    exact_compiler_alpha_zero_chain_has_root_order transitionRoom
      leftWitness.input
  obtain ⟨_rightProducer, rightFinal256Input, _rightBeforeAlpha,
      rightAfterAlpha, _rightAfterBlocks, rightAfterFinal256, _rightOutputs,
      _rightAdvances, _rightValue, _rightWorkAnswer, rightQ16Base,
      _rightProducerLookup, _rightProducerBoundary, _rightOrdered,
      _rightOutputsLength, _rightOutputsPositive, _rightAdvancesLength,
      _rightTerminalExact, _rightAfterAlphaExact, rightFinal256InputExact,
      rightFinal256Lookup, _rightWorkLookup, _rightWorkAccepted,
      rightFinalNonceLookup, rightQ16BaseExact, _rightAcceptedParameter,
      _rightDecode, _rightOperational⟩ :=
    exact_compiler_alpha_zero_chain_has_root_order transitionRoom
      rightWitness.input
  obtain ⟨_leftPrior, _leftLater, _leftSelectedActor, _leftSelectedInput,
      _leftSelectedAnswer, leftSelectedDigest, leftSelectedBase,
      leftSelectedAbsorbActor, _leftRootExact, _leftTrialExact,
      leftSelectedPrefix, _leftPrefinalOrigin, leftSelectedBaseExact,
      leftSelectedAbsorbMember⟩ :=
    exact_fixed_k13_actual_trial_has_selected_prefinal_prefix
      leftWitness.input trial leftWitness.actualTrial
  obtain ⟨_rightPrior, _rightLater, _rightSelectedActor,
      _rightSelectedInput, _rightSelectedAnswer, rightSelectedDigest,
      rightSelectedBase, rightSelectedAbsorbActor, _rightRootExact,
      _rightTrialExact, rightSelectedPrefix, _rightPrefinalOrigin,
      rightSelectedBaseExact, rightSelectedAbsorbMember⟩ :=
    exact_fixed_k13_actual_trial_has_selected_prefinal_prefix
      rightWitness.input trial rightWitness.actualTrial
  have leftAfterFinalExact :
      leftAfterFinal256.digest = leftSelectedDigest :=
    final_nonce_lookup_and_root_record_fix_digest leftWitness.input
      leftAfterFinal256.digest leftSelectedDigest leftQ16Base leftSelectedBase
      leftSelectedAbsorbActor leftFinalNonceLookup
      (leftQ16BaseExact.trans leftSelectedBaseExact.symm)
      leftSelectedAbsorbMember
  have rightAfterFinalExact :
      rightAfterFinal256.digest = rightSelectedDigest :=
    final_nonce_lookup_and_root_record_fix_digest rightWitness.input
      rightAfterFinal256.digest rightSelectedDigest rightQ16Base
      rightSelectedBase rightSelectedAbsorbActor rightFinalNonceLookup
      (rightQ16BaseExact.trans rightSelectedBaseExact.symm)
      rightSelectedAbsorbMember
  have leftSelectedInputExact :
      _leftSelectedInput = leftWitness.pivotInput := by
    have actualAt :
        (exactFixedRootRecords leftWitness.input.package.root)[trial.val]? =
          some (.machineFresh _leftSelectedActor _leftSelectedInput
            _leftSelectedAnswer : UnifiedExposureRecord) := by
      rw [_leftRootExact, _leftTrialExact]
      simp
    have witnessAt :
        (exactFixedRootRecords leftWitness.input.package.root)[trial.val]? =
          some (.machineFresh leftWitness.pivotActor leftWitness.pivotInput
            leftWitness.pivotAnswer : UnifiedExposureRecord) := by
      rw [leftWitness.rootExact, leftWitness.trialExact]
      simp
    rw [actualAt] at witnessAt
    have recordExact := Option.some.inj witnessAt
    injection recordExact
  have rightSelectedInputExact :
      _rightSelectedInput = rightWitness.pivotInput := by
    have actualAt :
        (exactFixedRootRecords rightWitness.input.package.root)[trial.val]? =
          some (.machineFresh _rightSelectedActor _rightSelectedInput
            _rightSelectedAnswer : UnifiedExposureRecord) := by
      rw [_rightRootExact, _rightTrialExact]
      simp
    have witnessAt :
        (exactFixedRootRecords rightWitness.input.package.root)[trial.val]? =
          some (.machineFresh rightWitness.pivotActor rightWitness.pivotInput
            rightWitness.pivotAnswer : UnifiedExposureRecord) := by
      rw [rightWitness.rootExact, rightWitness.trialExact]
      simp
    rw [actualAt] at witnessAt
    have recordExact := Option.some.inj witnessAt
    injection recordExact
  have leftSelectedCommon : leftSelectedDigest = commonDigest :=
    literal_prefix_input_eq_fixes_digest leftSelectedPrefix leftCommonPrefix
      leftSelectedInputExact
  have rightSelectedCommon : rightSelectedDigest = commonDigest :=
    literal_prefix_input_eq_fixes_digest rightSelectedPrefix rightCommonPrefix
      rightSelectedInputExact
  have leftAfterFinalCommon : leftAfterFinal256.digest = commonDigest :=
    leftAfterFinalExact.trans leftSelectedCommon
  have rightAfterFinalCommon : rightAfterFinal256.digest = commonDigest :=
    rightAfterFinalExact.trans rightSelectedCommon
  let leftCanonicalInput : ShaInput := bytes leftCanonicalBefore.digest ++
    [domAbsorb,
      (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
        (exactOperationalTape leftWitness.input).messages.finalValues).label] ++
    (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
      (exactOperationalTape leftWitness.input).messages.finalValues).data
  let rightCanonicalInput : ShaInput := bytes rightCanonicalBefore.digest ++
    [domAbsorb,
      (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
        (exactOperationalTape rightWitness.input).messages.finalValues).label] ++
    (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
      (exactOperationalTape rightWitness.input).messages.finalValues).data
  obtain ⟨leftAlphaActor, leftAlphaMember⟩ :=
    exact_final_table_lookup_has_root_record leftWitness.input
      leftFinal256Input commonDigest (by
        simpa [leftAfterFinalCommon] using leftFinal256Lookup)
  obtain ⟨rightAlphaActor, rightAlphaMember⟩ :=
    exact_final_table_lookup_has_root_record rightWitness.input
      rightFinal256Input commonDigest (by
        simpa [rightAfterFinalCommon] using rightFinal256Lookup)
  have leftCanonicalRootMember :
      (.machineFresh leftCanonicalActor leftCanonicalInput commonDigest :
        UnifiedExposureRecord) ∈
          exactFixedRootRecords leftWitness.input.package.root := by
    rw [leftWitness.rootExact]
    exact List.mem_append_left _ (by
      simpa [leftCanonicalInput] using leftCanonicalMember)
  have rightCanonicalRootMember :
      (.machineFresh rightCanonicalActor rightCanonicalInput commonDigest :
        UnifiedExposureRecord) ∈
          exactFixedRootRecords rightWitness.input.package.root := by
    rw [rightWitness.rootExact]
    exact List.mem_append_left _ (by
      simpa [rightCanonicalInput] using rightCanonicalMember)
  have leftFinalInputExact : leftFinal256Input = leftCanonicalInput := by
    have recordExact :
        (.machineFresh leftAlphaActor leftFinal256Input commonDigest :
            UnifiedExposureRecord) =
          .machineFresh leftCanonicalActor leftCanonicalInput commonDigest := by
      apply List.inj_on_of_nodup_map
        (exact_root_record_answers_nodup leftWitness.input)
        leftAlphaMember leftCanonicalRootMember
      rfl
    injection recordExact
  have rightFinalInputExact : rightFinal256Input = rightCanonicalInput := by
    have recordExact :
        (.machineFresh rightAlphaActor rightFinal256Input commonDigest :
            UnifiedExposureRecord) =
          .machineFresh rightCanonicalActor rightCanonicalInput commonDigest := by
      apply List.inj_on_of_nodup_map
        (exact_root_record_answers_nodup rightWitness.input)
        rightAlphaMember rightCanonicalRootMember
      rfl
    injection recordExact
  have leftTerminalExact :
      leftAfterAlpha.digest = leftCanonicalBefore.digest := by
    have prefixExact := congrArg (List.take 32) leftFinalInputExact
    have bytesExact : bytes leftAfterAlpha.digest =
        bytes leftCanonicalBefore.digest := by
      simpa [leftFinal256InputExact, leftCanonicalInput] using prefixExact
    exact List.ofFn_injective bytesExact
  have rightTerminalExact :
      rightAfterAlpha.digest = rightCanonicalBefore.digest := by
    have prefixExact := congrArg (List.take 32) rightFinalInputExact
    have bytesExact : bytes rightAfterAlpha.digest =
        bytes rightCanonicalBefore.digest := by
      simpa [rightFinal256InputExact, rightCanonicalInput] using prefixExact
    exact List.ofFn_injective bytesExact
  have canonicalDigestExact :
      leftCanonicalBefore.digest = rightCanonicalBefore.digest := by
    have prefixExact := congrArg (List.take 32) canonicalInputExact
    have bytesExact : bytes leftCanonicalBefore.digest =
        bytes rightCanonicalBefore.digest := by
      simpa [leftCanonicalInput, rightCanonicalInput] using prefixExact
    exact List.ofFn_injective bytesExact
  exact ⟨leftAfterAlpha, rightAfterAlpha,
    leftTerminalExact.trans
      (canonicalDigestExact.trans rightTerminalExact.symm)⟩

#print axioms exact_preQ16_k13_alpha_terminal_digest_eq

end

end AspisK1.V7Tag73K13PreQ16AlphaInvariant
