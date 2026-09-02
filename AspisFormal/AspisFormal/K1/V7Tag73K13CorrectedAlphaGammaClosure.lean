import AspisFormal.K1.V7Tag73K13CorrectedPairProfileInvariant
import AspisFormal.K1.V7Tag73ExactAlphaZeroActualTrialPrefinal
import AspisFormal.K1.V7Tag73ExactPairAlphaAdvanceChainClosure

/-!
# Corrected K1.3 alpha/gamma causal closure

This leaf works only with the corrected pre-q16 witness.  It exposes the
common canonical final256 record retained by the equal selected prefixes, then
uses that record as the terminal anchor for variable-prefix alpha and gamma
duplex replay.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73K13CorrectedAlphaGammaClosure

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactAdversaryAnchorSelectedInputInvariant
open AspisK1.V7Tag73ExactAlphaZeroActualTrialPrefinal
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRootCausalChain
open AspisK1.V7Tag73ExactPairAlphaAdvanceChainClosure
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K13CorrectedPairProfileInvariant
open AspisK1.V7Tag73K13CorrectedPairTrialProbability
open AspisK1.V7Tag73K13PreQ16JointEventHandoff
open AspisK1.V7Tag73K13PreQ16RootInvariant
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73RootAbsorbInputInjectivity
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- The two canonical final256 producer records have the same input and
answer inside the shared pre-anchor prefix. -/
theorem exact_preQ16_clean_pair_common_final256_record
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (transitionRoom : 2 ≤ transitionFuel)
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (left right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (leftWitness : ExactPreQ16CleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, left) foldTrial
        finalTrial)
    (rightWitness : ExactPreQ16CleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, right) foldTrial
        finalTrial)
    (priorExact : leftWitness.joint.prior = rightWitness.joint.prior) :
    ∃ (leftBefore rightBefore : EvalState) (digest : Digest256)
        (leftActor rightActor : QueryActor),
      let leftInput := bytes leftBefore.digest ++ [domAbsorb, final256Label] ++
        encodeBlocks
          (exactOperationalTape leftWitness.joint.input).messages.finalValues
      let rightInput := bytes rightBefore.digest ++ [domAbsorb, final256Label] ++
        encodeBlocks
          (exactOperationalTape rightWitness.joint.input).messages.finalValues
      leftInput = rightInput ∧
        tableLookup (exactOperationalTable leftWitness.joint.input) leftInput =
          some digest ∧
        tableLookup (exactOperationalTable rightWitness.joint.input) rightInput =
          some digest ∧
        (.machineFresh leftActor leftInput digest : UnifiedExposureRecord) ∈
          leftWitness.joint.prior ∧
        (.machineFresh rightActor rightInput digest : UnifiedExposureRecord) ∈
          rightWitness.joint.prior ∧
        HasLiteralStatePrefix digest leftWitness.joint.pivotInput ∧
        HasLiteralStatePrefix digest rightWitness.joint.pivotInput := by
  classical
  obtain ⟨leftBefore, leftDigest, leftActor, leftLookup, leftMember,
      leftPrefix⟩ := exact_preQ16_k13_final256_record_mem_prior
        transitionRoom finalTrial leftWitness.joint
  obtain ⟨rightBefore, rightDigest, rightActor, rightLookup, rightMember,
      rightPrefix⟩ := exact_preQ16_k13_final256_record_mem_prior
        transitionRoom finalTrial rightWitness.joint
  have selectedInputExact := exact_preQ16_clean_pair_selected_input_eq foldTrial
    finalTrial hidden left right leftWitness rightWitness priorExact
  have digestExact : leftDigest = rightDigest :=
    literal_prefix_input_eq_fixes_digest leftPrefix rightPrefix
      selectedInputExact
  let leftInput : ShaInput := bytes leftBefore.digest ++ [domAbsorb,
    final256Label] ++ encodeBlocks
      (exactOperationalTape leftWitness.joint.input).messages.finalValues
  let rightInput : ShaInput := bytes rightBefore.digest ++ [domAbsorb,
    final256Label] ++ encodeBlocks
      (exactOperationalTape rightWitness.joint.input).messages.finalValues
  have rightMemberCommon :
      (.machineFresh rightActor rightInput leftDigest : UnifiedExposureRecord) ∈
        leftWitness.joint.prior := by
    rw [priorExact]
    simpa [rightInput, digestExact,
      AspisK1.V7Tag73TranscriptSchedule.Payload.label,
      AspisK1.V7Tag73TranscriptSchedule.Payload.data] using rightMember
  have priorAnswersNodup :
      (leftWitness.joint.prior.map UnifiedExposureRecord.answer).Nodup := by
    have fullNodup := exact_root_record_answers_nodup leftWitness.joint.input
    rw [leftWitness.joint.rootExact, List.map_append, List.map_cons] at fullNodup
    exact (List.nodup_append.mp fullNodup).1
  have inputExact : leftInput = rightInput := by
    have recordExact :
        (.machineFresh leftActor leftInput leftDigest : UnifiedExposureRecord) =
          .machineFresh rightActor rightInput leftDigest :=
      List.inj_on_of_nodup_map priorAnswersNodup
        (by simpa [leftInput,
          AspisK1.V7Tag73TranscriptSchedule.Payload.label,
          AspisK1.V7Tag73TranscriptSchedule.Payload.data] using leftMember)
        rightMemberCommon rfl
    injection recordExact
  refine ⟨leftBefore, rightBefore, leftDigest, leftActor, rightActor, ?_⟩
  exact ⟨inputExact,
    by simpa [leftInput,
      AspisK1.V7Tag73TranscriptSchedule.Payload.label,
      AspisK1.V7Tag73TranscriptSchedule.Payload.data] using leftLookup,
    by simpa [rightInput, digestExact,
      AspisK1.V7Tag73TranscriptSchedule.Payload.label,
      AspisK1.V7Tag73TranscriptSchedule.Payload.data] using rightLookup,
    by simpa [leftInput,
      AspisK1.V7Tag73TranscriptSchedule.Payload.label,
      AspisK1.V7Tag73TranscriptSchedule.Payload.data] using leftMember,
    by simpa [rightInput, digestExact,
      AspisK1.V7Tag73TranscriptSchedule.Payload.label,
      AspisK1.V7Tag73TranscriptSchedule.Payload.data] using rightMember,
    leftPrefix, by simpa [digestExact] using rightPrefix⟩

#print axioms exact_preQ16_clean_pair_common_final256_record

end

end AspisK1.V7Tag73K13CorrectedAlphaGammaClosure
