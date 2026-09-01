import AspisFormal.K1.V7Tag73ExactPairTrialProbabilityClosure
import AspisFormal.K1.V7Tag73FoldAlphaPreFinalPrefix
import AspisFormal.K1.V7Tag73ExactFixedCleanQ16ProfileInvariant

/-!
# Complete-coordinate K1.3 source noninterference

This module replaces the obsolete 513-residual pre-anchor replay with the
complete fold/alpha/final-work/q16 controller.  The first endpoint below
reaches the identical literal adversary request on two tapes while leaving
the later q16 forest free.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace AspisK1.V7Tag73ExactPairCoordinateProfileInvariant

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedCleanQ16ProfileInvariant
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactFixedQ16VerifierAnchorInvariant
open AspisK1.V7Tag73ExactPairTrialProbabilityClosure
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRootPriorQueryHistory
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FoldAlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73FoldAlphaPreFinalPrefix
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73ProjectedMachineNativeRequestPrefix
open AspisK1.V7Tag73SchedulerCausalStateAlignment
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerNativePrefixTraversal
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Equal complete context and fold coordinates replay the raw master-tape
prefix before a clean adversary-owned final-work anchor. -/
theorem exact_fixed_clean_pair_k13_adversary_anchor_replays_raw_pre_anchor_tape
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
    (left right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (leftWitness : ExactFixedCleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, left) foldTrial
        finalTrial)
    (anchor : ExactFixedK13AdversaryAnchor leftWitness.joint.input finalTrial)
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (contextExact :
      let router := exactCompilerFoldAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val
        (alphaFinalWorkQ16DagController transitionFuel finalTrial.val
          (alphaZeroCausalController transitionFuel 0))
        (inactiveAlphaZeroMemory, inactiveDagMemory)
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          left).1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).1)
    (foldExact :
      let router := exactCompilerFoldAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val
        (alphaFinalWorkQ16DagController transitionFuel finalTrial.val
          (alphaZeroCausalController transitionFuel 0))
        (inactiveAlphaZeroMemory, inactiveDagMemory)
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          left).2.1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).2.1) :
    ∃ prior later target answer rightRemaining,
      exactFixedRootRecords leftWitness.joint.input.package.root =
          prior ++
            (.machineFresh .adversary target answer : UnifiedExposureRecord) ::
              later ∧
      finalTrial.val = prior.length ∧
      freshAnswerTapeToList right =
        prior.map UnifiedExposureRecord.answer ++ rightRemaining := by
  obtain ⟨prior, later, target, answer, rootExact, trialExact⟩ := anchor
  obtain ⟨rightRemaining, rightPrefix⟩ :=
    exact_fold_alpha_coordinates_force_pre_final_tape_prefix
      leftWitness.joint.input foldTrial finalTrial 0 prior
      ((.machineFresh .adversary target answer : UnifiedExposureRecord) ::
        later)
      (by simpa only [List.cons_append] using rootExact) trialExact
      programmedCover right contextExact foldExact
  rw [fold_alpha_final_work_q16_named_slot_tape_preserves_master_list]
    at rightPrefix
  exact ⟨prior, later, target, answer, rightRemaining, rootExact, trialExact,
    rightPrefix⟩

/-- Operational form: the right master tape reaches exactly the same native
adversary request from the same hidden root cursor. -/
theorem exact_fixed_clean_pair_k13_adversary_anchor_has_shared_native_pause
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
    (leftWitness : ExactFixedCleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, left) foldTrial
        finalTrial)
    (anchor : ExactFixedK13AdversaryAnchor leftWitness.joint.input finalTrial)
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (contextExact :
      let router := exactCompilerFoldAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val
        (alphaFinalWorkQ16DagController transitionFuel finalTrial.val
          (alphaZeroCausalController transitionFuel 0))
        (inactiveAlphaZeroMemory, inactiveDagMemory)
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          left).1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).1)
    (foldExact :
      let router := exactCompilerFoldAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val
        (alphaFinalWorkQ16DagController transitionFuel finalTrial.val
          (alphaZeroCausalController transitionFuel 0))
        (inactiveAlphaZeroMemory, inactiveDagMemory)
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          left).2.1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).2.1) :
    ∃ queryPrior queryLater target answer requestState rightRemaining,
      leftWitness.joint.input.package.root.full.projection.rootPrefixes.adversary.freshQueries =
          queryPrior ++ (target, answer) :: queryLater ∧
      freshAnswerTapeToList right =
          queryPrior.map Prod.snd ++ rightRemaining ∧
      IsExactSchedulerNativeMachineFreshRequest .adversary requestState target
        (seekSchedulerNativeExposure transitionFuel
          (schedulerNativePrefixCursor transitionFuel
            (exactPlainRomCursor configuration hidden)
            (queryPrior.map Prod.snd))) := by
  obtain ⟨prior, later, target, answer, rightRemaining, rootExact,
      _trialExact, rightPrefix⟩ :=
    exact_fixed_clean_pair_k13_adversary_anchor_replays_raw_pre_anchor_tape
      foldTrial finalTrial hidden left right leftWitness anchor programmedCover
        contextExact foldExact
  obtain ⟨queryPrior, queryLater, adversaryExact, priorExact⟩ :=
    exact_fixed_k13_adversary_anchor_has_literal_adversary_prefix
      leftWitness.joint.input prior later target answer rootExact
  obtain ⟨requestState, _priorHistory, requestExact⟩ :=
    exact_root_adversary_query_has_global_prior_history transitionRoom
      leftWitness.joint.input queryPrior target answer queryLater adversaryExact
  have rightPrefix' : freshAnswerTapeToList right =
      queryPrior.map Prod.snd ++ rightRemaining := by
    rw [priorExact, projected_machine_fresh_record_answers] at rightPrefix
    exact rightPrefix
  exact ⟨queryPrior, queryLater, target, answer, requestState, rightRemaining,
    adversaryExact, rightPrefix', requestExact⟩

#print axioms
  exact_fixed_clean_pair_k13_adversary_anchor_replays_raw_pre_anchor_tape
#print axioms
  exact_fixed_clean_pair_k13_adversary_anchor_has_shared_native_pause

end

end AspisK1.V7Tag73ExactPairCoordinateProfileInvariant
