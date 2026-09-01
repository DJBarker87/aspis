import AspisFormal.K1.V7Tag73ExactPairTrialProbabilityClosure
import AspisFormal.K1.V7Tag73FoldAlphaPreFinalPrefix
import AspisFormal.K1.V7Tag73ExactFixedCleanQ16ProfileInvariant
import AspisFormal.K1.V7Tag73ExactAdversaryAnchorSelectedInputInvariant

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
open AspisK1.V7Tag73ExactAdversaryAnchorSelectedInputInvariant
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactFixedCleanQ16ProfileInvariant
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactFixedQ16VerifierAnchorInvariant
open AspisK1.V7Tag73ExactFinal256DigestRootOrigin
open AspisK1.V7Tag73ExactPairTrialProbabilityClosure
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRootPriorQueryHistory
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FoldAlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73FoldAlphaPreFinalPrefix
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73ProjectedMachineNativeRequestPrefix
open AspisK1.V7Tag73SchedulerCausalStateAlignment
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerNativePrefixTraversal
open AspisK1.V7Tag73SqueezeInputStateInjectivity
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- The source-alignment argument needs only the literal master-tape prefix,
not the obsolete 513-coordinate representation that originally produced it. -/
theorem exact_fixed_k13_selected_root_priors_eq_of_right_tape_prefix
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    (trial : ExactCompilerExposureTrial parameters) (hidden : HiddenTape)
    (left right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (leftInput : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance (hidden, left))
    (rightInput : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance (hidden, right))
    (leftPrior leftLater rightPrior rightLater : List UnifiedExposureRecord)
    (leftActor rightActor : QueryActor)
    (leftTarget rightTarget : ShaInput)
    (leftAnswer rightAnswer : Digest256)
    (leftRootExact : exactFixedRootRecords leftInput.package.root =
      leftPrior ++ (.machineFresh leftActor leftTarget leftAnswer :
        UnifiedExposureRecord) :: leftLater)
    (rightRootExact : exactFixedRootRecords rightInput.package.root =
      rightPrior ++ (.machineFresh rightActor rightTarget rightAnswer :
        UnifiedExposureRecord) :: rightLater)
    (leftTrialExact : trial.val = leftPrior.length)
    (rightTrialExact : trial.val = rightPrior.length)
    (rightTapeFromLeft : ∃ remaining,
      freshAnswerTapeToList right =
        leftPrior.map UnifiedExposureRecord.answer ++ remaining) :
    leftPrior = rightPrior := by
  obtain ⟨_rightRemaining, rightTapeFromLeft⟩ := rightTapeFromLeft
  obtain ⟨_rightSourceRemaining, rightTapeFromRight⟩ :=
    exact_master_tape_has_root_record_prefix rightInput rightPrior rightLater
      (.machineFresh rightActor rightTarget rightAnswer) rightRootExact
  have leftLength : (leftPrior.map UnifiedExposureRecord.answer).length =
      trial.val := by simp [leftTrialExact]
  have rightLength : (rightPrior.map UnifiedExposureRecord.answer).length =
      trial.val := by simp [rightTrialExact]
  have priorAnswersExact :
      leftPrior.map UnifiedExposureRecord.answer =
        rightPrior.map UnifiedExposureRecord.answer := by
    have leftTake : List.take trial.val (freshAnswerTapeToList right) =
        leftPrior.map UnifiedExposureRecord.answer := by
      rw [rightTapeFromLeft, ← leftLength]
      simp
    have rightTake : List.take trial.val (freshAnswerTapeToList right) =
        rightPrior.map UnifiedExposureRecord.answer := by
      rw [rightTapeFromRight, ← rightLength]
      simp
    exact leftTake.symm.trans rightTake
  let controller := exactDagTrialController transitionFuel trial
  let initial := exactDagCandidateInitialState leftInput
  have leftAlignedRaw := exact_root_records_aligned_for_dag_controller
    leftInput trial.val
  have rightAlignedRaw := exact_root_records_aligned_for_dag_controller
    rightInput trial.val
  have leftAligned : IndexedRecordsAligned transitionFuel controller initial
      (exactFixedRootRecords leftInput.package.root) := by
    simpa [controller, initial, exactDagTrialController] using leftAlignedRaw
  have rightAligned : IndexedRecordsAligned transitionFuel controller initial
      (exactFixedRootRecords rightInput.package.root) := by
    simpa [controller, initial, exactDagTrialController,
      exactDagCandidateInitialState] using rightAlignedRaw
  have leftPriorAligned : IndexedRecordsAligned transitionFuel controller initial
      leftPrior := by
    apply indexed_records_aligned_segment transitionFuel controller initial
      (exactFixedRootRecords leftInput.package.root) [] leftPrior
      ((.machineFresh leftActor leftTarget leftAnswer :
        UnifiedExposureRecord) :: leftLater)
    · exact leftAligned
    · simpa only [List.nil_append, List.cons_append] using leftRootExact
  have rightPriorAligned : IndexedRecordsAligned transitionFuel controller initial
      rightPrior := by
    apply indexed_records_aligned_segment transitionFuel controller initial
      (exactFixedRootRecords rightInput.package.root) [] rightPrior
      ((.machineFresh rightActor rightTarget rightAnswer :
        UnifiedExposureRecord) :: rightLater)
    · exact rightAligned
    · simpa only [List.nil_append, List.cons_append] using rightRootExact
  exact indexed_records_aligned_eq_of_answer_maps_eq transitionFuel controller
    initial leftPrior rightPrior leftPriorAligned rightPriorAligned
      priorAnswersExact

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

/-- The complete-coordinate prefix fixes the selected literal SHA input and
its source-bound pre-final digest across two clean pair witnesses. -/
theorem exact_fixed_clean_pair_k13_adversary_anchor_selected_input_and_digest_eq
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
    (rightWitness : ExactFixedCleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, right) foldTrial
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
    ∃ selectedInput leftDigest rightDigest,
      HasLiteralStatePrefix leftDigest selectedInput ∧
      HasLiteralStatePrefix rightDigest selectedInput ∧
      leftDigest = rightDigest ∧
      ExactOperationalPrefinalDigest leftWitness.joint.input leftDigest ∧
      ExactOperationalPrefinalDigest rightWitness.joint.input rightDigest := by
  obtain ⟨leftPrior, leftLater, leftInput, leftAnswer, leftDigest, _leftBase,
      _leftAbsorbActor, leftRootExact, leftTrialExact, leftPrefix, leftOrigin,
      _leftKind, _leftBaseExact, _leftAbsorbMember⟩ :=
    exact_fixed_k13_adversary_anchor_has_prefinal_digest_prefix finalTrial
      leftWitness.joint anchor
  obtain ⟨rightPrior, rightLater, rightActor, rightInput, rightAnswer,
      rightDigest, _rightBase, _rightAbsorbActor, rightRootExact,
      rightTrialExact, rightPrefix, rightOrigin, _rightBaseExact,
      _rightAbsorbMember⟩ :=
    exact_fixed_k13_actual_trial_has_selected_prefinal_prefix
      rightWitness.joint.input finalTrial rightWitness.joint.actualTrial
  obtain ⟨rightRemaining, rightTapeFromLeft⟩ :=
    exact_fold_alpha_coordinates_force_pre_final_tape_prefix
      leftWitness.joint.input foldTrial finalTrial 0 leftPrior
      ((.machineFresh .adversary leftInput leftAnswer :
        UnifiedExposureRecord) :: leftLater)
      (by simpa only [List.cons_append] using leftRootExact) leftTrialExact
      programmedCover right contextExact foldExact
  rw [fold_alpha_final_work_q16_named_slot_tape_preserves_master_list]
    at rightTapeFromLeft
  have priorExact : leftPrior = rightPrior :=
    exact_fixed_k13_selected_root_priors_eq_of_right_tape_prefix finalTrial
      hidden left right leftWitness.joint.input rightWitness.joint.input
      leftPrior leftLater rightPrior rightLater .adversary rightActor leftInput
      rightInput leftAnswer rightAnswer leftRootExact rightRootExact
      leftTrialExact rightTrialExact ⟨rightRemaining, rightTapeFromLeft⟩
  let controller := exactDagTrialController transitionFuel finalTrial
  let initial := exactDagCandidateInitialState leftWitness.joint.input
  have leftAlignedRaw := exact_root_records_aligned_for_dag_controller
    leftWitness.joint.input finalTrial.val
  have rightAlignedRaw := exact_root_records_aligned_for_dag_controller
    rightWitness.joint.input finalTrial.val
  have leftAligned : IndexedRecordsAligned transitionFuel controller initial
      (exactFixedRootRecords leftWitness.joint.input.package.root) := by
    simpa [controller, initial, exactDagTrialController] using leftAlignedRaw
  have rightAligned : IndexedRecordsAligned transitionFuel controller initial
      (exactFixedRootRecords rightWitness.joint.input.package.root) := by
    simpa [controller, initial, exactDagTrialController,
      exactDagCandidateInitialState] using rightAlignedRaw
  have leftSelectedAligned := leftAligned leftPrior
    (.machineFresh .adversary leftInput leftAnswer) leftLater leftRootExact
  have rightSelectedAligned := rightAligned rightPrior
    (.machineFresh rightActor rightInput rightAnswer) rightLater rightRootExact
  have leftInputExact := aligned_machine_record_has_exact_input transitionFuel
    (indexedStateAfterRecords transitionFuel controller leftPrior initial).cursor
    .adversary leftInput leftAnswer leftSelectedAligned
  have rightInputExact := aligned_machine_record_has_exact_input transitionFuel
    (indexedStateAfterRecords transitionFuel controller rightPrior initial).cursor
    rightActor rightInput rightAnswer rightSelectedAligned
  have selectedInputExact : leftInput = rightInput := by
    rw [priorExact] at leftInputExact
    exact Option.some.inj (leftInputExact.symm.trans rightInputExact)
  have digestExact : leftDigest = rightDigest := by
    apply digest_bytes_injective
    calc
      bytes leftDigest = leftInput.take 32 := leftPrefix
      _ = rightInput.take 32 := by rw [selectedInputExact]
      _ = bytes rightDigest := rightPrefix.symm
  refine ⟨leftInput, leftDigest, rightDigest, leftPrefix, ?_, digestExact,
    leftOrigin, rightOrigin⟩
  simpa [selectedInputExact] using rightPrefix

#print axioms
  exact_fixed_clean_pair_k13_adversary_anchor_replays_raw_pre_anchor_tape
#print axioms
  exact_fixed_clean_pair_k13_adversary_anchor_has_shared_native_pause
#print axioms
  exact_fixed_clean_pair_k13_adversary_anchor_selected_input_and_digest_eq

end

end AspisK1.V7Tag73ExactPairCoordinateProfileInvariant
