import AspisFormal.K1.V7Tag73ExactPairTrialProbabilityClosure
import AspisFormal.K1.V7Tag73FoldAlphaPreFinalPrefix
import AspisFormal.K1.V7Tag73ExactFixedCleanQ16ProfileInvariant
import AspisFormal.K1.V7Tag73ExactAdversaryAnchorSelectedInputInvariant
import AspisFormal.K1.V7Tag73ExactAdversaryAnchorFinalProfile
import AspisFormal.K1.V7Tag73ExactAlphaZeroActualTrialPrefinal
import AspisFormal.K1.V7Tag73IncrementalSamplerControl
import AspisFormal.K1.V7Tag73FoldArmedPreFinalPrefix

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
open AspisK1.V7Tag73CausalSlotRouterLookup
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactAdversaryAnchorPrefinalChronology
open AspisK1.V7Tag73ExactAdversaryAnchorFinalProfile
open AspisK1.V7Tag73ExactAdversaryAnchorSelectedInputInvariant
open AspisK1.V7Tag73ExactAlphaZeroActualTrialPrefinal
open AspisK1.V7Tag73ExactAlphaZeroRootOrder
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open AspisK1.V7Tag73ExactCompilerGammaPrefixCoordinates
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactDagVerifierAnchorPrefix
open AspisK1.V7Tag73ExactFixedCleanQ16ProfileInvariant
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactK12PrefixWordCongruence
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactFixedQ16SemanticNoninterference
open AspisK1.V7Tag73ExactFixedQ16VerifierAnchorInvariant
open AspisK1.V7Tag73ExactFinal256DigestRootOrigin
open AspisK1.V7Tag73ExactFoldAlphaFinalWorkQ16RootRouting
open AspisK1.V7Tag73ExactPairTrialProbabilityClosure
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactQ16CausalCoordinateOrder
open AspisK1.V7Tag73ExactRootPriorQueryHistory
open AspisK1.V7Tag73ExactRootLookupCausalOrder
open AspisK1.V7Tag73ExactRootRecordOrderLift
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FoldAlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73FoldAlphaPreFinalPrefix
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73FoldArmedPreFinalPrefix
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73FixedFieldMessageBridge
open AspisK1.V7Tag73FutureFreeCheckedRefinementBisimulation
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IncrementalSamplerControl
open AspisK1.V7Tag73K12BudgetedSchedulerTree
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73ProjectedMachineNativeRequestPrefix
open AspisK1.V7Tag73RawProverMessages
open AspisK1.V7Tag73SchedulerCausalStateAlignment
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerNativePrefixTraversal
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73SqueezeInputStateInjectivity
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Equality of the complete conditioning context exposes both of its literal
components: the non-named residual and all four alpha-zero digest blocks. -/
theorem exact_fold_alpha_context_eq_components
    (parameters : ExactCompilerResourceParameters)
    (router : ExactCompilerCausalFoldAlphaFinalWorkQ16Router parameters)
    (left right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (contextExact :
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          left).1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).1) :
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        left).1.1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        right).1.1 ∧
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        left).1.2 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        right).1.2 := by
  exact ⟨congrArg Prod.fst contextExact, congrArg Prod.snd contextExact⟩

/-- Two exact accepted challenge prefixes of one four-block tape are the same
prefix and decode to the same value.  This is the deployed first-success
property, not an independence or fixed-length assumption. -/
theorem exact_challenge_prefixes_of_same_four_blocks_eq
    (circleMap : SecureCircleParameterMap) (id : ChallengeId)
    (full : Fin 4 → Digest256)
    (leftBlocks rightBlocks : List Digest256)
    (leftValue rightValue : Qm31Bytes)
    (leftPrefix : leftBlocks = (List.ofFn full).take leftBlocks.length)
    (rightPrefix : rightBlocks = (List.ofFn full).take rightBlocks.length)
    (leftAccepted : decodeChallengeParameter circleMap id leftBlocks =
      some leftValue)
    (rightAccepted : decodeChallengeParameter circleMap id rightBlocks =
      some rightValue) :
    leftBlocks = rightBlocks ∧ leftValue = rightValue := by
  rcases Nat.le_total leftBlocks.length rightBlocks.length with leftLe | rightLe
  · have isPrefix : leftBlocks <+: rightBlocks := by
      rw [leftPrefix, rightPrefix]
      exact List.take_prefix_take_left leftLe
    obtain ⟨suffix, rightExact⟩ := isPrefix
    have suffixNil := decodeChallengeParameter_accepted_prefix_suffix_nil
      circleMap id leftBlocks suffix leftValue rightValue leftAccepted (by
        simpa [rightExact] using rightAccepted)
    subst suffix
    have blocksExact : leftBlocks = rightBlocks := by simpa using rightExact
    refine ⟨blocksExact, decodeChallengeParameter_functional circleMap id leftBlocks
      leftValue rightValue leftAccepted ?_⟩
    simpa [blocksExact] using rightAccepted
  · have isPrefix : rightBlocks <+: leftBlocks := by
      rw [leftPrefix, rightPrefix]
      exact List.take_prefix_take_left rightLe
    obtain ⟨suffix, leftExact⟩ := isPrefix
    have suffixNil := decodeChallengeParameter_accepted_prefix_suffix_nil
      circleMap id rightBlocks suffix rightValue leftValue rightAccepted (by
        simpa [leftExact] using leftAccepted)
    subst suffix
    have blocksExact : leftBlocks = rightBlocks := by simpa using leftExact.symm
    refine ⟨blocksExact, decodeChallengeParameter_functional circleMap id leftBlocks
      leftValue rightValue leftAccepted ?_⟩
    simpa [blocksExact] using rightAccepted

/-- A routed alpha-zero answer is literally the corresponding component of
the complete 518-coordinate context. -/
theorem exact_fold_alpha_coordinate_eq_of_routed_lookup
    (parameters : ExactCompilerResourceParameters)
    (router : ExactCompilerCausalFoldAlphaFinalWorkQ16Router parameters)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (block : Fin 4) (answer : Digest256)
    (routed :
      causalRoutedAnswer? (some (Sum.inl block)) router
          (foldAlphaFinalWorkQ16NamedSlotInputTape
            (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters tape)) =
        some answer) :
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
      tape).1.2 block = answer := by
  change (router.coordinateEquiv
      (foldAlphaFinalWorkQ16NamedSlotInputTape
        (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters tape))).1
        ⟨some (Sum.inl block), Finset.mem_univ _⟩ = answer
  exact coordinate_eq_of_causalRoutedAnswer?_eq_some router
    (foldAlphaFinalWorkQ16NamedSlotInputTape
      (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters tape))
    (some (Sum.inl block)) (Finset.mem_univ _) answer routed

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
      let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val finalTrial.val
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          left).1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).1)
    (foldExact :
      let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val finalTrial.val
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
    exact_fold_armed_coordinates_force_pre_final_tape_prefix
      leftWitness.joint.input foldTrial finalTrial prior
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
      let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val finalTrial.val
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          left).1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).1)
    (foldExact :
      let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val finalTrial.val
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

/-- The two accepted executions have the identical literal combined-root
record prefix before the selected final-work exposure.  In particular this
transports inputs and actors, not merely the answer tape. -/
theorem exact_fixed_clean_pair_k13_adversary_anchor_root_priors_eq
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
      let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val finalTrial.val
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          left).1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).1)
    (foldExact :
      let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val finalTrial.val
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          left).2.1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).2.1) :
    ∃ leftPrior leftLater rightPrior rightLater leftInput rightInput
        leftAnswer rightAnswer rightActor,
      exactFixedRootRecords leftWitness.joint.input.package.root =
        leftPrior ++
          (.machineFresh .adversary leftInput leftAnswer :
            UnifiedExposureRecord) :: leftLater ∧
      exactFixedRootRecords rightWitness.joint.input.package.root =
        rightPrior ++
          (.machineFresh rightActor rightInput rightAnswer :
            UnifiedExposureRecord) :: rightLater ∧
      finalTrial.val = leftPrior.length ∧
      finalTrial.val = rightPrior.length ∧
      leftPrior = rightPrior := by
  obtain ⟨leftPrior, leftLater, leftInput, leftAnswer, _leftDigest, _leftBase,
      _leftAbsorbActor, leftRootExact, leftTrialExact, _leftPrefix, _leftOrigin,
      _leftKind, _leftBaseExact, _leftAbsorbMember⟩ :=
    exact_fixed_k13_adversary_anchor_has_prefinal_digest_prefix finalTrial
      leftWitness.joint anchor
  obtain ⟨rightPrior, rightLater, rightActor, rightInput, rightAnswer,
      _rightDigest, _rightBase, _rightAbsorbActor, rightRootExact,
      rightTrialExact, _rightPrefix, _rightOrigin, _rightBaseExact,
      _rightAbsorbMember⟩ :=
    exact_fixed_k13_actual_trial_has_selected_prefinal_prefix
      rightWitness.joint.input finalTrial rightWitness.joint.actualTrial
  obtain ⟨rightRemaining, rightTapeFromLeft⟩ :=
    exact_fold_armed_coordinates_force_pre_final_tape_prefix
      leftWitness.joint.input foldTrial finalTrial leftPrior
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
  exact ⟨leftPrior, leftLater, rightPrior, rightLater, leftInput, rightInput,
    leftAnswer, rightAnswer, rightActor, leftRootExact, rightRootExact,
    leftTrialExact, rightTrialExact, priorExact⟩

/-- Equality of the fold-armed conditioning coordinates fixes the complete
literal root prefix before the selected final-work exposure, independently of
which actor first queried either selected input.  Cached pre-fold alpha answers
are covered by the residual coordinate; post-fold answers are covered by the
four named alpha coordinates. -/
theorem exact_fixed_clean_pair_k13_selected_root_priors_eq
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
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (contextExact :
      let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val finalTrial.val
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          left).1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).1)
    (foldExact :
      let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val finalTrial.val
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          left).2.1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).2.1) :
    ∃ leftPrior leftLater rightPrior rightLater leftActor rightActor
        leftInput rightInput leftAnswer rightAnswer,
      exactFixedRootRecords leftWitness.joint.input.package.root =
        leftPrior ++
          (.machineFresh leftActor leftInput leftAnswer :
            UnifiedExposureRecord) :: leftLater ∧
      exactFixedRootRecords rightWitness.joint.input.package.root =
        rightPrior ++
          (.machineFresh rightActor rightInput rightAnswer :
            UnifiedExposureRecord) :: rightLater ∧
      finalTrial.val = leftPrior.length ∧
      finalTrial.val = rightPrior.length ∧
      leftPrior = rightPrior := by
  obtain ⟨leftPrior, leftLater, leftActor, leftInput, leftAnswer, _leftDigest,
      _leftBase, _leftAbsorbActor, leftRootExact, leftTrialExact, _leftPrefix,
      _leftPrefinal, _leftBaseExact, _leftAbsorbMember⟩ :=
    exact_fixed_k13_actual_trial_has_selected_prefinal_prefix
      leftWitness.joint.input finalTrial leftWitness.joint.actualTrial
  obtain ⟨rightPrior, rightLater, rightActor, rightInput, rightAnswer,
      _rightDigest, _rightBase, _rightAbsorbActor, rightRootExact,
      rightTrialExact, _rightPrefix, _rightPrefinal, _rightBaseExact,
      _rightAbsorbMember⟩ :=
    exact_fixed_k13_actual_trial_has_selected_prefinal_prefix
      rightWitness.joint.input finalTrial rightWitness.joint.actualTrial
  obtain ⟨rightRemaining, rightTapeFromLeft⟩ :=
    exact_fold_armed_coordinates_force_pre_final_tape_prefix
      leftWitness.joint.input foldTrial finalTrial leftPrior
      ((.machineFresh leftActor leftInput leftAnswer :
        UnifiedExposureRecord) :: leftLater)
      (by simpa only [List.cons_append] using leftRootExact) leftTrialExact
      programmedCover right contextExact foldExact
  rw [fold_alpha_final_work_q16_named_slot_tape_preserves_master_list]
    at rightTapeFromLeft
  have priorExact : leftPrior = rightPrior :=
    exact_fixed_k13_selected_root_priors_eq_of_right_tape_prefix finalTrial
      hidden left right leftWitness.joint.input rightWitness.joint.input
      leftPrior leftLater rightPrior rightLater leftActor rightActor leftInput
      rightInput leftAnswer rightAnswer leftRootExact rightRootExact
      leftTrialExact rightTrialExact ⟨rightRemaining, rightTapeFromLeft⟩
  exact ⟨leftPrior, leftLater, rightPrior, rightLater, leftActor, rightActor,
    leftInput, rightInput, leftAnswer, rightAnswer, leftRootExact,
    rightRootExact, leftTrialExact, rightTrialExact, priorExact⟩

/-- On the verifier-owned side of the chronological partition, the new
fold-armed conditioning coordinates replay the complete prover prefix.  Thus
the parsed pre-q16 proof and extracted K1.2 words agree without converting
back to the obsolete 513-coordinate residual. -/
theorem exact_fixed_clean_pair_k13_verifier_anchor_pre_q16_values_eq
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
    (anchor : ExactFixedK13VerifierAnchor leftWitness.joint.input finalTrial)
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (contextExact :
      let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val finalTrial.val
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          left).1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).1)
    (foldExact :
      let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val finalTrial.val
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          left).2.1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).2.1) :
    exactK13ParsedProof rightWitness.joint.input =
        exactK13ParsedProof leftWitness.joint.input ∧
      exactPrefixK12Words rightWitness.joint.input =
        exactPrefixK12Words leftWitness.joint.input := by
  obtain ⟨prior, later, target, answer, rootExact, trialExact⟩ := anchor
  obtain ⟨verifierPrior, _verifierLater, _verifierExact, priorExact⟩ :=
    exact_dag_verifier_root_record_has_completed_prover_prefix
      leftWitness.joint.input prior later target answer rootExact
  obtain ⟨rightRemaining, rightPrefix⟩ :=
    exact_fold_armed_coordinates_force_pre_final_tape_prefix
      leftWitness.joint.input foldTrial finalTrial prior
      ((.machineFresh .verifier target answer : UnifiedExposureRecord) :: later)
      (by simpa only [List.cons_append] using rootExact) trialExact
      programmedCover right contextExact foldExact
  rw [fold_alpha_final_work_q16_named_slot_tape_preserves_master_list]
    at rightPrefix
  have priorAnswers : prior.map UnifiedExposureRecord.answer =
      leftWitness.joint.input.package.root.full.projection.rootPrefixes.adversary.freshQueries.map
          Prod.snd ++ verifierPrior.map Prod.snd := by
    rw [priorExact, List.map_append, projected_machine_fresh_record_answers,
      projected_machine_fresh_record_answers]
  rw [priorAnswers] at rightPrefix
  have leftReplay := k12_prover_run_from_completed_prefix_append_exact
    configuration.machine hidden (freshAnswerTapeToList left)
    leftWitness.joint.input.package.root.fixedRoot.base.runtime
    leftWitness.joint.input.package.root.full.projection.rootPrefixes
    (verifierPrior.map Prod.snd ++ rightRemaining)
  have leftReplay' : k12ProverRunFromAnswerPrefix configuration.machine hidden
      (freshAnswerTapeToList right) =
        { halt := .returned
            leftWitness.joint.input.package.root.full.projection.rootPrefixes.adversaryValue
          oracle :=
            leftWitness.joint.input.package.root.full.projection.rootPrefixes.adversary.finalState
          steps :=
            leftWitness.joint.input.package.root.full.projection.rootPrefixes.adversary.steps } := by
    rw [rightPrefix]
    simpa only [List.append_assoc] using leftReplay
  let rightPrefixes :=
    rightWitness.joint.input.package.root.full.projection.rootPrefixes
  have rightReplay := k12_prover_run_from_completed_prefix_append_exact
    configuration.machine hidden (freshAnswerTapeToList right)
    rightWitness.joint.input.package.root.fixedRoot.base.runtime rightPrefixes
    rightPrefixes.adversary.remaining
  have rightAvailable : freshAnswerTapeToList right =
      rightPrefixes.adversary.freshQueries.map Prod.snd ++
        rightPrefixes.adversary.remaining := by
    simpa [rightPrefixes] using rightPrefixes.adversary.availableExact
  rw [← rightAvailable] at rightReplay
  have rawRunExact := leftReplay'.symm.trans rightReplay
  have adversaryExact :
      (exactK12Runtime rightWitness.joint.input).adversaryValue =
        (exactK12Runtime leftWitness.joint.input).adversaryValue := by
    have haltExact := congrArg (fun run => run.halt) rawRunExact
    have valueExact :
        leftWitness.joint.input.package.root.full.projection.rootPrefixes.adversaryValue =
          rightPrefixes.adversaryValue := by
      simpa only [MachineHalt.returned.injEq] using haltExact
    have leftRuntime := congrArg (fun runtime => runtime.adversaryValue)
      leftWitness.joint.input.package.root.full.projection.rootPrefixes.runtimeExact
    have rightRuntime := congrArg (fun runtime => runtime.adversaryValue)
      rightPrefixes.runtimeExact
    simpa [rightPrefixes, exactK12Runtime, operationalRootRuntime] using
      rightRuntime.trans (valueExact.symm.trans leftRuntime.symm)
  have proverExact :
      (exactK12Runtime rightWitness.joint.input).proverFinalOracle =
        (exactK12Runtime leftWitness.joint.input).proverFinalOracle := by
    have oracleExact := congrArg (fun run => run.oracle) rawRunExact
    have leftRuntime := congrArg (fun runtime => runtime.proverFinalOracle)
      leftWitness.joint.input.package.root.full.projection.rootPrefixes.runtimeExact
    have rightRuntime := congrArg (fun runtime => runtime.proverFinalOracle)
      rightPrefixes.runtimeExact
    simpa [rightPrefixes, exactK12Runtime, operationalRootRuntime] using
      rightRuntime.trans (oracleExact.symm.trans leftRuntime.symm)
  constructor
  · simpa only [exactK13ParsedProof] using congrArg
      (fun value => value.1.publicProof.proof.rawProof) adversaryExact
  · exact exact_prefix_k12_words_eq_of_same_prover_runtime
      rightWitness.joint.input leftWitness.joint.input adversaryExact proverExact

/-- The verifier-owned branch therefore has exactly one K1.3 intrinsic bad
set on every complete fold-armed coordinate fibre. -/
theorem exact_fixed_clean_pair_k13_verifier_anchor_bad_eq
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
    (anchor : ExactFixedK13VerifierAnchor leftWitness.joint.input finalTrial)
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (contextExact :
      let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val finalTrial.val
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          left).1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).1)
    (foldExact :
      let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val finalTrial.val
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          left).2.1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).2.1) :
    leftWitness.joint.bad = rightWitness.joint.bad := by
  obtain ⟨parsedExact, wordsExact⟩ :=
    exact_fixed_clean_pair_k13_verifier_anchor_pre_q16_values_eq foldTrial
      finalTrial hidden left right leftWitness rightWitness anchor
      programmedCover contextExact foldExact
  rw [leftWitness.joint.badExact, rightWitness.joint.badExact]
  apply exact_fixed_k13_intrinsic_bad_congr_of_semantic_fields decoder
    leftWitness.joint.input rightWitness.joint.input
  · exact wordsExact.symm
  · exact congrArg Tag73K12ParsedProof.gamma parsedExact.symm
  · exact congrArg Tag73K12ParsedProof.disclosedFinal parsedExact.symm
  · exact congrArg Tag73K12ParsedProof.schedule parsedExact.symm

/-- The sole remaining branch of complete-coordinate K1.3 noninterference:
the selected final-work coordinate was first exposed by the adversary. -/
def ExactFixedCleanK13PairBadInvariantOnAdversaryAnchors
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
        (exactCompilerTargetCaps parameters).length)
      (leftWitness : ExactFixedCleanK13PairTrialWitness transitionFuel
        configuration projection fixedInstance decoder (hidden, left)
          foldTrial finalTrial)
      (rightWitness : ExactFixedCleanK13PairTrialWitness transitionFuel
        configuration projection fixedInstance decoder (hidden, right)
          foldTrial finalTrial),
    ExactFixedK13AdversaryAnchor leftWitness.joint.input finalTrial →
    (let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
      transitionFuel foldTrial.val finalTrial.val
      (exactPlainRomCursor configuration hidden).erase
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        left).1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        right).1) →
    (let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
      transitionFuel foldTrial.val finalTrial.val
      (exactPlainRomCursor configuration hidden).erase
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        left).2.1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        right).2.1) →
    (let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
      transitionFuel foldTrial.val finalTrial.val
      (exactPlainRomCursor configuration hidden).erase
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        left).2.2.1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        right).2.2.1) →
    leftWitness.joint.bad = rightWitness.joint.bad

/-- Verifier-first anchors are discharged above, so the exact adversary-first
endpoint is sufficient for the complete pair-coordinate invariant consumed by
the one-forest K1.3 probability theorem. -/
theorem exact_fixed_clean_k13_pair_coordinate_invariant_of_adversary_anchors
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (adversaryInvariant :
      ExactFixedCleanK13PairBadInvariantOnAdversaryAnchors transitionFuel
        configuration projection fixedInstance decoder) :
    ExactFixedCleanK13PairCoordinateInvariant transitionFuel configuration
      projection fixedInstance decoder := by
  intro foldTrial finalTrial hidden left right leftMember rightMember
  dsimp only
  intro contextExact foldExact workExact
  change Nonempty (ExactFixedCleanK13PairTrialWitness transitionFuel
    configuration projection fixedInstance decoder (hidden, left) foldTrial
      finalTrial) at leftMember
  change Nonempty (ExactFixedCleanK13PairTrialWitness transitionFuel
    configuration projection fixedInstance decoder (hidden, right) foldTrial
      finalTrial) at rightMember
  let leftWitness := Classical.choice leftMember
  let rightWitness := Classical.choice rightMember
  have badExact : leftWitness.joint.bad = rightWitness.joint.bad := by
    rcases exact_fixed_k13_actual_joint_trial_anchor_actor_cases
        leftWitness.joint.input finalTrial leftWitness.joint.actualTrial with
      verifierAnchor | adversaryAnchor
    · exact exact_fixed_clean_pair_k13_verifier_anchor_bad_eq foldTrial
        finalTrial hidden left right leftWitness rightWitness verifierAnchor
        programmedCover contextExact foldExact
    · exact adversaryInvariant foldTrial finalTrial hidden left right
        leftWitness rightWitness adversaryAnchor contextExact foldExact workExact
  have leftPointwise : exactFixedCleanK13PairPointwiseBad transitionFuel
      configuration projection fixedInstance decoder foldTrial finalTrial
        (hidden, left) = leftWitness.joint.bad := by
    simpa [exactFixedCleanK13PairPointwiseBad, leftMember, leftWitness]
  have rightPointwise : exactFixedCleanK13PairPointwiseBad transitionFuel
      configuration projection fixedInstance decoder foldTrial finalTrial
        (hidden, right) = rightWitness.joint.bad := by
    simpa [exactFixedCleanK13PairPointwiseBad, rightMember, rightWitness]
  exact leftPointwise.trans (badExact.trans rightPointwise.symm)

/-- Within equal pre-anchor roots, one digest answer identifies one literal
SHA input.  This is record-answer uniqueness, not SHA injectivity. -/
theorem exact_equal_root_priors_same_answer_input_eq
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (leftPrior rightPrior : List UnifiedExposureRecord)
    (leftActor rightActor : QueryActor)
    (leftInput rightInput : ShaInput) (answer : Digest256)
    (priorExact : leftPrior = rightPrior)
    (leftMember :
      (.machineFresh leftActor leftInput answer : UnifiedExposureRecord) ∈
        leftPrior)
    (rightMember :
      (.machineFresh rightActor rightInput answer : UnifiedExposureRecord) ∈
        rightPrior)
    (leftPrefixMember : ∀ record, record ∈ leftPrior →
      record ∈ exactFixedRootRecords input.package.root) :
    leftInput = rightInput := by
  have rightMember' :
      (.machineFresh rightActor rightInput answer : UnifiedExposureRecord) ∈
        leftPrior := by
    simpa [priorExact] using rightMember
  have recordExact :
      (.machineFresh leftActor leftInput answer : UnifiedExposureRecord) =
        .machineFresh rightActor rightInput answer :=
    List.inj_on_of_nodup_map (exact_root_record_answers_nodup input)
      (leftPrefixMember _ leftMember) (leftPrefixMember _ rightMember') rfl
  injection recordExact

/-- In a duplicate-free chronological root, anything strictly before a named
pivot belongs to the pivot's canonical prefix. -/
theorem mem_canonical_prefix_of_strictly_before_pivot
    {Record : Type} [DecidableEq Record]
    (records prior later before middle after : List Record)
    (first pivot : Record)
    (recordsNodup : records.Nodup)
    (pivotExact : records = prior ++ pivot :: later)
    (orderedExact : records =
      before ++ first :: middle ++ pivot :: after) :
    first ∈ prior := by
  have orderedExact' : records =
      (before ++ first :: middle) ++ pivot :: after := by
    simpa only [List.cons_append, List.append_assoc] using orderedExact
  have prefixExact : prior = before ++ first :: middle :=
    nodup_equal_pivot_prefixes pivot prior later
      (before ++ first :: middle) after
      (by simpa only [← pivotExact] using recordsNodup)
      (pivotExact.symm.trans orderedExact')
  rw [prefixExact]
  simp

/-- Two chronological decompositions at the same ordinal have the same
prefix, independently of the actors or records selected at that ordinal. -/
theorem equal_prefixes_of_equal_decomposition_lengths
    {Record : Type}
    (records leftPrior leftLater rightPrior rightLater : List Record)
    (leftPivot rightPivot : Record)
    (leftExact : records = leftPrior ++ leftPivot :: leftLater)
    (rightExact : records = rightPrior ++ rightPivot :: rightLater)
    (lengthExact : leftPrior.length = rightPrior.length) :
    leftPrior = rightPrior := by
  have leftTake : records.take leftPrior.length = leftPrior := by
    rw [leftExact]
    simp
  have rightTake : records.take leftPrior.length = rightPrior := by
    rw [rightExact, lengthExact]
    simp
  exact leftTake.symm.trans rightTake

/-- Strict chronology is closed downward inside a canonical root prefix: if
the later record is already before the anchor, so is the earlier record. -/
theorem mem_prefix_of_strict_order_and_later_mem
    {Record : Type} [DecidableEq Record]
    (records prior anchorLater before middle after : List Record)
    (first second anchorRecord : Record)
    (recordsNodup : records.Nodup)
    (anchorExact : records = prior ++ anchorRecord :: anchorLater)
    (orderedExact : records =
      before ++ first :: middle ++ second :: after)
    (secondMember : second ∈ prior) :
    first ∈ prior := by
  obtain ⟨insideBefore, insideAfter, priorExact⟩ :=
    (List.mem_iff_append).mp secondMember
  have secondPivotExact : records =
      insideBefore ++ second ::
        (insideAfter ++ anchorRecord :: anchorLater) := by
    rw [anchorExact, priorExact]
    simp only [List.cons_append, List.append_assoc]
  have firstInside : first ∈ insideBefore :=
    mem_canonical_prefix_of_strictly_before_pivot records insideBefore
      (insideAfter ++ anchorRecord :: anchorLater) before middle after
      first second recordsNodup secondPivotExact orderedExact
  rw [priorExact]
  exact List.mem_append_left _ firstInside

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
      let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val finalTrial.val
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          left).1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).1)
    (foldExact :
      let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val finalTrial.val
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
    exact_fold_armed_coordinates_force_pre_final_tape_prefix
      leftWitness.joint.input foldTrial finalTrial leftPrior
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

/-- The complete-coordinate prefix also transports the already-created
canonical `final256` producer into the comparison root. -/
theorem exact_fixed_clean_pair_k13_adversary_anchor_final256_input_eq
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
    (rightWitness : ExactFixedCleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, right) foldTrial
        finalTrial)
    (anchor : ExactFixedK13AdversaryAnchor leftWitness.joint.input finalTrial)
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (contextExact :
      let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val finalTrial.val
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          left).1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).1)
    (foldExact :
      let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val finalTrial.val
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          left).2.1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).2.1) :
    ∃ (leftBefore rightBefore : EvalState) (digest leftBase rightBase : Digest256)
        (leftAbsorbActor rightAbsorbActor : QueryActor)
        (leftPrior rightPrior leftLater rightLater : List UnifiedExposureRecord)
        (leftAnchorRecord rightAnchorRecord : UnifiedExposureRecord),
      (bytes leftBefore.digest ++
          [domAbsorb,
            (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
              (exactOperationalTape leftWitness.joint.input).messages.finalValues).label] ++
          (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
            (exactOperationalTape leftWitness.joint.input).messages.finalValues).data) =
        (bytes rightBefore.digest ++
          [domAbsorb,
            (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
              (exactOperationalTape rightWitness.joint.input).messages.finalValues).label] ++
          (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
            (exactOperationalTape rightWitness.joint.input).messages.finalValues).data) ∧
      tableLookup (exactOperationalTable leftWitness.joint.input)
          (bytes leftBefore.digest ++ [domAbsorb,
            (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
              (exactOperationalTape leftWitness.joint.input).messages.finalValues).label] ++
            (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
              (exactOperationalTape leftWitness.joint.input).messages.finalValues).data) =
        some digest ∧
      tableLookup (exactOperationalTable rightWitness.joint.input)
          (bytes rightBefore.digest ++ [domAbsorb,
            (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
              (exactOperationalTape rightWitness.joint.input).messages.finalValues).label] ++
            (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
              (exactOperationalTape rightWitness.joint.input).messages.finalValues).data) =
        some digest ∧
      leftPrior = rightPrior ∧
      exactFixedRootRecords leftWitness.joint.input.package.root =
        leftPrior ++ leftAnchorRecord :: leftLater ∧
      exactFixedRootRecords rightWitness.joint.input.package.root =
        rightPrior ++ rightAnchorRecord :: rightLater ∧
      (.machineFresh .adversary
          (bytes leftBefore.digest ++ [domAbsorb,
            (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
              (exactOperationalTape leftWitness.joint.input).messages.finalValues).label] ++
            (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
              (exactOperationalTape leftWitness.joint.input).messages.finalValues).data)
          digest : UnifiedExposureRecord) ∈ leftPrior ∧
      (.machineFresh .adversary
          (bytes rightBefore.digest ++ [domAbsorb,
            (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
              (exactOperationalTape rightWitness.joint.input).messages.finalValues).label] ++
            (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
              (exactOperationalTape rightWitness.joint.input).messages.finalValues).data)
          digest : UnifiedExposureRecord) ∈ rightPrior ∧
      leftBase =
        (exactOperationalRawTrace leftWitness.joint.input).q16BaseDigest ∧
      rightBase =
        (exactOperationalRawTrace rightWitness.joint.input).q16BaseDigest ∧
      (.machineFresh leftAbsorbActor
        (literalFinalWorkKey digest
          (exactOperationalTape leftWitness.joint.input).messages.finalGrinding.selected).absorbInput
        leftBase : UnifiedExposureRecord) ∈
        exactFixedRootRecords leftWitness.joint.input.package.root ∧
      (.machineFresh rightAbsorbActor
        (literalFinalWorkKey digest
          (exactOperationalTape rightWitness.joint.input).messages.finalGrinding.selected).absorbInput
        rightBase : UnifiedExposureRecord) ∈
        exactFixedRootRecords rightWitness.joint.input.package.root := by
  obtain ⟨leftRootPrior, leftRootMiddle, leftRootLater, leftProducerInput,
      leftAnchorInput, leftAnchorAnswer, leftDigest, leftBase, leftAbsorbActor,
      leftRootExact, leftTrialExact, _leftProducerLookup, leftAnchorPrefix,
      leftOrigin, leftBaseExact, leftAbsorbMember⟩ :=
    exact_fixed_k13_adversary_anchor_has_earlier_final256_root_record
      transitionRoom finalTrial leftWitness.joint anchor
  obtain ⟨rightPrior, rightLater, rightActor, rightAnchorInput,
      rightAnchorAnswer, rightDigest, rightBase, rightAbsorbActor,
      rightRootExact, rightTrialExact, rightAnchorPrefix, rightOrigin,
      rightBaseExact, rightAbsorbMember⟩ :=
    exact_fixed_k13_actual_trial_has_selected_prefinal_prefix
      rightWitness.joint.input finalTrial rightWitness.joint.actualTrial
  let leftPrior : List UnifiedExposureRecord :=
    leftRootPrior ++
      (.machineFresh .adversary leftProducerInput leftDigest :
        UnifiedExposureRecord) :: leftRootMiddle
  have leftSelectedExact :
      exactFixedRootRecords leftWitness.joint.input.package.root =
        leftPrior ++
          (.machineFresh .adversary leftAnchorInput leftAnchorAnswer :
            UnifiedExposureRecord) :: leftRootLater := by
    simpa [leftPrior, List.append_assoc] using leftRootExact
  have leftTrialExact' : finalTrial.val = leftPrior.length := by
    simpa [leftPrior] using leftTrialExact
  obtain ⟨rightRemaining, rightTapeFromLeft⟩ :=
    exact_fold_armed_coordinates_force_pre_final_tape_prefix
      leftWitness.joint.input foldTrial finalTrial leftPrior
      ((.machineFresh .adversary leftAnchorInput leftAnchorAnswer :
        UnifiedExposureRecord) :: leftRootLater)
      (by simpa only [List.cons_append] using leftSelectedExact)
      leftTrialExact' programmedCover right contextExact foldExact
  rw [fold_alpha_final_work_q16_named_slot_tape_preserves_master_list]
    at rightTapeFromLeft
  have priorExact : leftPrior = rightPrior :=
    exact_fixed_k13_selected_root_priors_eq_of_right_tape_prefix finalTrial
      hidden left right leftWitness.joint.input rightWitness.joint.input
      leftPrior leftRootLater rightPrior rightLater .adversary rightActor
      leftAnchorInput rightAnchorInput leftAnchorAnswer rightAnchorAnswer
      leftSelectedExact rightRootExact leftTrialExact' rightTrialExact
      ⟨rightRemaining, rightTapeFromLeft⟩
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
    (.machineFresh .adversary leftAnchorInput leftAnchorAnswer)
    leftRootLater leftSelectedExact
  have rightSelectedAligned := rightAligned rightPrior
    (.machineFresh rightActor rightAnchorInput rightAnchorAnswer)
    rightLater rightRootExact
  have leftInputExact := aligned_machine_record_has_exact_input transitionFuel
    (indexedStateAfterRecords transitionFuel controller leftPrior initial).cursor
    .adversary leftAnchorInput leftAnchorAnswer leftSelectedAligned
  have rightInputExact := aligned_machine_record_has_exact_input transitionFuel
    (indexedStateAfterRecords transitionFuel controller rightPrior initial).cursor
    rightActor rightAnchorInput rightAnchorAnswer rightSelectedAligned
  have anchorInputExact : leftAnchorInput = rightAnchorInput := by
    rw [priorExact] at leftInputExact
    exact Option.some.inj (leftInputExact.symm.trans rightInputExact)
  have digestExact : leftDigest = rightDigest := by
    apply digest_bytes_injective
    calc
      bytes leftDigest = leftAnchorInput.take 32 := leftAnchorPrefix
      _ = rightAnchorInput.take 32 := by rw [anchorInputExact]
      _ = bytes rightDigest := rightAnchorPrefix.symm
  obtain ⟨leftBefore, leftLookup⟩ := leftOrigin
  obtain ⟨rightBefore, rightLookup⟩ := rightOrigin
  let leftCanonicalInput : ShaInput :=
    bytes leftBefore.digest ++ [domAbsorb,
      (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
        (exactOperationalTape leftWitness.joint.input).messages.finalValues).label] ++
      (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
        (exactOperationalTape leftWitness.joint.input).messages.finalValues).data
  let rightCanonicalInput : ShaInput :=
    bytes rightBefore.digest ++ [domAbsorb,
      (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
        (exactOperationalTape rightWitness.joint.input).messages.finalValues).label] ++
      (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
        (exactOperationalTape rightWitness.joint.input).messages.finalValues).data
  obtain ⟨leftCanonicalActor, leftCanonicalMember⟩ :=
    exact_final_table_lookup_has_root_record leftWitness.joint.input
      leftCanonicalInput leftDigest (by simpa [leftCanonicalInput] using leftLookup)
  have leftProducerMember :
      (.machineFresh .adversary leftProducerInput leftDigest :
        UnifiedExposureRecord) ∈
        exactFixedRootRecords leftWitness.joint.input.package.root := by
    rw [leftRootExact]
    simp
  have leftCanonicalRecordExact :=
    List.inj_on_of_nodup_map
      (exact_root_record_answers_nodup leftWitness.joint.input)
      leftProducerMember leftCanonicalMember rfl
  have leftProducerCanonical : leftProducerInput = leftCanonicalInput := by
    injection leftCanonicalRecordExact
  obtain ⟨rightCanonicalActor, rightCanonicalMemberRaw⟩ :=
    exact_final_table_lookup_has_root_record rightWitness.joint.input
      rightCanonicalInput rightDigest (by
        simpa [rightCanonicalInput] using rightLookup)
  have transportedProducerMember :
      (.machineFresh .adversary leftProducerInput leftDigest :
        UnifiedExposureRecord) ∈
        exactFixedRootRecords rightWitness.joint.input.package.root := by
    rw [rightRootExact, ← priorExact]
    simp [leftPrior]
  have rightCanonicalMember :
      (.machineFresh rightCanonicalActor rightCanonicalInput leftDigest :
        UnifiedExposureRecord) ∈
        exactFixedRootRecords rightWitness.joint.input.package.root := by
    simpa [digestExact] using rightCanonicalMemberRaw
  have rightCanonicalRecordExact :=
    List.inj_on_of_nodup_map
      (exact_root_record_answers_nodup rightWitness.joint.input)
      transportedProducerMember rightCanonicalMember rfl
  have producerInputExact : leftProducerInput = rightCanonicalInput := by
    injection rightCanonicalRecordExact
  have leftProducerPriorMember :
      (.machineFresh .adversary leftCanonicalInput leftDigest :
        UnifiedExposureRecord) ∈ leftPrior := by
    rw [← leftProducerCanonical]
    simp [leftPrior]
  have rightProducerPriorMember :
      (.machineFresh .adversary rightCanonicalInput leftDigest :
        UnifiedExposureRecord) ∈ rightPrior := by
    rw [← producerInputExact, ← priorExact]
    simp [leftPrior]
  refine ⟨leftBefore, rightBefore, leftDigest, leftBase, rightBase,
    leftAbsorbActor, rightAbsorbActor, leftPrior, rightPrior, leftRootLater,
    rightLater,
    (.machineFresh .adversary leftAnchorInput leftAnchorAnswer),
    (.machineFresh rightActor rightAnchorInput rightAnchorAnswer),
    leftProducerCanonical.symm.trans producerInputExact, ?_, ?_, priorExact,
    leftSelectedExact, rightRootExact, ?_, ?_, leftBaseExact, rightBaseExact,
    leftAbsorbMember, ?_⟩
  · simpa [leftCanonicalInput] using leftLookup
  · simpa [rightCanonicalInput, digestExact] using rightLookup
  · simpa [leftCanonicalInput] using leftProducerPriorMember
  · simpa [rightCanonicalInput] using rightProducerPriorMember
  · simpa [digestExact] using rightAbsorbMember

/-- Equal complete-coordinate `final256` inputs fix the transcript digest
immediately before that absorption.  This uses fixed-width serialization,
not SHA-256 inversion. -/
theorem exact_fixed_clean_pair_k13_adversary_anchor_before_final256_digest_eq
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
    (rightWitness : ExactFixedCleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, right) foldTrial
        finalTrial)
    (anchor : ExactFixedK13AdversaryAnchor leftWitness.joint.input finalTrial)
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (contextExact :
      let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val finalTrial.val
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          left).1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).1)
    (foldExact :
      let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val finalTrial.val
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          left).2.1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).2.1) :
    ∃ leftBefore rightBefore : EvalState,
      leftBefore.digest = rightBefore.digest := by
  obtain ⟨leftBefore, rightBefore, _digest, _leftBase, _rightBase,
      _leftAbsorbActor, _rightAbsorbActor, _leftPrior, _rightPrior, _leftLater,
      _rightLater, _leftAnchorRecord, _rightAnchorRecord, inputExact,
      _leftLookup, _rightLookup, _priorExact, _leftRootExact, _rightRootExact,
      _leftProducerMember, _rightProducerMember, _leftBaseExact,
      _rightBaseExact, _leftAbsorbMember, _rightAbsorbMember⟩ :=
    exact_fixed_clean_pair_k13_adversary_anchor_final256_input_eq
      transitionRoom foldTrial finalTrial hidden left right leftWitness
      rightWitness anchor programmedCover contextExact foldExact
  refine ⟨leftBefore, rightBefore, ?_⟩
  apply digest_bytes_injective
  have prefixExact := congrArg (List.take 32) inputExact
  simpa using prefixExact

/-- The complete-coordinate pair comparison reaches one common transcript
state after the deployed alpha-zero sampler.  Both literal ordered chains are
retained for the subsequent block-by-block profile proof. -/
theorem exact_fixed_clean_pair_k13_adversary_anchor_alpha_terminal_eq
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
    (rightWitness : ExactFixedCleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, right) foldTrial
        finalTrial)
    (anchor : ExactFixedK13AdversaryAnchor leftWitness.joint.input finalTrial)
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (contextExact :
      let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val finalTrial.val
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          left).1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).1)
    (foldExact :
      let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val finalTrial.val
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          left).2.1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).2.1) :
    ∃ (leftProducer rightProducer leftFinal256Input rightFinal256Input : ShaInput)
        (leftBeforeAlpha rightBeforeAlpha leftAfterAlpha rightAfterAlpha
          leftAfterBlocks rightAfterBlocks leftAfterFinal256 rightAfterFinal256 :
          EvalState)
        (leftOutputs leftAdvances rightOutputs rightAdvances : List Digest256)
        (leftValue rightValue : QM31Exact) (prefinalDigest : Digest256)
        (leftPrior rightPrior leftLater rightLater : List UnifiedExposureRecord)
        (leftAnchorRecord rightAnchorRecord : UnifiedExposureRecord),
      ExactRootOrderedQ16Chain leftWitness.joint.input leftProducer
          leftBeforeAlpha.digest leftOutputs leftAdvances ∧
      ExactRootOrderedQ16Chain rightWitness.joint.input rightProducer
          rightBeforeAlpha.digest rightOutputs rightAdvances ∧
      0 < leftOutputs.length ∧
      0 < rightOutputs.length ∧
      leftAdvances.length = leftOutputs.length ∧
      rightAdvances.length = rightOutputs.length ∧
      leftAfterBlocks.digest =
        gammaTerminalDigest leftBeforeAlpha.digest leftAdvances ∧
      rightAfterBlocks.digest =
        gammaTerminalDigest rightBeforeAlpha.digest rightAdvances ∧
      leftAfterAlpha.digest = leftAfterBlocks.digest ∧
      rightAfterAlpha.digest = rightAfterBlocks.digest ∧
      leftAfterAlpha.digest = rightAfterAlpha.digest ∧
      leftAfterFinal256.digest = prefinalDigest ∧
      rightAfterFinal256.digest = prefinalDigest ∧
      leftAfterFinal256.digest = rightAfterFinal256.digest ∧
      HasLiteralStatePrefix leftAfterAlpha.digest leftFinal256Input ∧
      HasLiteralStatePrefix rightAfterAlpha.digest rightFinal256Input ∧
      tableLookup (exactOperationalTable leftWitness.joint.input)
          leftFinal256Input = some prefinalDigest ∧
      tableLookup (exactOperationalTable rightWitness.joint.input)
          rightFinal256Input = some prefinalDigest ∧
      leftPrior = rightPrior ∧
      exactFixedRootRecords leftWitness.joint.input.package.root =
        leftPrior ++ leftAnchorRecord :: leftLater ∧
      exactFixedRootRecords rightWitness.joint.input.package.root =
        rightPrior ++ rightAnchorRecord :: rightLater ∧
      (.machineFresh .adversary leftFinal256Input prefinalDigest :
        UnifiedExposureRecord) ∈ leftPrior ∧
      (.machineFresh .adversary rightFinal256Input prefinalDigest :
        UnifiedExposureRecord) ∈ rightPrior ∧
      decodeTagQM31ExactLE
          ((exactOperationalTape leftWitness.joint.input).messages.challengeValue
            (.alpha 0)) = some leftValue ∧
      decodeTagQM31ExactLE
          ((exactOperationalTape rightWitness.joint.input).messages.challengeValue
            (.alpha 0)) = some rightValue ∧
      exactOperationalChallenge leftWitness.joint.input (.alpha 0) = leftValue ∧
      exactOperationalChallenge rightWitness.joint.input (.alpha 0) =
        rightValue := by
  obtain ⟨leftCanonicalBefore, rightCanonicalBefore, digest, leftBase,
      rightBase, leftAbsorbActor, rightAbsorbActor, leftPrior, rightPrior,
      leftLater, rightLater, leftAnchorRecord, rightAnchorRecord,
      canonicalInputExact, leftCanonicalLookup, rightCanonicalLookup,
      priorExact, leftRootExact, rightRootExact, leftProducerMember,
      rightProducerMember, leftBaseExact, rightBaseExact, leftAbsorbMember,
      rightAbsorbMember⟩ :=
    exact_fixed_clean_pair_k13_adversary_anchor_final256_input_eq
      transitionRoom foldTrial finalTrial hidden left right leftWitness
      rightWitness anchor programmedCover contextExact foldExact
  obtain ⟨leftProducer, leftFinal256Input, leftBeforeAlpha, leftAfterAlpha,
      leftAfterBlocks, leftAfterFinal256, leftOutputs, leftAdvances, leftValue,
      _leftWorkAnswer, leftQ16Base, _leftProducerLookup, _leftProducerBoundary,
      leftOrdered, _leftOutputsLength, leftOutputsPositive,
      leftAdvancesLength, leftTerminalExact, leftAfterAlphaExact,
      leftFinal256InputExact, leftFinal256Lookup, _leftWorkLookup,
      _leftWorkAccepted, leftFinalNonceLookup, leftQ16BaseExact, leftDecode,
      leftOperational⟩ :=
    exact_compiler_alpha_zero_chain_has_root_order transitionRoom
      leftWitness.joint.input
  obtain ⟨rightProducer, rightFinal256Input, rightBeforeAlpha, rightAfterAlpha,
      rightAfterBlocks, rightAfterFinal256, rightOutputs, rightAdvances,
      rightValue, _rightWorkAnswer, rightQ16Base, _rightProducerLookup,
      _rightProducerBoundary, rightOrdered, _rightOutputsLength,
      rightOutputsPositive, rightAdvancesLength, rightTerminalExact,
      rightAfterAlphaExact, rightFinal256InputExact, rightFinal256Lookup,
      _rightWorkLookup, _rightWorkAccepted, rightFinalNonceLookup,
      rightQ16BaseExact, rightDecode, rightOperational⟩ :=
    exact_compiler_alpha_zero_chain_has_root_order transitionRoom
      rightWitness.joint.input
  have leftPrefinalExact : leftAfterFinal256.digest = digest :=
    final_nonce_lookup_and_root_record_fix_digest leftWitness.joint.input
      leftAfterFinal256.digest digest leftQ16Base leftBase leftAbsorbActor
      leftFinalNonceLookup (leftQ16BaseExact.trans leftBaseExact.symm)
      leftAbsorbMember
  have rightPrefinalExact : rightAfterFinal256.digest = digest :=
    final_nonce_lookup_and_root_record_fix_digest rightWitness.joint.input
      rightAfterFinal256.digest digest rightQ16Base rightBase rightAbsorbActor
      rightFinalNonceLookup (rightQ16BaseExact.trans rightBaseExact.symm)
      rightAbsorbMember
  have terminalSuccessorExact :
      leftAfterFinal256.digest = rightAfterFinal256.digest :=
    leftPrefinalExact.trans rightPrefinalExact.symm
  let leftCanonicalInput : ShaInput :=
    bytes leftCanonicalBefore.digest ++
      [domAbsorb,
        (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
          (exactOperationalTape leftWitness.joint.input).messages.finalValues).label] ++
      (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
        (exactOperationalTape leftWitness.joint.input).messages.finalValues).data
  let rightCanonicalInput : ShaInput :=
    bytes rightCanonicalBefore.digest ++
      [domAbsorb,
        (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
          (exactOperationalTape rightWitness.joint.input).messages.finalValues).label] ++
      (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
        (exactOperationalTape rightWitness.joint.input).messages.finalValues).data
  obtain ⟨leftAlphaActor, leftAlphaMember⟩ :=
    exact_final_table_lookup_has_root_record leftWitness.joint.input
      leftFinal256Input digest (by
        simpa [leftPrefinalExact] using leftFinal256Lookup)
  obtain ⟨leftCanonicalActor, leftCanonicalMember⟩ :=
    exact_final_table_lookup_has_root_record leftWitness.joint.input
      leftCanonicalInput digest (by
        simpa [leftCanonicalInput] using leftCanonicalLookup)
  have leftInputExact : leftFinal256Input = leftCanonicalInput := by
    have recordExact :
        (.machineFresh leftAlphaActor leftFinal256Input digest :
            UnifiedExposureRecord) =
          .machineFresh leftCanonicalActor leftCanonicalInput digest :=
      List.inj_on_of_nodup_map
        (exact_root_record_answers_nodup leftWitness.joint.input)
        leftAlphaMember leftCanonicalMember rfl
    injection recordExact
  obtain ⟨rightAlphaActor, rightAlphaMember⟩ :=
    exact_final_table_lookup_has_root_record rightWitness.joint.input
      rightFinal256Input digest (by
        simpa [rightPrefinalExact] using rightFinal256Lookup)
  obtain ⟨rightCanonicalActor, rightCanonicalMember⟩ :=
    exact_final_table_lookup_has_root_record rightWitness.joint.input
      rightCanonicalInput digest (by
        simpa [rightCanonicalInput] using rightCanonicalLookup)
  have rightInputExact : rightFinal256Input = rightCanonicalInput := by
    have recordExact :
        (.machineFresh rightAlphaActor rightFinal256Input digest :
            UnifiedExposureRecord) =
          .machineFresh rightCanonicalActor rightCanonicalInput digest :=
      List.inj_on_of_nodup_map
        (exact_root_record_answers_nodup rightWitness.joint.input)
        rightAlphaMember rightCanonicalMember rfl
    injection recordExact
  have canonicalInputExact' : leftCanonicalInput = rightCanonicalInput := by
    simpa [leftCanonicalInput, rightCanonicalInput] using canonicalInputExact
  have alphaFinal256InputExact : leftFinal256Input = rightFinal256Input :=
    leftInputExact.trans (canonicalInputExact'.trans rightInputExact.symm)
  have alphaTerminalExact :
      leftAfterAlpha.digest = rightAfterAlpha.digest := by
    rw [leftFinal256InputExact, rightFinal256InputExact] at alphaFinal256InputExact
    apply digest_bytes_injective
    have prefixExact := congrArg (List.take 32) alphaFinal256InputExact
    simpa using prefixExact
  have leftFinal256Prefix :
      HasLiteralStatePrefix leftAfterAlpha.digest leftFinal256Input := by
    unfold HasLiteralStatePrefix
    rw [leftFinal256InputExact]
    simp
  have rightFinal256Prefix :
      HasLiteralStatePrefix rightAfterAlpha.digest rightFinal256Input := by
    unfold HasLiteralStatePrefix
    rw [rightFinal256InputExact]
    simp
  have leftFinal256Lookup' :
      tableLookup (exactOperationalTable leftWitness.joint.input)
          leftFinal256Input = some digest := by
    simpa [leftPrefinalExact] using leftFinal256Lookup
  have rightFinal256Lookup' :
      tableLookup (exactOperationalTable rightWitness.joint.input)
          rightFinal256Input = some digest := by
    simpa [rightPrefinalExact] using rightFinal256Lookup
  have leftFinal256PriorMember :
      (.machineFresh .adversary leftFinal256Input digest :
        UnifiedExposureRecord) ∈ leftPrior := by
    rw [leftInputExact]
    simpa [leftCanonicalInput] using leftProducerMember
  have rightFinal256PriorMember :
      (.machineFresh .adversary rightFinal256Input digest :
        UnifiedExposureRecord) ∈ rightPrior := by
    rw [rightInputExact]
    simpa [rightCanonicalInput] using rightProducerMember
  exact ⟨leftProducer, rightProducer, leftFinal256Input, rightFinal256Input,
    leftBeforeAlpha, rightBeforeAlpha,
    leftAfterAlpha, rightAfterAlpha, leftAfterBlocks, rightAfterBlocks,
    leftAfterFinal256, rightAfterFinal256, leftOutputs, leftAdvances,
    rightOutputs, rightAdvances, leftValue, rightValue, digest, leftPrior,
    rightPrior, leftLater, rightLater, leftAnchorRecord, rightAnchorRecord,
    leftOrdered,
    rightOrdered, leftOutputsPositive, rightOutputsPositive,
    leftAdvancesLength, rightAdvancesLength, leftTerminalExact,
    rightTerminalExact, leftAfterAlphaExact, rightAfterAlphaExact,
    alphaTerminalExact, leftPrefinalExact, rightPrefinalExact,
    terminalSuccessorExact, leftFinal256Prefix, rightFinal256Prefix,
    leftFinal256Lookup', rightFinal256Lookup', priorExact, leftRootExact,
    rightRootExact, leftFinal256PriorMember, rightFinal256PriorMember,
    leftDecode, rightDecode,
    leftOperational, rightOperational⟩

/-- If a final256 producer is already inside an anchor prefix, the terminal
advance of its nonempty ordered alpha chain is inside that prefix as well. -/
theorem exact_alpha_terminal_advance_mem_anchor_prior
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (prior anchorLater : List UnifiedExposureRecord)
    (anchorRecord : UnifiedExposureRecord)
    (rootExact : exactFixedRootRecords input.package.root =
      prior ++ anchorRecord :: anchorLater)
    (producerInput : ShaInput) (initialDigest : Digest256)
    (outputs advances : List Digest256)
    (chain : ExactRootOrderedQ16Chain input producerInput initialDigest
      outputs advances)
    (nonempty : 0 < outputs.length)
    (final256Input : ShaInput) (prefinalDigest : Digest256)
    (final256Prefix :
      HasLiteralStatePrefix (gammaTerminalDigest initialDigest advances)
        final256Input)
    (final256Lookup : tableLookup (exactOperationalTable input) final256Input =
      some prefinalDigest)
    (final256Actor : QueryActor)
    (final256Member :
      (.machineFresh final256Actor final256Input prefinalDigest :
        UnifiedExposureRecord) ∈ prior) :
    ∃ blockDigest blockOutput advanceActor,
      tableLookup (exactOperationalTable input)
          (gammaOutputInput blockDigest) = some blockOutput ∧
      tableLookup (exactOperationalTable input)
          (gammaAdvanceInput blockDigest) =
        some (gammaTerminalDigest initialDigest advances) ∧
      (.machineFresh advanceActor (gammaAdvanceInput blockDigest)
          (gammaTerminalDigest initialDigest advances) :
        UnifiedExposureRecord) ∈ prior := by
  classical
  obtain ⟨blockDigest, blockOutput, outputLookup, advanceLookup,
      _outputMember, _advanceMember⟩ :=
    exact_root_ordered_q16_chain_terminal_pair_mem chain nonempty
  obtain ⟨before, middle, after, pairOrder⟩ :=
    exact_compiler_literal_dependency_has_strict_root_order transitionRoom
      input (gammaAdvanceInput blockDigest) final256Input
      (gammaTerminalDigest initialDigest advances) prefinalDigest
      advanceLookup final256Lookup final256Prefix
  obtain ⟨beforeRecords, middleRecords, afterRecords, advanceActor,
      orderedFinalActor, recordOrder⟩ :=
    exact_root_pair_order_lifts_to_records input
      (gammaAdvanceInput blockDigest) final256Input
      (gammaTerminalDigest initialDigest advances) prefinalDigest
      before middle after pairOrder
  have final256MemberRoot :
      (.machineFresh final256Actor final256Input prefinalDigest :
        UnifiedExposureRecord) ∈ exactFixedRootRecords input.package.root := by
    rw [rootExact]
    exact List.mem_append_left _ final256Member
  have orderedFinalMemberRoot :
      (.machineFresh orderedFinalActor final256Input prefinalDigest :
        UnifiedExposureRecord) ∈ exactFixedRootRecords input.package.root := by
    rw [recordOrder]
    simp
  have finalRecordExact :
      (.machineFresh orderedFinalActor final256Input prefinalDigest :
          UnifiedExposureRecord) =
        .machineFresh final256Actor final256Input prefinalDigest :=
    List.inj_on_of_nodup_map (exact_root_record_answers_nodup input)
      orderedFinalMemberRoot final256MemberRoot rfl
  have orderedFinalMember :
      (.machineFresh orderedFinalActor final256Input prefinalDigest :
        UnifiedExposureRecord) ∈ prior := by
    simpa [finalRecordExact] using final256Member
  have rootNodup : (exactFixedRootRecords input.package.root).Nodup :=
    List.Nodup.of_map UnifiedExposureRecord.answer
      (exact_root_record_answers_nodup input)
  have advanceMember := mem_prefix_of_strict_order_and_later_mem
    (exactFixedRootRecords input.package.root) prior anchorLater beforeRecords
    middleRecords afterRecords
    (.machineFresh advanceActor (gammaAdvanceInput blockDigest)
      (gammaTerminalDigest initialDigest advances))
    (.machineFresh orderedFinalActor final256Input prefinalDigest)
    anchorRecord rootNodup rootExact recordOrder orderedFinalMember
  exact ⟨blockDigest, blockOutput, advanceActor, outputLookup, advanceLookup,
    advanceMember⟩

/-- The canonical `final256` producer itself lies in the shared pre-anchor
root prefix.  Thus both executions literally retain the same actor-tagged
producer record, not merely the same final digest. -/
theorem exact_fixed_clean_pair_k13_final256_record_mem_shared_priors
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
    (rightWitness : ExactFixedCleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, right) foldTrial
        finalTrial)
    (anchor : ExactFixedK13AdversaryAnchor leftWitness.joint.input finalTrial)
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (contextExact :
      let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val finalTrial.val
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          left).1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).1)
    (foldExact :
      let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val finalTrial.val
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          left).2.1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).2.1) :
    ∃ (leftPrior rightPrior leftLater rightLater : List UnifiedExposureRecord)
        (leftAnchorRecord rightAnchorRecord : UnifiedExposureRecord)
        (producerInput : ShaInput) (prefinalDigest : Digest256),
      leftPrior = rightPrior ∧
      exactFixedRootRecords leftWitness.joint.input.package.root =
        leftPrior ++ leftAnchorRecord :: leftLater ∧
      exactFixedRootRecords rightWitness.joint.input.package.root =
        rightPrior ++ rightAnchorRecord :: rightLater ∧
      tableLookup (exactOperationalTable leftWitness.joint.input)
        producerInput = some prefinalDigest ∧
      (.machineFresh .adversary producerInput prefinalDigest :
          UnifiedExposureRecord) ∈ leftPrior ∧
      (.machineFresh .adversary producerInput prefinalDigest :
          UnifiedExposureRecord) ∈ rightPrior := by
  obtain ⟨leftBefore, _rightBefore, digest, _leftBase, _rightBase,
      _leftAbsorbActor, _rightAbsorbActor, leftPrior, rightPrior, leftLater,
      rightLater, leftAnchorRecord, rightAnchorRecord, inputExact,
      leftLookup, _rightLookup, priorExact, leftRootExact, rightRootExact,
      leftMember, rightMember, _leftBaseExact, _rightBaseExact,
      _leftAbsorbMember, _rightAbsorbMember⟩ :=
    exact_fixed_clean_pair_k13_adversary_anchor_final256_input_eq
      transitionRoom foldTrial finalTrial hidden left right leftWitness
      rightWitness anchor programmedCover contextExact foldExact
  let producerInput : ShaInput :=
    bytes leftBefore.digest ++ [domAbsorb,
      (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
        (exactOperationalTape leftWitness.joint.input).messages.finalValues).label] ++
      (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
        (exactOperationalTape leftWitness.joint.input).messages.finalValues).data
  exact ⟨leftPrior, rightPrior, leftLater, rightLater, leftAnchorRecord,
    rightAnchorRecord, producerInput, digest, priorExact, leftRootExact,
    rightRootExact, by simpa [producerInput] using leftLookup,
    by simpa [producerInput] using leftMember,
    by simpa [producerInput, inputExact] using rightMember⟩

/-- The last consumed alpha duplex block is identical across the two clean
complete-coordinate fibres.  Equality comes from the shared root record for
the common terminal answer, not from hash injectivity. -/
theorem exact_fixed_clean_pair_k13_alpha_terminal_block_eq
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
    (rightWitness : ExactFixedCleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, right) foldTrial
        finalTrial)
    (anchor : ExactFixedK13AdversaryAnchor leftWitness.joint.input finalTrial)
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (contextExact :
      let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val finalTrial.val
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          left).1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).1)
    (foldExact :
      let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val finalTrial.val
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          left).2.1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).2.1) :
    ∃ leftBlock rightBlock : Digest256, leftBlock = rightBlock := by
  obtain ⟨leftProducer, rightProducer, leftFinal256Input, rightFinal256Input,
      leftBeforeAlpha, rightBeforeAlpha, leftAfterAlpha, rightAfterAlpha,
      leftAfterBlocks, rightAfterBlocks, _leftAfterFinal256,
      _rightAfterFinal256, leftOutputs, leftAdvances, rightOutputs,
      rightAdvances, _leftValue, _rightValue, prefinalDigest, leftPrior,
      rightPrior, leftLater, rightLater, leftAnchorRecord, rightAnchorRecord,
      leftChain,
      rightChain, leftPositive, rightPositive, _leftLengths, _rightLengths,
      leftTerminal, rightTerminal, leftAfterExact, rightAfterExact,
      alphaTerminalExact, _leftPrefinal, _rightPrefinal, _prefinalExact,
      leftFinal256Prefix, rightFinal256Prefix, leftFinal256Lookup,
      rightFinal256Lookup, priorExact, leftRootExact, rightRootExact,
      leftFinalMember, rightFinalMember, _leftDecode, _rightDecode,
      _leftOperational, _rightOperational⟩ :=
    exact_fixed_clean_pair_k13_adversary_anchor_alpha_terminal_eq
      transitionRoom foldTrial finalTrial hidden left right leftWitness
      rightWitness anchor programmedCover contextExact foldExact
  have leftGammaTerminal :
      gammaTerminalDigest leftBeforeAlpha.digest leftAdvances =
        leftAfterAlpha.digest :=
    leftTerminal.symm.trans leftAfterExact.symm
  have rightGammaTerminal :
      gammaTerminalDigest rightBeforeAlpha.digest rightAdvances =
        rightAfterAlpha.digest :=
    rightTerminal.symm.trans rightAfterExact.symm
  have leftPrefix :
      HasLiteralStatePrefix
          (gammaTerminalDigest leftBeforeAlpha.digest leftAdvances)
        leftFinal256Input := by
    simpa only [leftGammaTerminal] using leftFinal256Prefix
  have rightPrefix :
      HasLiteralStatePrefix
          (gammaTerminalDigest rightBeforeAlpha.digest rightAdvances)
        rightFinal256Input := by
    simpa only [rightGammaTerminal] using rightFinal256Prefix
  obtain ⟨leftBlock, _leftOutput, leftAdvanceActor, _leftOutputLookup,
      _leftAdvanceLookup, leftAdvanceMember⟩ :=
    exact_alpha_terminal_advance_mem_anchor_prior transitionRoom
      leftWitness.joint.input leftPrior leftLater leftAnchorRecord leftRootExact
      leftProducer leftBeforeAlpha.digest leftOutputs leftAdvances leftChain
      leftPositive leftFinal256Input prefinalDigest leftPrefix
      leftFinal256Lookup .adversary leftFinalMember
  obtain ⟨rightBlock, _rightOutput, rightAdvanceActor, _rightOutputLookup,
      _rightAdvanceLookup, rightAdvanceMember⟩ :=
    exact_alpha_terminal_advance_mem_anchor_prior transitionRoom
      rightWitness.joint.input rightPrior rightLater rightAnchorRecord
      rightRootExact rightProducer rightBeforeAlpha.digest rightOutputs
      rightAdvances rightChain rightPositive rightFinal256Input prefinalDigest
      rightPrefix rightFinal256Lookup .adversary rightFinalMember
  have leftAdvanceMember' :
      (.machineFresh leftAdvanceActor (gammaAdvanceInput leftBlock)
          leftAfterAlpha.digest : UnifiedExposureRecord) ∈ leftPrior := by
    simpa only [leftGammaTerminal] using leftAdvanceMember
  have rightAdvanceMember' :
      (.machineFresh rightAdvanceActor (gammaAdvanceInput rightBlock)
          leftAfterAlpha.digest : UnifiedExposureRecord) ∈ rightPrior := by
    simpa only [rightGammaTerminal, ← alphaTerminalExact] using
      rightAdvanceMember
  have advanceInputExact :
      gammaAdvanceInput leftBlock = gammaAdvanceInput rightBlock :=
    exact_equal_root_priors_same_answer_input_eq leftWitness.joint.input
      leftPrior rightPrior leftAdvanceActor rightAdvanceActor
      (gammaAdvanceInput leftBlock) (gammaAdvanceInput rightBlock)
      leftAfterAlpha.digest priorExact leftAdvanceMember' rightAdvanceMember'
      (by
        intro record member
        rw [leftRootExact]
        exact List.mem_append_left _ member)
  have blockExact : leftBlock = rightBlock := by
    apply digest_bytes_injective
    have prefixExact := congrArg (List.take 32) advanceInputExact
    simpa [gammaAdvanceInput] using prefixExact
  exact ⟨leftBlock, rightBlock, blockExact⟩

/-- Equality of the canonical `final256` inputs fixes every serialized field
block before q16; this is fixed-width decoding, not hash inversion. -/
theorem exact_fixed_clean_pair_k13_adversary_anchor_final_values_eq
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
    (rightWitness : ExactFixedCleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, right) foldTrial
        finalTrial)
    (anchor : ExactFixedK13AdversaryAnchor leftWitness.joint.input finalTrial)
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (contextExact :
      let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val finalTrial.val
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          left).1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).1)
    (foldExact :
      let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val finalTrial.val
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          left).2.1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).2.1) :
    (exactOperationalTape leftWitness.joint.input).messages.finalValues =
      (exactOperationalTape rightWitness.joint.input).messages.finalValues := by
  obtain ⟨leftBefore, rightBefore, _digest, _leftBase, _rightBase,
      _leftAbsorbActor, _rightAbsorbActor, _leftPrior, _rightPrior, _leftLater,
      _rightLater, _leftAnchorRecord, _rightAnchorRecord, inputExact,
      _leftLookup, _rightLookup, _priorExact, _leftRootExact, _rightRootExact,
      _leftProducerMember, _rightProducerMember, _leftBaseExact,
      _rightBaseExact, _leftAbsorbMember, _rightAbsorbMember⟩ :=
    exact_fixed_clean_pair_k13_adversary_anchor_final256_input_eq
      transitionRoom foldTrial finalTrial hidden left right leftWitness
      rightWitness anchor programmedCover contextExact foldExact
  have leftDrop :
      List.drop 34
          (bytes leftBefore.digest ++ [domAbsorb, final256Label] ++
            encodeBlocks
              (exactOperationalTape leftWitness.joint.input).messages.finalValues) =
        encodeBlocks
          (exactOperationalTape leftWitness.joint.input).messages.finalValues := by
    convert (List.drop_append_length
      (l₁ := bytes leftBefore.digest ++ [domAbsorb, final256Label])
      (l₂ := encodeBlocks
        (exactOperationalTape leftWitness.joint.input).messages.finalValues)) using 1 <;>
      simp
  have rightDrop :
      List.drop 34
          (bytes rightBefore.digest ++ [domAbsorb, final256Label] ++
            encodeBlocks
              (exactOperationalTape rightWitness.joint.input).messages.finalValues) =
        encodeBlocks
          (exactOperationalTape rightWitness.joint.input).messages.finalValues := by
    convert (List.drop_append_length
      (l₁ := bytes rightBefore.digest ++ [domAbsorb, final256Label])
      (l₂ := encodeBlocks
        (exactOperationalTape rightWitness.joint.input).messages.finalValues)) using 1 <;>
      simp
  have canonicalExact :
      bytes leftBefore.digest ++ [domAbsorb, final256Label] ++
          encodeBlocks
            (exactOperationalTape leftWitness.joint.input).messages.finalValues =
        bytes rightBefore.digest ++ [domAbsorb, final256Label] ++
          encodeBlocks
            (exactOperationalTape rightWitness.joint.input).messages.finalValues := by
    simpa only [AspisK1.V7Tag73TranscriptSchedule.Payload.label,
      AspisK1.V7Tag73TranscriptSchedule.Payload.data] using inputExact
  apply encode_blocks_injective 16 256
  calc
    encodeBlocks
        (exactOperationalTape leftWitness.joint.input).messages.finalValues =
      List.drop 34
        (bytes leftBefore.digest ++ [domAbsorb, final256Label] ++
          encodeBlocks
            (exactOperationalTape leftWitness.joint.input).messages.finalValues) :=
      leftDrop.symm
    _ = List.drop 34
        (bytes rightBefore.digest ++ [domAbsorb, final256Label] ++
          encodeBlocks
            (exactOperationalTape rightWitness.joint.input).messages.finalValues) := by
      rw [canonicalExact]
    _ = encodeBlocks
        (exactOperationalTape rightWitness.joint.input).messages.finalValues :=
      rightDrop

/-- Canonical fixed-field decoding transports the serialized equality to the
parsed mathematical final vector. -/
theorem exact_fixed_clean_pair_k13_adversary_anchor_disclosed_final_eq
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (source : ExactFixedK13DecodedParsedSourceProvider transitionFuel
      configuration projection fixedInstance)
    (transitionRoom : 2 ≤ transitionFuel)
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
      let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val finalTrial.val
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          left).1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).1)
    (foldExact :
      let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val finalTrial.val
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          left).2.1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).2.1) :
    (exactK13ParsedProof leftWitness.joint.input).disclosedFinal =
      (exactK13ParsedProof rightWitness.joint.input).disclosedFinal := by
  obtain ⟨leftDecoded, leftDecode, leftBinding⟩ :=
    source (hidden, left) leftWitness.joint.input
  obtain ⟨rightDecoded, rightDecode, rightBinding⟩ :=
    source (hidden, right) rightWitness.joint.input
  have operationalFinalExact :=
    exact_fixed_clean_pair_k13_adversary_anchor_final_values_eq transitionRoom
      foldTrial finalTrial hidden left right leftWitness rightWitness anchor
      programmedCover contextExact foldExact
  have rawFinalExact :
      (fixedTapeRawMessages
          (exactOperationalTape leftWitness.joint.input)).finalValues =
        (fixedTapeRawMessages
          (exactOperationalTape rightWitness.joint.input)).finalValues := by
    simpa [fixedTapeRawMessages, rawOfMessages] using operationalFinalExact
  have decodedExact := decoded_final_message_eq_of_final_values_eq leftDecode
    rightDecode rawFinalExact
  exact leftBinding.disclosedFinalExact.trans
    (decodedExact.trans rightBinding.disclosedFinalExact.symm)

#print axioms
  exact_fold_alpha_context_eq_components
#print axioms
  exact_challenge_prefixes_of_same_four_blocks_eq
#print axioms
  exact_fold_alpha_coordinate_eq_of_routed_lookup
#print axioms
  exact_fixed_clean_pair_k13_adversary_anchor_replays_raw_pre_anchor_tape
#print axioms
  exact_fixed_clean_pair_k13_adversary_anchor_has_shared_native_pause
#print axioms
  exact_fixed_clean_pair_k13_adversary_anchor_root_priors_eq
#print axioms
  exact_fixed_clean_pair_k13_selected_root_priors_eq
#print axioms
  exact_fixed_clean_pair_k13_verifier_anchor_pre_q16_values_eq
#print axioms
  exact_fixed_clean_pair_k13_verifier_anchor_bad_eq
#print axioms
  ExactFixedCleanK13PairBadInvariantOnAdversaryAnchors
#print axioms
  exact_fixed_clean_k13_pair_coordinate_invariant_of_adversary_anchors
#print axioms
  exact_equal_root_priors_same_answer_input_eq
#print axioms
  mem_canonical_prefix_of_strictly_before_pivot
#print axioms
  equal_prefixes_of_equal_decomposition_lengths
#print axioms
  mem_prefix_of_strict_order_and_later_mem
#print axioms
  exact_fixed_clean_pair_k13_adversary_anchor_selected_input_and_digest_eq
#print axioms
  exact_fixed_clean_pair_k13_adversary_anchor_final256_input_eq
#print axioms
  exact_fixed_clean_pair_k13_adversary_anchor_before_final256_digest_eq
#print axioms
  exact_fixed_clean_pair_k13_adversary_anchor_alpha_terminal_eq
#print axioms
  exact_alpha_terminal_advance_mem_anchor_prior
#print axioms
  exact_fixed_clean_pair_k13_final256_record_mem_shared_priors
#print axioms
  exact_fixed_clean_pair_k13_alpha_terminal_block_eq
#print axioms
  exact_fixed_clean_pair_k13_adversary_anchor_final_values_eq
#print axioms
  exact_fixed_clean_pair_k13_adversary_anchor_disclosed_final_eq

end

end AspisK1.V7Tag73ExactPairCoordinateProfileInvariant
