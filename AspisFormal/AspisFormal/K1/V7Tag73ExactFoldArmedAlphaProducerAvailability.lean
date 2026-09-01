import AspisFormal.K1.V7Tag73ExactFoldArmedAlphaDigestNodup
import AspisFormal.K1.V7Tag73ExactFoldArmedRootRouting
import AspisFormal.K1.V7Tag73FoldArmedAlphaProducerPersistence

/-!
# Exact post-fold alpha producer availability

This leaf specializes the schedule-independent producer persistence theorem to
literal prefixes of one accepted Tag-73 root.  It is the chronological bridge
needed by output-slot freshness: once a producer is live at one post-fold
prefix, no intervening accepted-root record can reset it before a later child.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactFoldArmedAlphaProducerAvailability

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AlphaZeroProducerInvariant
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalSlotRouterLookup
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactAlphaZeroControllerAlignment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFinalWorkPairControllerCompletion
open AspisK1.V7Tag73ExactFoldAlphaFinalWorkQ16RootRouting
open AspisK1.V7Tag73ExactFoldArmedAlphaDigestNodup
open AspisK1.V7Tag73ExactFoldArmedAlphaPrefixInvariant
open AspisK1.V7Tag73ExactFoldArmedRootRouting
open AspisK1.V7Tag73ExactFoldArmedAlphaSourceAlignment
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FoldArmedAlphaProducerPersistence
open AspisK1.V7Tag73FoldArmedAlphaCoreInvariant
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- A producer live after any post-fold accepted-root prefix remains live
through every later accepted-root segment.  The proof constructs the actual
block-zero seed and its literal source record from the exact prefix invariant;
there is no abstract restore or source-alignment premise. -/
theorem exact_fold_armed_live_producer_persists_over_post_fold_segment
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (fold : ExactAcceptedFoldTrial input)
    (finalTrial : ExactCompilerExposureTrial parameters)
    (before segment rest : List UnifiedExposureRecord)
    (laterExact : fold.later = before ++ segment ++ rest)
    (producer : AlphaZeroProducer) :
    let controller := foldArmedCompleteController
      (globalOracleCalls := globalFull256OracleCallCap parameters)
      transitionFuel fold.trial.val finalTrial.val
    let initial := foldArmedInitialState
      (exactPlainRomCursor configuration sample.1).erase
    let reachedFold := indexedStateAfterRecords transitionFuel controller
      fold.prior initial
    let afterFold := controller.afterAnswer transitionFuel reachedFold
      fold.answer
    let reached := indexedStateAfterRecords transitionFuel controller before
      afterFold
    producer ∈ reached.memory.2.1.alpha.producers →
      producer ∈
        (indexedStateAfterRecords transitionFuel controller segment
          reached).memory.2.1.alpha.producers := by
  let controller := foldArmedCompleteController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel fold.trial.val finalTrial.val
  let initial := foldArmedInitialState
    (exactPlainRomCursor configuration sample.1).erase
  let reachedFold := indexedStateAfterRecords transitionFuel controller
    fold.prior initial
  let selected : UnifiedExposureRecord := .machineFresh fold.actor
    (bytes fold.digest ++ [domGrind] ++
      bytes (exactOperationalTape input).messages.foldGrinding.selected)
    fold.answer
  let afterFold := controller.afterAnswer transitionFuel reachedFold fold.answer
  let consumedBase := fold.prior ++ [selected]
  let consumed := consumedBase ++ before
  let reached := indexedStateAfterRecords transitionFuel controller before
    afterFold
  dsimp only
  intro producerMember
  have beforeLater : fold.later = before ++ (segment ++ rest) := by
    simpa [List.append_assoc] using laterExact
  have invariant := exact_fold_armed_post_fold_prefix_invariant input fold
    finalTrial before (segment ++ rest) beforeLater
  change FoldArmedAlphaPrefixInvariant consumed reached.memory.2.1 at invariant
  obtain ⟨seed, seedMember, seedZero⟩ :=
    alpha_zero_inventory_member_has_block_zero
      reached.memory.2.1.alpha.producers
      invariant.core.producer.inventoryValid producer producerMember
  obtain ⟨seedActor, seedRecord⟩ :=
    invariant.sourcesLiteral seed seedMember
  have afterFoldIndex : fold.trial.val < afterFold.exposureIndex := by
    have count := indexed_state_after_records_exposure_index transitionFuel
      controller fold.prior initial
    have reachedIndex : reachedFold.exposureIndex = fold.trial.val := by
      simpa [reachedFold, initial, foldArmedInitialState, fold.trialExact] using
        count
    simp [afterFold, reachedIndex]
  have reachedAfterFold : fold.trial.val < reached.exposureIndex := by
    have count := indexed_state_after_records_exposure_index transitionFuel
      controller before afterFold
    rw [count]
    omega
  have consumedState : indexedStateAfterRecords transitionFuel controller
      consumed initial = reached := by
    simp [consumed, consumedBase, selected, reached, afterFold, reachedFold,
      indexed_state_after_records_append, UnifiedExposureRecord.answer]
  have rootAligned := exact_root_records_aligned_for_fold_armed_controller input
    fold.trial finalTrial
  have segmentAligned : IndexedRecordsAligned transitionFuel controller reached
      segment := by
    have aligned := indexed_records_aligned_segment transitionFuel controller
      initial (exactFixedRootRecords input.package.root) consumed segment rest
        rootAligned (by
          rw [fold.rootDecomposition, laterExact]
          simp [consumed, consumedBase, selected, List.append_assoc])
    simpa [consumedState] using aligned
  have segmentOnly : OnlyMachineFreshRecords segment := by
    intro record member
    apply exact_root_records_only_machine_fresh input record
    rw [fold.rootDecomposition, laterExact]
    exact List.mem_append_right fold.prior
      (List.mem_cons_of_mem selected
        (List.mem_append_left rest (List.mem_append_right before member)))
  have prefixNodup : ((consumed ++ segment).map causalInput?).Nodup := by
    have rootNodup := exact_root_record_causal_inputs_nodup input
    rw [fold.rootDecomposition, laterExact] at rootNodup
    have normalized :
        ((consumed ++ segment).map causalInput? ++
          rest.map causalInput?).Nodup := by
      simpa [consumed, consumedBase, selected, List.map_append,
        List.append_assoc] using rootNodup
    exact (List.nodup_append.mp normalized).1
  exact fold_armed_live_producers_persist_over_aligned_records transitionFuel
    fold.trial.val finalTrial.val segment consumed reached seed producer
      seedActor reachedAfterFold segmentAligned segmentOnly prefixNodup
      (by
        simpa [reached] using
          exact_fold_armed_post_fold_prefix_block_zero_expected input fold
            finalTrial before)
      seedZero seedRecord seedMember producerMember

/-- At a literal post-fold output child, the live producer's logical block
cannot already have been consumed.  Any alleged earlier use yields another
live producer at the same block; accepted-root persistence and block
uniqueness identify it with the current producer, after which causal-input
uniqueness says the earlier record is the current record, contradicting strict
prefix length. -/
theorem exact_fold_armed_live_producer_output_slot_unused
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (fold : ExactAcceptedFoldTrial input)
    (finalTrial : ExactCompilerExposureTrial parameters)
    (before later : List UnifiedExposureRecord)
    (outputActor : QueryActor) (producer : AlphaZeroProducer)
    (output : Digest256)
    (laterExact : fold.later = before ++
      (.machineFresh outputActor (gammaOutputInput producer.digest) output :
        UnifiedExposureRecord) :: later) :
    let controller := foldArmedCompleteController
      (globalOracleCalls := globalFull256OracleCallCap parameters)
      transitionFuel fold.trial.val finalTrial.val
    let initial := foldArmedInitialState
      (exactPlainRomCursor configuration sample.1).erase
    let reachedFold := indexedStateAfterRecords transitionFuel controller
      fold.prior initial
    let afterFold := controller.afterAnswer transitionFuel reachedFold
      fold.answer
    let reached := indexedStateAfterRecords transitionFuel controller before
      afterFold
    producer ∈ reached.memory.2.1.alpha.producers →
      producer.block ∉ reached.memory.2.1.alpha.usedSlots := by
  let controller := foldArmedCompleteController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel fold.trial.val finalTrial.val
  let initial := foldArmedInitialState
    (exactPlainRomCursor configuration sample.1).erase
  let reachedFold := indexedStateAfterRecords transitionFuel controller
    fold.prior initial
  let selected : UnifiedExposureRecord := .machineFresh fold.actor
    (bytes fold.digest ++ [domGrind] ++
      bytes (exactOperationalTape input).messages.foldGrinding.selected)
    fold.answer
  let outputRecord : UnifiedExposureRecord := .machineFresh outputActor
    (gammaOutputInput producer.digest) output
  let afterFold := controller.afterAnswer transitionFuel reachedFold fold.answer
  let consumedBase := fold.prior ++ [selected]
  let outputPrefix := consumedBase ++ before
  let reached := indexedStateAfterRecords transitionFuel controller before
    afterFold
  dsimp only
  intro producerMember slotUsed
  have outputRootExact : exactFixedRootRecords input.package.root =
      outputPrefix ++ outputRecord :: later := by
    rw [fold.rootDecomposition, laterExact]
    simp [outputPrefix, consumedBase, selected, outputRecord,
      List.append_assoc]
  have initialFresh : producer.block ∉ initial.memory.2.1.alpha.usedSlots := by
    simp [initial, foldArmedInitialState, inactiveFoldArmedAlphaZeroMemory,
      inactiveAlphaZeroMemory]
  have outputPrefixState : indexedStateAfterRecords transitionFuel controller
      outputPrefix initial = reached := by
    simp [outputPrefix, consumedBase, selected, reached, afterFold, reachedFold,
      indexed_state_after_records_append, UnifiedExposureRecord.answer]
  obtain ⟨usedPrior, usedRecord, usedLater, outputPrefixExact,
      usedPreferred⟩ :=
    fold_armed_complete_alpha_used_slot_has_prior_record transitionFuel
      fold.trial.val finalTrial.val outputPrefix initial producer.block
        initialFresh (by rw [outputPrefixState]; exact slotUsed)
  have usedMemberRoot : usedRecord ∈
      exactFixedRootRecords input.package.root := by
    rw [outputRootExact, outputPrefixExact]
    simp
  obtain ⟨usedActor, usedInput, usedAnswer, usedRecordExact⟩ :=
    exact_root_records_only_machine_fresh input usedRecord usedMemberRoot
  subst usedRecord
  let usedState := indexedStateAfterRecords transitionFuel controller usedPrior
    initial
  have usedPreferred' : controller.preferredSlot usedState =
      some (some (Sum.inl producer.block)) := by
    simpa [controller, usedState] using usedPreferred
  obtain ⟨selectedInput, earlierProducer, selectedInputExact,
      earlierMember, selectedIsOutput, earlierBlock⟩ :=
    fold_armed_complete_alpha_preferred_has_producer transitionFuel
      fold.trial.val finalTrial.val usedState producer.block usedPreferred'
  have usedRootExact : exactFixedRootRecords input.package.root =
      usedPrior ++
        (.machineFresh usedActor usedInput usedAnswer : UnifiedExposureRecord) ::
          (usedLater ++ outputRecord :: later) := by
    rw [outputRootExact, outputPrefixExact]
    simp [List.append_assoc]
  have usedAligned : unifiedRecordAtAnswer transitionFuel usedState.cursor
      usedAnswer = UnifiedExposureRecord.machineFresh usedActor usedInput
        usedAnswer := by
    have rootAligned := exact_root_records_aligned_for_fold_armed_controller
      input fold.trial finalTrial
    exact rootAligned usedPrior _ (usedLater ++ outputRecord :: later)
      usedRootExact
  have usedInputExact : unifiedInputBeforeAnswer? transitionFuel
      usedState.cursor = some usedInput :=
    aligned_machine_record_has_exact_input transitionFuel usedState.cursor
      usedActor usedInput usedAnswer usedAligned
  have selectedInputEq : selectedInput = usedInput :=
    Option.some.inj (selectedInputExact.symm.trans usedInputExact)
  have usedPriorLength : fold.trial.val < usedPrior.length := by
    by_contra notAfter
    have beforeOrAt : usedPrior.length ≤ fold.trial.val := by omega
    have empty := fold_armed_alpha_empty_before_selected_fold transitionFuel
      fold.trial.val finalTrial.val usedPrior initial (by
        simpa [initial, foldArmedInitialState] using beforeOrAt) (by
        simp [initial, foldArmedInitialState,
          inactiveFoldArmedAlphaZeroMemory]) (by
        simp [initial, foldArmedInitialState,
          inactiveFoldArmedAlphaZeroMemory, inactiveAlphaZeroMemory])
    have impossible : earlierProducer ∈
        (indexedStateAfterRecords transitionFuel controller usedPrior
          initial).memory.2.1.alpha.producers := by
      simpa [usedState, controller] using earlierMember
    rw [show
        (indexedStateAfterRecords transitionFuel controller usedPrior
          initial).memory.2.1.alpha.producers = [] by
      simpa [controller] using empty.2] at impossible
    simp at impossible
  have consumedLength : consumedBase.length ≤ usedPrior.length := by
    have foldLength : fold.prior.length = fold.trial.val :=
      fold.trialExact.symm
    simp [consumedBase, foldLength]
    omega
  have appendExact : consumedBase ++ before = usedPrior ++
      (.machineFresh usedActor usedInput usedAnswer : UnifiedExposureRecord) ::
        usedLater := by
    simpa [outputPrefix] using outputPrefixExact
  obtain ⟨usedBefore, usedPriorExact, beforeExact⟩ : ∃ usedBefore,
      usedPrior = consumedBase ++ usedBefore ∧
      before = usedBefore ++
        (.machineFresh usedActor usedInput usedAnswer :
          UnifiedExposureRecord) :: usedLater := by
    rcases List.append_eq_append_iff.mp appendExact with
      ⟨usedBefore, priorExact, tailExact⟩ |
      ⟨gap, baseExact, tailExact⟩
    · exact ⟨usedBefore, priorExact, tailExact⟩
    · have gapLength : gap.length = 0 := by
        have lengths := congrArg List.length baseExact
        simp only [List.length_append] at lengths
        omega
      have gapEmpty : gap = [] := List.eq_nil_of_length_eq_zero gapLength
      subst gap
      simp only [List.append_nil, List.nil_append] at baseExact tailExact
      exact ⟨[], by simpa using baseExact.symm, tailExact.symm⟩
  have consumedBaseState : indexedStateAfterRecords transitionFuel controller
      consumedBase initial = afterFold := by
    simp [consumedBase, selected, afterFold, reachedFold,
      indexed_state_after_records_append, UnifiedExposureRecord.answer]
  have usedStateExact : usedState =
      indexedStateAfterRecords transitionFuel controller usedBefore
        afterFold := by
    change indexedStateAfterRecords transitionFuel controller usedPrior
      initial = _
    rw [usedPriorExact, indexed_state_after_records_append, consumedBaseState]
  have earlierReached : earlierProducer ∈ reached.memory.2.1.alpha.producers := by
    have persisted :=
      exact_fold_armed_live_producer_persists_over_post_fold_segment input fold
        finalTrial usedBefore
          ((.machineFresh usedActor usedInput usedAnswer :
              UnifiedExposureRecord) :: usedLater)
          (outputRecord :: later) (by
            simpa [outputRecord, beforeExact, List.append_assoc] using
              laterExact) earlierProducer
    have persisted' := persisted (by simpa [usedStateExact] using earlierMember)
    simpa [reached, beforeExact, indexed_state_after_records_append,
      usedStateExact] using persisted'
  have reachedInvariant := exact_fold_armed_post_fold_prefix_invariant input
    fold finalTrial before (outputRecord :: later) (by
      simpa [outputRecord] using laterExact)
  change FoldArmedAlphaPrefixInvariant outputPrefix reached.memory.2.1 at reachedInvariant
  have producerExact : earlierProducer = producer :=
    alpha_zero_producer_eq_of_block_eq earlierProducer producer
      reached.memory.2.1.alpha.producers
      reachedInvariant.core.producer.blocksNodup earlierReached producerMember
        earlierBlock
  have sameInput : usedInput = gammaOutputInput producer.digest := by
    rw [← producerExact, ← selectedInputEq]
    simpa [gammaOutputInput] using selectedIsOutput
  have prefixCollision : usedPrior = outputPrefix := by
    apply alpha_mapped_nodup_selected_prefix_eq causalInput?
      (exactFixedRootRecords input.package.root) usedPrior
        (usedLater ++ outputRecord :: later) outputPrefix later
      (.machineFresh usedActor usedInput usedAnswer : UnifiedExposureRecord)
      outputRecord (exact_root_record_causal_inputs_nodup input) usedRootExact
        outputRootExact
    simp [outputRecord, causalInput?, sameInput]
  rw [outputPrefixExact] at prefixCollision
  have impossible := congrArg List.length prefixCollision
  simp at impossible

/-- A literal output child of a live post-fold alpha producer receives the
producer's exact complete-controller label.  The input is recovered from the
accepted-root alignment; digest uniqueness and slot freshness are derived
from the exact prefix rather than assumed. -/
theorem exact_fold_armed_live_producer_output_is_preferred
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (fold : ExactAcceptedFoldTrial input)
    (finalTrial : ExactCompilerExposureTrial parameters)
    (before later : List UnifiedExposureRecord)
    (outputActor : QueryActor) (producer : AlphaZeroProducer)
    (output : Digest256)
    (laterExact : fold.later = before ++
      (.machineFresh outputActor (gammaOutputInput producer.digest) output :
        UnifiedExposureRecord) :: later) :
    let controller := foldArmedCompleteController
      (globalOracleCalls := globalFull256OracleCallCap parameters)
      transitionFuel fold.trial.val finalTrial.val
    let initial := foldArmedInitialState
      (exactPlainRomCursor configuration sample.1).erase
    let reachedFold := indexedStateAfterRecords transitionFuel controller
      fold.prior initial
    let afterFold := controller.afterAnswer transitionFuel reachedFold
      fold.answer
    let reached := indexedStateAfterRecords transitionFuel controller before
      afterFold
    producer ∈ reached.memory.2.1.alpha.producers →
      controller.preferredSlot reached = some (some (Sum.inl producer.block)) := by
  let controller := foldArmedCompleteController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel fold.trial.val finalTrial.val
  let initial := foldArmedInitialState
    (exactPlainRomCursor configuration sample.1).erase
  let reachedFold := indexedStateAfterRecords transitionFuel controller
    fold.prior initial
  let selected : UnifiedExposureRecord := .machineFresh fold.actor
    (bytes fold.digest ++ [domGrind] ++
      bytes (exactOperationalTape input).messages.foldGrinding.selected)
    fold.answer
  let outputRecord : UnifiedExposureRecord := .machineFresh outputActor
    (gammaOutputInput producer.digest) output
  let afterFold := controller.afterAnswer transitionFuel reachedFold fold.answer
  let consumedBase := fold.prior ++ [selected]
  let outputPrefix := consumedBase ++ before
  let reached := indexedStateAfterRecords transitionFuel controller before
    afterFold
  dsimp only
  intro producerMember
  have rootExact : exactFixedRootRecords input.package.root =
      outputPrefix ++ outputRecord :: later := by
    rw [fold.rootDecomposition, laterExact]
    simp [outputPrefix, consumedBase, selected, outputRecord,
      List.append_assoc]
  have prefixState : indexedStateAfterRecords transitionFuel controller
      outputPrefix initial = reached := by
    simp [outputPrefix, consumedBase, selected, reached, afterFold, reachedFold,
      indexed_state_after_records_append, UnifiedExposureRecord.answer]
  have aligned := exact_root_records_aligned_for_fold_armed_controller input
    fold.trial finalTrial outputPrefix outputRecord later rootExact
  have inputExact : unifiedInputBeforeAnswer? transitionFuel reached.cursor =
      some (gammaOutputInput producer.digest) := by
    have exact := aligned_machine_record_has_exact_input transitionFuel
      (indexedStateAfterRecords transitionFuel controller outputPrefix initial).cursor
      outputActor (gammaOutputInput producer.digest) output aligned
    simpa [prefixState] using exact
  have digestNodup :
      (reached.memory.2.1.alpha.producers.map AlphaZeroProducer.digest).Nodup := by
    simpa [reached] using
      exact_fold_armed_post_fold_prefix_producer_digests_nodup input fold
        finalTrial before (outputRecord :: later) (by
          simpa [outputRecord] using laterExact)
  have slotUnused : producer.block ∉ reached.memory.2.1.alpha.usedSlots :=
    exact_fold_armed_live_producer_output_slot_unused input fold finalTrial
      before later outputActor producer output laterExact producerMember
  let armedAlphaReached := foldArmedAlphaState reached
  let alphaReached := foldArmedAlphaIndexedState armedAlphaReached
  have alphaInputExact : unifiedInputBeforeAnswer? transitionFuel
      alphaReached.cursor = some (gammaOutputInput producer.digest) := by
    simpa [alphaReached, armedAlphaReached, foldArmedAlphaIndexedState,
      foldArmedAlphaState, alphaIndexedState,
      foldArmedUnderlyingState] using inputExact
  have alphaDigestNodup :
      (alphaReached.memory.producers.map AlphaZeroProducer.digest).Nodup := by
    simpa [alphaReached, armedAlphaReached, foldArmedAlphaIndexedState,
      foldArmedAlphaState, alphaIndexedState,
      foldArmedUnderlyingState] using digestNodup
  have alphaProducerMember : producer ∈ alphaReached.memory.producers := by
    simpa [alphaReached, armedAlphaReached, foldArmedAlphaIndexedState,
      foldArmedAlphaState, alphaIndexedState,
      foldArmedUnderlyingState] using producerMember
  have alphaSlotUnused : producer.block ∉ alphaReached.memory.usedSlots := by
    simpa [alphaReached, armedAlphaReached, foldArmedAlphaIndexedState,
      foldArmedAlphaState, alphaIndexedState,
      foldArmedUnderlyingState] using slotUnused
  have alphaPreferred : alphaZeroPreferredSlot transitionFuel
      alphaReached = some producer.block :=
    alpha_zero_output_is_preferred_of_producer transitionFuel
      alphaReached producer
      (by simpa [gammaOutputInput] using alphaInputExact)
      alphaDigestNodup alphaProducerMember alphaSlotUnused
  have underlyingPreferred :
      (alphaFinalWorkQ16DagController transitionFuel finalTrial.val
        (foldArmedAlphaZeroController transitionFuel)).preferredSlot
          (foldArmedUnderlyingState reached) =
        some (Sum.inl producer.block) := by
    apply alpha_final_work_q16_preferred_of_alpha
    simpa [foldArmedAlphaZeroController, alphaReached, armedAlphaReached,
      foldArmedAlphaIndexedState, foldArmedAlphaState, alphaIndexedState,
      foldArmedUnderlyingState] using alphaPreferred
  have reachedAfterFold : fold.trial.val < reached.exposureIndex := by
    have foldCount := indexed_state_after_records_exposure_index transitionFuel
      controller fold.prior initial
    have reachedFoldIndex : reachedFold.exposureIndex = fold.trial.val := by
      simpa [reachedFold, initial, foldArmedInitialState, fold.trialExact] using
        foldCount
    have afterFoldIndex : afterFold.exposureIndex = fold.trial.val + 1 := by
      simp [afterFold, reachedFoldIndex]
    have beforeCount := indexed_state_after_records_exposure_index
      transitionFuel controller before afterFold
    rw [beforeCount, afterFoldIndex]
    omega
  have notFold : reached.exposureIndex ≠ fold.trial.val := by omega
  change controller.preferredSlot reached = some (some (Sum.inl producer.block))
  simp only [controller, foldArmedCompleteController, notFold, and_false,
    if_false]
  simpa [foldArmedUnderlyingState] using congrArg (Option.map some)
    underlyingPreferred

/-- The exact preferred label is consumed by the fixed 518-coordinate router,
so the literal accepted-root answer is installed at the producer's named alpha
coordinate. -/
theorem exact_fold_armed_live_producer_output_is_routed
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (fold : ExactAcceptedFoldTrial input)
    (finalTrial : ExactCompilerExposureTrial parameters)
    (before later : List UnifiedExposureRecord)
    (outputActor : QueryActor) (producer : AlphaZeroProducer)
    (output : Digest256)
    (laterExact : fold.later = before ++
      (.machineFresh outputActor (gammaOutputInput producer.digest) output :
        UnifiedExposureRecord) :: later)
    (producerMember :
      let controller := foldArmedCompleteController
        (globalOracleCalls := globalFull256OracleCallCap parameters)
        transitionFuel fold.trial.val finalTrial.val
      let initial := foldArmedInitialState
        (exactPlainRomCursor configuration sample.1).erase
      let reachedFold := indexedStateAfterRecords transitionFuel controller
        fold.prior initial
      let afterFold := controller.afterAnswer transitionFuel reachedFold
        fold.answer
      let reached := indexedStateAfterRecords transitionFuel controller before
        afterFold
      producer ∈ reached.memory.2.1.alpha.producers) :
    causalRoutedAnswer? (some (Sum.inl producer.block))
      (exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters transitionFuel
        fold.trial.val finalTrial.val
        (exactPlainRomCursor configuration sample.1).erase)
      (foldAlphaFinalWorkQ16NamedSlotInputTape
        (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters sample.2)) =
      some output := by
  let controller := foldArmedCompleteController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel fold.trial.val finalTrial.val
  let initial := foldArmedInitialState
    (exactPlainRomCursor configuration sample.1).erase
  let reachedFold := indexedStateAfterRecords transitionFuel controller
    fold.prior initial
  let selected : UnifiedExposureRecord := .machineFresh fold.actor
    (bytes fold.digest ++ [domGrind] ++
      bytes (exactOperationalTape input).messages.foldGrinding.selected)
    fold.answer
  let outputRecord : UnifiedExposureRecord := .machineFresh outputActor
    (gammaOutputInput producer.digest) output
  let afterFold := controller.afterAnswer transitionFuel reachedFold fold.answer
  let outputPrefix := fold.prior ++ [selected] ++ before
  let reached := indexedStateAfterRecords transitionFuel controller before
    afterFold
  have rootExact : exactFixedRootRecords input.package.root =
      outputPrefix ++ outputRecord :: later := by
    rw [fold.rootDecomposition, laterExact]
    simp [outputPrefix, selected, outputRecord, List.append_assoc]
  have preferred : controller.preferredSlot reached =
      some (some (Sum.inl producer.block)) := by
    simpa [controller, initial, reachedFold, afterFold, reached] using
      exact_fold_armed_live_producer_output_is_preferred input fold finalTrial
        before later outputActor producer output laterExact producerMember
  have prefixState : indexedStateAfterRecords transitionFuel controller
      outputPrefix initial = reached := by
    simp [outputPrefix, selected, reached, afterFold, reachedFold,
      indexed_state_after_records_append, UnifiedExposureRecord.answer]
  apply exact_fold_armed_root_answer_is_routed programmedCover input fold.trial
    finalTrial outputPrefix later outputActor (gammaOutputInput producer.digest)
      output (some (Sum.inl producer.block))
  · simpa [outputRecord] using rootExact
  · simpa [controller, initial, prefixState] using preferred

/-- A post-fold advance input below a live producer appends the exact next
producer in the armed memory.  The still-armed boundary cannot alias the
33-byte advance coordinate because every valid boundary has length 43. -/
theorem fold_armed_alpha_after_advance_contains_next
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedAlphaZeroMemory)
    (parent : AlphaZeroProducer) (advanced : Digest256)
    (bounded : parent.block.val + 1 < 4)
    (inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor =
      some (gammaAdvanceInput parent.digest))
    (invariant : FoldArmedAlphaCoreInvariant state.memory)
    (digestNodup :
      (state.memory.alpha.producers.map AlphaZeroProducer.digest).Nodup)
    (parentMember : parent ∈ state.memory.alpha.producers) :
    ({ digest := advanced, block := ⟨parent.block.val + 1, bounded⟩,
        sourceInput := gammaAdvanceInput parent.digest } : AlphaZeroProducer) ∈
      (foldArmedAlphaAfterMemory transitionFuel state advanced).alpha.producers := by
  have notBoundary : state.memory.expectedBoundary ≠
      some (gammaAdvanceInput parent.digest) := by
    intro exact
    have lengthExact := invariant.expectedBoundaryLength
      (gammaAdvanceInput parent.digest) exact
    simp [gammaAdvanceInput] at lengthExact
  have producersExact := fold_armed_alpha_nonboundary_uses_advance_update
    transitionFuel state (gammaAdvanceInput parent.digest) advanced inputExact
      notBoundary
  rw [producersExact]
  have selected : alphaZeroAdvancedSlot? state.memory.alpha.producers
      (gammaAdvanceInput parent.digest) =
        some ⟨parent.block.val + 1, bounded⟩ := by
    unfold gammaAdvanceInput
    exact alpha_zero_advanced_slot_of_digest_nodup parent bounded
      state.memory.alpha.producers digestNodup parentMember
  unfold updateAlphaZeroProducers
  rw [selected]
  simp

/-- Literal accepted-root specialization of advance installation. -/
theorem exact_fold_armed_live_producer_advance_installs_next
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (fold : ExactAcceptedFoldTrial input)
    (finalTrial : ExactCompilerExposureTrial parameters)
    (before later : List UnifiedExposureRecord)
    (advanceActor : QueryActor) (parent : AlphaZeroProducer)
    (advanced : Digest256) (bounded : parent.block.val + 1 < 4)
    (laterExact : fold.later = before ++
      (.machineFresh advanceActor (gammaAdvanceInput parent.digest) advanced :
        UnifiedExposureRecord) :: later) :
    let controller := foldArmedCompleteController
      (globalOracleCalls := globalFull256OracleCallCap parameters)
      transitionFuel fold.trial.val finalTrial.val
    let initial := foldArmedInitialState
      (exactPlainRomCursor configuration sample.1).erase
    let reachedFold := indexedStateAfterRecords transitionFuel controller
      fold.prior initial
    let afterFold := controller.afterAnswer transitionFuel reachedFold
      fold.answer
    let reached := indexedStateAfterRecords transitionFuel controller before
      afterFold
    parent ∈ reached.memory.2.1.alpha.producers →
      ({ digest := advanced, block := ⟨parent.block.val + 1, bounded⟩,
          sourceInput := gammaAdvanceInput parent.digest } : AlphaZeroProducer) ∈
        (controller.afterAnswer transitionFuel reached advanced).memory.2.1.alpha.producers := by
  let controller := foldArmedCompleteController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel fold.trial.val finalTrial.val
  let initial := foldArmedInitialState
    (exactPlainRomCursor configuration sample.1).erase
  let reachedFold := indexedStateAfterRecords transitionFuel controller
    fold.prior initial
  let selected : UnifiedExposureRecord := .machineFresh fold.actor
    (bytes fold.digest ++ [domGrind] ++
      bytes (exactOperationalTape input).messages.foldGrinding.selected)
    fold.answer
  let advanceRecord : UnifiedExposureRecord := .machineFresh advanceActor
    (gammaAdvanceInput parent.digest) advanced
  let afterFold := controller.afterAnswer transitionFuel reachedFold fold.answer
  let outputPrefix := fold.prior ++ [selected] ++ before
  let reached := indexedStateAfterRecords transitionFuel controller before
    afterFold
  dsimp only
  intro parentMember
  have rootExact : exactFixedRootRecords input.package.root =
      outputPrefix ++ advanceRecord :: later := by
    rw [fold.rootDecomposition, laterExact]
    simp [outputPrefix, selected, advanceRecord, List.append_assoc]
  have prefixState : indexedStateAfterRecords transitionFuel controller
      outputPrefix initial = reached := by
    simp [outputPrefix, selected, reached, afterFold, reachedFold,
      indexed_state_after_records_append, UnifiedExposureRecord.answer]
  have aligned := exact_root_records_aligned_for_fold_armed_controller input
    fold.trial finalTrial outputPrefix advanceRecord later rootExact
  have inputExact : unifiedInputBeforeAnswer? transitionFuel reached.cursor =
      some (gammaAdvanceInput parent.digest) := by
    have exact := aligned_machine_record_has_exact_input transitionFuel
      (indexedStateAfterRecords transitionFuel controller outputPrefix initial).cursor
      advanceActor (gammaAdvanceInput parent.digest) advanced aligned
    simpa [prefixState] using exact
  have prefixInvariant := exact_fold_armed_post_fold_prefix_invariant input fold
    finalTrial before (advanceRecord :: later) (by
      simpa [advanceRecord] using laterExact)
  have invariant : FoldArmedAlphaCoreInvariant reached.memory.2.1 := by
    simpa [outputPrefix, selected, reached] using prefixInvariant.core
  have digestNodup :
      (reached.memory.2.1.alpha.producers.map AlphaZeroProducer.digest).Nodup := by
    simpa [reached] using
      exact_fold_armed_post_fold_prefix_producer_digests_nodup input fold
        finalTrial before (advanceRecord :: later) (by
          simpa [advanceRecord] using laterExact)
  let armedAlphaReached := foldArmedAlphaState reached
  have nextMember := fold_armed_alpha_after_advance_contains_next transitionFuel
    armedAlphaReached parent advanced bounded
      (by simpa [armedAlphaReached, foldArmedAlphaState, alphaIndexedState,
        foldArmedUnderlyingState] using inputExact)
      (by simpa [armedAlphaReached, foldArmedAlphaState, alphaIndexedState,
        foldArmedUnderlyingState] using invariant)
      (by simpa [armedAlphaReached, foldArmedAlphaState, alphaIndexedState,
        foldArmedUnderlyingState] using digestNodup)
      (by simpa [armedAlphaReached, foldArmedAlphaState, alphaIndexedState,
        foldArmedUnderlyingState] using parentMember)
  have reachedAfterFold : fold.trial.val < reached.exposureIndex := by
    have foldCount := indexed_state_after_records_exposure_index transitionFuel
      controller fold.prior initial
    have reachedFoldIndex : reachedFold.exposureIndex = fold.trial.val := by
      simpa [reachedFold, initial, foldArmedInitialState, fold.trialExact] using
        foldCount
    have afterFoldIndex : afterFold.exposureIndex = fold.trial.val + 1 := by
      simp [afterFold, reachedFoldIndex]
    have beforeCount := indexed_state_after_records_exposure_index
      transitionFuel controller before afterFold
    rw [beforeCount, afterFoldIndex]
    omega
  have notFold : reached.exposureIndex ≠ fold.trial.val := by omega
  have afterMemoryAlpha :
      (controller.afterMemory reached advanced).2.1 =
        foldArmedAlphaAfterMemory transitionFuel armedAlphaReached advanced := by
    simp [controller, foldArmedCompleteController, notFold, armedAlphaReached,
      foldArmedAlphaState, alphaIndexedState, foldArmedUnderlyingState,
      alpha_final_work_q16_after_memory, foldArmedAlphaZeroController]
  change AlphaZeroProducer.mk advanced ⟨parent.block.val + 1, bounded⟩
      (gammaAdvanceInput parent.digest) ∈
    (controller.afterMemory reached advanced).2.1.alpha.producers
  rw [afterMemoryAlpha]
  exact nextMember

#print axioms
  exact_fold_armed_live_producer_persists_over_post_fold_segment
#print axioms exact_fold_armed_live_producer_output_slot_unused
#print axioms exact_fold_armed_live_producer_output_is_preferred
#print axioms exact_fold_armed_live_producer_output_is_routed
#print axioms fold_armed_alpha_after_advance_contains_next
#print axioms exact_fold_armed_live_producer_advance_installs_next

end

end AspisK1.V7Tag73ExactFoldArmedAlphaProducerAvailability
