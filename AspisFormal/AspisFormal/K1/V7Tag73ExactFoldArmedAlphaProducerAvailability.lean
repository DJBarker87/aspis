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
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFinalWorkPairControllerCompletion
open AspisK1.V7Tag73ExactFoldArmedAlphaPrefixInvariant
open AspisK1.V7Tag73ExactFoldArmedAlphaSourceAlignment
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FoldArmedAlphaProducerPersistence
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalSemanticReplay
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

#print axioms
  exact_fold_armed_live_producer_persists_over_post_fold_segment

end

end AspisK1.V7Tag73ExactFoldArmedAlphaProducerAvailability
