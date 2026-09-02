import AspisFormal.K1.V7Tag73ExactFoldArmedAlphaDigestNodup

/-!
# Fold-armed alpha producer persistence

This leaf develops the schedule-independent producer facts used by the
adversary-first Tag-73 alpha routing argument.  In particular, every live
nonempty recursive producer inventory contains a genuine block-zero ancestor;
there is no orphan positive-block producer.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73FoldArmedAlphaProducerPersistence

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AlphaZeroProducerInvariant
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFoldArmedAlphaPrefixInvariant
open AspisK1.V7Tag73FoldArmedAlphaCoreInvariant
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Every live block-zero producer is the unique armed boundary seed. -/
def AlphaBlockZeroMatchesExpected (memory : FoldArmedAlphaZeroMemory) : Prop :=
  ∀ producer ∈ memory.alpha.producers,
    producer.block.val = 0 →
      memory.expectedBoundary = some producer.sourceInput

/-- Recursive source validity forces every live producer to descend from a
producer at logical block zero. -/
theorem alpha_zero_inventory_member_has_block_zero
    (producers : List AlphaZeroProducer)
    (valid : AlphaZeroProducerInventoryValid producers) :
    ∀ producer ∈ producers,
      ∃ seed ∈ producers, seed.block.val = 0 := by
  intro producer producerMember
  generalize blockValue : producer.block.val = value
  induction value using Nat.strong_induction_on generalizing producer with
  | h value ih =>
      rcases valid producer producerMember with zero |
          ⟨parent, parentMember, parentBlock, _sourceExact⟩
      · exact ⟨producer, producerMember, zero⟩
      · have parentLt : parent.block.val < value := by omega
        exact ih parent.block.val parentLt parent parentMember rfl

/-- Away from the unique armed boundary, an ordinary fold-armed step can
only retain or append to the alpha producer inventory. -/
theorem fold_armed_alpha_producers_prefix_of_nonboundary
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedAlphaZeroMemory)
    (input : ShaInput) (answer : Digest256)
    (inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor =
      some input)
    (notBoundary : state.memory.expectedBoundary ≠ some input) :
    state.memory.alpha.producers <+:
      (foldArmedAlphaAfterMemory transitionFuel state answer).alpha.producers := by
  rw [fold_armed_alpha_nonboundary_uses_advance_update transitionFuel state
    input answer inputExact notBoundary]
  exact update_alpha_zero_producers_prefix state.memory.alpha.producers input
    answer

/-- Complete-controller projection of the preceding local fact once the
selected fold record has already armed the outer controller. -/
theorem fold_armed_complete_alpha_producers_prefix_of_nonboundary
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalWorkAnchorIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedCompleteMemory)
    (input : ShaInput) (answer : Digest256)
    (afterFold : foldExposureIndex < state.exposureIndex)
    (inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor =
      some input)
    (notBoundary : state.memory.2.1.expectedBoundary ≠ some input) :
    state.memory.2.1.alpha.producers <+:
      ((foldArmedCompleteController transitionFuel foldExposureIndex
        finalWorkAnchorIndex).afterAnswer transitionFuel state answer).memory.2.1.alpha.producers := by
  have indexNe : state.exposureIndex ≠ foldExposureIndex := by omega
  simp only [IndexedUnifiedExposureController.afterAnswer,
    foldArmedCompleteController, indexNe, if_false,
    alpha_final_work_q16_after_memory]
  change state.memory.2.1.alpha.producers <+:
    (foldArmedAlphaAfterMemory transitionFuel (foldArmedAlphaState state)
      answer).alpha.producers
  apply fold_armed_alpha_producers_prefix_of_nonboundary transitionFuel
    (foldArmedAlphaState state) input answer
  · simpa [foldArmedAlphaState, foldArmedUnderlyingState,
      alphaIndexedState] using inputExact
  · simpa [foldArmedAlphaState, foldArmedUnderlyingState,
      alphaIndexedState] using notBoundary

/-- Ordinary fold-armed replay preserves the identity of the block-zero
boundary seed. -/
theorem fold_armed_alpha_after_memory_preserves_block_zero_expected
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedAlphaZeroMemory)
    (answer : Digest256)
    (matching : AlphaBlockZeroMatchesExpected state.memory) :
    AlphaBlockZeroMatchesExpected
      (foldArmedAlphaAfterMemory transitionFuel state answer) := by
  unfold AlphaBlockZeroMatchesExpected
  cases inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor with
  | none =>
      intro producer member blockZero
      have expectedExact :
          (foldArmedAlphaAfterMemory transitionFuel state answer).expectedBoundary =
            state.memory.expectedBoundary := by
        simp [foldArmedAlphaAfterMemory, inputExact]
      rw [expectedExact]
      exact matching producer (by
        simpa [foldArmedAlphaAfterMemory, inputExact] using member) blockZero
  | some input =>
      have expectedExact :
          (foldArmedAlphaAfterMemory transitionFuel state answer).expectedBoundary =
            state.memory.expectedBoundary := by
        simp [foldArmedAlphaAfterMemory, inputExact]
      by_cases boundary : state.memory.expectedBoundary = some input
      · intro producer member blockZero
        have installed := fold_armed_alpha_exact_boundary_installs_block_zero
          transitionFuel state input answer inputExact boundary
        rw [installed] at member
        simp only [List.mem_singleton] at member
        subst producer
        rw [expectedExact]
        exact boundary
      · intro producer member blockZero
        rw [expectedExact]
        have updated := fold_armed_alpha_nonboundary_uses_advance_update
          transitionFuel state input answer inputExact boundary
        rw [updated] at member
        cases advanced : alphaZeroAdvancedSlot? state.memory.alpha.producers
            input with
        | none =>
            exact matching producer (by
              simpa [updateAlphaZeroProducers, advanced] using member) blockZero
        | some block =>
            have member' : producer ∈ state.memory.alpha.producers ++
                [{ digest := answer, block := block, sourceInput := input }] := by
              simpa [updateAlphaZeroProducers, advanced] using member
            rw [List.mem_append] at member'
            rcases member' with old | added
            · exact matching producer old blockZero
            · simp only [List.mem_singleton] at added
              subst producer
              obtain ⟨_parent, _parentMember, _inputShape, successor⟩ :=
                alpha_zero_advanced_slot_cases state.memory.alpha.producers
                  input block advanced
              simp at blockZero
              omega

/-- Arming an empty pre-fold inventory either leaves it empty or installs the
cached boundary answer as the unique matching block-zero seed. -/
theorem arm_fold_alpha_memory_empty_block_zero_expected
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedAlphaZeroMemory)
    (answer : Digest256)
    (empty : state.memory.alpha.producers = []) :
    AlphaBlockZeroMatchesExpected
      (armFoldAlphaMemory transitionFuel state answer) := by
  unfold AlphaBlockZeroMatchesExpected armFoldAlphaMemory
  split
  next noBoundary =>
    intro producer member _blockZero
    rw [empty] at member
    simp at member
  next target armed =>
    split
    next uncached =>
      intro producer member _blockZero
      rw [empty] at member
      simp at member
    next boundaryAnswer cached =>
      intro producer member _blockZero
      let seed : AlphaZeroProducer := ⟨boundaryAnswer, 0, target⟩
      have closed := cached_alpha_producer_closure_invariant
        state.memory.seenMachine target boundaryAnswer
          state.memory.alpha.usedSlots (by
            unfold armFoldAlphaBoundary at armed
            cases inputExact : unifiedInputBeforeAnswer? transitionFuel
                state.cursor with
            | none => simp [inputExact] at armed
            | some input =>
                simp only [inputExact, Option.bind_some] at armed
                exact fold_work_input_to_alpha_boundary_length input target
                  armed)
      have seedMember : seed ∈ cachedAlphaProducerClosure
          state.memory.seenMachine target boundaryAnswer := by
        exact cached_alpha_producer_closure_contains_block_zero
          state.memory.seenMachine target boundaryAnswer
      have blockEq : producer.block = seed.block := Fin.ext (by
        simpa [seed] using _blockZero)
      have producerEq : producer = seed :=
        alpha_zero_producer_eq_of_block_eq producer seed
          (cachedAlphaProducerClosure state.memory.seenMachine target
            boundaryAnswer) closed.1.blocksNodup member seedMember blockEq
      subst producer
      rfl

/-- Exact accepted execution immediately after its selected fold record. -/
theorem exact_fold_armed_after_fold_block_zero_expected
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
    (finalTrial : ExactCompilerExposureTrial parameters) :
    let controller := foldArmedCompleteController
      (globalOracleCalls := globalFull256OracleCallCap parameters)
      transitionFuel fold.trial.val finalTrial.val
    let reached := indexedStateAfterRecords transitionFuel controller
      fold.prior
      (foldArmedInitialState
        (exactPlainRomCursor configuration sample.1).erase)
    let afterFold := controller.afterAnswer transitionFuel reached fold.answer
    AlphaBlockZeroMatchesExpected afterFold.memory.2.1 := by
  let controller := foldArmedCompleteController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel fold.trial.val finalTrial.val
  let initial := foldArmedInitialState
    (exactPlainRomCursor configuration sample.1).erase
  let reached := indexedStateAfterRecords transitionFuel controller fold.prior
    initial
  let afterFold := controller.afterAnswer transitionFuel reached fold.answer
  have empty := exact_fold_armed_reached_fold_alpha_empty input fold finalTrial
  change reached.memory.2.1.expectedBoundary = none ∧
    reached.memory.2.1.alpha.producers = [] at empty
  have atFold : reached.exposureIndex = fold.trial.val := by
    have count := indexed_state_after_records_exposure_index transitionFuel
      controller fold.prior initial
    simpa [reached, initial, foldArmedInitialState, fold.trialExact] using count
  have alphaMemoryExact : afterFold.memory.2.1 =
      armFoldAlphaMemory transitionFuel (foldArmedAlphaState reached)
        fold.answer := by
    simp [afterFold, controller, IndexedUnifiedExposureController.afterAnswer,
      foldArmedCompleteController, atFold]
  dsimp only
  rw [alphaMemoryExact]
  apply arm_fold_alpha_memory_empty_block_zero_expected transitionFuel
    (foldArmedAlphaState reached) fold.answer
  simpa [foldArmedAlphaState, foldArmedUnderlyingState, alphaIndexedState]
    using empty.2

/-- One complete-controller step after the selected fold preserves the
block-zero/boundary identity. -/
theorem fold_armed_complete_after_fold_preserves_block_zero_expected
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalWorkAnchorIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedCompleteMemory)
    (answer : Digest256)
    (afterFold : foldExposureIndex < state.exposureIndex)
    (matching : AlphaBlockZeroMatchesExpected state.memory.2.1) :
    AlphaBlockZeroMatchesExpected
      ((foldArmedCompleteController transitionFuel foldExposureIndex
        finalWorkAnchorIndex).afterAnswer transitionFuel state answer).memory.2.1 := by
  have indexNe : state.exposureIndex ≠ foldExposureIndex := by omega
  simp only [IndexedUnifiedExposureController.afterAnswer,
    foldArmedCompleteController, indexNe, if_false,
    alpha_final_work_q16_after_memory]
  exact fold_armed_alpha_after_memory_preserves_block_zero_expected
    transitionFuel (foldArmedAlphaState state) answer (by
      simpa [foldArmedAlphaState, foldArmedUnderlyingState, alphaIndexedState]
        using matching)

/-- Arbitrary literal replay after the fold retains the same boundary seed
identity. -/
theorem fold_armed_complete_records_preserve_block_zero_expected
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalWorkAnchorIndex : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        FoldArmedCompleteMemory),
      foldExposureIndex < state.exposureIndex →
      AlphaBlockZeroMatchesExpected state.memory.2.1 →
      AlphaBlockZeroMatchesExpected
        (indexedStateAfterRecords transitionFuel
          (foldArmedCompleteController transitionFuel foldExposureIndex
            finalWorkAnchorIndex) records state).memory.2.1 := by
  intro records
  induction records with
  | nil =>
      intro state _afterFold matching
      simpa using matching
  | cons head tail ih =>
      intro state afterFold matching
      rw [indexed_state_after_records_cons]
      apply ih
      · simp only [indexed_after_answer_exposure_index]
        omega
      · exact fold_armed_complete_after_fold_preserves_block_zero_expected
          transitionFuel foldExposureIndex finalWorkAnchorIndex state
            head.answer afterFold matching

/-- Exact accepted-root prefix form used by later producer persistence. -/
theorem exact_fold_armed_post_fold_prefix_block_zero_expected
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
    (segment : List UnifiedExposureRecord) :
    let controller := foldArmedCompleteController
      (globalOracleCalls := globalFull256OracleCallCap parameters)
      transitionFuel fold.trial.val finalTrial.val
    let reachedFold := indexedStateAfterRecords transitionFuel controller
      fold.prior
      (foldArmedInitialState
        (exactPlainRomCursor configuration sample.1).erase)
    let afterFold := controller.afterAnswer transitionFuel reachedFold
      fold.answer
    let reached := indexedStateAfterRecords transitionFuel controller segment
      afterFold
    AlphaBlockZeroMatchesExpected reached.memory.2.1 := by
  let controller := foldArmedCompleteController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel fold.trial.val finalTrial.val
  let initial := foldArmedInitialState
    (exactPlainRomCursor configuration sample.1).erase
  let reachedFold := indexedStateAfterRecords transitionFuel controller
    fold.prior initial
  let afterFold := controller.afterAnswer transitionFuel reachedFold fold.answer
  have matching := exact_fold_armed_after_fold_block_zero_expected input fold
    finalTrial
  have afterIndex : fold.trial.val < afterFold.exposureIndex := by
    have count := indexed_state_after_records_exposure_index transitionFuel
      controller fold.prior initial
    have reachedIndex : reachedFold.exposureIndex = fold.trial.val := by
      simpa [reachedFold, initial, foldArmedInitialState, fold.trialExact] using
        count
    simp [afterFold, reachedIndex]
  dsimp only
  exact fold_armed_complete_records_preserve_block_zero_expected
    transitionFuel fold.trial.val finalTrial.val segment afterFold afterIndex
      (by simpa [controller, initial, reachedFold, afterFold] using matching)

/-- A fresh literal root input cannot encounter the armed boundary again
while any descendant producer remains live. -/
theorem live_alpha_producer_forces_nonboundary_of_fresh_input
    (records : List UnifiedExposureRecord)
    (memory : FoldArmedAlphaZeroMemory)
    (producer : AlphaZeroProducer)
    (input : ShaInput)
    (matching : AlphaBlockZeroMatchesExpected memory)
    (valid : AlphaZeroProducerInventoryValid memory.alpha.producers)
    (literal : AlphaProducersHaveLiteralRecords records memory)
    (producerMember : producer ∈ memory.alpha.producers)
    (fresh : some input ∉ records.map causalInput?) :
    memory.expectedBoundary ≠ some input := by
  intro boundary
  obtain ⟨seed, seedMember, seedZero⟩ :=
    alpha_zero_inventory_member_has_block_zero memory.alpha.producers valid
      producer producerMember
  have seedBoundary := matching seed seedMember seedZero
  have sourceExact : seed.sourceInput = input := by
    exact Option.some.inj (seedBoundary.symm.trans boundary)
  obtain ⟨actor, recordMember⟩ := literal seed seedMember
  apply fresh
  rw [List.mem_map]
  refine ⟨.machineFresh actor seed.sourceInput seed.digest, recordMember, ?_⟩
  simpa [causalInput?, sourceExact]

/-- Once a concrete block-zero seed and one of its descendants are live,
aligned fresh-root replay after the fold cannot reset them. -/
theorem fold_armed_live_producers_persist_over_aligned_records
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalWorkAnchorIndex : Nat) :
    ∀ (segment consumed : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        FoldArmedCompleteMemory)
      (seed producer : AlphaZeroProducer) (seedActor : QueryActor),
      foldExposureIndex < state.exposureIndex →
      IndexedRecordsAligned transitionFuel
        (foldArmedCompleteController transitionFuel foldExposureIndex
          finalWorkAnchorIndex) state segment →
      OnlyMachineFreshRecords segment →
      ((consumed ++ segment).map causalInput?).Nodup →
      AlphaBlockZeroMatchesExpected state.memory.2.1 →
      seed.block.val = 0 →
      (.machineFresh seedActor seed.sourceInput seed.digest :
        UnifiedExposureRecord) ∈ consumed →
      seed ∈ state.memory.2.1.alpha.producers →
      producer ∈ state.memory.2.1.alpha.producers →
      producer ∈
        (indexedStateAfterRecords transitionFuel
          (foldArmedCompleteController transitionFuel foldExposureIndex
            finalWorkAnchorIndex) segment state).memory.2.1.alpha.producers := by
  intro segment
  induction segment with
  | nil =>
      intro consumed state seed producer seedActor _afterFold _aligned
        _onlyMachine _nodup _matching _seedZero _seedRecord _seedMember
        producerMember
      simpa using producerMember
  | cons head tail ih =>
      intro consumed state seed producer seedActor afterFold aligned onlyMachine
        nodup matching seedZero seedRecord seedMember producerMember
      obtain ⟨actor, input, answer, headExact⟩ :=
        onlyMachine head (by simp)
      subst head
      let controller := foldArmedCompleteController
        (globalOracleCalls := globalOracleCalls) transitionFuel
          foldExposureIndex finalWorkAnchorIndex
      have headAligned := aligned [] (.machineFresh actor input answer) tail
        (by rfl)
      have inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor =
          some input := by
        simpa only [indexed_state_after_records_nil] using
          aligned_machine_record_has_exact_input transitionFuel state.cursor
            actor input answer headAligned
      have splitNodup := List.nodup_append.mp (by
        simpa [List.map_append] using nodup)
      have seedInputMember : some seed.sourceInput ∈
          consumed.map causalInput? := by
        rw [List.mem_map]
        exact ⟨.machineFresh seedActor seed.sourceInput seed.digest,
          seedRecord, by simp [causalInput?]⟩
      have inputMember : some input ∈
          ((.machineFresh actor input answer : UnifiedExposureRecord) ::
            tail).map causalInput? := by
        simp [causalInput?]
      have inputNe : seed.sourceInput ≠ input := by
        intro exactInput
        exact splitNodup.2.2 (some seed.sourceInput) seedInputMember
          (some input) inputMember (by simp [exactInput])
      have notBoundary : state.memory.2.1.expectedBoundary ≠ some input := by
        intro boundary
        have seedBoundary := matching seed seedMember seedZero
        exact inputNe (Option.some.inj (seedBoundary.symm.trans boundary))
      have growth :=
        fold_armed_complete_alpha_producers_prefix_of_nonboundary
          transitionFuel foldExposureIndex finalWorkAnchorIndex state input
            answer afterFold inputExact notBoundary
      let next := controller.afterAnswer transitionFuel state answer
      have tailAligned : IndexedRecordsAligned transitionFuel controller next
          tail := by
        apply indexed_records_aligned_segment transitionFuel controller state
          ((.machineFresh actor input answer : UnifiedExposureRecord) :: tail)
          [(.machineFresh actor input answer : UnifiedExposureRecord)] tail []
          aligned
        simp
      have tailOnly : OnlyMachineFreshRecords tail := by
        intro record member
        exact onlyMachine record (by simp [member])
      have nextMatching : AlphaBlockZeroMatchesExpected next.memory.2.1 := by
        exact fold_armed_complete_after_fold_preserves_block_zero_expected
          transitionFuel foldExposureIndex finalWorkAnchorIndex state answer
            afterFold matching
      have nextAfterFold : foldExposureIndex < next.exposureIndex := by
        simp [next, controller]
        omega
      have nextSeed : seed ∈ next.memory.2.1.alpha.producers :=
        growth.subset seedMember
      have nextProducer : producer ∈ next.memory.2.1.alpha.producers :=
        growth.subset producerMember
      have nextNodup :
          (((consumed ++
              [(.machineFresh actor input answer : UnifiedExposureRecord)]) ++
            tail).map causalInput?).Nodup := by
        simpa [List.append_assoc] using nodup
      rw [indexed_state_after_records_cons]
      exact ih
        (consumed ++ [(.machineFresh actor input answer :
          UnifiedExposureRecord)]) next seed producer seedActor nextAfterFold
          tailAligned tailOnly nextNodup nextMatching seedZero
          (List.mem_append_left _ seedRecord) nextSeed nextProducer

/-- Every alpha slot newly consumed by fold-armed replay was selected at one
literal earlier pre-answer state.  Unlike the retrospective alpha controller,
this statement permits the boundary to be cached before the fold or installed
after it; only the online pre-answer preference can consume a slot. -/
theorem fold_armed_alpha_used_slot_has_prior_record
    {globalOracleCalls : Nat}
    (transitionFuel : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        FoldArmedAlphaZeroMemory) (slot : Fin 4),
      slot ∉ state.memory.alpha.usedSlots →
      slot ∈
        (indexedStateAfterRecords transitionFuel
          (foldArmedAlphaZeroController transitionFuel)
          records state).memory.alpha.usedSlots →
      ∃ prior record later,
        records = prior ++ record :: later ∧
        (foldArmedAlphaZeroController transitionFuel).preferredSlot
          (indexedStateAfterRecords transitionFuel
            (foldArmedAlphaZeroController transitionFuel)
            prior state) = some slot := by
  intro records
  induction records with
  | nil =>
      intro state slot fresh used
      simp only [indexed_state_after_records_nil] at used
      exact (fresh used).elim
  | cons head tail ih =>
      intro state slot fresh used
      let controller := foldArmedAlphaZeroController
        (globalOracleCalls := globalOracleCalls) transitionFuel
      let next := controller.afterAnswer transitionFuel state head.answer
      have tailUsed : slot ∈
          (indexedStateAfterRecords transitionFuel controller tail
            next).memory.alpha.usedSlots := by
        simpa [controller, next, indexed_state_after_records_cons] using used
      cases preferred : controller.preferredSlot state with
      | none =>
          have preferred' : alphaZeroPreferredSlot transitionFuel
              (foldArmedAlphaIndexedState state) = none := by
            simpa [controller] using preferred
          have nextFresh : slot ∉ next.memory.alpha.usedSlots := by
            have nextUsed := fold_armed_alpha_after_memory_used_slots
              transitionFuel state head.answer
            rw [show next.memory.alpha.usedSlots =
                state.memory.alpha.usedSlots by
              change
                (foldArmedAlphaAfterMemory transitionFuel state
                  head.answer).alpha.usedSlots = state.memory.alpha.usedSlots
              simpa [preferred'] using nextUsed]
            exact fresh
          obtain ⟨prior, record, later, decomposition, selected⟩ :=
            ih next slot nextFresh tailUsed
          refine ⟨head :: prior, record, later, ?_, ?_⟩
          · simp [decomposition]
          · simpa [controller, next, indexed_state_after_records_cons] using
              selected
      | some current =>
          have preferred' : alphaZeroPreferredSlot transitionFuel
              (foldArmedAlphaIndexedState state) = some current := by
            simpa [controller] using preferred
          by_cases currentExact : current = slot
          · subst current
            exact ⟨[], head, tail, by simp, by
              simpa [controller, indexed_state_after_records_nil] using
                preferred⟩
          · have nextFresh : slot ∉ next.memory.alpha.usedSlots := by
              have nextUsed := fold_armed_alpha_after_memory_used_slots
                transitionFuel state head.answer
              rw [show next.memory.alpha.usedSlots =
                  insert current state.memory.alpha.usedSlots by
                change
                  (foldArmedAlphaAfterMemory transitionFuel state
                    head.answer).alpha.usedSlots =
                      insert current state.memory.alpha.usedSlots
                simpa [preferred'] using nextUsed]
              have slotNe : slot ≠ current := fun equal =>
                currentExact equal.symm
              simp [fresh, slotNe]
            obtain ⟨prior, record, later, decomposition, selected⟩ :=
              ih next slot nextFresh tailUsed
            refine ⟨head :: prior, record, later, ?_, ?_⟩
            · simp [decomposition]
            · simpa [controller, next, indexed_state_after_records_cons] using
                selected

/-- Exact alpha used-set update inside the complete fold/final/q16 controller.
The selected fold record only arms the boundary and preserves used slots;
every other record delegates to the online fold-armed alpha preference. -/
theorem fold_armed_complete_alpha_used_slots
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalWorkAnchorIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedCompleteMemory)
    (answer : Digest256) :
    ((foldArmedCompleteController transitionFuel foldExposureIndex
      finalWorkAnchorIndex).afterAnswer transitionFuel state
        answer).memory.2.1.alpha.usedSlots =
      if state.exposureIndex = foldExposureIndex then
        state.memory.2.1.alpha.usedSlots
      else
        match alphaZeroPreferredSlot transitionFuel
            (foldArmedAlphaIndexedState (foldArmedAlphaState state)) with
        | none => state.memory.2.1.alpha.usedSlots
        | some slot => insert slot state.memory.2.1.alpha.usedSlots := by
  simp only [IndexedUnifiedExposureController.afterAnswer,
    foldArmedCompleteController]
  split
  next atFold =>
    simpa [foldArmedAlphaState, foldArmedUnderlyingState,
      alphaIndexedState] using
        arm_fold_alpha_memory_used_slots transitionFuel
          (foldArmedAlphaState state) answer
  next notFold =>
    simp only [alphaFinalWorkQ16DagController,
      foldArmedAlphaZeroController]
    change
      (foldArmedAlphaAfterMemory transitionFuel
        (foldArmedAlphaState state) answer).alpha.usedSlots = _
    exact fold_armed_alpha_after_memory_used_slots transitionFuel
      (foldArmedAlphaState state) answer

/-- Complete-controller provenance for a newly consumed alpha slot.  The
outer fold record and all final-work/q16 activity are traversed explicitly;
the witness record is precisely the earlier online alpha preference. -/
theorem fold_armed_complete_alpha_used_slot_has_prior_record
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalWorkAnchorIndex : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        FoldArmedCompleteMemory) (slot : Fin 4),
      slot ∉ state.memory.2.1.alpha.usedSlots →
      slot ∈
        (indexedStateAfterRecords transitionFuel
          (foldArmedCompleteController transitionFuel foldExposureIndex
            finalWorkAnchorIndex) records state).memory.2.1.alpha.usedSlots →
      ∃ prior record later,
        records = prior ++ record :: later ∧
        (foldArmedCompleteController transitionFuel foldExposureIndex
          finalWorkAnchorIndex).preferredSlot
            (indexedStateAfterRecords transitionFuel
              (foldArmedCompleteController transitionFuel foldExposureIndex
                finalWorkAnchorIndex) prior state) =
          some (some (Sum.inl slot)) := by
  intro records
  induction records with
  | nil =>
      intro state slot fresh used
      simp only [indexed_state_after_records_nil] at used
      exact (fresh used).elim
  | cons head tail ih =>
      intro state slot fresh used
      let controller := foldArmedCompleteController
        (globalOracleCalls := globalOracleCalls) transitionFuel
          foldExposureIndex finalWorkAnchorIndex
      let next := controller.afterAnswer transitionFuel state head.answer
      have tailUsed : slot ∈
          (indexedStateAfterRecords transitionFuel controller tail
            next).memory.2.1.alpha.usedSlots := by
        simpa [controller, next, indexed_state_after_records_cons] using used
      by_cases atFold : state.exposureIndex = foldExposureIndex
      · have nextFresh : slot ∉ next.memory.2.1.alpha.usedSlots := by
          have update := fold_armed_complete_alpha_used_slots transitionFuel
            foldExposureIndex finalWorkAnchorIndex state head.answer
          rw [show next.memory.2.1.alpha.usedSlots =
              state.memory.2.1.alpha.usedSlots by
            simpa [next, controller, atFold] using update]
          exact fresh
        obtain ⟨prior, record, later, decomposition, selected⟩ :=
          ih next slot nextFresh tailUsed
        refine ⟨head :: prior, record, later, ?_, ?_⟩
        · simp [decomposition]
        · simpa [controller, next, indexed_state_after_records_cons] using
            selected
      · cases alphaPreferred : alphaZeroPreferredSlot transitionFuel
            (foldArmedAlphaIndexedState (foldArmedAlphaState state)) with
        | none =>
            have nextFresh : slot ∉ next.memory.2.1.alpha.usedSlots := by
              have update := fold_armed_complete_alpha_used_slots transitionFuel
                foldExposureIndex finalWorkAnchorIndex state head.answer
              rw [show next.memory.2.1.alpha.usedSlots =
                  state.memory.2.1.alpha.usedSlots by
                simpa [next, controller, atFold, alphaPreferred] using update]
              exact fresh
            obtain ⟨prior, record, later, decomposition, selected⟩ :=
              ih next slot nextFresh tailUsed
            refine ⟨head :: prior, record, later, ?_, ?_⟩
            · simp [decomposition]
            · simpa [controller, next, indexed_state_after_records_cons] using
                selected
        | some current =>
            by_cases currentExact : current = slot
            · subst current
              refine ⟨[], head, tail, by simp, ?_⟩
              simp only [indexed_state_after_records_nil]
              have underlying :
                  (alphaFinalWorkQ16DagController transitionFuel
                    finalWorkAnchorIndex
                    (foldArmedAlphaZeroController transitionFuel)).preferredSlot
                      (foldArmedUnderlyingState state) =
                    some (Sum.inl slot) := by
                apply alpha_final_work_q16_preferred_of_alpha
                simpa [foldArmedAlphaZeroController, foldArmedAlphaState]
                  using alphaPreferred
              simp [controller, foldArmedCompleteController, atFold,
                underlying]
            · have nextFresh : slot ∉ next.memory.2.1.alpha.usedSlots := by
                have update := fold_armed_complete_alpha_used_slots
                  transitionFuel foldExposureIndex finalWorkAnchorIndex state
                    head.answer
                rw [show next.memory.2.1.alpha.usedSlots =
                    insert current state.memory.2.1.alpha.usedSlots by
                  simpa [next, controller, atFold, alphaPreferred] using update]
                have slotNe : slot ≠ current := fun equal =>
                  currentExact equal.symm
                simp [fresh, slotNe]
              obtain ⟨prior, record, later, decomposition, selected⟩ :=
                ih next slot nextFresh tailUsed
              refine ⟨head :: prior, record, later, ?_, ?_⟩
              · simp [decomposition]
              · simpa [controller, next, indexed_state_after_records_cons]
                  using selected

/-- An emitted complete-router alpha label is exactly the underlying online
alpha preference.  In particular it cannot be the fold slot or a q16 slot. -/
theorem fold_armed_complete_alpha_preferred_projects
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalWorkAnchorIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedCompleteMemory)
    (slot : Fin 4)
    (preferred :
      (foldArmedCompleteController transitionFuel foldExposureIndex
        finalWorkAnchorIndex).preferredSlot state =
          some (some (Sum.inl slot))) :
    alphaZeroPreferredSlot transitionFuel
      (foldArmedAlphaIndexedState (foldArmedAlphaState state)) = some slot := by
  simp only [foldArmedCompleteController] at preferred
  split at preferred
  next atFold => simp at preferred
  next notFold =>
    have underlyingPreferred :
        (alphaFinalWorkQ16DagController transitionFuel finalWorkAnchorIndex
          (foldArmedAlphaZeroController transitionFuel)).preferredSlot
            (foldArmedUnderlyingState state) = some (Sum.inl slot) := by
      cases underlyingExact :
          (alphaFinalWorkQ16DagController transitionFuel finalWorkAnchorIndex
            (foldArmedAlphaZeroController transitionFuel)).preferredSlot
              (foldArmedUnderlyingState state) with
      | none => simp [underlyingExact] at preferred
      | some selected =>
          have selectedExact : selected = Sum.inl slot := by
            simpa [underlyingExact] using preferred
          simpa [selectedExact] using underlyingExact
    change
      (match
        (foldArmedAlphaZeroController transitionFuel).preferredSlot
          (alphaIndexedState (foldArmedUnderlyingState state)) with
       | some alphaSlot => some (Sum.inl alphaSlot)
       | none =>
          ((AspisK1.V7Tag73CausalDagFinalWorkQ16Controller.finalWorkQ16DagController
            globalOracleCalls transitionFuel finalWorkAnchorIndex).preferredSlot
              (finalWorkQ16IndexedState
                (foldArmedUnderlyingState state))).map Sum.inr) =
        some (Sum.inl slot) at underlyingPreferred
    cases alphaPreferred :
        (foldArmedAlphaZeroController transitionFuel).preferredSlot
          (alphaIndexedState (foldArmedUnderlyingState state)) with
    | none =>
        rw [alphaPreferred] at underlyingPreferred
        cases dagPreferred :
            (AspisK1.V7Tag73CausalDagFinalWorkQ16Controller.finalWorkQ16DagController
              globalOracleCalls transitionFuel finalWorkAnchorIndex).preferredSlot
                (finalWorkQ16IndexedState
                  (foldArmedUnderlyingState state)) <;> simp_all
    | some current =>
        rw [alphaPreferred] at underlyingPreferred
        have currentExact : current = slot := by
          exact Sum.inl.inj (Option.some.inj underlyingPreferred)
        have raw : alphaZeroPreferredSlot transitionFuel
            (foldArmedAlphaIndexedState (foldArmedAlphaState state)) =
              some current := by
          simpa [foldArmedAlphaZeroController, foldArmedAlphaState] using
            alphaPreferred
        simpa [currentExact] using raw

/-- Source-free inversion of a complete-router alpha label: the current
machine input is the output child of a live producer at exactly that block. -/
theorem fold_armed_complete_alpha_preferred_has_producer
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalWorkAnchorIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedCompleteMemory)
    (slot : Fin 4)
    (preferred :
      (foldArmedCompleteController transitionFuel foldExposureIndex
        finalWorkAnchorIndex).preferredSlot state =
          some (some (Sum.inl slot))) :
    ∃ selectedInput producer,
      unifiedInputBeforeAnswer? transitionFuel state.cursor =
          some selectedInput ∧
      producer ∈ state.memory.2.1.alpha.producers ∧
      selectedInput = gammaOutputInput producer.digest ∧
      producer.block = slot := by
  have projected := fold_armed_complete_alpha_preferred_projects
    transitionFuel foldExposureIndex finalWorkAnchorIndex state slot preferred
  obtain ⟨selectedInput, producer, inputExact, producerMember,
      outputExact, blockExact⟩ :=
    alpha_zero_preferred_slot_has_producer transitionFuel
      (foldArmedAlphaIndexedState (foldArmedAlphaState state)) slot projected
  change producer ∈ state.memory.2.1.alpha.producers at producerMember
  exact ⟨selectedInput, producer, by
    simpa [foldArmedAlphaIndexedState, foldArmedAlphaState,
      foldArmedUnderlyingState, alphaIndexedState] using inputExact,
    producerMember,
    by simpa [gammaOutputInput] using outputExact, blockExact⟩

#print axioms AlphaBlockZeroMatchesExpected
#print axioms alpha_zero_inventory_member_has_block_zero
#print axioms fold_armed_alpha_producers_prefix_of_nonboundary
#print axioms
  fold_armed_complete_alpha_producers_prefix_of_nonboundary
#print axioms
  fold_armed_alpha_after_memory_preserves_block_zero_expected
#print axioms arm_fold_alpha_memory_empty_block_zero_expected
#print axioms exact_fold_armed_after_fold_block_zero_expected
#print axioms
  fold_armed_complete_after_fold_preserves_block_zero_expected
#print axioms
  fold_armed_complete_records_preserve_block_zero_expected
#print axioms
  exact_fold_armed_post_fold_prefix_block_zero_expected
#print axioms live_alpha_producer_forces_nonboundary_of_fresh_input
#print axioms fold_armed_live_producers_persist_over_aligned_records
#print axioms fold_armed_alpha_used_slot_has_prior_record
#print axioms fold_armed_complete_alpha_used_slots
#print axioms fold_armed_complete_alpha_used_slot_has_prior_record
#print axioms fold_armed_complete_alpha_preferred_projects
#print axioms fold_armed_complete_alpha_preferred_has_producer

end

end AspisK1.V7Tag73FoldArmedAlphaProducerPersistence
