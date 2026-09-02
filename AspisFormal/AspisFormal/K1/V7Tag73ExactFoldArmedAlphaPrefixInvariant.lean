import AspisFormal.K1.V7Tag73FoldArmedAlphaCoreInvariant
import AspisFormal.K1.V7Tag73ExactFoldArmedAlphaSourceAlignment

/-!
# Exact-root producer provenance for the fold-armed alpha controller

This file begins the accepted-root invariant needed to separate live alpha
and q16 producer inventories.  Before the selected fold exposure the dynamic
alpha inventory is empty.  Immediately afterwards it is either the unique
cached literal boundary producer or remains empty while the same boundary is
armed for its later first creation.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactFoldArmedAlphaPrefixInvariant

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73AlphaZeroBoundaryInvariant
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AlphaZeroProducerInvariant
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactFinalWorkPairControllerCompletion
open AspisK1.V7Tag73ExactFoldArmedAlphaSourceAlignment
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FoldArmedAlphaCoreInvariant
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Until the selected fold-work exposure, no dynamic boundary has been armed
and an empty alpha producer inventory remains empty. -/
theorem fold_armed_alpha_empty_before_selected_fold
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalWorkAnchorIndex : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        FoldArmedCompleteMemory),
      state.exposureIndex + records.length ≤ foldExposureIndex →
      state.memory.2.1.expectedBoundary = none →
      state.memory.2.1.alpha.producers = [] →
      let reached := indexedStateAfterRecords transitionFuel
        (foldArmedCompleteController transitionFuel foldExposureIndex
          finalWorkAnchorIndex) records state
      reached.memory.2.1.expectedBoundary = none ∧
        reached.memory.2.1.alpha.producers = [] := by
  intro records
  induction records with
  | nil =>
      intro state _endExact expectedEmpty producersEmpty
      exact ⟨expectedEmpty, producersEmpty⟩
  | cons head tail ih =>
      intro state endExact expectedEmpty producersEmpty
      let controller := foldArmedCompleteController
        (globalOracleCalls := globalOracleCalls) transitionFuel
          foldExposureIndex finalWorkAnchorIndex
      let next := controller.afterAnswer transitionFuel state head.answer
      have notFold : state.exposureIndex ≠ foldExposureIndex := by
        intro equal
        rw [equal] at endExact
        simp only [List.length_cons] at endExact
        omega
      have nextExpected : next.memory.2.1.expectedBoundary = none := by
        simp only [next, controller, IndexedUnifiedExposureController.afterAnswer,
          foldArmedCompleteController, notFold, if_false,
          alpha_final_work_q16_after_memory]
        change (foldArmedAlphaAfterMemory transitionFuel
          (foldArmedAlphaState state) head.answer).expectedBoundary = none
        unfold foldArmedAlphaAfterMemory
        split <;> exact expectedEmpty
      have nextProducers : next.memory.2.1.alpha.producers = [] := by
        simp only [next, controller, IndexedUnifiedExposureController.afterAnswer,
          foldArmedCompleteController, notFold, if_false,
          alpha_final_work_q16_after_memory]
        change (foldArmedAlphaAfterMemory transitionFuel
          (foldArmedAlphaState state) head.answer).alpha.producers = []
        unfold foldArmedAlphaAfterMemory
        cases inputExact : unifiedInputBeforeAnswer? transitionFuel
            (foldArmedAlphaState state).cursor with
        | none => exact producersEmpty
        | some input =>
            have notBoundary :
                (foldArmedAlphaState state).memory.expectedBoundary ≠
                  some input := by
              rw [show (foldArmedAlphaState state).memory.expectedBoundary =
                none by exact expectedEmpty]
              simp
            change (if (foldArmedAlphaState state).memory.expectedBoundary =
                some input then
              [{ digest := head.answer, block := 0, sourceInput := input }]
            else updateAlphaZeroProducers
              (foldArmedAlphaState state).memory.alpha.producers input
                head.answer) = []
            rw [if_neg notBoundary]
            rw [show (foldArmedAlphaState state).memory.alpha.producers = [] by
              exact producersEmpty]
            simp [updateAlphaZeroProducers, alphaZeroAdvancedSlot?]
      have nextEnd : next.exposureIndex + tail.length ≤ foldExposureIndex := by
        simp only [next, controller, indexed_after_answer_exposure_index,
          List.length_cons] at endExact ⊢
        omega
      rw [indexed_state_after_records_cons]
      exact ih next nextEnd nextExpected nextProducers

/-- Exact empty pre-fold state for the accepted fold trial. -/
theorem exact_fold_armed_reached_fold_alpha_empty
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
    let reached := indexedStateAfterRecords transitionFuel
      (foldArmedCompleteController transitionFuel fold.trial.val finalTrial.val)
      fold.prior
      (foldArmedInitialState
        (exactPlainRomCursor configuration sample.1).erase)
    reached.memory.2.1.expectedBoundary = none ∧
      reached.memory.2.1.alpha.producers = [] := by
  apply fold_armed_alpha_empty_before_selected_fold transitionFuel
    fold.trial.val finalTrial.val fold.prior
      (foldArmedInitialState
        (exactPlainRomCursor configuration sample.1).erase)
  · have exact : fold.prior.length = fold.trial.val := fold.trialExact.symm
    simpa [foldArmedInitialState, exact]
  · rfl
  · rfl

/-- Processing the exact selected fold-work record establishes the full core
producer invariant, independently of whether the boundary query was created
before or after that record. -/
theorem exact_fold_armed_after_fold_alpha_core
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
    FoldArmedAlphaCoreInvariant afterFold.memory.2.1 := by
  let controller := foldArmedCompleteController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel fold.trial.val finalTrial.val
  let reached := indexedStateAfterRecords transitionFuel controller fold.prior
    (foldArmedInitialState
      (exactPlainRomCursor configuration sample.1).erase)
  have empty := exact_fold_armed_reached_fold_alpha_empty input fold finalTrial
  change reached.memory.2.1.expectedBoundary = none ∧
    reached.memory.2.1.alpha.producers = [] at empty
  have reachedCore : FoldArmedAlphaCoreInvariant reached.memory.2.1 := by
    refine
      { producer := ?_
        blockZeroBoundary := ?_
        expectedBoundaryLength := ?_ }
    · constructor
      · simpa [reached, empty.2, AlphaZeroProducerInventoryValid]
      · simpa [reached, empty.2]
      · simpa [reached, empty.2]
    · simpa [reached, empty.2, AlphaZeroBlockZeroBoundaryValid]
    · intro target impossible
      rw [empty.1] at impossible
      simp at impossible
  have atFold : reached.exposureIndex = fold.trial.val := by
    have count := indexed_state_after_records_exposure_index transitionFuel
      controller fold.prior
      (foldArmedInitialState
        (exactPlainRomCursor configuration sample.1).erase)
    simpa [reached, controller, foldArmedInitialState, fold.trialExact] using
      count
  have armedCore := arm_fold_alpha_memory_preserves_core transitionFuel
    (foldArmedAlphaState reached) fold.answer reachedCore
  have alphaMemoryExact :
      (controller.afterAnswer transitionFuel reached fold.answer).memory.2.1 =
        armFoldAlphaMemory transitionFuel (foldArmedAlphaState reached)
          fold.answer := by
    simp [controller, IndexedUnifiedExposureController.afterAnswer,
      foldArmedCompleteController, atFold]
  dsimp only
  rw [alphaMemoryExact]
  exact armedCore

def AlphaProducersHaveLiteralRecords
    (records : List UnifiedExposureRecord)
    (memory : FoldArmedAlphaZeroMemory) : Prop :=
  ∀ producer ∈ memory.alpha.producers,
    ∃ actor,
      (.machineFresh actor producer.sourceInput producer.digest :
        UnifiedExposureRecord) ∈ records

structure FoldArmedAlphaPrefixInvariant
    (records : List UnifiedExposureRecord)
    (memory : FoldArmedAlphaZeroMemory) : Prop where
  core : FoldArmedAlphaCoreInvariant memory
  sourcesLiteral : AlphaProducersHaveLiteralRecords records memory

/-- A machine input fresh relative to the consumed prefix is fresh relative
to every live alpha producer source recorded by that prefix. -/
theorem source_fresh_of_literal_records
    (records : List UnifiedExposureRecord)
    (memory : FoldArmedAlphaZeroMemory)
    (input : ShaInput)
    (literal : AlphaProducersHaveLiteralRecords records memory)
    (fresh : some input ∉ records.map causalInput?) :
    input ∉ memory.alpha.producers.map AlphaZeroProducer.sourceInput := by
  intro member
  obtain ⟨producer, producerMember, sourceExact⟩ := List.mem_map.mp member
  obtain ⟨actor, recordMember⟩ := literal producer producerMember
  apply fresh
  rw [List.mem_map]
  refine ⟨.machineFresh actor producer.sourceInput producer.digest,
    recordMember, ?_⟩
  simpa [causalInput?, sourceExact]

/-- One ordinary machine-fresh alpha step extends literal provenance by at
most the current record. -/
theorem fold_armed_alpha_after_memory_preserves_literal_sources
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (records : List UnifiedExposureRecord)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedAlphaZeroMemory)
    (actor : QueryActor) (input : ShaInput) (answer : Digest256)
    (inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor =
      some input)
    (literal : AlphaProducersHaveLiteralRecords records state.memory) :
    AlphaProducersHaveLiteralRecords
      (records ++ [(.machineFresh actor input answer : UnifiedExposureRecord)])
      (foldArmedAlphaAfterMemory transitionFuel state answer) := by
  intro producer member
  by_cases boundary : state.memory.expectedBoundary = some input
  · have installed := fold_armed_alpha_exact_boundary_installs_block_zero
      transitionFuel state input answer inputExact boundary
    rw [installed] at member
    simp only [List.mem_singleton] at member
    subst producer
    exact ⟨actor, by simp⟩
  · have updated := fold_armed_alpha_nonboundary_uses_advance_update
      transitionFuel state input answer inputExact boundary
    rw [updated] at member
    rcases update_alpha_zero_producers_eq_or_append
        state.memory.alpha.producers input answer with unchanged |
        ⟨block, appended⟩
    · rw [unchanged] at member
      obtain ⟨sourceActor, sourceMember⟩ := literal producer member
      exact ⟨sourceActor, List.mem_append_left _ sourceMember⟩
    · rw [appended, List.mem_append] at member
      rcases member with old | added
      · obtain ⟨sourceActor, sourceMember⟩ := literal producer old
        exact ⟨sourceActor, List.mem_append_left _ sourceMember⟩
      · simp only [List.mem_singleton] at added
        subst producer
        exact ⟨actor, by simp⟩

theorem fold_armed_alpha_after_memory_preserves_prefix_invariant
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (records : List UnifiedExposureRecord)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedAlphaZeroMemory)
    (actor : QueryActor) (input : ShaInput) (answer : Digest256)
    (inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor =
      some input)
    (fresh : some input ∉ records.map causalInput?)
    (invariant : FoldArmedAlphaPrefixInvariant records state.memory) :
    FoldArmedAlphaPrefixInvariant
      (records ++ [(.machineFresh actor input answer : UnifiedExposureRecord)])
      (foldArmedAlphaAfterMemory transitionFuel state answer) := by
  refine
    { core := fold_armed_alpha_after_memory_preserves_core transitionFuel state
        answer invariant.core ?_
      sourcesLiteral :=
        fold_armed_alpha_after_memory_preserves_literal_sources transitionFuel
          records state actor input answer inputExact invariant.sourcesLiteral }
  intro selected selectedExact
  have selectedEq : selected = input := Option.some.inj
    (selectedExact.symm.trans inputExact)
  subst selected
  exact source_fresh_of_literal_records records state.memory input
    invariant.sourcesLiteral fresh

/-- Replay a machine-only post-fold segment while preserving both the alpha
inventory mathematics and literal source provenance. -/
theorem fold_armed_post_fold_segment_preserves_prefix_invariant
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalWorkAnchorIndex : Nat) :
    ∀ (segment consumed : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        FoldArmedCompleteMemory),
      foldExposureIndex < state.exposureIndex →
      IndexedRecordsAligned transitionFuel
        (foldArmedCompleteController transitionFuel foldExposureIndex
          finalWorkAnchorIndex) state segment →
      OnlyMachineFreshRecords segment →
      ((consumed ++ segment).map causalInput?).Nodup →
      FoldArmedAlphaPrefixInvariant consumed state.memory.2.1 →
      let reached := indexedStateAfterRecords transitionFuel
        (foldArmedCompleteController transitionFuel foldExposureIndex
          finalWorkAnchorIndex) segment state
      FoldArmedAlphaPrefixInvariant (consumed ++ segment)
        reached.memory.2.1 := by
  intro segment
  induction segment with
  | nil =>
      intro consumed state _afterFold _aligned _onlyMachine _nodup invariant
      simpa using invariant
  | cons head tail ih =>
      intro consumed state afterFold aligned onlyMachine nodup invariant
      obtain ⟨actor, input, answer, headExact⟩ :=
        onlyMachine head (by simp)
      subst head
      let controller := foldArmedCompleteController
        (globalOracleCalls := globalOracleCalls) transitionFuel
          foldExposureIndex finalWorkAnchorIndex
      let next := controller.afterAnswer transitionFuel state answer
      have selectedAligned := aligned []
        (.machineFresh actor input answer) tail (by rfl)
      have inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor =
          some input :=
        aligned_machine_record_has_exact_input transitionFuel state.cursor actor
          input answer selectedAligned
      have splitNodup := List.nodup_append.mp (by
        simpa [List.map_append] using nodup)
      have fresh : some input ∉ consumed.map causalInput? := by
        intro member
        exact splitNodup.2.2 (some input) member (some input) (by
          simp [causalInput?]) rfl
      have alphaStep :=
        fold_armed_alpha_after_memory_preserves_prefix_invariant transitionFuel
          consumed (foldArmedAlphaState state) actor input answer (by
            simpa [foldArmedAlphaState, foldArmedUnderlyingState,
              alphaIndexedState] using inputExact) fresh invariant
      have notFold : state.exposureIndex ≠ foldExposureIndex := by omega
      have nextInvariant : FoldArmedAlphaPrefixInvariant
          (consumed ++ [(.machineFresh actor input answer :
            UnifiedExposureRecord)]) next.memory.2.1 := by
        simpa [next, controller, IndexedUnifiedExposureController.afterAnswer,
          foldArmedCompleteController, notFold,
          alpha_final_work_q16_after_memory, foldArmedAlphaZeroController,
          foldArmedAlphaState,
          foldArmedUnderlyingState, alphaIndexedState] using alphaStep
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
      have tailNodup :
          (((consumed ++ [(.machineFresh actor input answer :
              UnifiedExposureRecord)]) ++ tail).map causalInput?).Nodup := by
        simpa [List.append_assoc] using nodup
      have nextAfter : foldExposureIndex < next.exposureIndex := by
        simp only [next, controller, indexed_after_answer_exposure_index]
        omega
      rw [indexed_state_after_records_cons]
      change FoldArmedAlphaPrefixInvariant
        (consumed ++
          ((.machineFresh actor input answer : UnifiedExposureRecord) :: tail))
        (indexedStateAfterRecords transitionFuel controller tail next).memory.2.1
      simpa [List.append_assoc] using ih
        (consumed ++ [(.machineFresh actor input answer :
          UnifiedExposureRecord)]) next nextAfter tailAligned tailOnly
            tailNodup nextInvariant

/-- Immediately after the selected fold record, every installed alpha
producer has a literal source record in the consumed root prefix.  This is the
key adversary-first provenance fact: a cached boundary seed points back to its
earlier machine creation rather than being treated as fresh at fold time. -/
theorem exact_fold_armed_after_fold_alpha_sources_literal
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
    AlphaProducersHaveLiteralRecords
      (fold.prior ++ [(.machineFresh fold.actor
        (bytes fold.digest ++ [domGrind] ++
          bytes (exactOperationalTape input).messages.foldGrinding.selected)
        fold.answer : UnifiedExposureRecord)]) afterFold.memory.2.1 := by
  let controller := foldArmedCompleteController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel fold.trial.val finalTrial.val
  let initial := foldArmedInitialState
    (exactPlainRomCursor configuration sample.1).erase
  let reached := indexedStateAfterRecords transitionFuel controller fold.prior
    initial
  let target : ShaInput :=
    bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
      bytes (exactOperationalTape input).messages.foldGrinding.selected
  have empty := exact_fold_armed_reached_fold_alpha_empty input fold finalTrial
  change reached.memory.2.1.expectedBoundary = none ∧
    reached.memory.2.1.alpha.producers = [] at empty
  have rootAligned := exact_root_records_aligned_for_fold_armed_controller input
    fold.trial finalTrial
  have selectedAligned :
      unifiedRecordAtAnswer transitionFuel reached.cursor fold.answer =
        (.machineFresh fold.actor
          (bytes fold.digest ++ [domGrind] ++
            bytes (exactOperationalTape input).messages.foldGrinding.selected)
          fold.answer : UnifiedExposureRecord) := by
    exact rootAligned fold.prior _ fold.later fold.rootDecomposition
  have inputExact : unifiedInputBeforeAnswer? transitionFuel reached.cursor =
      some (bytes fold.digest ++ [domGrind] ++
        bytes (exactOperationalTape input).messages.foldGrinding.selected) :=
    aligned_machine_record_has_exact_input transitionFuel reached.cursor
      fold.actor _ fold.answer selectedAligned
  have atFold : reached.exposureIndex = fold.trial.val := by
    have count := indexed_state_after_records_exposure_index transitionFuel
      controller fold.prior initial
    simpa [reached, initial, foldArmedInitialState, fold.trialExact] using count
  have projectedInput : unifiedInputBeforeAnswer? transitionFuel
      (foldArmedAlphaState reached).cursor =
        some (bytes fold.digest ++ [domGrind] ++
          bytes (exactOperationalTape input).messages.foldGrinding.selected) := by
    simpa [foldArmedAlphaState, foldArmedUnderlyingState, alphaIndexedState]
      using inputExact
  have armedExact : armFoldAlphaBoundary transitionFuel
      (foldArmedAlphaState reached) = some target := by
    simp only [armFoldAlphaBoundary, projectedInput, Option.bind_some]
    simpa [target] using literal_fold_work_arms_exact_alpha_boundary fold.digest
      (exactOperationalTape input).messages.foldGrinding.selected
  have alphaMemoryExact :
      (controller.afterAnswer transitionFuel reached fold.answer).memory.2.1 =
        armFoldAlphaMemory transitionFuel (foldArmedAlphaState reached)
          fold.answer := by
    simp [controller, IndexedUnifiedExposureController.afterAnswer,
      foldArmedCompleteController, atFold]
  obtain ⟨boundaryActor, before | after⟩ :=
    exact_accepted_fold_boundary_record_before_or_after input fold
  · have cached := exact_fold_boundary_before_is_cached input fold finalTrial
      boundaryActor before
    have cached' : seenMachineAnswer? (foldArmedAlphaState reached).memory
        target = some fold.boundaryAnswer := by
      change seenMachineAnswer? reached.memory.2.1 target =
        some fold.boundaryAnswer
      simpa [reached, controller, initial, target] using cached
    dsimp only
    rw [alphaMemoryExact]
    intro producer member
    have closureMember : producer ∈ cachedAlphaProducerClosure
        (foldArmedAlphaState reached).memory.seenMachine target
          fold.boundaryAnswer := by
      simpa [armFoldAlphaMemory, armedExact, cached'] using member
    rcases cached_alpha_producer_closure_member_seed_or_seen
        (foldArmedAlphaState reached).memory.seenMachine target
          fold.boundaryAnswer producer
          closureMember with seed | seen
    · subst producer
      exact ⟨boundaryActor, by
        rw [List.mem_append]
        exact Or.inl (by simpa [target] using before)⟩
    · have seen' : (producer.sourceInput, producer.digest) ∈
          reached.memory.2.1.seenMachine := by
        simpa [foldArmedAlphaState, foldArmedUnderlyingState,
          alphaIndexedState] using seen
      have seenExact := exact_fold_reached_seen_machine_exact input fold
          finalTrial
      change reached.memory.2.1.seenMachine =
          fold.prior.filterMap machineFreshPair? at seenExact
      rw [seenExact] at seen'
      obtain ⟨record, recordMember, pairExact⟩ := List.mem_filterMap.mp seen'
      cases record with
      | machineFresh actor recordInput recordAnswer =>
          have pairEq : (recordInput, recordAnswer) =
              (producer.sourceInput, producer.digest) := by
            simpa [machineFreshPair?, machineFreshInput?,
              UnifiedExposureRecord.answer] using pairExact
          have inputEq : recordInput = producer.sourceInput :=
            congrArg Prod.fst pairEq
          have answerEq : recordAnswer = producer.digest :=
            congrArg Prod.snd pairEq
          exact ⟨actor, List.mem_append_left _ (by
            simpa [inputEq, answerEq] using recordMember)⟩
      | padding value => simp [machineFreshPair?, machineFreshInput?] at pairExact
      | forkOutput actor input output advance answer =>
          simp [machineFreshPair?, machineFreshInput?] at pairExact
      | forkAdvance answer =>
          simp [machineFreshPair?, machineFreshInput?] at pairExact
  · have uncached := exact_fold_boundary_after_is_uncached input fold finalTrial
      boundaryActor after
    have uncached' : seenMachineAnswer? (foldArmedAlphaState reached).memory
        target = none := by
      change seenMachineAnswer? reached.memory.2.1 target = none
      simpa [reached, controller, initial, target] using uncached
    have retained := arm_fold_alpha_memory_uncached_retains_inventory
      transitionFuel (foldArmedAlphaState reached) target fold.answer armedExact
        uncached'
    dsimp only
    rw [alphaMemoryExact]
    intro producer member
    have impossible : producer ∈ reached.memory.2.1.alpha.producers := by
      rw [retained] at member
      exact member
    rw [empty.2] at impossible
    simp at impossible

/-- Every exact prefix of the accepted root after the selected fold record
inherits the core alpha inventory invariant and literal source provenance. -/
theorem exact_fold_armed_post_fold_prefix_invariant
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
    (segment rest : List UnifiedExposureRecord)
    (laterExact : fold.later = segment ++ rest) :
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
    let afterFold := controller.afterAnswer transitionFuel reachedFold
      fold.answer
    let consumed := fold.prior ++ [selected]
    let reached := indexedStateAfterRecords transitionFuel controller segment
      afterFold
    FoldArmedAlphaPrefixInvariant (consumed ++ segment)
      reached.memory.2.1 := by
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
  let consumed := fold.prior ++ [selected]
  have initialInvariant : FoldArmedAlphaPrefixInvariant consumed
      afterFold.memory.2.1 :=
    { core := by
        simpa [controller, reachedFold, afterFold] using
          exact_fold_armed_after_fold_alpha_core input fold finalTrial
      sourcesLiteral := by
        simpa [controller, reachedFold, afterFold, consumed, selected] using
          exact_fold_armed_after_fold_alpha_sources_literal input fold finalTrial }
  have afterIndex : fold.trial.val < afterFold.exposureIndex := by
    have count := indexed_state_after_records_exposure_index transitionFuel
      controller fold.prior initial
    have reachedIndex : reachedFold.exposureIndex = fold.trial.val := by
      simpa [reachedFold, initial, foldArmedInitialState, fold.trialExact] using
        count
    simp only [afterFold, indexed_after_answer_exposure_index, reachedIndex]
    omega
  have rootAligned := exact_root_records_aligned_for_fold_armed_controller input
    fold.trial finalTrial
  have consumedState : indexedStateAfterRecords transitionFuel controller
      consumed initial = afterFold := by
    simp [consumed, selected, afterFold, reachedFold,
      indexed_state_after_records_append, UnifiedExposureRecord.answer]
  have segmentAligned : IndexedRecordsAligned transitionFuel controller
      afterFold segment := by
    have aligned := indexed_records_aligned_segment transitionFuel controller
      initial (exactFixedRootRecords input.package.root) consumed segment rest
        rootAligned (by
          rw [fold.rootDecomposition, laterExact]
          simp [consumed, selected, List.append_assoc])
    simpa [consumedState] using aligned
  have segmentOnly : OnlyMachineFreshRecords segment := by
    intro record member
    apply exact_root_records_only_machine_fresh input record
    rw [fold.rootDecomposition, laterExact]
    exact List.mem_append_right fold.prior
      (List.mem_cons_of_mem selected (List.mem_append_left rest member))
  have prefixNodup : ((consumed ++ segment).map causalInput?).Nodup := by
    have rootNodup := exact_root_record_causal_inputs_nodup input
    rw [fold.rootDecomposition, laterExact] at rootNodup
    have normalized :
        ((consumed ++ segment).map causalInput? ++
          rest.map causalInput?).Nodup := by
      simpa [consumed, selected, List.map_append, List.append_assoc] using
        rootNodup
    exact (List.nodup_append.mp normalized).1
  dsimp only
  exact fold_armed_post_fold_segment_preserves_prefix_invariant transitionFuel
    fold.trial.val finalTrial.val segment consumed afterFold afterIndex
      segmentAligned segmentOnly prefixNodup initialInvariant

#print axioms fold_armed_alpha_empty_before_selected_fold
#print axioms exact_fold_armed_reached_fold_alpha_empty
#print axioms exact_fold_armed_after_fold_alpha_core
#print axioms exact_fold_armed_after_fold_alpha_sources_literal
#print axioms exact_fold_armed_post_fold_prefix_invariant

end

end AspisK1.V7Tag73ExactFoldArmedAlphaPrefixInvariant
