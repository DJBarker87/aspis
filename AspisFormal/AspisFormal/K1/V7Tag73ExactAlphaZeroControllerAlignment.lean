import AspisFormal.K1.V7Tag73AlphaZeroCausalController
import AspisFormal.K1.V7Tag73ExactAlphaZeroRootOrder
import AspisFormal.K1.V7Tag73ExactDagCandidateLabeledRootRouting
import AspisFormal.K1.V7Tag73ExactRootRecordOrderLift

/-!
# Exact accepted-source alignment of the alpha-zero controller

The pre-answer alpha controller is useful only if its boundary index is the
literal fold-nonce absorption in the accepted compiler execution.  This file
locates that exact root record, replays its strict prefix through the same
unified scheduler cursor used by the causal router, and proves that consuming
the boundary answer installs block zero's producer.

No raw-input role classifier is used.  An adversary may have queried the
fold-nonce input first; the chosen root record retains whichever actor made
the unique fresh exposure.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactAlphaZeroControllerAlignment

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ExactAlphaZeroPrefixCoordinates
open AspisK1.V7Tag73ExactAlphaZeroRootOrder
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactFinalWorkPairControllerCompletion
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactProbabilityCoverageAudit
open AspisK1.V7Tag73ExactRootLookupCausalOrder
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactRootRecordOrderLift
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73FullCursorClientLineageLift
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Two decompositions selecting the same projected key in a projected-nodup
list have the same strict prefix.  This small local copy keeps the alpha
controller independent of the much larger q16 recursive-routing module. -/
theorem alpha_mapped_nodup_selected_prefix_eq
    {A B : Type} [BEq B] [LawfulBEq B]
    (f : A → B) (values firstPrefix firstSuffix secondPrefix secondSuffix :
      List A)
    (first second : A)
    (nodup : (values.map f).Nodup)
    (firstExact : values = firstPrefix ++ first :: firstSuffix)
    (secondExact : values = secondPrefix ++ second :: secondSuffix)
    (selectedExact : f first = f second) :
    firstPrefix = secondPrefix := by
  have firstFresh : f first ∉ firstPrefix.map f := by
    rw [firstExact, List.map_append, List.map_cons] at nodup
    have separated := (List.nodup_append.mp nodup).2.2
    intro member
    exact separated (f first) member (f first) (by simp) rfl
  have secondFresh : f second ∉ secondPrefix.map f := by
    rw [secondExact, List.map_append, List.map_cons] at nodup
    have separated := (List.nodup_append.mp nodup).2.2
    intro member
    exact separated (f second) member (f second) (by simp) rfl
  have firstIndex : (values.map f).idxOf (f first) = firstPrefix.length := by
    rw [firstExact, List.map_append, List.map_cons,
      List.idxOf_append_of_notMem firstFresh, List.idxOf_cons_self,
      List.length_map]
    omega
  have secondIndex : (values.map f).idxOf (f second) = secondPrefix.length := by
    rw [secondExact, List.map_append, List.map_cons,
      List.idxOf_append_of_notMem secondFresh, List.idxOf_cons_self,
      List.length_map]
    omega
  have lengthsExact : firstPrefix.length = secondPrefix.length := by
    rw [selectedExact] at firstIndex
    omega
  have firstPrefixOf : firstPrefix <+: values := by
    exact ⟨first :: firstSuffix, firstExact.symm⟩
  have secondPrefixOf : secondPrefix <+: values := by
    exact ⟨second :: secondSuffix, secondExact.symm⟩
  rw [List.prefix_iff_eq_take] at firstPrefixOf secondPrefixOf
  rw [firstPrefixOf, secondPrefixOf, lengthsExact]

/-- Canonical initial state of the accepted run's alpha-zero controller. -/
def exactAlphaZeroInitialState
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (_input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    IndexedUnifiedExposureState (globalFull256OracleCallCap parameters)
      AlphaZeroControllerMemory :=
  { exposureIndex := 0
    cursor := (exactPlainRomCursor configuration sample.1).erase
    memory := inactiveAlphaZeroMemory }

/-- A literal exact-root coordinate has installed its alpha producer after
any actor-tagged decomposition selecting that same source coordinate. -/
def ExactAlphaZeroProducerInstalled
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
    (boundaryIndex : Nat)
    (producer : AlphaZeroProducer) : Prop :=
  ∀ prior later actor,
    exactFixedRootRecords input.package.root =
      prior ++
        (.machineFresh actor producer.sourceInput producer.digest :
          UnifiedExposureRecord) :: later →
    boundaryIndex ≤ prior.length ∧
      producer ∈
        (indexedStateAfterRecords transitionFuel
          (alphaZeroCausalController transitionFuel boundaryIndex)
          (prior ++
            [(.machineFresh actor producer.sourceInput producer.digest :
              UnifiedExposureRecord)])
          (exactAlphaZeroInitialState input)).memory.producers

/-- Every producer present after an aligned machine-fresh replay was either
present initially or was created by one literal record in that replay. -/
theorem alpha_zero_indexed_state_producer_has_literal_record
    {globalOracleCalls : Nat}
    (transitionFuel boundaryIndex : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        AlphaZeroControllerMemory),
      IndexedRecordsAligned transitionFuel
          (alphaZeroCausalController transitionFuel boundaryIndex) state
          records →
      OnlyMachineFreshRecords records →
      ∀ producer,
        producer ∈
          (indexedStateAfterRecords transitionFuel
            (alphaZeroCausalController transitionFuel boundaryIndex)
            records state).memory.producers →
        producer ∈ state.memory.producers ∨
          ∃ actor input answer,
            (.machineFresh actor input answer : UnifiedExposureRecord) ∈
                records ∧
              producer.sourceInput = input ∧ producer.digest = answer := by
  intro records
  induction records with
  | nil =>
      intro state _aligned _onlyMachine producer member
      exact Or.inl (by
        simpa only [indexed_state_after_records_nil] using member)
  | cons head tail ih =>
      intro state aligned onlyMachine producer member
      obtain ⟨actor, input, answer, headExact⟩ :=
        onlyMachine head (by simp)
      subst head
      let controller := alphaZeroCausalController
        (globalOracleCalls := globalOracleCalls) transitionFuel boundaryIndex
      let next := controller.afterAnswer transitionFuel state answer
      have headAligned := aligned [] (.machineFresh actor input answer) tail
        (by rfl)
      have inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor =
          some input := by
        simpa only [indexed_state_after_records_nil] using
          aligned_machine_record_has_exact_input transitionFuel state.cursor
            actor input answer headAligned
      have tailAligned : IndexedRecordsAligned transitionFuel controller next
          tail := by
        apply indexed_records_aligned_segment transitionFuel controller state
          ((.machineFresh actor input answer) :: tail)
          [(.machineFresh actor input answer)] tail [] aligned
        simp
      have tailOnly : OnlyMachineFreshRecords tail := by
        intro record recordMember
        exact onlyMachine record (by simp [recordMember])
      have tailMember : producer ∈
          (indexedStateAfterRecords transitionFuel controller tail
            next).memory.producers := by
        simpa [controller, next, indexed_state_after_records_cons,
          UnifiedExposureRecord.answer] using member
      rcases ih next tailAligned tailOnly producer tailMember with
        nextMember | ⟨recordActor, recordInput, recordAnswer, recordMember,
          sourceExact, digestExact⟩
      · change producer ∈
          (alphaZeroAfterMemory transitionFuel boundaryIndex state
            answer).producers at nextMember
        rcases alpha_zero_after_memory_member_old_or_current transitionFuel
            boundaryIndex state input answer producer inputExact nextMember with
          old | ⟨sourceExact, digestExact⟩
        · exact Or.inl old
        · exact Or.inr ⟨actor, input, answer, by simp,
            sourceExact, digestExact⟩
      · exact Or.inr ⟨recordActor, recordInput, recordAnswer,
          by simp [recordMember], sourceExact, digestExact⟩

/-- Along an aligned machine-fresh replay, globally fresh root answers imply
that the alpha producer inventory never contains duplicate digests. -/
theorem alpha_zero_aligned_replay_producer_digests_nodup
    {globalOracleCalls : Nat}
    (transitionFuel boundaryIndex : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        AlphaZeroControllerMemory)
      (consumedAnswers : List Digest256),
      IndexedRecordsAligned transitionFuel
          (alphaZeroCausalController transitionFuel boundaryIndex) state
          records →
      OnlyMachineFreshRecords records →
      (consumedAnswers ++ records.map UnifiedExposureRecord.answer).Nodup →
      (state.memory.producers.map AlphaZeroProducer.digest).Nodup →
      (∀ producer ∈ state.memory.producers,
        producer.digest ∈ consumedAnswers) →
      ((indexedStateAfterRecords transitionFuel
        (alphaZeroCausalController transitionFuel boundaryIndex)
        records state).memory.producers.map AlphaZeroProducer.digest).Nodup := by
  intro records
  induction records with
  | nil =>
      intro state consumedAnswers _aligned _onlyMachine _allNodup
        currentNodup _provenance
      simpa only [indexed_state_after_records_nil] using currentNodup
  | cons head tail ih =>
      intro state consumedAnswers aligned onlyMachine allNodup currentNodup
        provenance
      obtain ⟨actor, input, answer, headExact⟩ :=
        onlyMachine head (by simp)
      subst head
      change (consumedAnswers ++ answer ::
        tail.map UnifiedExposureRecord.answer).Nodup at allNodup
      let controller := alphaZeroCausalController
        (globalOracleCalls := globalOracleCalls) transitionFuel boundaryIndex
      let next := controller.afterAnswer transitionFuel state answer
      have headAligned := aligned [] (.machineFresh actor input answer) tail
        (by rfl)
      have inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor =
          some input := by
        simpa only [indexed_state_after_records_nil] using
          aligned_machine_record_has_exact_input transitionFuel state.cursor
            actor input answer headAligned
      have tailAligned : IndexedRecordsAligned transitionFuel controller next
          tail := by
        apply indexed_records_aligned_segment transitionFuel controller state
          ((.machineFresh actor input answer) :: tail)
          [(.machineFresh actor input answer)] tail [] aligned
        simp
      have tailOnly : OnlyMachineFreshRecords tail := by
        intro record recordMember
        exact onlyMachine record (by simp [recordMember])
      have answerFreshConsumed : answer ∉ consumedAnswers := by
        have normalized :
            (consumedAnswers ++ answer ::
              tail.map UnifiedExposureRecord.answer).Nodup := by
          exact allNodup
        have separated := (List.nodup_append.mp normalized).2.2
        intro member
        exact separated answer member answer (by simp) rfl
      have answerFreshProducers : answer ∉
          state.memory.producers.map AlphaZeroProducer.digest := by
        intro member
        obtain ⟨producer, producerMember, digestExact⟩ :=
          List.mem_map.mp member
        apply answerFreshConsumed
        exact digestExact ▸ provenance producer producerMember
      have nextNodup :
          (next.memory.producers.map AlphaZeroProducer.digest).Nodup := by
        simpa [next, controller, alphaZeroCausalController,
          IndexedUnifiedExposureController.afterAnswer] using
          alpha_zero_after_memory_producer_digests_nodup transitionFuel
            boundaryIndex state input answer inputExact currentNodup
              answerFreshProducers
      have nextProvenance : ∀ producer ∈ next.memory.producers,
          producer.digest ∈ consumedAnswers ++ [answer] := by
        intro producer producerMember
        change producer ∈
          (alphaZeroAfterMemory transitionFuel boundaryIndex state
            answer).producers at producerMember
        rcases alpha_zero_after_memory_member_old_or_current transitionFuel
            boundaryIndex state input answer producer inputExact producerMember with
          old | ⟨_sourceExact, digestExact⟩
        · exact List.mem_append_left _ (provenance producer old)
        · rw [digestExact]
          simp
      have tailNodup :
          ((consumedAnswers ++ [answer]) ++
            tail.map UnifiedExposureRecord.answer).Nodup := by
        simpa [List.append_assoc] using
          (show (consumedAnswers ++ answer ::
            tail.map UnifiedExposureRecord.answer).Nodup by
              exact allNodup)
      rw [indexed_state_after_records_cons]
      exact ih next (consumedAnswers ++ [answer]) tailAligned tailOnly
        tailNodup nextNodup nextProvenance

/-- The complete accepted root prefix is cursor-aligned with the alpha
controller for any fixed boundary ordinal. -/
theorem exact_root_records_aligned_for_alpha_zero_controller
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
    (boundaryIndex : Nat) :
    IndexedRecordsAligned transitionFuel
      (alphaZeroCausalController
        (globalOracleCalls := globalFull256OracleCallCap parameters)
        transitionFuel boundaryIndex)
      (exactAlphaZeroInitialState input)
      (exactFixedRootRecords input.package.root) := by
  let controller := alphaZeroCausalController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel boundaryIndex
  let rootTape := operationalTapeCoordinates
    (globalFull256OracleCallCap parameters) 1
    (unifiedFull256ExposureCap parameters)
    (exactCompilerOperationalIndexedTape parameters sample.2)
  have traceExact :
      runUnifiedExposureTrace transitionFuel
          (unifiedFull256ExposureCap parameters)
          (exactPlainRomCursor configuration sample.1).erase rootTape =
        (runExactPlainRom transitionFuel configuration sample).trace := by
    simpa [rootTape, exactCompilerUnifiedExposureTrace] using
      exact_compiler_unified_exposure_trace_is_actual_plain_rom_trace
        transitionFuel configuration sample
  have fullAligned := indexed_records_aligned_of_trace transitionFuel
    controller (exactAlphaZeroInitialState input) rootTape
      (runExactPlainRom transitionFuel configuration sample).trace traceExact
  have fullSplit :
      (runExactPlainRom transitionFuel configuration sample).trace =
        [] ++ exactFixedRootRecords input.package.root ++
          (exactFixedComputedClientTailRun transitionFuel configuration sample
            input.package.root).trace := by
    rw [exact_fixed_operational_state_map_trace_is_full_trace transitionFuel
      configuration projection fixedInstance sample input.package]
    rfl
  have rootAligned := indexed_records_aligned_segment transitionFuel controller
    (exactAlphaZeroInitialState input)
    (runExactPlainRom transitionFuel configuration sample).trace []
    (exactFixedRootRecords input.package.root)
    (exactFixedComputedClientTailRun transitionFuel configuration sample
      input.package.root).trace fullAligned fullSplit
  simpa only [indexed_state_after_records_nil] using rootAligned

/-- Every exact accepted root prefix reaches an alpha controller state whose
producer digests are duplicate-free. -/
theorem exact_alpha_zero_prefix_producer_digests_nodup
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
    (boundaryIndex : Nat)
    (prior later : List UnifiedExposureRecord)
    (decomposition : exactFixedRootRecords input.package.root = prior ++ later) :
    ((indexedStateAfterRecords transitionFuel
      (alphaZeroCausalController transitionFuel boundaryIndex) prior
      (exactAlphaZeroInitialState input)).memory.producers.map
        AlphaZeroProducer.digest).Nodup := by
  let controller := alphaZeroCausalController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel boundaryIndex
  let initial := exactAlphaZeroInitialState input
  have priorAligned : IndexedRecordsAligned transitionFuel controller initial
      prior := by
    apply indexed_records_aligned_segment transitionFuel controller initial
      (exactFixedRootRecords input.package.root) [] prior later
      (by simpa [controller, initial] using
        exact_root_records_aligned_for_alpha_zero_controller input boundaryIndex)
    simpa using decomposition
  have priorOnly : OnlyMachineFreshRecords prior := by
    apply only_machine_fresh_records_segment
      (exactFixedRootRecords input.package.root) [] prior later
      (exact_root_records_only_machine_fresh input)
    simpa using decomposition
  have priorNodup : (prior.map UnifiedExposureRecord.answer).Nodup := by
    have rootNodup := exact_root_record_answers_nodup input
    rw [decomposition, List.map_append] at rootNodup
    exact (List.nodup_append.mp rootNodup).1
  have replay := alpha_zero_aligned_replay_producer_digests_nodup
    transitionFuel boundaryIndex prior initial [] priorAligned priorOnly
      (by simpa using priorNodup) (by simp [initial, exactAlphaZeroInitialState,
        inactiveAlphaZeroMemory]) (by simp [initial, exactAlphaZeroInitialState,
          inactiveAlphaZeroMemory])
  simpa [controller, initial] using replay

/-- The exact fold-nonce root record fixes a boundary ordinal at which the
returned digest is installed as alpha block zero's producer.  The statement
retains the literal actor-tagged trace decomposition and the exact replayed
post-record memory. -/
theorem exact_compiler_alpha_zero_boundary_installs_block_zero
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
      fixedInstance sample) :
    ∃ boundaryIndex prior later actor producerInput beforeAlphaDigest,
      exactFixedRootRecords input.package.root =
        prior ++
          (.machineFresh actor producerInput beforeAlphaDigest :
            UnifiedExposureRecord) :: later ∧
      boundaryIndex = prior.length ∧
      isAlphaZeroBoundaryInput producerInput = true ∧
      (indexedStateAfterRecords transitionFuel
        (alphaZeroCausalController
          (globalOracleCalls := globalFull256OracleCallCap parameters)
          transitionFuel boundaryIndex)
        (prior ++
          [(.machineFresh actor producerInput beforeAlphaDigest :
            UnifiedExposureRecord)])
        (exactAlphaZeroInitialState input)).memory.producers =
          [{ digest := beforeAlphaDigest, block := 0, sourceInput := producerInput }] := by
  obtain ⟨producerInput, _final256Input, beforeAlpha, _afterAlpha,
      _afterBlocks, _afterFinal256, _outputs, _advances, _exactValue,
      _workAnswer, _q16Base, producerLookup,
      ⟨producerDigest, producerInputExact⟩, _ordered, _outputsLength,
      _outputsPositive, _advancesLength, _terminalExact, _afterAlphaExact,
      _final256InputExact, _final256Lookup, _workLookup, _workAccepted,
      _finalNonceLookup, _q16BaseExact, _exactDecode, _operationalExact⟩ :=
    exact_compiler_alpha_zero_chain_has_root_order transitionRoom input
  obtain ⟨actor, rootMember⟩ :=
    exact_final_table_lookup_has_root_record input producerInput
      beforeAlpha.digest producerLookup
  obtain ⟨prior, later, rootExact⟩ := (List.mem_iff_append).mp rootMember
  let boundaryIndex := prior.length
  let selected : UnifiedExposureRecord :=
    .machineFresh actor producerInput beforeAlpha.digest
  let controller := alphaZeroCausalController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel boundaryIndex
  let reached := indexedStateAfterRecords transitionFuel controller prior
    (exactAlphaZeroInitialState input)
  have selectedAligned : unifiedRecordAtAnswer transitionFuel reached.cursor
      beforeAlpha.digest = selected := by
    exact exact_root_records_aligned_for_alpha_zero_controller input
      boundaryIndex prior selected later (by simpa [selected] using rootExact)
  have inputExact : unifiedInputBeforeAnswer? transitionFuel reached.cursor =
      some producerInput :=
    aligned_machine_record_has_exact_input transitionFuel reached.cursor actor
      producerInput beforeAlpha.digest (by simpa [selected] using selectedAligned)
  have reachedIndex : reached.exposureIndex = boundaryIndex := by
    simpa [reached, boundaryIndex, exactAlphaZeroInitialState] using
      indexed_state_after_records_exposure_index transitionFuel controller
        prior (exactAlphaZeroInitialState input)
  have boundary : isAlphaZeroBoundaryInput producerInput = true := by
    rw [producerInputExact]
    simp [isAlphaZeroBoundaryInput, alphaZeroBoundaryPayload,
      AspisK1.V7Tag73TranscriptSchedule.Payload.label,
      AspisK1.V7Tag73TranscriptSchedule.Payload.data]
  have installed :
      (alphaZeroAfterMemory transitionFuel boundaryIndex reached
        beforeAlpha.digest).producers =
        [{ digest := beforeAlpha.digest, block := 0, sourceInput := producerInput }] :=
    alpha_zero_after_boundary_has_block_zero_producer transitionFuel
      boundaryIndex reached producerInput beforeAlpha.digest inputExact
      reachedIndex boundary
  refine ⟨boundaryIndex, prior, later, actor, producerInput,
    beforeAlpha.digest, by simpa [selected] using rootExact, rfl, boundary, ?_⟩
  rw [indexed_state_after_records_append,
    indexed_state_after_records_cons, indexed_state_after_records_nil]
  change
    (alphaZeroAfterMemory transitionFuel boundaryIndex reached
      beforeAlpha.digest).producers =
        [{ digest := beforeAlpha.digest, block := 0, sourceInput := producerInput }]
  exact installed

/-- The boundary producer is installed independently of which actor made the
unique first exposure of its source coordinate. -/
theorem exact_compiler_alpha_zero_initial_producer_installed
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
      fixedInstance sample) :
    ∃ boundaryIndex producer,
      producer.block = (0 : Fin 4) ∧
      ExactAlphaZeroProducerInstalled input boundaryIndex producer := by
  obtain ⟨boundaryIndex, prior, later, actor, producerInput,
      beforeAlphaDigest, rootExact, indexExact, _boundary, installedExact⟩ :=
    exact_compiler_alpha_zero_boundary_installs_block_zero transitionRoom input
  let producer : AlphaZeroProducer :=
    { digest := beforeAlphaDigest, block := 0, sourceInput := producerInput }
  refine ⟨boundaryIndex, producer, rfl, ?_⟩
  intro arbitraryPrior arbitraryLater arbitraryActor arbitraryExact
  have prefixExact : prior = arbitraryPrior := by
    apply alpha_mapped_nodup_selected_prefix_eq UnifiedExposureRecord.answer
      (exactFixedRootRecords input.package.root) prior later arbitraryPrior
        arbitraryLater
      (.machineFresh actor producerInput beforeAlphaDigest :
        UnifiedExposureRecord)
      (.machineFresh arbitraryActor producer.sourceInput producer.digest :
        UnifiedExposureRecord)
      (exact_root_record_answers_nodup input) rootExact arbitraryExact
    rfl
  subst arbitraryPrior
  refine ⟨by omega, ?_⟩
  have canonicalMember : producer ∈
      (indexedStateAfterRecords transitionFuel
        (alphaZeroCausalController transitionFuel boundaryIndex)
        (prior ++
          [(.machineFresh actor producerInput beforeAlphaDigest :
            UnifiedExposureRecord)])
        (exactAlphaZeroInitialState input)).memory.producers := by
    rw [installedExact]
    simp [producer]
  rw [indexed_state_after_records_append,
    indexed_state_after_records_cons, indexed_state_after_records_nil] at canonicalMember ⊢
  change producer ∈
    ((alphaZeroCausalController transitionFuel boundaryIndex).afterAnswer
      transitionFuel
      (indexedStateAfterRecords transitionFuel
        (alphaZeroCausalController transitionFuel boundaryIndex) prior
        (exactAlphaZeroInitialState input)) beforeAlphaDigest).memory.producers at canonicalMember ⊢
  exact canonicalMember

/-- An installed alpha producer remains available at every strictly later
child coordinate in the exact accepted root chronology. -/
theorem exact_alpha_installed_producer_available_before_ordered_child
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
    (boundaryIndex : Nat) (producer : AlphaZeroProducer)
    (childInput : ShaInput) (childAnswer : Digest256)
    (installed : ExactAlphaZeroProducerInstalled input boundaryIndex producer)
    (ordered : ∃ before middle after,
      exactRootFreshQueries input =
        before ++ (producer.sourceInput, producer.digest) :: middle ++
          (childInput, childAnswer) :: after) :
    ∃ prior middle later producerActor childActor,
      exactFixedRootRecords input.package.root =
        prior ++
          (.machineFresh producerActor producer.sourceInput producer.digest :
            UnifiedExposureRecord) :: middle ++
          (.machineFresh childActor childInput childAnswer :
            UnifiedExposureRecord) :: later ∧
      boundaryIndex <
        (indexedStateAfterRecords transitionFuel
          (alphaZeroCausalController transitionFuel boundaryIndex)
          (prior ++
            (.machineFresh producerActor producer.sourceInput producer.digest :
              UnifiedExposureRecord) :: middle)
          (exactAlphaZeroInitialState input)).exposureIndex ∧
      producer ∈
        (indexedStateAfterRecords transitionFuel
          (alphaZeroCausalController transitionFuel boundaryIndex)
          (prior ++
            (.machineFresh producerActor producer.sourceInput producer.digest :
              UnifiedExposureRecord) :: middle)
          (exactAlphaZeroInitialState input)).memory.producers := by
  obtain ⟨before, middle, after, pairExact⟩ := ordered
  obtain ⟨prior, between, later, producerActor, childActor, recordsExact⟩ :=
    exact_root_pair_order_lifts_to_records input producer.sourceInput
      childInput producer.digest childAnswer before middle after pairExact
  let producerRecord : UnifiedExposureRecord :=
    .machineFresh producerActor producer.sourceInput producer.digest
  let childRecord : UnifiedExposureRecord :=
    .machineFresh childActor childInput childAnswer
  obtain ⟨boundaryBeforeProducer, installedAfter⟩ :=
    installed prior (between ++ childRecord :: later) producerActor (by
      simpa only [producerRecord, childRecord, List.cons_append,
        List.append_assoc] using recordsExact)
  let afterProducer := indexedStateAfterRecords transitionFuel
    (alphaZeroCausalController transitionFuel boundaryIndex)
    (prior ++ [producerRecord]) (exactAlphaZeroInitialState input)
  have afterProducerIndex : afterProducer.exposureIndex = prior.length + 1 := by
    have count := indexed_state_after_records_exposure_index transitionFuel
      (alphaZeroCausalController
        (globalOracleCalls := globalFull256OracleCallCap parameters)
        transitionFuel boundaryIndex) (prior ++ [producerRecord])
          (exactAlphaZeroInitialState input)
    simpa [afterProducer, exactAlphaZeroInitialState] using count
  have afterBoundary : boundaryIndex < afterProducer.exposureIndex := by
    rw [afterProducerIndex]
    omega
  have growth : afterProducer.memory.producers <+:
      (indexedStateAfterRecords transitionFuel
        (alphaZeroCausalController transitionFuel boundaryIndex) between
        afterProducer).memory.producers :=
    alpha_zero_indexed_state_producers_prefix_after_boundary transitionFuel
      boundaryIndex between afterProducer afterBoundary
  have available : producer ∈
      (indexedStateAfterRecords transitionFuel
        (alphaZeroCausalController transitionFuel boundaryIndex)
        (prior ++ producerRecord :: between)
        (exactAlphaZeroInitialState input)).memory.producers := by
    have member := growth.subset (by
      simpa [afterProducer] using installedAfter)
    simpa [afterProducer, indexed_state_after_records_append] using member
  have reachedAfterBoundary : boundaryIndex <
      (indexedStateAfterRecords transitionFuel
        (alphaZeroCausalController transitionFuel boundaryIndex)
        (prior ++ producerRecord :: between)
        (exactAlphaZeroInitialState input)).exposureIndex := by
    rw [show prior ++ producerRecord :: between =
      (prior ++ [producerRecord]) ++ between by
        simp]
    rw [indexed_state_after_records_append]
    change boundaryIndex <
      (indexedStateAfterRecords transitionFuel
        (alphaZeroCausalController transitionFuel boundaryIndex) between
        afterProducer).exposureIndex
    have count := indexed_state_after_records_exposure_index transitionFuel
      (alphaZeroCausalController
        (globalOracleCalls := globalFull256OracleCallCap parameters)
        transitionFuel boundaryIndex) between afterProducer
    rw [count]
    omega
  exact ⟨prior, between, later, producerActor, childActor, by
    simpa only [producerRecord, childRecord] using recordsExact,
      reachedAfterBoundary, available⟩

/-- An exact advance child below an installed producer is itself installed at
its unique accepted-root record. -/
theorem exact_alpha_advance_installs_next_producer
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
    (boundaryIndex : Nat) (parent : AlphaZeroProducer)
    (advanced : Digest256)
    (bounded : parent.block.val + 1 < 4)
    (installed : ExactAlphaZeroProducerInstalled input boundaryIndex parent)
    (ordered : ∃ before middle after,
      exactRootFreshQueries input =
        before ++ (parent.sourceInput, parent.digest) :: middle ++
          (gammaAdvanceInput parent.digest, advanced) :: after) :
    ExactAlphaZeroProducerInstalled input boundaryIndex
      (AlphaZeroProducer.mk advanced ⟨parent.block.val + 1, bounded⟩
        (gammaAdvanceInput parent.digest)) := by
  let nextProducer : AlphaZeroProducer :=
    AlphaZeroProducer.mk advanced ⟨parent.block.val + 1, bounded⟩
      (gammaAdvanceInput parent.digest)
  intro arbitraryPrior arbitraryLater arbitraryActor arbitraryExact
  obtain ⟨prior, between, later, producerActor, childActor,
      recordsExact, reachedAfterBoundary, parentMember⟩ :=
    exact_alpha_installed_producer_available_before_ordered_child input
      boundaryIndex parent (gammaAdvanceInput parent.digest) advanced
        installed ordered
  let producerRecord : UnifiedExposureRecord :=
    .machineFresh producerActor parent.sourceInput parent.digest
  let childRecord : UnifiedExposureRecord :=
    .machineFresh childActor (gammaAdvanceInput parent.digest) advanced
  let childPrefix := prior ++ producerRecord :: between
  have canonicalChildExact : exactFixedRootRecords input.package.root =
      childPrefix ++ childRecord :: later := by
    simpa only [childPrefix, producerRecord, childRecord, List.cons_append,
      List.append_assoc] using recordsExact
  have prefixExact : childPrefix = arbitraryPrior := by
    apply alpha_mapped_nodup_selected_prefix_eq UnifiedExposureRecord.answer
      (exactFixedRootRecords input.package.root) childPrefix later
        arbitraryPrior arbitraryLater childRecord
      (.machineFresh arbitraryActor nextProducer.sourceInput
        nextProducer.digest : UnifiedExposureRecord)
      (exact_root_record_answers_nodup input) canonicalChildExact
      (by simpa only [nextProducer] using arbitraryExact)
    rfl
  subst arbitraryPrior
  let reached := indexedStateAfterRecords transitionFuel
    (alphaZeroCausalController transitionFuel boundaryIndex) childPrefix
    (exactAlphaZeroInitialState input)
  have reachedMember : parent ∈ reached.memory.producers := by
    simpa [reached, childPrefix, producerRecord, childRecord] using parentMember
  have reachedNodup :
      (reached.memory.producers.map AlphaZeroProducer.digest).Nodup := by
    simpa [reached] using exact_alpha_zero_prefix_producer_digests_nodup
      input boundaryIndex childPrefix (childRecord :: later)
        canonicalChildExact
  have aligned : unifiedRecordAtAnswer transitionFuel reached.cursor advanced =
      .machineFresh arbitraryActor nextProducer.sourceInput
        nextProducer.digest := by
    have rootAligned := exact_root_records_aligned_for_alpha_zero_controller
      input boundaryIndex childPrefix
        (.machineFresh arbitraryActor nextProducer.sourceInput
          nextProducer.digest : UnifiedExposureRecord)
        arbitraryLater (by simpa only [nextProducer] using arbitraryExact)
    simpa [reached, nextProducer, UnifiedExposureRecord.answer] using rootAligned
  have inputExact : unifiedInputBeforeAnswer? transitionFuel reached.cursor =
      some (gammaAdvanceInput parent.digest) := by
    have exact := aligned_machine_record_has_exact_input transitionFuel
      reached.cursor arbitraryActor nextProducer.sourceInput
        nextProducer.digest aligned
    simpa [nextProducer] using exact
  have installedMemory := alpha_zero_memory_after_advance_contains_producer
    transitionFuel boundaryIndex reached (gammaAdvanceInput parent.digest)
      advanced parent bounded (Nat.ne_of_gt reachedAfterBoundary) inputExact
        rfl reachedNodup reachedMember
  refine ⟨?_, ?_⟩
  · have count := indexed_state_after_records_exposure_index transitionFuel
      (alphaZeroCausalController
        (globalOracleCalls := globalFull256OracleCallCap parameters)
        transitionFuel boundaryIndex) childPrefix
          (exactAlphaZeroInitialState input)
    have reachedLength : reached.exposureIndex = childPrefix.length := by
      simpa [reached, exactAlphaZeroInitialState] using count
    rw [reachedLength] at reachedAfterBoundary
    exact Nat.le_of_lt reachedAfterBoundary
  · change nextProducer ∈
      (indexedStateAfterRecords transitionFuel
        (alphaZeroCausalController transitionFuel boundaryIndex)
        (childPrefix ++
          [(.machineFresh arbitraryActor nextProducer.sourceInput
            nextProducer.digest : UnifiedExposureRecord)])
        (exactAlphaZeroInitialState input)).memory.producers
    rw [indexed_state_after_records_append,
      indexed_state_after_records_cons, indexed_state_after_records_nil]
    change nextProducer ∈
      (alphaZeroAfterMemory transitionFuel boundaryIndex reached
        advanced).producers
    simpa [nextProducer, gammaAdvanceInput] using installedMemory

#print axioms exactAlphaZeroInitialState
#print axioms alpha_mapped_nodup_selected_prefix_eq
#print axioms ExactAlphaZeroProducerInstalled
#print axioms alpha_zero_indexed_state_producer_has_literal_record
#print axioms alpha_zero_aligned_replay_producer_digests_nodup
#print axioms exact_root_records_aligned_for_alpha_zero_controller
#print axioms exact_alpha_zero_prefix_producer_digests_nodup
#print axioms exact_compiler_alpha_zero_boundary_installs_block_zero
#print axioms exact_compiler_alpha_zero_initial_producer_installed
#print axioms exact_alpha_installed_producer_available_before_ordered_child
#print axioms exact_alpha_advance_installs_next_producer

end

end AspisK1.V7Tag73ExactAlphaZeroControllerAlignment
