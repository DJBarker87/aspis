import AspisFormal.K1.V7Tag73IndexedAlignedRecordReplay

/-!
# Exact completion of the accepted final-work controller pair

The accepted work query and nonce-absorb query can be first-created by either
actor and in either chronological order.  This file combines their exact root
order with prefix-aligned controller replay.  Whichever query occurs first
activates the exposure-indexed controller; after the later query is consumed,
the controller has both `workSeen = true` and the exact returned q16 base.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactFinalWorkPairControllerCompletion

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalQ16FinalWorkProbability
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFinalWorkPairRootOrder
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactProbabilityCoverageAudit
open AspisK1.V7Tag73ExactRootFreshInputUniqueness
open AspisK1.V7Tag73ExactRootLookupCausalOrder
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkDigestProbability
open AspisK1.V7Tag73FinalWorkEarliestExposure
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73FullCursorClientLineageLift
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalNodeCertificate
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Projecting the causal input from a machine-fresh record list recovers the
underlying query inputs, wrapped in `some`. -/
theorem projected_machine_fresh_causal_inputs
    (actor : QueryActor) :
    ∀ queries : List (ShaInput × Digest256),
      (projectedMachineFreshRecords actor queries).map causalInput? =
        queries.map (fun query => some query.1) := by
  intro queries
  induction queries with
  | nil => rfl
  | cons query rest ih =>
      rcases query with ⟨input, answer⟩
      simp [projectedMachineFreshRecords, causalInput?, ih]

/-- The actor-tagged root records retain pairwise-distinct fresh SHA inputs. -/
theorem exact_root_record_causal_inputs_nodup
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    ((exactFixedRootRecords input.package.root).map causalInput?).Nodup := by
  have inputNodup := exact_root_fresh_query_inputs_nodup input
  have optionNodup :
      ((exactRootFreshQueries input).map
        (fun query => some query.1)).Nodup := by
    have lifted :
        (((exactRootFreshQueries input).map Prod.fst).map
          (fun value : ShaInput => some value)).Nodup :=
      List.Pairwise.map (fun value => some value)
        (fun first second different equal =>
          different (Option.some.inj equal)) inputNodup
    simpa [List.map_map, Function.comp_def] using lifted
  unfold exactRootFreshQueries at optionNodup
  unfold exactFixedRootRecords fullProjectedRootRecords
  rw [List.map_append, projected_machine_fresh_causal_inputs,
    projected_machine_fresh_causal_inputs]
  simpa only [List.map_append] using optionNodup

/-- Every exact root record is a machine-fresh record for one of the two root
actors. -/
theorem exact_root_records_only_machine_fresh
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    OnlyMachineFreshRecords (exactFixedRootRecords input.package.root) := by
  intro record member
  unfold exactFixedRootRecords fullProjectedRootRecords at member
  rw [List.mem_append] at member
  rcases member with adversary | verifier
  · obtain ⟨queryInput, answer, exact⟩ :=
      only_machine_fresh_actor_projected_records .adversary
        input.package.root.full.projection.rootPrefixes.adversary.freshQueries
        record adversary
    exact ⟨.adversary, queryInput, answer, exact⟩
  · obtain ⟨queryInput, answer, exact⟩ :=
      only_machine_fresh_actor_projected_records .verifier
        input.package.root.full.projection.rootPrefixes.verifier.freshQueries
        record verifier
    exact ⟨.verifier, queryInput, answer, exact⟩

/-- In a noduplicated causal-input list, every record strictly between two
selected coordinates avoids the later coordinate's input. -/
theorem strict_record_middle_avoids_second_input
    (records before middle after : List UnifiedExposureRecord)
    (first second : UnifiedExposureRecord)
    (nodup : (records.map causalInput?).Nodup)
    (decomposition : records =
      before ++ first :: middle ++ second :: after) :
    ∀ record ∈ middle,
      causalInput? record ≠ causalInput? second := by
  rw [decomposition] at nodup
  have splitNodup :
      ((before ++ first :: middle).map causalInput? ++
        (second :: after).map causalInput?).Nodup := by
    simpa only [List.map_append, List.map_cons, List.cons_append,
      List.append_assoc] using nodup
  have separated := (List.nodup_append.mp splitNodup).2.2
  intro record member equal
  exact separated (causalInput? record)
    (List.mem_map.mpr ⟨record,
      List.mem_append_right before (by simp [member]), rfl⟩)
    (causalInput? second) (by simp) equal

/-! ## Deterministic completion in both chronological orders -/

/-- If the work record is first, its answer activates the work slot.  Every
intervening root coordinate avoids the unique nonce-absorb input, so the later
absorb answer installs the exact q16 base without changing the branch map. -/
theorem aligned_work_then_absorb_completes_pair
    {globalOracleCalls : Nat}
    (transitionFuel : Nat) (cursor : UnifiedExposureCursor globalOracleCalls)
    (records before middle after : List UnifiedExposureRecord)
    (digest : Digest256) (nonce : NonceBytes)
    (workAnswer q16Base : Digest256)
    (workActor absorbActor : QueryActor)
    (decomposition : records =
      before ++
        (.machineFresh workActor
          (literalFinalWorkKey digest nonce).workInput workAnswer :
          UnifiedExposureRecord) ::
        middle ++
        (.machineFresh absorbActor
          (literalFinalWorkKey digest nonce).absorbInput q16Base :
          UnifiedExposureRecord) :: after)
    (aligned : IndexedRecordsAligned transitionFuel
      (finalWorkQ16CandidateController globalOracleCalls transitionFuel
        before.length)
      { exposureIndex := 0
        cursor := cursor
        memory := inactiveCandidateMemory }
      records)
    (onlyMachine : OnlyMachineFreshRecords records)
    (nodup : (records.map causalInput?).Nodup) :
    let controller := finalWorkQ16CandidateController globalOracleCalls
      transitionFuel before.length
    let initial : IndexedUnifiedExposureState globalOracleCalls
        FinalWorkQ16CandidateMemory :=
      { exposureIndex := 0
        cursor := cursor
        memory := inactiveCandidateMemory }
    let workRecord : UnifiedExposureRecord :=
      .machineFresh workActor (literalFinalWorkKey digest nonce).workInput
        workAnswer
    let absorbRecord : UnifiedExposureRecord :=
      .machineFresh absorbActor (literalFinalWorkKey digest nonce).absorbInput
        q16Base
    (controller.afterAnswer transitionFuel
      (indexedStateAfterRecords transitionFuel controller middle
        (controller.afterAnswer transitionFuel
          (indexedStateAfterRecords transitionFuel controller before initial)
          workAnswer)) q16Base).memory =
      .tracked (literalFinalWorkKey digest nonce) true (some q16Base)
        emptyRawQ16Branches := by
  dsimp only
  let key := literalFinalWorkKey digest nonce
  let controller := finalWorkQ16CandidateController globalOracleCalls
    transitionFuel before.length
  let initial : IndexedUnifiedExposureState globalOracleCalls
      FinalWorkQ16CandidateMemory :=
    { exposureIndex := 0
      cursor := cursor
      memory := inactiveCandidateMemory }
  let workRecord : UnifiedExposureRecord :=
    .machineFresh workActor key.workInput workAnswer
  let absorbRecord : UnifiedExposureRecord :=
    .machineFresh absorbActor key.absorbInput q16Base
  let beforeWork := indexedStateAfterRecords transitionFuel controller before
    initial
  have beforeWorkIndex : beforeWork.exposureIndex = before.length := by
    simpa [beforeWork, initial] using
      indexed_state_after_records_exposure_index transitionFuel controller
        before initial
  have beforeWorkInactive : beforeWork.memory = inactiveCandidateMemory := by
    apply candidate_memory_stays_inactive_before_anchor transitionFuel
      before.length before initial
    · simp [initial]
    · rfl
  have workDecomposition : records =
      before ++ workRecord :: (middle ++ absorbRecord :: after) := by
    simpa only [key, workRecord, absorbRecord, List.cons_append,
      List.append_assoc] using decomposition
  have workAligned := aligned before workRecord
    (middle ++ absorbRecord :: after) workDecomposition
  have workInputExact : unifiedInputBeforeAnswer? transitionFuel
      beforeWork.cursor = some key.workInput := by
    exact aligned_machine_record_has_exact_input transitionFuel
      beforeWork.cursor workActor key.workInput workAnswer (by
        simpa only [beforeWork, UnifiedExposureRecord.answer] using workAligned)
  let afterWork := controller.afterAnswer transitionFuel beforeWork workAnswer
  have afterWorkMemory : afterWork.memory =
      .tracked key true none emptyRawQ16Branches := by
    simp [afterWork, controller, key, finalWorkQ16CandidateController,
      IndexedUnifiedExposureController.afterAnswer, candidateAfterMemory,
      beforeWorkIndex, beforeWorkInactive, workInputExact,
      inactiveCandidateMemory]
  have segmentDecomposition : records =
      (before ++ [workRecord]) ++ middle ++ (absorbRecord :: after) := by
    simpa only [key, workRecord, absorbRecord, List.nil_append,
      List.cons_append, List.append_assoc] using decomposition
  have middleAlignedRaw := indexed_records_aligned_segment transitionFuel
    controller initial records (before ++ [workRecord]) middle
      (absorbRecord :: after) aligned segmentDecomposition
  have prefixAfterWork :
      indexedStateAfterRecords transitionFuel controller
          (before ++ [workRecord]) initial = afterWork := by
    rw [indexed_state_after_records_append]
    rfl
  have middleAligned : IndexedRecordsAligned transitionFuel controller
      afterWork middle := by
    simpa only [prefixAfterWork] using middleAlignedRaw
  have middleOnly := only_machine_fresh_records_segment records
    (before ++ [workRecord]) middle (absorbRecord :: after) onlyMachine
      segmentDecomposition
  have middleAvoidsRaw := strict_record_middle_avoids_second_input records
    before middle after workRecord absorbRecord nodup (by
      simpa only [key, workRecord, absorbRecord] using decomposition)
  have middleAvoids : ∀ record ∈ middle,
      causalInput? record ≠ some key.absorbInput := by
    intro record member
    simpa only [absorbRecord, causalInput?] using
      middleAvoidsRaw record member
  have beforeAbsorbMemory :=
    aligned_machine_records_preserve_work_without_base transitionFuel
      before.length key emptyRawQ16Branches middle afterWork middleAligned
        middleOnly middleAvoids afterWorkMemory
  let beforeAbsorb := indexedStateAfterRecords transitionFuel controller middle
    afterWork
  have absorbDecomposition : records =
      (before ++ workRecord :: middle) ++ absorbRecord :: after := by
    simpa only [key, workRecord, absorbRecord, List.cons_append,
      List.append_assoc] using decomposition
  have absorbAlignedRaw := aligned (before ++ workRecord :: middle)
    absorbRecord after absorbDecomposition
  have prefixBeforeAbsorb :
      indexedStateAfterRecords transitionFuel controller
          (before ++ workRecord :: middle) initial = beforeAbsorb := by
    have prefixExact : before ++ workRecord :: middle =
        (before ++ [workRecord]) ++ middle := by
      simp only [List.nil_append, List.cons_append, List.append_assoc]
    rw [prefixExact, indexed_state_after_records_append, prefixAfterWork]
  have absorbAligned : unifiedRecordAtAnswer transitionFuel
      beforeAbsorb.cursor absorbRecord.answer = absorbRecord := by
    rw [prefixBeforeAbsorb] at absorbAlignedRaw
    exact absorbAlignedRaw
  have absorbInputExact : unifiedInputBeforeAnswer? transitionFuel
      beforeAbsorb.cursor = some key.absorbInput := by
    exact aligned_machine_record_has_exact_input transitionFuel
      beforeAbsorb.cursor absorbActor key.absorbInput q16Base (by
        simpa only [absorbRecord, UnifiedExposureRecord.answer] using
          absorbAligned)
  have beforeAbsorbMemory' : beforeAbsorb.memory =
      .tracked key true none emptyRawQ16Branches := by
    exact beforeAbsorbMemory
  simpa only [key, controller, beforeWork, afterWork, beforeAbsorb] using (by
    simp [controller, finalWorkQ16CandidateController,
      IndexedUnifiedExposureController.afterAnswer, candidateAfterMemory,
      beforeAbsorbMemory', absorbInputExact,
      RawFinalWorkKey.absorbInput_ne_workInput] :
      (controller.afterAnswer transitionFuel beforeAbsorb q16Base).memory =
        .tracked key true (some q16Base) emptyRawQ16Branches)

/-- If the nonce-absorb record is first, it installs the exact q16 base.
Intervening root records may legitimately populate q16 branch state, but they
cannot consume the unique work input.  The later work answer therefore marks
the same controller as work-qualified while retaining that base. -/
theorem aligned_absorb_then_work_completes_pair
    {globalOracleCalls : Nat}
    (transitionFuel : Nat) (cursor : UnifiedExposureCursor globalOracleCalls)
    (records before middle after : List UnifiedExposureRecord)
    (digest : Digest256) (nonce : NonceBytes)
    (workAnswer q16Base : Digest256)
    (workActor absorbActor : QueryActor)
    (decomposition : records =
      before ++
        (.machineFresh absorbActor
          (literalFinalWorkKey digest nonce).absorbInput q16Base :
          UnifiedExposureRecord) ::
        middle ++
        (.machineFresh workActor
          (literalFinalWorkKey digest nonce).workInput workAnswer :
          UnifiedExposureRecord) :: after)
    (aligned : IndexedRecordsAligned transitionFuel
      (finalWorkQ16CandidateController globalOracleCalls transitionFuel
        before.length)
      { exposureIndex := 0
        cursor := cursor
        memory := inactiveCandidateMemory }
      records)
    (onlyMachine : OnlyMachineFreshRecords records)
    (nodup : (records.map causalInput?).Nodup) :
    ∃ completedBranches,
      let controller := finalWorkQ16CandidateController globalOracleCalls
        transitionFuel before.length
      let initial : IndexedUnifiedExposureState globalOracleCalls
          FinalWorkQ16CandidateMemory :=
        { exposureIndex := 0
          cursor := cursor
          memory := inactiveCandidateMemory }
      (controller.afterAnswer transitionFuel
        (indexedStateAfterRecords transitionFuel controller middle
          (controller.afterAnswer transitionFuel
            (indexedStateAfterRecords transitionFuel controller before initial)
            q16Base)) workAnswer).memory =
        .tracked (literalFinalWorkKey digest nonce) true (some q16Base)
          completedBranches := by
  let key := literalFinalWorkKey digest nonce
  let controller := finalWorkQ16CandidateController globalOracleCalls
    transitionFuel before.length
  let initial : IndexedUnifiedExposureState globalOracleCalls
      FinalWorkQ16CandidateMemory :=
    { exposureIndex := 0
      cursor := cursor
      memory := inactiveCandidateMemory }
  let absorbRecord : UnifiedExposureRecord :=
    .machineFresh absorbActor key.absorbInput q16Base
  let workRecord : UnifiedExposureRecord :=
    .machineFresh workActor key.workInput workAnswer
  let beforeAbsorb := indexedStateAfterRecords transitionFuel controller before
    initial
  have beforeAbsorbIndex : beforeAbsorb.exposureIndex = before.length := by
    simpa [beforeAbsorb, initial] using
      indexed_state_after_records_exposure_index transitionFuel controller
        before initial
  have beforeAbsorbInactive : beforeAbsorb.memory =
      inactiveCandidateMemory := by
    apply candidate_memory_stays_inactive_before_anchor transitionFuel
      before.length before initial
    · simp [initial]
    · rfl
  have absorbDecomposition : records =
      before ++ absorbRecord :: (middle ++ workRecord :: after) := by
    simpa only [key, absorbRecord, workRecord, List.cons_append,
      List.append_assoc] using decomposition
  have absorbAligned := aligned before absorbRecord
    (middle ++ workRecord :: after) absorbDecomposition
  have absorbInputExact : unifiedInputBeforeAnswer? transitionFuel
      beforeAbsorb.cursor = some key.absorbInput := by
    exact aligned_machine_record_has_exact_input transitionFuel
      beforeAbsorb.cursor absorbActor key.absorbInput q16Base (by
        simpa only [beforeAbsorb, absorbRecord, UnifiedExposureRecord.answer]
          using absorbAligned)
  let afterAbsorb := controller.afterAnswer transitionFuel beforeAbsorb q16Base
  have afterAbsorbMemory : afterAbsorb.memory =
      .tracked key false (some q16Base) emptyRawQ16Branches := by
    simp [afterAbsorb, controller, key, finalWorkQ16CandidateController,
      IndexedUnifiedExposureController.afterAnswer, candidateAfterMemory,
      beforeAbsorbIndex, beforeAbsorbInactive, absorbInputExact,
      inactiveCandidateMemory]
  have segmentDecomposition : records =
      (before ++ [absorbRecord]) ++ middle ++ (workRecord :: after) := by
    simpa only [key, absorbRecord, workRecord, List.nil_append,
      List.cons_append, List.append_assoc] using decomposition
  have middleAlignedRaw := indexed_records_aligned_segment transitionFuel
    controller initial records (before ++ [absorbRecord]) middle
      (workRecord :: after) aligned segmentDecomposition
  have prefixAfterAbsorb :
      indexedStateAfterRecords transitionFuel controller
          (before ++ [absorbRecord]) initial = afterAbsorb := by
    rw [indexed_state_after_records_append]
    rfl
  have middleAligned : IndexedRecordsAligned transitionFuel controller
      afterAbsorb middle := by
    simpa only [prefixAfterAbsorb] using middleAlignedRaw
  have middleOnly := only_machine_fresh_records_segment records
    (before ++ [absorbRecord]) middle (workRecord :: after) onlyMachine
      segmentDecomposition
  have middleAvoidsRaw := strict_record_middle_avoids_second_input records
    before middle after absorbRecord workRecord nodup (by
      simpa only [key, absorbRecord, workRecord] using decomposition)
  have middleAvoids : ∀ record ∈ middle,
      causalInput? record ≠ some key.workInput := by
    intro record member
    simpa only [workRecord, causalInput?] using
      middleAvoidsRaw record member
  obtain ⟨branches, beforeWorkMemory⟩ :=
    aligned_machine_records_preserve_base_without_work transitionFuel
      before.length key q16Base middle afterAbsorb emptyRawQ16Branches
        middleAligned middleOnly middleAvoids afterAbsorbMemory
  let beforeWork := indexedStateAfterRecords transitionFuel controller middle
    afterAbsorb
  have workDecomposition : records =
      (before ++ absorbRecord :: middle) ++ workRecord :: after := by
    simpa only [key, absorbRecord, workRecord, List.cons_append,
      List.append_assoc] using decomposition
  have workAlignedRaw := aligned (before ++ absorbRecord :: middle)
    workRecord after workDecomposition
  have prefixBeforeWork :
      indexedStateAfterRecords transitionFuel controller
          (before ++ absorbRecord :: middle) initial = beforeWork := by
    have prefixExact : before ++ absorbRecord :: middle =
        (before ++ [absorbRecord]) ++ middle := by
      simp only [List.nil_append, List.cons_append, List.append_assoc]
    rw [prefixExact, indexed_state_after_records_append, prefixAfterAbsorb]
  have workAligned : unifiedRecordAtAnswer transitionFuel beforeWork.cursor
      workRecord.answer = workRecord := by
    rw [prefixBeforeWork] at workAlignedRaw
    exact workAlignedRaw
  have workInputExact : unifiedInputBeforeAnswer? transitionFuel
      beforeWork.cursor = some key.workInput := by
    exact aligned_machine_record_has_exact_input transitionFuel
      beforeWork.cursor workActor key.workInput workAnswer (by
        simpa only [workRecord, UnifiedExposureRecord.answer] using workAligned)
  have beforeWorkMemory' : beforeWork.memory =
      .tracked key false (some q16Base) branches := beforeWorkMemory
  let completedBranches :=
    updateRawQ16Branches q16Base branches key.workInput workAnswer
  refine ⟨completedBranches, ?_⟩
  dsimp only
  simpa only [key, controller, beforeAbsorb, afterAbsorb, beforeWork] using (by
    simp [controller, completedBranches, finalWorkQ16CandidateController,
      IndexedUnifiedExposureController.afterAnswer, candidateAfterMemory,
      beforeWorkMemory', workInputExact] :
      (controller.afterAnswer transitionFuel beforeWork workAnswer).memory =
        .tracked key true (some q16Base) completedBranches)

/-! ## Exact accepted-source instantiation -/

/-- Canonical inactive state for one exposure-indexed controller on the exact
compiler cursor. -/
def exactPairControllerInitialState
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
      FinalWorkQ16CandidateMemory :=
  { exposureIndex := 0
    cursor := (exactPlainRomCursor configuration sample.1).erase
    memory := inactiveCandidateMemory }

/-- Every exact root prefix is aligned with the candidate controller at any
fixed chronological anchor. -/
theorem exact_root_records_aligned_for_candidate_controller
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
    (anchor : Nat) :
    IndexedRecordsAligned transitionFuel
      (finalWorkQ16CandidateController
        (globalFull256OracleCallCap parameters) transitionFuel anchor)
      (exactPairControllerInitialState input)
      (exactFixedRootRecords input.package.root) := by
  let controller := finalWorkQ16CandidateController
    (globalFull256OracleCallCap parameters) transitionFuel anchor
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
    controller (exactPairControllerInitialState input) rootTape
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
    (exactPairControllerInitialState input)
    (runExactPlainRom transitionFuel configuration sample).trace []
    (exactFixedRootRecords input.package.root)
    (exactFixedComputedClientTailRun transitionFuel configuration sample
      input.package.root).trace fullAligned fullSplit
  simpa only [indexed_state_after_records_nil] using rootAligned

/-- Any strict prefix ending immediately before a selected root coordinate is
an inhabitant of the exact compiler exposure inventory. -/
theorem exact_root_strict_prefix_lt_exposure_cap
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
    (before later : List UnifiedExposureRecord)
    (selected : UnifiedExposureRecord)
    (decomposition : exactFixedRootRecords input.package.root =
      before ++ selected :: later) :
    before.length < unifiedFull256ExposureCap parameters := by
  have beforeRoot : before.length <
      (exactFixedRootRecords input.package.root).length := by
    rw [decomposition]
    simp
  have rootFull : (exactFixedRootRecords input.package.root).length ≤
      (runExactPlainRom transitionFuel configuration sample).trace.length := by
    rw [exact_fixed_operational_state_map_trace_is_full_trace transitionFuel
      configuration projection fixedInstance sample input.package]
    unfold exactFixedOperationalStateMapTrace
    simp
  rw [← exact_compiler_full_trace_length transitionFuel configuration sample]
  exact beforeRoot.trans_le rootFull

/-- Main pair-completion endpoint.  Strict accepted source execution supplies
one exposure-indexed trial and an actual prefix of the actor-tagged root trace
whose concrete controller state has observed accepted final work and retains
the exact returned q16 base. -/
theorem exact_compiler_accepted_final_work_pair_controller_completes
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    ∃ (digest workAnswer q16Base : Digest256)
        (trial : ExactCompilerExposureTrial parameters)
        (completedPrefix remaining : List UnifiedExposureRecord)
        (branches : Fin 64 → RawQ16BranchPhase),
      FinalWork34Accepted workAnswer ∧
      q16Base = (exactOperationalRawTrace input).q16BaseDigest ∧
      exactFixedRootRecords input.package.root =
        completedPrefix ++ remaining ∧
      trial.val < completedPrefix.length ∧
      (indexedStateAfterRecords transitionFuel
        (finalWorkQ16CandidateController
          (globalFull256OracleCallCap parameters) transitionFuel trial.val)
        completedPrefix (exactPairControllerInitialState input)).memory =
          .tracked
            (literalFinalWorkKey digest
              (exactOperationalTape input).messages.finalGrinding.selected)
            true (some q16Base) branches := by
  obtain ⟨digest, workAnswer, q16Base, workActor, absorbActor,
      workAccepted, q16BaseExact, order⟩ :=
    exact_compiler_accepted_final_work_pair_has_strict_root_record_order input
  let nonce := (exactOperationalTape input).messages.finalGrinding.selected
  let key := literalFinalWorkKey digest nonce
  let rootRecords := exactFixedRootRecords input.package.root
  have rootOnly := exact_root_records_only_machine_fresh input
  have rootNodup := exact_root_record_causal_inputs_nodup input
  rcases order with
      ⟨before, middle, after, workFirst⟩ |
      ⟨before, middle, after, absorbFirst⟩
  · let workRecord : UnifiedExposureRecord :=
      .machineFresh workActor key.workInput workAnswer
    let absorbRecord : UnifiedExposureRecord :=
      .machineFresh absorbActor key.absorbInput q16Base
    have workFirst' : rootRecords =
        before ++ workRecord :: middle ++ absorbRecord :: after := by
      simpa only [rootRecords, nonce, key, workRecord, absorbRecord] using
        workFirst
    have trialBound : before.length <
        unifiedFull256ExposureCap parameters :=
      exact_root_strict_prefix_lt_exposure_cap input before
        (middle ++ absorbRecord :: after) workRecord (by
          simpa only [List.cons_append, List.append_assoc] using workFirst')
    let trial : ExactCompilerExposureTrial parameters :=
      ⟨before.length, trialBound⟩
    have aligned := exact_root_records_aligned_for_candidate_controller input
      before.length
    have completed := aligned_work_then_absorb_completes_pair transitionFuel
      (exactPlainRomCursor configuration sample.1).erase rootRecords before
      middle after digest nonce workAnswer q16Base workActor absorbActor
      workFirst' aligned rootOnly rootNodup
    let completedPrefix :=
      before ++ workRecord :: middle ++ [absorbRecord]
    have rootSplit : rootRecords = completedPrefix ++ after := by
      simpa only [completedPrefix, List.nil_append, List.cons_append,
        List.append_assoc] using workFirst'
    have anchorBeforeEnd : trial.val < completedPrefix.length := by
      simp [trial, completedPrefix]
    refine ⟨digest, workAnswer, q16Base, trial, completedPrefix, after,
      emptyRawQ16Branches, workAccepted, q16BaseExact, rootSplit,
      anchorBeforeEnd, ?_⟩
    simpa [trial, nonce, key, completedPrefix, workRecord, absorbRecord,
      exactPairControllerInitialState, UnifiedExposureRecord.answer,
      indexed_state_after_records_append] using completed
  · let absorbRecord : UnifiedExposureRecord :=
      .machineFresh absorbActor key.absorbInput q16Base
    let workRecord : UnifiedExposureRecord :=
      .machineFresh workActor key.workInput workAnswer
    have absorbFirst' : rootRecords =
        before ++ absorbRecord :: middle ++ workRecord :: after := by
      simpa only [rootRecords, nonce, key, absorbRecord, workRecord] using
        absorbFirst
    have trialBound : before.length <
        unifiedFull256ExposureCap parameters :=
      exact_root_strict_prefix_lt_exposure_cap input before
        (middle ++ workRecord :: after) absorbRecord (by
          simpa only [List.cons_append, List.append_assoc] using absorbFirst')
    let trial : ExactCompilerExposureTrial parameters :=
      ⟨before.length, trialBound⟩
    have aligned := exact_root_records_aligned_for_candidate_controller input
      before.length
    obtain ⟨branches, completed⟩ :=
      aligned_absorb_then_work_completes_pair transitionFuel
        (exactPlainRomCursor configuration sample.1).erase rootRecords before
        middle after digest nonce workAnswer q16Base workActor absorbActor
        absorbFirst' aligned rootOnly rootNodup
    let completedPrefix :=
      before ++ absorbRecord :: middle ++ [workRecord]
    have rootSplit : rootRecords = completedPrefix ++ after := by
      simpa only [completedPrefix, List.nil_append, List.cons_append,
        List.append_assoc] using absorbFirst'
    have anchorBeforeEnd : trial.val < completedPrefix.length := by
      simp [trial, completedPrefix]
    refine ⟨digest, workAnswer, q16Base, trial, completedPrefix, after,
      branches, workAccepted, q16BaseExact, rootSplit, anchorBeforeEnd, ?_⟩
    simpa [trial, nonce, key, completedPrefix, absorbRecord, workRecord,
      exactPairControllerInitialState, UnifiedExposureRecord.answer,
      indexed_state_after_records_append] using completed

#print axioms projected_machine_fresh_causal_inputs
#print axioms exact_root_record_causal_inputs_nodup
#print axioms exact_root_records_only_machine_fresh
#print axioms strict_record_middle_avoids_second_input
#print axioms aligned_work_then_absorb_completes_pair
#print axioms aligned_absorb_then_work_completes_pair
#print axioms exactPairControllerInitialState
#print axioms exact_root_records_aligned_for_candidate_controller
#print axioms exact_root_strict_prefix_lt_exposure_cap
#print axioms
  exact_compiler_accepted_final_work_pair_controller_completes

end

end AspisK1.V7Tag73ExactFinalWorkPairControllerCompletion
