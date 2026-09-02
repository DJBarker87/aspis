import AspisFormal.K1.V7Tag73FoldArmedAlphaZeroController
import AspisFormal.K1.V7Tag73ExactAcceptedFoldTrialPackage

/-!
# Exact-source alignment for the fold-armed alpha controller

This module connects the answer-independent controller to the literal accepted
root.  Replaying the exact root prefix reaches the selected fold-work record;
the record's pre-answer input then arms precisely the deployed fold-nonce
absorption.  The result closes the boundary-ordinal mismatch without fixing a
tape-dependent ordinal in the probability router.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactFoldArmedAlphaSourceAlignment

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactFinalWorkPairControllerCompletion
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactProbabilityCoverageAudit
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- The exact accepted root is cursor-aligned with the fold-armed controller.
This is controller-independent scheduler replay specialized to the new
memory. -/
theorem exact_root_records_aligned_for_fold_armed_controller
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
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters) :
    IndexedRecordsAligned transitionFuel
      (foldArmedCompleteController transitionFuel foldTrial.val finalTrial.val)
      (foldArmedInitialState
        (exactPlainRomCursor configuration sample.1).erase)
      (exactFixedRootRecords input.package.root) := by
  let controller := foldArmedCompleteController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel foldTrial.val finalTrial.val
  let initial := foldArmedInitialState
    (exactPlainRomCursor configuration sample.1).erase
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
    controller initial rootTape
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
    initial (runExactPlainRom transitionFuel configuration sample).trace []
    (exactFixedRootRecords input.package.root)
    (exactFixedComputedClientTailRun transitionFuel configuration sample
      input.package.root).trace fullAligned fullSplit
  simpa only [indexed_state_after_records_nil, controller, initial] using
    rootAligned

/-- At the exact selected fold-work record, the complete controller arms the
literal fold-nonce absorption input. -/
theorem exact_accepted_fold_record_arms_alpha_boundary
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
    let initial := foldArmedInitialState
      (exactPlainRomCursor configuration sample.1).erase
    let reached := indexedStateAfterRecords transitionFuel controller
      fold.prior initial
    (controller.afterMemory reached fold.answer).2.1.expectedBoundary =
      some (bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
        bytes (exactOperationalTape input).messages.foldGrinding.selected) := by
  let controller := foldArmedCompleteController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel fold.trial.val finalTrial.val
  let initial := foldArmedInitialState
    (exactPlainRomCursor configuration sample.1).erase
  let reached := indexedStateAfterRecords transitionFuel controller
    fold.prior initial
  have aligned := exact_root_records_aligned_for_fold_armed_controller input
    fold.trial finalTrial
  have selectedAligned :
      unifiedRecordAtAnswer transitionFuel reached.cursor fold.answer =
        (.machineFresh fold.actor
          (bytes fold.digest ++ [domGrind] ++
            bytes (exactOperationalTape input).messages.foldGrinding.selected)
          fold.answer : UnifiedExposureRecord) := by
    exact aligned fold.prior _ fold.later fold.rootDecomposition
  have inputExact : unifiedInputBeforeAnswer? transitionFuel reached.cursor =
      some (bytes fold.digest ++ [domGrind] ++
        bytes (exactOperationalTape input).messages.foldGrinding.selected) :=
    aligned_machine_record_has_exact_input transitionFuel reached.cursor
      fold.actor _ fold.answer selectedAligned
  have atFold : reached.exposureIndex = fold.trial.val := by
    have count := indexed_state_after_records_exposure_index transitionFuel
      controller fold.prior initial
    simpa [reached, initial, foldArmedInitialState, fold.trialExact] using count
  exact fold_armed_complete_literal_fold_step_arms_boundary transitionFuel
    fold.trial.val finalTrial.val reached fold.digest fold.answer
    (exactOperationalTape input).messages.foldGrinding.selected atFold inputExact

/-- The exact fold-nonce boundary first creation is causally comparable with
the selected fold-work record.  It is either already present in the root
prefix visible at the fold exposure, or occurs in the remaining root suffix.
The middle case is impossible because the two literal inputs have distinct
domain bytes (`domGrind = 3`, `domAbsorb = 0`). -/
theorem exact_accepted_fold_boundary_record_before_or_after
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
    (fold : ExactAcceptedFoldTrial input) :
    ∃ boundaryActor,
      (.machineFresh boundaryActor
          (bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
            bytes (exactOperationalTape input).messages.foldGrinding.selected)
          fold.boundaryAnswer : UnifiedExposureRecord) ∈ fold.prior ∨
      (.machineFresh boundaryActor
          (bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
            bytes (exactOperationalTape input).messages.foldGrinding.selected)
          fold.boundaryAnswer : UnifiedExposureRecord) ∈ fold.later := by
  let boundaryInput : ShaInput :=
    bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
      bytes (exactOperationalTape input).messages.foldGrinding.selected
  obtain ⟨boundaryActor, boundaryMember⟩ :=
    exact_final_table_lookup_has_root_record input boundaryInput
      fold.boundaryAnswer (by simpa [boundaryInput] using fold.boundaryLookup)
  rw [fold.rootDecomposition] at boundaryMember
  rcases List.mem_append.mp boundaryMember with before | selectedOrAfter
  · exact ⟨boundaryActor, Or.inl before⟩
  · rcases List.mem_cons.mp selectedOrAfter with selected | after
    · have inputEqual :
          boundaryInput =
            bytes fold.digest ++ [domGrind] ++
              bytes (exactOperationalTape input).messages.foldGrinding.selected := by
        injection selected
      have domainEqual := congrArg (fun input : ShaInput => input[32]?) inputEqual
      norm_num [boundaryInput, bytes_length, domAbsorb, domGrind] at domainEqual
      exact ((by decide : (0 : UInt8) ≠ 3) domainEqual).elim
    · exact ⟨boundaryActor, Or.inr after⟩

/-- A selected aligned machine-fresh record exposes its exact input through
the machine-only pre-answer view used by causal memory. -/
theorem aligned_machine_record_has_exact_machine_fresh_input
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (cursor : UnifiedExposureCursor globalOracleCalls)
    (actor : QueryActor) (input : ShaInput) (answer : Digest256)
    (aligned : unifiedRecordAtAnswer transitionFuel cursor answer =
      .machineFresh actor input answer) :
    unifiedMachineFreshInputBefore? transitionFuel cursor = some input := by
  unfold unifiedRecordAtAnswer at aligned
  unfold unifiedMachineFreshInputBefore?
  generalize requestExact : seekUnifiedExposure transitionFuel cursor = request
  cases request <;> simp_all

def machineFreshInput? : UnifiedExposureRecord → Option ShaInput
  | .machineFresh _actor input _answer => some input
  | .padding _ | .forkOutput .. | .forkAdvance _ => none

def machineFreshPair? (record : UnifiedExposureRecord) :
    Option (ShaInput × Digest256) :=
  (machineFreshInput? record).map (fun input => (input, record.answer))

theorem aligned_record_machine_fresh_input_exact
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (cursor : UnifiedExposureCursor globalOracleCalls)
    (record : UnifiedExposureRecord)
    (aligned : unifiedRecordAtAnswer transitionFuel cursor record.answer =
      record) :
    unifiedMachineFreshInputBefore? transitionFuel cursor =
      machineFreshInput? record := by
  unfold unifiedRecordAtAnswer at aligned
  unfold unifiedMachineFreshInputBefore?
  generalize requestExact : seekUnifiedExposure transitionFuel cursor = request
  cases request <;> cases record <;> simp_all [machineFreshInput?]

/-- Before the selected fold ordinal, one aligned controller step appends
exactly the current machine-fresh pair and nothing for fork/padding records. -/
theorem fold_armed_before_fold_seen_machine_step_exact
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalWorkAnchorIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedCompleteMemory)
    (record : UnifiedExposureRecord)
    (beforeFold : state.exposureIndex ≠ foldExposureIndex)
    (aligned : unifiedRecordAtAnswer transitionFuel state.cursor record.answer =
      record) :
    ((foldArmedCompleteController transitionFuel foldExposureIndex
        finalWorkAnchorIndex).afterMemory state record.answer).2.1.seenMachine =
      state.memory.2.1.seenMachine ++ (machineFreshPair? record).toList := by
  have machineExact := aligned_record_machine_fresh_input_exact transitionFuel
    state.cursor record aligned
  have projectedMachineExact :
      unifiedMachineFreshInputBefore? transitionFuel
          (foldArmedAlphaState state).cursor = machineFreshInput? record := by
    simpa [foldArmedAlphaState, foldArmedUnderlyingState, alphaIndexedState]
      using machineExact
  simp only [foldArmedCompleteController, beforeFold, if_false,
    alpha_final_work_q16_after_memory]
  change
    (foldArmedAlphaAfterMemory transitionFuel (foldArmedAlphaState state)
      record.answer).seenMachine = _
  unfold foldArmedAlphaAfterMemory
  split
  · rename_i _ noCausalInput
    cases record with
    | padding answer =>
        simp [foldArmedAlphaState, foldArmedUnderlyingState,
          alphaIndexedState, machineFreshPair?, machineFreshInput?]
    | machineFresh actor input answer =>
        have machineInput :
            unifiedMachineFreshInputBefore? transitionFuel
                (foldArmedAlphaState state).cursor = some input := by
          simpa [machineFreshInput?] using projectedMachineExact
        have causalInput := unified_machine_fresh_input_is_unified_input
          transitionFuel (foldArmedAlphaState state).cursor input machineInput
        rw [noCausalInput] at causalInput
        cases causalInput
    | forkOutput history outputInput advanceInput template answer =>
        simp [foldArmedAlphaState, foldArmedUnderlyingState,
          alphaIndexedState, machineFreshPair?, machineFreshInput?]
    | forkAdvance scheduled =>
        simp [foldArmedAlphaState, foldArmedUnderlyingState,
          alphaIndexedState, machineFreshPair?, machineFreshInput?]
  · change rememberCurrentMachine transitionFuel (foldArmedAlphaState state)
        record.answer = _
    unfold rememberCurrentMachine
    rw [projectedMachineExact]
    cases record <;> simp [machineFreshPair?, machineFreshInput?,
      foldArmedAlphaState, foldArmedUnderlyingState, alphaIndexedState]

/-- Seen-machine membership is monotone across replayed records. -/
theorem fold_armed_seen_machine_replay_monotone
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalWorkAnchorIndex : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        FoldArmedCompleteMemory)
      (pair : ShaInput × Digest256),
      pair ∈ state.memory.2.1.seenMachine →
      pair ∈
        (indexedStateAfterRecords transitionFuel
          (foldArmedCompleteController transitionFuel foldExposureIndex
            finalWorkAnchorIndex) records state).memory.2.1.seenMachine := by
  intro records
  induction records with
  | nil =>
      intro state pair member
      exact member
  | cons head tail ih =>
      intro state pair member
      rw [indexed_state_after_records_cons]
      apply ih
      exact fold_armed_complete_seen_machine_monotone transitionFuel
        foldExposureIndex finalWorkAnchorIndex state head.answer pair member

/-- An armed boundary remains exact across every post-fold replay prefix. -/
theorem fold_armed_expected_boundary_replay_after_fold
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalWorkAnchorIndex : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        FoldArmedCompleteMemory)
      (target : ShaInput),
      foldExposureIndex < state.exposureIndex →
      state.memory.2.1.expectedBoundary = some target →
      (indexedStateAfterRecords transitionFuel
        (foldArmedCompleteController transitionFuel foldExposureIndex
          finalWorkAnchorIndex) records state).memory.2.1.expectedBoundary =
        some target := by
  intro records
  induction records with
  | nil =>
      intro state target _afterFold armed
      exact armed
  | cons head tail ih =>
      intro state target afterFold armed
      let controller := foldArmedCompleteController
        (globalOracleCalls := globalOracleCalls) transitionFuel
          foldExposureIndex finalWorkAnchorIndex
      let next := controller.afterAnswer transitionFuel state head.answer
      have nextArmed : next.memory.2.1.expectedBoundary = some target := by
        exact (fold_armed_complete_after_fold_preserves_expected_boundary
          transitionFuel foldExposureIndex finalWorkAnchorIndex state
            head.answer afterFold).trans armed
      have nextAfter : foldExposureIndex < next.exposureIndex := by
        simp only [next, controller, indexed_after_answer_exposure_index]
        omega
      rw [indexed_state_after_records_cons]
      exact ih next target nextAfter nextArmed

/-- Exact causal-memory contents at a strict prefix ending at the selected
fold ordinal. -/
theorem aligned_prefix_before_fold_seen_machine_exact
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalWorkAnchorIndex : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        FoldArmedCompleteMemory),
      IndexedRecordsAligned transitionFuel
        (foldArmedCompleteController transitionFuel foldExposureIndex
          finalWorkAnchorIndex) state records →
      state.exposureIndex + records.length = foldExposureIndex →
      (indexedStateAfterRecords transitionFuel
        (foldArmedCompleteController transitionFuel foldExposureIndex
          finalWorkAnchorIndex) records state).memory.2.1.seenMachine =
        state.memory.2.1.seenMachine ++ records.filterMap machineFreshPair? := by
  intro records
  induction records with
  | nil =>
      intro state _aligned _endExact
      simp
  | cons head tail ih =>
      intro state aligned endExact
      let controller := foldArmedCompleteController
        (globalOracleCalls := globalOracleCalls) transitionFuel
          foldExposureIndex finalWorkAnchorIndex
      let next := controller.afterAnswer transitionFuel state head.answer
      have headAligned := aligned [] head tail (by rfl)
      have beforeFold : state.exposureIndex ≠ foldExposureIndex := by
        intro equal
        rw [equal] at endExact
        simp only [List.length_cons] at endExact
        omega
      have stepExact : next.memory.2.1.seenMachine =
          state.memory.2.1.seenMachine ++ (machineFreshPair? head).toList := by
        exact fold_armed_before_fold_seen_machine_step_exact transitionFuel
          foldExposureIndex finalWorkAnchorIndex state head beforeFold
            headAligned
      have tailAligned : IndexedRecordsAligned transitionFuel controller next
          tail := by
        apply indexed_records_aligned_segment transitionFuel controller state
          (head :: tail) [head] tail [] aligned
        simp
      have nextEnd : next.exposureIndex + tail.length = foldExposureIndex := by
        simp only [next, controller, indexed_after_answer_exposure_index,
          List.length_cons] at endExact ⊢
        omega
      rw [indexed_state_after_records_cons]
      rw [ih next tailAligned nextEnd, stepExact]
      cases pairExact : machineFreshPair? head <;>
        simp [List.append_assoc, pairExact]

/-- On a machine-only record list, distinct optional causal inputs imply
distinct raw inputs in the machine-pair projection. -/
theorem machine_only_filter_map_inputs_nodup
    (records : List UnifiedExposureRecord)
    (onlyMachine : OnlyMachineFreshRecords records)
    (nodup : (records.map causalInput?).Nodup) :
    ((records.filterMap machineFreshPair?).map Prod.fst).Nodup := by
  induction records with
  | nil => simp
  | cons head tail ih =>
      obtain ⟨actor, input, answer, headExact⟩ :=
        onlyMachine head (by simp)
      subst head
      have tailOnly : OnlyMachineFreshRecords tail := by
        intro record member
        exact onlyMachine record (by simp [member])
      have splitNodup :
          some input ∉ tail.map causalInput? ∧
            (tail.map causalInput?).Nodup := by
        simpa [causalInput?] using nodup
      have inputFresh : input ∉
          (tail.filterMap machineFreshPair?).map Prod.fst := by
        intro member
        have pairMember := List.mem_map.mp member
        obtain ⟨pair, pairMember, pairInput⟩ := pairMember
        obtain ⟨record, recordMember, pairExact⟩ :=
          List.mem_filterMap.mp pairMember
        obtain ⟨tailActor, tailInput, tailAnswer, recordExact⟩ :=
          tailOnly record recordMember
        subst record
        simp [machineFreshPair?, machineFreshInput?] at pairExact
        subst pair
        apply splitNodup.1
        simp only [List.mem_map]
        exact ⟨.machineFresh tailActor tailInput tailAnswer, recordMember,
          by simpa [causalInput?] using congrArg some pairInput⟩
      change (input ::
        (tail.filterMap machineFreshPair?).map Prod.fst).Nodup
      exact List.nodup_cons.mpr
        ⟨inputFresh, ih tailOnly splitNodup.2⟩

/-- A member of a first-input-nodup causal memory is exactly returned by its
input lookup. -/
theorem seen_machine_answer_exact_of_member
    (memory : FoldArmedAlphaZeroMemory)
    (target : ShaInput) (answer : Digest256)
    (member : (target, answer) ∈ memory.seenMachine)
    (nodup : (memory.seenMachine.map Prod.fst).Nodup) :
    seenMachineAnswer? memory target = some answer := by
  unfold seenMachineAnswer?
  cases found : memory.seenMachine.find? (fun pair => pair.1 = target) with
  | none =>
      have rejected := List.find?_eq_none.mp found (target, answer) member
      simp at rejected
  | some pair =>
      have pairMember : pair ∈ memory.seenMachine :=
        List.mem_of_find?_eq_some found
      have inputExact : pair.1 = target :=
        of_decide_eq_true (List.find?_eq_some_iff_append.mp found).1
      have pairExact : pair = (target, answer) :=
        List.inj_on_of_nodup_map nodup pairMember member inputExact
      subst pair
      simp

/-- Exact machine-memory contents immediately before the retained fold-work
record. -/
theorem exact_fold_reached_seen_machine_exact
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
    let initial := foldArmedInitialState
      (exactPlainRomCursor configuration sample.1).erase
    let reached := indexedStateAfterRecords transitionFuel controller
      fold.prior initial
    reached.memory.2.1.seenMachine =
      fold.prior.filterMap machineFreshPair? := by
  let controller := foldArmedCompleteController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel fold.trial.val finalTrial.val
  let initial := foldArmedInitialState
    (exactPlainRomCursor configuration sample.1).erase
  have rootAligned := exact_root_records_aligned_for_fold_armed_controller input
    fold.trial finalTrial
  have priorAligned : IndexedRecordsAligned transitionFuel controller initial
      fold.prior := by
    apply indexed_records_aligned_segment transitionFuel controller initial
      (exactFixedRootRecords input.package.root) [] fold.prior
      ((.machineFresh fold.actor
        (bytes fold.digest ++ [domGrind] ++
          bytes (exactOperationalTape input).messages.foldGrinding.selected)
        fold.answer : UnifiedExposureRecord) :: fold.later) rootAligned
    simpa [controller, initial] using fold.rootDecomposition
  have endExact : initial.exposureIndex + fold.prior.length = fold.trial.val := by
    simpa [initial, foldArmedInitialState] using fold.trialExact.symm
  have exact := aligned_prefix_before_fold_seen_machine_exact transitionFuel
    fold.trial.val finalTrial.val fold.prior initial priorAligned endExact
  simpa [controller, initial, foldArmedInitialState,
    inactiveFoldArmedAlphaZeroMemory] using exact

/-- Machine inputs remembered at the fold cut are pairwise distinct. -/
theorem exact_fold_reached_seen_machine_inputs_nodup
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
    let initial := foldArmedInitialState
      (exactPlainRomCursor configuration sample.1).erase
    let reached := indexedStateAfterRecords transitionFuel controller
      fold.prior initial
    (reached.memory.2.1.seenMachine.map Prod.fst).Nodup := by
  let selected : UnifiedExposureRecord := .machineFresh fold.actor
    (bytes fold.digest ++ [domGrind] ++
      bytes (exactOperationalTape input).messages.foldGrinding.selected)
    fold.answer
  have rootOnly := exact_root_records_only_machine_fresh input
  have priorOnly : OnlyMachineFreshRecords fold.prior := by
    apply only_machine_fresh_records_segment
      (exactFixedRootRecords input.package.root) [] fold.prior
        (selected :: fold.later) rootOnly
    simpa [selected] using fold.rootDecomposition
  have rootNodup := exact_root_record_causal_inputs_nodup input
  have priorNodup : (fold.prior.map causalInput?).Nodup := by
    rw [fold.rootDecomposition, List.map_append] at rootNodup
    exact (List.nodup_append.mp rootNodup).1
  have filteredNodup := machine_only_filter_map_inputs_nodup fold.prior
    priorOnly priorNodup
  dsimp only
  rw [exact_fold_reached_seen_machine_exact input fold finalTrial]
  exact filteredNodup

/-- If the exact boundary first creation is before fold work, the causal
memory lookup returns its uniquely correct answer. -/
theorem exact_fold_boundary_before_is_cached
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
    (boundaryActor : QueryActor)
    (before :
      (.machineFresh boundaryActor
          (bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
            bytes (exactOperationalTape input).messages.foldGrinding.selected)
          fold.boundaryAnswer : UnifiedExposureRecord) ∈ fold.prior) :
    let controller := foldArmedCompleteController
      (globalOracleCalls := globalFull256OracleCallCap parameters)
      transitionFuel fold.trial.val finalTrial.val
    let initial := foldArmedInitialState
      (exactPlainRomCursor configuration sample.1).erase
    let reached := indexedStateAfterRecords transitionFuel controller
      fold.prior initial
    seenMachineAnswer? reached.memory.2.1
      (bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
        bytes (exactOperationalTape input).messages.foldGrinding.selected) =
      some fold.boundaryAnswer := by
  let target : ShaInput :=
    bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
      bytes (exactOperationalTape input).messages.foldGrinding.selected
  let boundaryRecord : UnifiedExposureRecord :=
    .machineFresh boundaryActor target fold.boundaryAnswer
  have filteredMember : (target, fold.boundaryAnswer) ∈
      fold.prior.filterMap machineFreshPair? := by
    exact List.mem_filterMap.mpr ⟨boundaryRecord, by simpa [boundaryRecord,
      target] using before, by simp [boundaryRecord, target, machineFreshPair?,
        machineFreshInput?, UnifiedExposureRecord.answer]⟩
  have seenExact := exact_fold_reached_seen_machine_exact input fold finalTrial
  have seenMember : (target, fold.boundaryAnswer) ∈
      (indexedStateAfterRecords transitionFuel
        (foldArmedCompleteController transitionFuel fold.trial.val
          finalTrial.val) fold.prior
        (foldArmedInitialState
          (exactPlainRomCursor configuration sample.1).erase)).memory.2.1.seenMachine := by
    rw [seenExact]
    exact filteredMember
  have nodup := exact_fold_reached_seen_machine_inputs_nodup input fold
    finalTrial
  exact seen_machine_answer_exact_of_member _ target fold.boundaryAnswer
    seenMember nodup

/-- If the exact boundary first creation is after fold work, it is absent from
the causal machine memory at the fold cut. -/
theorem exact_fold_boundary_after_is_uncached
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
    (boundaryActor : QueryActor)
    (after :
      (.machineFresh boundaryActor
          (bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
            bytes (exactOperationalTape input).messages.foldGrinding.selected)
          fold.boundaryAnswer : UnifiedExposureRecord) ∈ fold.later) :
    let controller := foldArmedCompleteController
      (globalOracleCalls := globalFull256OracleCallCap parameters)
      transitionFuel fold.trial.val finalTrial.val
    let initial := foldArmedInitialState
      (exactPlainRomCursor configuration sample.1).erase
    let reached := indexedStateAfterRecords transitionFuel controller
      fold.prior initial
    seenMachineAnswer? reached.memory.2.1
      (bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
        bytes (exactOperationalTape input).messages.foldGrinding.selected) =
      none := by
  let target : ShaInput :=
    bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
      bytes (exactOperationalTape input).messages.foldGrinding.selected
  change seenMachineAnswer?
      (indexedStateAfterRecords transitionFuel
        (foldArmedCompleteController transitionFuel fold.trial.val
          finalTrial.val) fold.prior
        (foldArmedInitialState
          (exactPlainRomCursor configuration sample.1).erase)).memory.2.1
        target = none
  let selected : UnifiedExposureRecord := .machineFresh fold.actor
    (bytes fold.digest ++ [domGrind] ++
      bytes (exactOperationalTape input).messages.foldGrinding.selected)
    fold.answer
  have rootNodup := exact_root_record_causal_inputs_nodup input
  rw [fold.rootDecomposition, List.map_append] at rootNodup
  have separated := (List.nodup_append.mp rootNodup).2.2
  have targetInSuffix : some target ∈ (selected :: fold.later).map
      causalInput? := by
    simp only [List.mem_map]
    exact ⟨.machineFresh boundaryActor target fold.boundaryAnswer,
      by simpa [selected, target] using List.mem_cons_of_mem selected after,
      by simp [causalInput?]⟩
  have targetNotPrior : some target ∉ fold.prior.map causalInput? := by
    intro member
    exact separated (some target) member (some target) targetInSuffix rfl
  have seenExact := exact_fold_reached_seen_machine_exact input fold finalTrial
  unfold seenMachineAnswer?
  cases found :
      (indexedStateAfterRecords transitionFuel
        (foldArmedCompleteController transitionFuel fold.trial.val
          finalTrial.val) fold.prior
        (foldArmedInitialState
          (exactPlainRomCursor configuration sample.1).erase)).memory.2.1.seenMachine.find?
        (fun pair => pair.1 = target) with
  | none => simp
  | some pair =>
      have pairMember := List.mem_of_find?_eq_some found
      rw [seenExact] at pairMember
      obtain ⟨record, recordMember, pairExact⟩ :=
        List.mem_filterMap.mp pairMember
      have inputExact : pair.1 = target :=
        of_decide_eq_true (List.find?_eq_some_iff_append.mp found).1
      obtain ⟨actor, recordInput, recordAnswer, recordExact⟩ :=
        exact_root_records_only_machine_fresh input record (by
          rw [fold.rootDecomposition]
          exact List.mem_append_left _ recordMember)
      subst record
      simp [machineFreshPair?, machineFreshInput?] at pairExact
      subst pair
      have forbidden : some target ∈ fold.prior.map causalInput? := by
        simp only [List.mem_map]
        exact ⟨.machineFresh actor recordInput recordAnswer, recordMember,
          by simpa [causalInput?] using congrArg some inputExact⟩
      exact (targetNotPrior forbidden).elim

/-- Exact adversary-first dichotomy at the retained fold-work exposure.  A
prior boundary is installed immediately with its unique source answer;
otherwise the exact boundary remains armed and its first-creation record is
still in the literal root suffix. -/
theorem exact_fold_step_cached_or_future_armed
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
    let initial := foldArmedInitialState
      (exactPlainRomCursor configuration sample.1).erase
    let reached := indexedStateAfterRecords transitionFuel controller
      fold.prior initial
    let afterFold := controller.afterMemory reached fold.answer
    ∃ boundaryActor,
      (({ digest := fold.boundaryAnswer, block := 0,
          sourceInput := bytes fold.digest ++
            [domAbsorb, foldWorkNonceLabel, 0] ++
            bytes (exactOperationalTape input).messages.foldGrinding.selected } :
          AlphaZeroProducer) ∈ afterFold.2.1.alpha.producers) ∨
      (seenMachineAnswer? reached.memory.2.1
          (bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
            bytes (exactOperationalTape input).messages.foldGrinding.selected) =
          none ∧
        afterFold.2.1.expectedBoundary =
          some (bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
            bytes (exactOperationalTape input).messages.foldGrinding.selected) ∧
        (.machineFresh boundaryActor
            (bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
              bytes (exactOperationalTape input).messages.foldGrinding.selected)
            fold.boundaryAnswer : UnifiedExposureRecord) ∈ fold.later) := by
  let controller := foldArmedCompleteController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel fold.trial.val finalTrial.val
  let initial := foldArmedInitialState
    (exactPlainRomCursor configuration sample.1).erase
  let reached := indexedStateAfterRecords transitionFuel controller
    fold.prior initial
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
  obtain ⟨boundaryActor, before | after⟩ :=
    exact_accepted_fold_boundary_record_before_or_after input fold
  · have cached := exact_fold_boundary_before_is_cached input fold finalTrial
      boundaryActor before
    refine ⟨boundaryActor, Or.inl ?_⟩
    exact fold_armed_complete_literal_fold_step_cached_contains_block_zero
      transitionFuel fold.trial.val finalTrial.val reached fold.digest
        fold.answer fold.boundaryAnswer
        (exactOperationalTape input).messages.foldGrinding.selected atFold
          inputExact cached
  · have uncached := exact_fold_boundary_after_is_uncached input fold
      finalTrial boundaryActor after
    have armed := exact_accepted_fold_record_arms_alpha_boundary input fold
      finalTrial
    refine ⟨boundaryActor, Or.inr ⟨uncached, ?_, after⟩⟩
    simpa [controller, initial, reached] using armed

/-- In the future-boundary branch, literal replay reaches that exact record
with the boundary still armed and installs its source answer as alpha block
zero. -/
theorem exact_future_fold_boundary_installs_block_zero
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
    (boundaryActor : QueryActor)
    (after :
      (.machineFresh boundaryActor
          (bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
            bytes (exactOperationalTape input).messages.foldGrinding.selected)
          fold.boundaryAnswer : UnifiedExposureRecord) ∈ fold.later) :
    ∃ beforeBoundary afterBoundary,
      fold.later = beforeBoundary ++
        (.machineFresh boundaryActor
          (bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
            bytes (exactOperationalTape input).messages.foldGrinding.selected)
          fold.boundaryAnswer : UnifiedExposureRecord) :: afterBoundary ∧
      let controller := foldArmedCompleteController
        (globalOracleCalls := globalFull256OracleCallCap parameters)
        transitionFuel fold.trial.val finalTrial.val
      let initial := foldArmedInitialState
        (exactPlainRomCursor configuration sample.1).erase
      let reachedFold := indexedStateAfterRecords transitionFuel controller
        fold.prior initial
      let afterFold := controller.afterAnswer transitionFuel reachedFold
        fold.answer
      let reachedBoundary := indexedStateAfterRecords transitionFuel controller
        beforeBoundary afterFold
      (controller.afterMemory reachedBoundary fold.boundaryAnswer).2.1.alpha.producers =
        [⟨fold.boundaryAnswer, 0,
          bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
            bytes (exactOperationalTape input).messages.foldGrinding.selected⟩] := by
  obtain ⟨beforeBoundary, afterBoundary, laterExact⟩ :=
    (List.mem_iff_append).mp after
  refine ⟨beforeBoundary, afterBoundary, laterExact, ?_⟩
  let controller := foldArmedCompleteController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel fold.trial.val finalTrial.val
  let initial := foldArmedInitialState
    (exactPlainRomCursor configuration sample.1).erase
  let reachedFold := indexedStateAfterRecords transitionFuel controller
    fold.prior initial
  let afterFold := controller.afterAnswer transitionFuel reachedFold fold.answer
  let reachedBoundary := indexedStateAfterRecords transitionFuel controller
    beforeBoundary afterFold
  have rootAligned := exact_root_records_aligned_for_fold_armed_controller input
    fold.trial finalTrial
  let selected : UnifiedExposureRecord := .machineFresh fold.actor
    (bytes fold.digest ++ [domGrind] ++
      bytes (exactOperationalTape input).messages.foldGrinding.selected)
    fold.answer
  have laterAligned : IndexedRecordsAligned transitionFuel controller afterFold
      fold.later := by
    have raw := indexed_records_aligned_segment transitionFuel controller
      initial (exactFixedRootRecords input.package.root)
        (fold.prior ++ [selected]) fold.later [] rootAligned (by
          rw [fold.rootDecomposition]
          simp [selected])
    simpa [afterFold, reachedFold, selected,
      indexed_state_after_records_append, UnifiedExposureRecord.answer] using raw
  have boundaryAligned :
      unifiedRecordAtAnswer transitionFuel reachedBoundary.cursor
          fold.boundaryAnswer =
        (.machineFresh boundaryActor
          (bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
            bytes (exactOperationalTape input).messages.foldGrinding.selected)
          fold.boundaryAnswer : UnifiedExposureRecord) := by
    exact laterAligned beforeBoundary _ afterBoundary laterExact
  have boundaryInputExact :
      unifiedInputBeforeAnswer? transitionFuel reachedBoundary.cursor =
        some (bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
          bytes (exactOperationalTape input).messages.foldGrinding.selected) :=
    aligned_machine_record_has_exact_input transitionFuel reachedBoundary.cursor
      boundaryActor _ fold.boundaryAnswer boundaryAligned
  have armedAfterFold : afterFold.memory.2.1.expectedBoundary =
      some (bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
        bytes (exactOperationalTape input).messages.foldGrinding.selected) := by
    have armed := exact_accepted_fold_record_arms_alpha_boundary input fold
      finalTrial
    simpa [controller, initial, reachedFold, afterFold,
      IndexedUnifiedExposureController.afterAnswer] using armed
  have afterFoldIndex : fold.trial.val < afterFold.exposureIndex := by
    have count := indexed_state_after_records_exposure_index transitionFuel
      controller fold.prior initial
    simp only [afterFold, indexed_after_answer_exposure_index]
    have reachedIndex : reachedFold.exposureIndex = fold.trial.val := by
      simpa [reachedFold, initial, foldArmedInitialState, fold.trialExact]
        using count
    rw [reachedIndex]
    omega
  have armedAtBoundary : reachedBoundary.memory.2.1.expectedBoundary =
      some (bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
        bytes (exactOperationalTape input).messages.foldGrinding.selected) := by
    exact fold_armed_expected_boundary_replay_after_fold transitionFuel
      fold.trial.val finalTrial.val beforeBoundary afterFold _ afterFoldIndex
        armedAfterFold
  have boundaryAfterFold : fold.trial.val < reachedBoundary.exposureIndex := by
    have count := indexed_state_after_records_exposure_index transitionFuel
      controller beforeBoundary afterFold
    rw [count]
    omega
  exact fold_armed_complete_after_fold_boundary_installs_block_zero
    transitionFuel fold.trial.val finalTrial.val reachedBoundary _
      fold.boundaryAnswer boundaryAfterFold boundaryInputExact armedAtBoundary

/-- Every literal machine record in an aligned strict prefix ending at the
selected fold ordinal is present in the causal seen-machine memory at that
cut.  This is the deterministic adversary-first cache bridge. -/
theorem aligned_prefix_before_fold_remembers_machine_record
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalWorkAnchorIndex : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        FoldArmedCompleteMemory)
      (actor : QueryActor) (input : ShaInput) (answer : Digest256),
      IndexedRecordsAligned transitionFuel
        (foldArmedCompleteController transitionFuel foldExposureIndex
          finalWorkAnchorIndex) state records →
      state.exposureIndex + records.length = foldExposureIndex →
      (.machineFresh actor input answer : UnifiedExposureRecord) ∈ records →
      (input, answer) ∈
        (indexedStateAfterRecords transitionFuel
          (foldArmedCompleteController transitionFuel foldExposureIndex
            finalWorkAnchorIndex) records state).memory.2.1.seenMachine := by
  intro records
  induction records with
  | nil =>
      intro state actor input answer _aligned _endExact member
      simp at member
  | cons head tail ih =>
      intro state actor input answer aligned endExact member
      let controller := foldArmedCompleteController
        (globalOracleCalls := globalOracleCalls) transitionFuel
          foldExposureIndex finalWorkAnchorIndex
      let next := controller.afterAnswer transitionFuel state head.answer
      have tailAligned : IndexedRecordsAligned transitionFuel controller next
          tail := by
        apply indexed_records_aligned_segment transitionFuel controller state
          (head :: tail) [head] tail [] aligned
        simp
      have nextEnd : next.exposureIndex + tail.length = foldExposureIndex := by
        simp only [next, controller, indexed_after_answer_exposure_index,
          List.length_cons] at endExact ⊢
        omega
      simp only [List.mem_cons] at member
      rcases member with headExact | tailMember
      · subst head
        have selectedAligned := aligned []
          (.machineFresh actor input answer) tail (by rfl)
        have inputExact :
            unifiedMachineFreshInputBefore? transitionFuel state.cursor =
            some input := by
          simpa only [indexed_state_after_records_nil] using
            aligned_machine_record_has_exact_machine_fresh_input
              transitionFuel state.cursor
              actor input answer selectedAligned
        have beforeFold : state.exposureIndex ≠ foldExposureIndex := by
          intro equal
          rw [equal] at endExact
          simp only [List.length_cons] at endExact
          omega
        have remembered : (input, answer) ∈ next.memory.2.1.seenMachine := by
          exact fold_armed_complete_before_fold_remembers_current_machine
            transitionFuel foldExposureIndex finalWorkAnchorIndex state input
              answer beforeFold inputExact
        rw [indexed_state_after_records_cons]
        exact fold_armed_seen_machine_replay_monotone transitionFuel
          foldExposureIndex finalWorkAnchorIndex tail next (input, answer)
            remembered
      · rw [indexed_state_after_records_cons]
        exact ih next actor input answer tailAligned nextEnd tailMember

#print axioms exact_root_records_aligned_for_fold_armed_controller
#print axioms exact_accepted_fold_record_arms_alpha_boundary
#print axioms exact_accepted_fold_boundary_record_before_or_after
#print axioms aligned_prefix_before_fold_remembers_machine_record
#print axioms exact_fold_step_cached_or_future_armed
#print axioms exact_future_fold_boundary_installs_block_zero

end

end AspisK1.V7Tag73ExactFoldArmedAlphaSourceAlignment
