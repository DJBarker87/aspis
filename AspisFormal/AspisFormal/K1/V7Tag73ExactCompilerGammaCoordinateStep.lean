import AspisFormal.K1.V7Tag73ExactCompilerGammaCachedCoordinate
import AspisFormal.K1.V7Tag73SchedulerNativePausePrefixBridge

/-!
# Exact compiler gamma coordinate step

This leaf begins the future-fresh half of the exact compiler replay.  It first
proves the purely chronological fact needed by the executable scanner: if a
final production-table coordinate is absent at an aligned cursor, its literal
input/answer pair lies in the remaining root suffix, not in the consumed
prefix.  The proof uses the exact root split and immutable table projection;
it does not classify the SHA input by protocol role.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactCompilerGammaCoordinateStep

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73SourceAnchoredSchedulerCut
open AspisK1.V7Tag73ExactCompilerSourceAnchoredCut
open AspisK1.V7Tag73ExactCompilerGammaCachedCoordinate
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73SharedOracleVerifierRunner
open AspisK1.V7Tag73SchedulerNativeTargetPause
open AspisK1.V7Tag73SchedulerNativePausePrefixBridge
open AspisK1.V7Tag73SchedulerNativePrefixTraversal

noncomputable section

/-- At every aligned cursor the literal final root oracle is the current
immutable table followed by exactly the remaining chronological fresh suffix.
This is the table-level source equation used by both cache and future cases. -/
theorem exact_compiler_aligned_final_oracle_table_extension
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
    (state : SchedulerNativeGammaCursor
      (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement
        Tag73K12ParsedProof Payload Result))
    (aligned : ExactCompilerRootGammaCursorAligned input state) :
    input.package.root.full.projection.rootPrefixes.verifier.finalState.table =
      state.oracle.table ++ aligned.future.map projectedFreshEntry := by
  let prefixes := input.package.root.full.projection.rootPrefixes
  have adversaryTable := projected_machine_prefix_table_eq_fresh_coordinates
    configuration.machine.adversaryLimits .adversary
    configuration.machine.adversaryFuel emptyOracle
    (AspisK1.V7Tag73ConcreteRestorationClient.schedulerStageProgram
      (SchedulerNativePlainRomResult TapeIdentity Statement
        Tag73K12ParsedProof Payload Result)
      (AspisK1.V7Tag73ConcreteRestorationClient.totalizeOracleMachine
        configuration.machine.adversaryFuel
        (configuration.machine.blackBox.start sample.1
          configuration.machine.observation)))
    (AspisK1.V7Tag73OperationalOracleExposure.freshAnswerTapeToList sample.2)
    prefixes.adversary
  have verifierTable := projected_machine_prefix_table_eq_fresh_coordinates
    configuration.machine.verifierLimits .verifier
    configuration.machine.verifierFuel prefixes.adversary.finalState
    (AspisK1.V7Tag73ConcreteRestorationClient.schedulerStageProgram
      (SchedulerNativePlainRomResult TapeIdentity Statement
        Tag73K12ParsedProof Payload Result)
      (AspisK1.V7Tag73ConcreteRestorationClient.totalizeOracleMachine
        configuration.machine.verifierFuel
        (initialRawFutureFreeProgram configuration.machine.environment
          prefixes.adversaryValue.rawMessages
          configuration.machine.driverFuel)))
    prefixes.adversary.remaining prefixes.verifier
  change prefixes.verifier.finalState.table = _
  calc
    prefixes.verifier.finalState.table =
        prefixes.adversary.finalState.table ++
          prefixes.verifier.freshQueries.map projectedFreshEntry := by
            change prefixes.verifier.finalState.table =
              prefixes.adversary.finalState.table ++
                prefixes.verifier.freshQueries.map projectedFreshEntry
              at verifierTable
            exact verifierTable
    _ = (emptyOracle.table ++
          prefixes.adversary.freshQueries.map projectedFreshEntry) ++
          prefixes.verifier.freshQueries.map projectedFreshEntry := by
            rw [adversaryTable]
            rfl
    _ = (prefixes.adversary.freshQueries ++
          prefixes.verifier.freshQueries).map projectedFreshEntry := by
            simp [emptyOracle, List.map_append]
    _ = (aligned.consumed ++ aligned.future).map projectedFreshEntry := by
            rw [aligned.rootSplit]
    _ = state.oracle.table ++ aligned.future.map projectedFreshEntry := by
            rw [List.map_append, ← aligned.tableExact]

/-- An aligned retained cache hit has the same output as the actual final
compiler table.  This follows from append-only table extension, not from an
independence or logical-role premise. -/
theorem exact_compiler_aligned_cached_answer_exact
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
    (state : SchedulerNativeGammaCursor
      (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement
        Tag73K12ParsedProof Payload Result))
    (aligned : ExactCompilerRootGammaCursorAligned input state)
    (expectedInput : ShaInput) (expectedAnswer : Digest256)
    (entry : AspisK1.V7FsAokExperiment.TableEntry)
    (cached : lookupEntry state.oracle expectedInput = some entry)
    (found : tableLookup (exactOperationalTable input) expectedInput =
      some expectedAnswer) :
    entry.output = expectedAnswer := by
  let prefixes := input.package.root.full.projection.rootPrefixes
  have runtimeExact : (exactK12Runtime input).verifierFinalOracle =
      prefixes.verifier.finalState := by
    have exact := congrArg
      (fun runtime => runtime.verifierFinalOracle) prefixes.runtimeExact
    simpa [exactK12Runtime, prefixes, operationalRootRuntime] using exact
  have finalSelected :
      lookupEntry prefixes.verifier.finalState expectedInput = some entry := by
    unfold lookupEntry at cached ⊢
    rw [exact_compiler_aligned_final_oracle_table_extension input state aligned,
      List.find?_append, cached]
    rfl
  have finalFound :
      (lookupEntry prefixes.verifier.finalState expectedInput).map
          AspisK1.V7FsAokExperiment.TableEntry.output = some expectedAnswer := by
    change tableLookup
        (AspisK1.V7Tag73CoupledReplayAlignment.fixedTableOfOracleState
          (exactK12Runtime input).verifierFinalOracle) expectedInput =
        some expectedAnswer at found
    rw [fixed_table_lookup_eq_lookup_entry_output] at found
    change (lookupEntry (exactK12Runtime input).verifierFinalOracle
      expectedInput).map AspisK1.V7FsAokExperiment.TableEntry.output =
        some expectedAnswer at found
    rwa [runtimeExact] at found
  rw [finalSelected] at finalFound
  simpa using finalFound

/-- A literal projected entry in the consumed list contradicts a missing
lookup in the exact projected table.  No uniqueness of logical owner or
answer independence is used. -/
theorem projected_fresh_pair_not_mem_of_lookup_missing
    (state : OracleState) (consumed : List (ShaInput × Digest256))
    (input : ShaInput) (answer : Digest256)
    (tableExact : state.table = consumed.map projectedFreshEntry)
    (missing : lookupEntry state input = none) :
    (input, answer) ∉ consumed := by
  intro member
  have mappedMember : projectedFreshEntry (input, answer) ∈ state.table := by
    rw [tableExact]
    exact List.mem_map.mpr ⟨(input, answer), member, rfl⟩
  unfold lookupEntry at missing
  have rejected := List.find?_eq_none.mp missing
    (projectedFreshEntry (input, answer)) mappedMember
  simp [projectedFreshEntry] at rejected

/-- Cursor-relative source routing at an evolving exact compiler cut.  A
coordinate in the actual final verifier table that is not cached at this cut
must occur in the chronological root suffix still ahead of the cursor. -/
theorem exact_compiler_aligned_missing_coordinate_mem_future
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
    (state : SchedulerNativeGammaCursor
      (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement
        Tag73K12ParsedProof Payload Result))
    (aligned : ExactCompilerRootGammaCursorAligned input state)
    (expectedInput : ShaInput) (expectedAnswer : Digest256)
    (missing : lookupEntry state.oracle expectedInput = none)
    (found : tableLookup (exactOperationalTable input) expectedInput =
      some expectedAnswer) :
    (expectedInput, expectedAnswer) ∈ aligned.future := by
  have rootMember :
      (expectedInput, expectedAnswer) ∈
        input.package.root.full.projection.rootPrefixes.adversary.freshQueries ++
          input.package.root.full.projection.rootPrefixes.verifier.freshQueries := by
    exact List.mem_append.mpr
      (exact_compiler_final_lookup_in_ordered_root_suffix input expectedInput
        expectedAnswer found)
  have splitMember :
      (expectedInput, expectedAnswer) ∈ aligned.consumed ++ aligned.future := by
    rw [← aligned.rootSplit]
    exact rootMember
  rcases List.mem_append.mp splitMember with consumed | future
  · exact (projected_fresh_pair_not_mem_of_lookup_missing state.oracle
      aligned.consumed expectedInput expectedAnswer aligned.tableExact missing
      consumed).elim
  · exact future

/-- Generic preservation theorem for the future-fresh branch.  The remaining
source-specific work is precisely to identify the scanner's consumed answers
and pre-target request table with a chronological prefix of `aligned.future`.
Once those executable equalities are known, the selected actual answer extends
all four alignment components by the same literal prefix. -/
theorem exact_compiler_aligned_future_pause_preserves_alignment
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
    (state : SchedulerNativeGammaCursor
      (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement
        Tag73K12ParsedProof Payload Result))
    (aligned : ExactCompilerRootGammaCursorAligned input state)
    (kind : SchedulerNativeGammaQueryKind)
    (expectedInput : ShaInput) (expectedAnswer : Digest256)
    (prior later : List (ShaInput × Digest256))
    (futureExact : aligned.future =
      prior ++ (expectedInput, expectedAnswer) :: later)
    (missing : lookupEntry state.oracle expectedInput = none)
    (pause : SchedulerNativeFreshPause
      (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement
        Tag73K12ParsedProof Payload Result) expectedInput)
    (paused : scanSchedulerNativeToInput transitionFuel expectedInput
      state.cursor state.remainingAnswers = .paused pause)
    (targetAnswerExact : pause.targetAnswer = expectedAnswer)
    (consumedAnswersExact : pause.consumedAnswers = prior.map Prod.snd)
    (requestTableExact : pause.requestState.table =
      state.oracle.table ++ prior.map projectedFreshEntry) :
    ∃ nextState,
      consumeSchedulerNativeGammaCoordinate transitionFuel kind expectedInput
          expectedAnswer state = .ok nextState ∧
      Nonempty (ExactCompilerRootGammaCursorAligned input nextState) := by
  let nextState : SchedulerNativeGammaCursor
      (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement
        Tag73K12ParsedProof Payload Result) :=
    { cursor := pause.resumeCursorWith expectedAnswer
      remainingAnswers := pause.remainingAnswers
      oracle := freshQueryState pause.actor pause.requestState pause.input
        expectedAnswer
      tracePrefix := state.tracePrefix ++ pause.consumedTrace ++
        [machineFreshRecord pause expectedAnswer] }
  have consumedInputExact : pause.input = expectedInput := pause.input_eq_target
  have consumeExact :
      consumeSchedulerNativeGammaCoordinate transitionFuel kind expectedInput
          expectedAnswer state = .ok nextState := by
    simpa [nextState] using
      consume_scheduler_native_gamma_fresh_uses_exact_pause_actor
        transitionFuel kind expectedInput expectedAnswer state missing pause
          paused
  have answersSplit : state.remainingAnswers =
      pause.consumedAnswers ++
        pause.targetAnswer :: pause.remainingAnswers :=
    scan_scheduler_native_to_input_paused_answers_exact transitionFuel
      expectedInput state.cursor state.remainingAnswers pause paused
  have remainingExact : pause.remainingAnswers =
      later.map Prod.snd ++
        input.package.root.full.projection.rootPrefixes.verifier.remaining := by
    have equal :
        prior.map Prod.snd ++ expectedAnswer ::
            (later.map Prod.snd ++
              input.package.root.full.projection.rootPrefixes.verifier.remaining) =
          prior.map Prod.snd ++ expectedAnswer :: pause.remainingAnswers := by
      calc
        prior.map Prod.snd ++ expectedAnswer ::
              (later.map Prod.snd ++
                input.package.root.full.projection.rootPrefixes.verifier.remaining) =
            aligned.future.map Prod.snd ++
              input.package.root.full.projection.rootPrefixes.verifier.remaining := by
                rw [futureExact]
                simp [List.map_append, List.append_assoc]
        _ = state.remainingAnswers := aligned.answersExact.symm
        _ = pause.consumedAnswers ++
              pause.targetAnswer :: pause.remainingAnswers := answersSplit
        _ = prior.map Prod.snd ++ expectedAnswer :: pause.remainingAnswers := by
              rw [consumedAnswersExact, targetAnswerExact]
    exact (List.cons.inj (List.append_cancel_left equal) |>.2).symm
  let nextConsumed := aligned.consumed ++ prior ++
    [(expectedInput, expectedAnswer)]
  have nextRootSplit :
      input.package.root.full.projection.rootPrefixes.adversary.freshQueries ++
          input.package.root.full.projection.rootPrefixes.verifier.freshQueries =
        nextConsumed ++ later := by
    rw [aligned.rootSplit, futureExact]
    simp [nextConsumed, List.append_assoc]
  have nextCursorExact : nextState.cursor =
      schedulerNativePrefixCursor transitionFuel
        (exactPlainRomCursor configuration sample.1)
        (nextConsumed.map Prod.snd) := by
    have resumed :=
      scan_scheduler_native_to_input_paused_resume_cursor_with_exact
        transitionFuel expectedInput state.cursor state.remainingAnswers pause
          paused expectedAnswer
    change pause.resumeCursorWith expectedAnswer = _
    rw [resumed, consumedAnswersExact, aligned.cursorExact]
    rw [← scheduler_native_prefix_cursor_append]
    simp [nextConsumed, List.map_append, List.append_assoc]
  have nextTableExact : nextState.oracle.table =
      nextConsumed.map projectedFreshEntry := by
    change (freshQueryState pause.actor pause.requestState pause.input
      expectedAnswer).table = _
    rw [freshQueryState, requestTableExact, aligned.tableExact,
      consumedInputExact]
    simp [nextConsumed, List.map_append, projectedFreshEntry,
      List.append_assoc]
  have nextTraceExact : nextState.tracePrefix =
      schedulerNativePrefixRecords transitionFuel
        (exactPlainRomCursor configuration sample.1)
        (nextConsumed.map Prod.snd) := by
    have records :=
      scan_scheduler_native_to_input_paused_resume_records_exact
        transitionFuel expectedInput state.cursor state.remainingAnswers pause
          paused expectedAnswer
    change state.tracePrefix ++ pause.consumedTrace ++
      [machineFreshRecord pause expectedAnswer] = _
    rw [aligned.traceExact]
    rw [show nextConsumed.map Prod.snd =
        aligned.consumed.map Prod.snd ++
          (prior.map Prod.snd ++ [expectedAnswer]) by
      simp [nextConsumed, List.map_append, List.append_assoc]]
    rw [scheduler_native_prefix_records_append, ← aligned.cursorExact,
      ← consumedAnswersExact, records]
    simp [machineFreshRecord, consumedInputExact, List.append_assoc]
  refine ⟨nextState, consumeExact, ?_⟩
  exact ⟨{
    consumed := nextConsumed
    future := later
    rootSplit := nextRootSplit
    cursorExact := nextCursorExact
    answersExact := remainingExact
    tableExact := nextTableExact
    traceExact := nextTraceExact }⟩

#print axioms projected_fresh_pair_not_mem_of_lookup_missing
#print axioms exact_compiler_aligned_final_oracle_table_extension
#print axioms exact_compiler_aligned_cached_answer_exact
#print axioms exact_compiler_aligned_missing_coordinate_mem_future
#print axioms exact_compiler_aligned_future_pause_preserves_alignment

end

end AspisK1.V7Tag73ExactCompilerGammaCoordinateStep
