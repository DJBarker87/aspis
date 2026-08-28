import AspisFormal.K1.V7Tag73SchedulerNativePausePrefixBridge
import AspisFormal.K1.V7Tag73SourceAnchoredNativeCursorFactorization

/-!
# Seek-aligned scheduler-native pause splitting

The production actor boundary can leave the caller at a cursor which is not
definitionally the literal projected-machine cursor, while normalization of
both cursors exposes the same request.  This file transports the exact
projected fresh-prefix pause split across precisely that executable equality.
No role, probability, or completed-execution classifier is introduced.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73SchedulerNativeAlignedPauseSplit

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerNativeTargetPause
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73SourceAnchoredSchedulerCut
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73SchedulerNativeCachedGammaReplay
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactCompilerSourceAnchoredCut
open AspisK1.V7Tag73SourceAnchoredNativeCursorFactorization
open AspisK1.V7Tag73FullCursorClientLineageLift

noncomputable section

universe u

/-- A seek-aligned cursor has the same exact chronological pause split as the
literal projected machine.  This includes the empty-prior case: the pause is
installed directly at the request exposed across an actor boundary, before
its answer is consumed. -/
theorem projected_fresh_trace_seek_aligned_scan_pauses_with_exact_split
    {globalOracleCalls : Nat} {Final MachineResult : Type u}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (limits : OracleLimits)
    (limitBound : limits.totalCalls ≤ globalOracleCalls)
    (actor : QueryActor)
    (onReturned : (result : MachineResult) → (state : OracleState) →
      HistoryTotalCoherent state → SchedulerNativeCursor globalOracleCalls Final)
    {fuel : Nat} {state : OracleState}
    {program : OracleMachine MachineResult}
    {freshQueries : List (ShaInput × Digest256)}
    {result : MachineResult} {finalState : OracleState} {steps : Nat}
    (coherent : HistoryTotalCoherent state)
    (trace : ProjectedFreshReturnedTrace limits actor fuel state program
      freshQueries result finalState steps)
    (sourceCursor : SchedulerNativeCursor globalOracleCalls Final)
    (aligned : seekSchedulerNativeExposure transitionFuel sourceCursor =
      seekSchedulerNativeExposure transitionFuel
        (.machine limits limitBound actor state program fuel coherent
          onReturned))
    (suffix : List Digest256) (input : ShaInput) (answer : Digest256)
    (future : (input, answer) ∈ freshQueries) :
    ∃ (prior later : List (ShaInput × Digest256))
      (pause : SchedulerNativeFreshPause globalOracleCalls Final input),
      freshQueries = prior ++ (input, answer) :: later ∧
      scanSchedulerNativeToInput transitionFuel input sourceCursor
          (freshQueries.map Prod.snd ++ suffix) = .paused pause ∧
      pause.targetAnswer = answer ∧
      pause.consumedAnswers = prior.map Prod.snd ∧
      pause.remainingAnswers = later.map Prod.snd ++ suffix ∧
      pause.requestState.table =
        state.table ++ prior.map projectedFreshEntry := by
  induction trace generalizing sourceCursor suffix input answer with
  | returned fuel state program traceCoherent result finalState steps sought =>
      simp at future
  | fresh fuel state requestState program traceCoherent headInput nextProgram
      remainingFuel cachedSteps requestCoherent totalRoom freshRoom missing
      sought headAnswer rest result finalState tailSteps tail ih =>
      have coherentExact : coherent = traceCoherent := Subsingleton.elim _ _
      cases coherentExact
      cases transitionFuel with
      | zero => omega
      | succ current =>
          simp only [List.mem_cons, Prod.mk.injEq] at future
          have normalizedLiteral :=
            seek_scheduler_native_exposure_machine_of_fresh current limits
              limitBound actor fuel state requestState program traceCoherent
              headInput nextProgram remainingFuel cachedSteps requestCoherent
              totalRoom freshRoom missing onReturned sought
          have normalizedSource :
              seekSchedulerNativeExposure (Nat.succ current) sourceCursor =
                .machineFresh limits limitBound actor requestState headInput
                  nextProgram remainingFuel requestCoherent totalRoom freshRoom
                  missing onReturned := aligned.trans normalizedLiteral
          rcases future with head | laterMember
          · rcases head with ⟨rfl, rfl⟩
            have prefixTable := seek_next_fresh_oracle_table_eq limits actor
              fuel state program traceCoherent
            rw [sought] at prefixTable
            change requestState.table = state.table at prefixTable
            refine ⟨[], rest, ?_⟩
            simp only [List.map_cons, List.cons_append,
              scanSchedulerNativeToInput, scanSchedulerNativeToInputFrom]
            split <;> rename_i requestExact
            all_goals rw [normalizedSource] at requestExact
            all_goals cases requestExact
            simp [prefixTable]
          · have different : headInput ≠ input := by
              intro equal
              subst input
              have tailMissing :=
                projected_fresh_returned_trace_future_input_missing limits actor
                  remainingFuel
                  (freshQueryState actor requestState headInput headAnswer)
                  (nextProgram headAnswer) rest result finalState tailSteps tail
                  headInput answer laterMember
              unfold lookupEntry freshQueryState at tailMissing
              unfold lookupEntry at missing
              rw [List.find?_append, missing] at tailMissing
              simp at tailMissing
            let nextCursor : SchedulerNativeCursor globalOracleCalls Final :=
              .machine limits limitBound actor
                (freshQueryState actor requestState headInput headAnswer)
                (nextProgram headAnswer) remainingFuel
                (fresh_query_state_preserves_history_total_coherent actor
                  requestState headInput headAnswer requestCoherent)
                onReturned
            obtain ⟨prior, later, pause, decomposition, paused, answerExact,
                consumedExact, remainingExact, requestTableExact⟩ := ih
              (fresh_query_state_preserves_history_total_coherent actor
                requestState headInput headAnswer requestCoherent)
              nextCursor rfl suffix input answer laterMember
            refine ⟨(headInput, headAnswer) :: prior, later,
              pause.prepend headAnswer
                (.machineFresh actor headInput headAnswer), ?_, ?_,
              answerExact, ?_, remainingExact, ?_⟩
            · simpa [List.cons_append] using
                congrArg (List.cons (headInput, headAnswer)) decomposition
            · simp only [List.map_cons, List.cons_append,
                scanSchedulerNativeToInput, scanSchedulerNativeToInputFrom]
              split <;> rename_i requestExact
              all_goals rw [normalizedSource] at requestExact
              all_goals cases requestExact
              split
              · rename_i equal
                exact (different equal).elim
              · rename_i notEqual
                rename_i limitBound2 coherent2 totalRoom2 freshRoom2 missing2
                have limitBoundExact : limitBound2 = limitBound :=
                  Subsingleton.elim _ _
                cases limitBoundExact
                have coherentProofExact : coherent2 = requestCoherent :=
                  Subsingleton.elim _ _
                cases coherentProofExact
                have totalRoomExact : totalRoom2 = totalRoom :=
                  Subsingleton.elim _ _
                cases totalRoomExact
                have freshRoomExact : freshRoom2 = freshRoom :=
                  Subsingleton.elim _ _
                cases freshRoomExact
                have missingExact : missing2 = missing := Subsingleton.elim _ _
                cases missingExact
                unfold scanSchedulerNativeToInput at paused
                simp only [nextCursor] at paused
                simp only [paused]
            · simp [SchedulerNativeFreshPause.prepend, consumedExact]
            · have prefixTable := seek_next_fresh_oracle_table_eq limits actor
                fuel state program traceCoherent
              rw [sought] at prefixTable
              change requestState.table = state.table at prefixTable
              change pause.requestState.table = _
              rw [requestTableExact]
              simp [freshQueryState, prefixTable, projectedFreshEntry,
                List.map_cons, List.append_assoc]

/-! ## Exact compiler verifier phase -/

/-- Exact joined-root pause split once the aligned cursor is in the verifier
phase.  This includes `verifierConsumed = []`, where the cursor is still the
literal adversary predecessor but its normalized request is exactly the first
verifier request. -/
theorem exact_compiler_aligned_verifier_phase_pause_split
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters} {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (state : SchedulerNativeGammaCursor
      (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement
        Tag73K12ParsedProof Payload Result))
    (aligned : ExactCompilerRootGammaCursorAligned input state)
    (verifierConsumed : List (ShaInput × Digest256))
    (consumedExact : aligned.consumed =
      input.package.root.full.projection.rootPrefixes.adversary.freshQueries ++
        verifierConsumed)
    (verifierExact :
      input.package.root.full.projection.rootPrefixes.verifier.freshQueries =
        verifierConsumed ++ aligned.future)
    (expectedInput : ShaInput) (expectedAnswer : Digest256)
    (future : (expectedInput, expectedAnswer) ∈ aligned.future) :
    ∃ (prior later : List (ShaInput × Digest256))
      (pause : SchedulerNativeFreshPause
        (globalFull256OracleCallCap parameters)
        (SchedulerNativePlainRomResult TapeIdentity Statement
          Tag73K12ParsedProof Payload Result) expectedInput),
      aligned.future = prior ++ (expectedInput, expectedAnswer) :: later ∧
      scanSchedulerNativeToInput transitionFuel expectedInput state.cursor
          state.remainingAnswers = .paused pause ∧
      pause.targetAnswer = expectedAnswer ∧
      pause.consumedAnswers = prior.map Prod.snd ∧
      pause.remainingAnswers = later.map Prod.snd ++
        input.package.root.full.projection.rootPrefixes.verifier.remaining ∧
      pause.requestState.table =
        state.oracle.table ++ prior.map projectedFreshEntry := by
  let prefixes := input.package.root.full.projection.rootPrefixes
  let verifierCut := (exactCompilerRootSourceAnchoredCut input).second
  have adversaryTable : prefixes.adversary.finalState.table =
      prefixes.adversary.freshQueries.map projectedFreshEntry := by
    have exact := (exactCompilerRootSourceAnchoredCut input).first.table_exact
    change prefixes.adversary.finalState.table = emptyOracle.table ++
      prefixes.adversary.freshQueries.map projectedFreshEntry at exact
    simpa [emptyOracle] using exact
  have answersExact : state.remainingAnswers =
      aligned.future.map Prod.snd ++ prefixes.verifier.remaining := by
    simpa [prefixes] using aligned.answersExact
  cases verifierConsumed with
  | nil =>
      have verifierNonempty : prefixes.verifier.freshQueries ≠ [] := by
        rw [verifierExact]
        simpa using (List.ne_nil_of_mem future)
      have boundary := exact_compiler_adversary_boundary_seek_eq_verifier
        transitionRoom input verifierNonempty
      have sourceSeek : seekSchedulerNativeExposure transitionFuel state.cursor =
          seekSchedulerNativeExposure transitionFuel
            (SchedulerNativeCursor.machine configuration.machine.verifierLimits
              configuration.rootLimitBounds.verifier .verifier
              verifierCut.state verifierCut.program verifierCut.fuel
              (projected_fresh_returned_trace_start_coherent verifierCut.trace)
              (fullRootVerifierReturnedContinuation configuration sample.1
                prefixes.adversaryValue prefixes.adversary.finalState)) := by
        change seekSchedulerNativeExposure transitionFuel state.cursor =
          seekSchedulerNativeExposure transitionFuel
            (fullRootVerifierCursor configuration sample.1
              prefixes.adversaryValue prefixes.adversary.finalState
              prefixes.adversary.finalCoherent)
        rw [aligned.cursorExact, consumedExact]
        simpa [prefixes] using boundary
      have sourceTable : state.oracle.table = verifierCut.state.table := by
        change state.oracle.table = prefixes.adversary.finalState.table
        rw [aligned.tableExact, consumedExact]
        simpa using adversaryTable.symm
      obtain ⟨prior, later, pause, decomposition, paused, targetAnswer,
          consumedAnswers, remainingAnswers, requestTable⟩ :=
        projected_fresh_trace_seek_aligned_scan_pauses_with_exact_split
          transitionFuel (by omega) configuration.machine.verifierLimits
          configuration.rootLimitBounds.verifier .verifier
          (fullRootVerifierReturnedContinuation configuration sample.1
            prefixes.adversaryValue prefixes.adversary.finalState)
          (projected_fresh_returned_trace_start_coherent verifierCut.trace)
          verifierCut.trace state.cursor sourceSeek prefixes.verifier.remaining
          expectedInput expectedAnswer (by
            simpa [verifierCut, prefixes, verifierExact] using future)
      refine ⟨prior, later, pause, ?_, ?_, targetAnswer, consumedAnswers,
        remainingAnswers, ?_⟩
      · simpa [verifierCut, prefixes, verifierExact] using decomposition
      · have verifierRemaining : verifierCut.remainingFresh = aligned.future := by
          simpa [verifierCut, prefixes] using verifierExact
        rw [verifierRemaining] at paused
        rw [answersExact]
        exact paused
      · rw [requestTable, sourceTable]
  | cons verifierHead verifierTail =>
      let verifierConsumed := verifierHead :: verifierTail
      obtain ⟨nextCut, nextCoherent, nextRemaining, nextTableExact,
          cursorExact⟩ :=
        exact_compiler_root_cursor_after_nonempty_verifier_prefix
          transitionRoom input verifierConsumed aligned.future (by
            simpa [verifierConsumed] using verifierExact) (by
              simp [verifierConsumed])
      have stateCursorExact : state.cursor =
          SchedulerNativeCursor.machine configuration.machine.verifierLimits
            configuration.rootLimitBounds.verifier .verifier nextCut.state
            nextCut.program nextCut.fuel nextCoherent
            (fullRootVerifierReturnedContinuation configuration sample.1
              prefixes.adversaryValue prefixes.adversary.finalState) := by
        rw [aligned.cursorExact, consumedExact]
        simpa [prefixes, verifierConsumed] using cursorExact
      have nextTable : nextCut.state.table = state.oracle.table := by
        rw [aligned.tableExact, consumedExact]
        simpa [prefixes, verifierConsumed] using nextTableExact
      obtain ⟨prior, later, pause, decomposition, paused, targetAnswer,
          consumedAnswers, remainingAnswers, requestTable⟩ :=
        projected_fresh_trace_seek_aligned_scan_pauses_with_exact_split
          transitionFuel (by omega) configuration.machine.verifierLimits
          configuration.rootLimitBounds.verifier .verifier
          (fullRootVerifierReturnedContinuation configuration sample.1
            prefixes.adversaryValue prefixes.adversary.finalState)
          nextCoherent nextCut.trace state.cursor (by rw [stateCursorExact])
          prefixes.verifier.remaining expectedInput expectedAnswer (by
            rw [nextRemaining]
            exact future)
      refine ⟨prior, later, pause, ?_, ?_, targetAnswer, consumedAnswers,
        remainingAnswers, ?_⟩
      · rw [nextRemaining] at decomposition
        exact decomposition
      · rw [nextRemaining] at paused
        rw [answersExact]
        exact paused
      · rw [requestTable, nextTable]

/-- Exact joined-root pause split while the selected coordinate remains in
the residual adversary segment.  The returned `later` is the whole joined
future after the target, so it includes the untouched verifier segment and
matches the generic alignment-preservation theorem without a trace rewrite. -/
theorem exact_compiler_aligned_adversary_phase_pause_split
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters} {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (state : SchedulerNativeGammaCursor
      (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement
        Tag73K12ParsedProof Payload Result))
    (aligned : ExactCompilerRootGammaCursorAligned input state)
    (adversaryFuture : List (ShaInput × Digest256))
    (adversaryExact :
      input.package.root.full.projection.rootPrefixes.adversary.freshQueries =
        aligned.consumed ++ adversaryFuture)
    (futureExact : aligned.future = adversaryFuture ++
      input.package.root.full.projection.rootPrefixes.verifier.freshQueries)
    (expectedInput : ShaInput) (expectedAnswer : Digest256)
    (future : (expectedInput, expectedAnswer) ∈ adversaryFuture) :
    ∃ (prior later : List (ShaInput × Digest256))
      (pause : SchedulerNativeFreshPause
        (globalFull256OracleCallCap parameters)
        (SchedulerNativePlainRomResult TapeIdentity Statement
          Tag73K12ParsedProof Payload Result) expectedInput),
      aligned.future = prior ++ (expectedInput, expectedAnswer) :: later ∧
      scanSchedulerNativeToInput transitionFuel expectedInput state.cursor
          state.remainingAnswers = .paused pause ∧
      pause.targetAnswer = expectedAnswer ∧
      pause.consumedAnswers = prior.map Prod.snd ∧
      pause.remainingAnswers = later.map Prod.snd ++
        input.package.root.full.projection.rootPrefixes.verifier.remaining ∧
      pause.requestState.table =
        state.oracle.table ++ prior.map projectedFreshEntry := by
  let prefixes := input.package.root.full.projection.rootPrefixes
  obtain ⟨nextCut, nextCoherent, nextRemaining, nextTableExact,
      cursorExact⟩ := exact_compiler_root_cursor_after_adversary_prefix
    transitionRoom input aligned.consumed adversaryFuture (by
      simpa [prefixes] using adversaryExact)
  have stateCursorExact : state.cursor =
      SchedulerNativeCursor.machine configuration.machine.adversaryLimits
        configuration.rootLimitBounds.adversary .adversary nextCut.state
        nextCut.program nextCut.fuel nextCoherent
        (fullRootAdversaryReturnedContinuation configuration sample.1) := by
    rw [aligned.cursorExact]
    exact cursorExact
  have nextTable : nextCut.state.table = state.oracle.table := by
    rw [aligned.tableExact]
    exact nextTableExact
  have answersExact : state.remainingAnswers =
      adversaryFuture.map Prod.snd ++
        (prefixes.verifier.freshQueries.map Prod.snd ++
          prefixes.verifier.remaining) := by
    rw [aligned.answersExact, futureExact]
    simp [prefixes, List.map_append, List.append_assoc]
  obtain ⟨prior, adversaryLater, pause, decomposition, paused, targetAnswer,
      consumedAnswers, remainingAnswers, requestTable⟩ :=
    projected_fresh_trace_seek_aligned_scan_pauses_with_exact_split
      transitionFuel (by omega) configuration.machine.adversaryLimits
      configuration.rootLimitBounds.adversary .adversary
      (fullRootAdversaryReturnedContinuation configuration sample.1)
      nextCoherent nextCut.trace state.cursor (by rw [stateCursorExact])
      (prefixes.verifier.freshQueries.map Prod.snd ++
        prefixes.verifier.remaining)
      expectedInput expectedAnswer (by
        rw [nextRemaining]
        exact future)
  refine ⟨prior, adversaryLater ++ prefixes.verifier.freshQueries, pause,
    ?_, ?_, targetAnswer, consumedAnswers, ?_, ?_⟩
  · rw [futureExact]
    rw [nextRemaining] at decomposition
    rw [decomposition]
    simp [prefixes, List.append_assoc]
  · rw [nextRemaining] at paused
    rw [answersExact]
    exact paused
  · simpa [List.map_append, List.append_assoc] using remainingAnswers
  · rw [requestTable, nextTable]

#print axioms projected_fresh_trace_seek_aligned_scan_pauses_with_exact_split
#print axioms exact_compiler_aligned_verifier_phase_pause_split
#print axioms exact_compiler_aligned_adversary_phase_pause_split

end

end AspisK1.V7Tag73SchedulerNativeAlignedPauseSplit
