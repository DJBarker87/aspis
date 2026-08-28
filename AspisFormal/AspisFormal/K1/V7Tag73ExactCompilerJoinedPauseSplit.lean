import AspisFormal.K1.V7Tag73SchedulerNativeAlignedPauseSplit
import AspisFormal.K1.V7Tag73ExactCompilerGammaCoordinateStep

/-!
# Sequential projected-machine pause splitting

This file lifts the exact verifier pause through a preceding returned
projected machine trace.  It is the executable adversary-to-verifier crossing
case: the target is absent from the completed first-machine table, the first
machine is run to its callback, and the callback is seek-aligned with the
second machine before any second-machine answer is consumed.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactCompilerJoinedPauseSplit

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerNativeTargetPause
open AspisK1.V7Tag73SchedulerNativePrefixTraversal
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73SchedulerNativeCachedGammaReplay
open AspisK1.V7Tag73SourceAnchoredSchedulerCut
open AspisK1.V7Tag73SchedulerNativeAlignedPauseSplit
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactCompilerSourceAnchoredCut
open AspisK1.V7Tag73SourceAnchoredNativeCursorFactorization
open AspisK1.V7Tag73FullCursorClientLineageLift
open AspisK1.V7Tag73ExactCompilerGammaCachedCoordinate
open AspisK1.V7Tag73ExactCompilerGammaCoordinateStep

noncomputable section

universe u

/-- Run a returned projected first machine completely, then pause at a
selected fresh coordinate of a seek-aligned second machine.  The pause fields
retain the exact joined answer prefix and immutable-table extension. -/
theorem projected_fresh_trace_then_seek_aligned_trace_pauses_exact
    {globalOracleCalls : Nat}
    {Final FirstResult SecondResult : Type u}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (firstLimits secondLimits : OracleLimits)
    (firstLimitBound : firstLimits.totalCalls ≤ globalOracleCalls)
    (secondLimitBound : secondLimits.totalCalls ≤ globalOracleCalls)
    (firstActor secondActor : QueryActor)
    (firstOnReturned : (result : FirstResult) → (state : OracleState) →
      HistoryTotalCoherent state →
        SchedulerNativeCursor globalOracleCalls Final)
    (secondOnReturned : (result : SecondResult) → (state : OracleState) →
      HistoryTotalCoherent state →
        SchedulerNativeCursor globalOracleCalls Final)
    {firstFuel : Nat} {firstState : OracleState}
    {firstProgram : OracleMachine FirstResult}
    {firstFresh : List (ShaInput × Digest256)}
    {firstResult : FirstResult} {middle : OracleState} {firstSteps : Nat}
    (firstCoherent : HistoryTotalCoherent firstState)
    (firstTrace : ProjectedFreshReturnedTrace firstLimits firstActor firstFuel
      firstState firstProgram firstFresh firstResult middle firstSteps)
    {secondFuel : Nat} {secondProgram : OracleMachine SecondResult}
    {secondFresh : List (ShaInput × Digest256)}
    {secondResult : SecondResult} {finalState : OracleState}
    {secondSteps : Nat}
    (middleCoherent : HistoryTotalCoherent middle)
    (secondTrace : ProjectedFreshReturnedTrace secondLimits secondActor
      secondFuel middle secondProgram secondFresh secondResult finalState
      secondSteps)
    (boundaryAligned :
      seekSchedulerNativeExposure transitionFuel
          (schedulerNativePrefixCursor transitionFuel
            (.machine firstLimits firstLimitBound firstActor firstState
              firstProgram firstFuel firstCoherent firstOnReturned)
            (firstFresh.map Prod.snd)) =
        seekSchedulerNativeExposure transitionFuel
          (.machine secondLimits secondLimitBound secondActor middle
            secondProgram secondFuel middleCoherent secondOnReturned))
    (suffix : List Digest256) (input : ShaInput) (answer : Digest256)
    (targetMissing : lookupEntry middle input = none)
    (future : (input, answer) ∈ secondFresh) :
    ∃ (secondPrior secondLater : List (ShaInput × Digest256))
      (pause : SchedulerNativeFreshPause globalOracleCalls Final input),
      secondFresh = secondPrior ++ (input, answer) :: secondLater ∧
      scanSchedulerNativeToInput transitionFuel input
          (.machine firstLimits firstLimitBound firstActor firstState
            firstProgram firstFuel firstCoherent firstOnReturned)
          (firstFresh.map Prod.snd ++ secondFresh.map Prod.snd ++ suffix) =
        .paused pause ∧
      pause.targetAnswer = answer ∧
      pause.consumedAnswers =
        firstFresh.map Prod.snd ++ secondPrior.map Prod.snd ∧
      pause.remainingAnswers = secondLater.map Prod.snd ++ suffix ∧
      pause.requestState.table =
        firstState.table ++ firstFresh.map projectedFreshEntry ++
          secondPrior.map projectedFreshEntry := by
  induction firstTrace with
  | returned fuel state program traceCoherent result finalState steps sought =>
      have coherentExact : firstCoherent = traceCoherent := Subsingleton.elim _ _
      cases coherentExact
      have firstTable : finalState.table = state.table := by
        have exact := seek_next_fresh_oracle_table_eq firstLimits firstActor
          fuel state program traceCoherent
        rw [sought] at exact
        simpa [seekNextFreshOracle] using exact
      obtain ⟨prior, later, pause, decomposition, paused, targetAnswer,
          consumedAnswers, remainingAnswers, requestTable⟩ :=
        projected_fresh_trace_seek_aligned_scan_pauses_with_exact_split
          transitionFuel positive secondLimits secondLimitBound secondActor
          secondOnReturned middleCoherent secondTrace
          (.machine firstLimits firstLimitBound firstActor state program fuel
            traceCoherent firstOnReturned)
          (by
            simpa only [List.map_nil, schedulerNativePrefixCursor] using
              boundaryAligned) suffix input answer future
      refine ⟨prior, later, pause, decomposition, ?_, targetAnswer, ?_,
        remainingAnswers, ?_⟩
      · simpa using paused
      · simpa using consumedAnswers
      · simpa [firstTable] using requestTable
  | fresh fuel state requestState program traceCoherent headInput nextProgram
      remainingFuel cachedSteps requestCoherent totalRoom freshRoom missing
      sought headAnswer rest result finalState tailSteps tail ih =>
      have coherentExact : firstCoherent = traceCoherent := Subsingleton.elim _ _
      cases coherentExact
      have different : headInput ≠ input := by
        intro equal
        subst input
        let branchTrace : ProjectedFreshReturnedTrace firstLimits firstActor
            fuel state program ((headInput, headAnswer) :: rest) result
            finalState (tailSteps + (cachedSteps + 1)) :=
          .fresh fuel state requestState program traceCoherent headInput
            nextProgram remainingFuel cachedSteps requestCoherent totalRoom
            freshRoom missing sought headAnswer rest result finalState
            tailSteps tail
        have finalTable := projected_fresh_returned_trace_table_exact
          firstLimits firstActor fuel state program
          ((headInput, headAnswer) :: rest) result finalState
          (tailSteps + (cachedSteps + 1)) branchTrace
        have mappedMember : projectedFreshEntry (headInput, headAnswer) ∈
            finalState.table := by
          rw [finalTable]
          exact List.mem_append_right _
            (List.mem_map.mpr ⟨(headInput, headAnswer),
              List.mem_cons_self, rfl⟩)
        unfold lookupEntry at targetMissing
        have rejected := List.find?_eq_none.mp targetMissing
          (projectedFreshEntry (headInput, headAnswer)) mappedMember
        simp [projectedFreshEntry] at rejected
      let nextCursor : SchedulerNativeCursor globalOracleCalls Final :=
        .machine firstLimits firstLimitBound firstActor
          (freshQueryState firstActor requestState headInput headAnswer)
          (nextProgram headAnswer) remainingFuel
          (fresh_query_state_preserves_history_total_coherent firstActor
            requestState headInput headAnswer requestCoherent)
          firstOnReturned
      have tailBoundary :
          seekSchedulerNativeExposure transitionFuel
              (schedulerNativePrefixCursor transitionFuel nextCursor
                (rest.map Prod.snd)) =
            seekSchedulerNativeExposure transitionFuel
              (.machine secondLimits secondLimitBound secondActor finalState
                secondProgram secondFuel middleCoherent secondOnReturned) := by
        cases transitionFuel with
        | zero => omega
        | succ current =>
            simp only [List.map_cons, schedulerNativePrefixCursor] at boundaryAligned
            rw [seek_scheduler_native_exposure_machine_of_fresh current
              firstLimits firstLimitBound firstActor fuel state requestState
              program traceCoherent headInput nextProgram remainingFuel
              cachedSteps requestCoherent totalRoom freshRoom missing
              firstOnReturned sought] at boundaryAligned
            simpa only [nextCursor, schedulerNativeRequestNext] using
              boundaryAligned
      obtain ⟨prior, later, pause, decomposition, paused, targetAnswer,
          consumedAnswers, remainingAnswers, requestTable⟩ := ih
        (fresh_query_state_preserves_history_total_coherent firstActor
          requestState headInput headAnswer requestCoherent)
        middleCoherent secondTrace tailBoundary targetMissing
      refine ⟨prior, later,
        pause.prepend headAnswer (.machineFresh firstActor headInput headAnswer),
        decomposition, ?_, targetAnswer, ?_, remainingAnswers, ?_⟩
      · cases transitionFuel with
        | zero => omega
        | succ current =>
            have normalizedSource :=
              seek_scheduler_native_exposure_machine_of_fresh current
                firstLimits firstLimitBound firstActor fuel state requestState
                program traceCoherent headInput nextProgram remainingFuel
                cachedSteps requestCoherent totalRoom freshRoom missing
                firstOnReturned sought
            simp only [List.map_cons, List.cons_append,
              scanSchedulerNativeToInput, scanSchedulerNativeToInputFrom]
            split <;> rename_i requestExact
            all_goals rw [normalizedSource] at requestExact
            all_goals cases requestExact
            split
            · rename_i equal
              exact (different equal).elim
            · unfold scanSchedulerNativeToInput at paused
              simp only [paused]
      · simp [SchedulerNativeFreshPause.prepend, consumedAnswers]
      · have prefixTable := seek_next_fresh_oracle_table_eq firstLimits
          firstActor fuel state program traceCoherent
        rw [sought] at prefixTable
        change requestState.table = state.table at prefixTable
        change pause.requestState.table = _
        rw [requestTable]
        simp [freshQueryState, prefixTable, projectedFreshEntry,
          List.map_cons, List.append_assoc]

/-! ## Exact compiler crossing specialization -/

/-- Exact pause split when the aligned cursor is still in the adversary but
the selected future coordinate belongs to the verifier. -/
theorem exact_compiler_aligned_cross_actor_pause_split
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
    (future : (expectedInput, expectedAnswer) ∈
      input.package.root.full.projection.rootPrefixes.verifier.freshQueries) :
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
  have verifierNonempty : prefixes.verifier.freshQueries ≠ [] :=
    List.ne_nil_of_mem future
  have rootBoundary := exact_compiler_adversary_boundary_seek_eq_verifier
    transitionRoom input verifierNonempty
  have boundaryAligned :
      seekSchedulerNativeExposure transitionFuel
          (schedulerNativePrefixCursor transitionFuel
            (SchedulerNativeCursor.machine
              configuration.machine.adversaryLimits
              configuration.rootLimitBounds.adversary .adversary nextCut.state
              nextCut.program nextCut.fuel nextCoherent
              (fullRootAdversaryReturnedContinuation configuration sample.1))
            (nextCut.remainingFresh.map Prod.snd)) =
        seekSchedulerNativeExposure transitionFuel
          (SchedulerNativeCursor.machine configuration.machine.verifierLimits
            configuration.rootLimitBounds.verifier .verifier verifierCut.state
            verifierCut.program verifierCut.fuel
            (projected_fresh_returned_trace_start_coherent verifierCut.trace)
            (fullRootVerifierReturnedContinuation configuration sample.1
              prefixes.adversaryValue prefixes.adversary.finalState)) := by
    have prefixCursorExact :
        schedulerNativePrefixCursor transitionFuel
            (SchedulerNativeCursor.machine
              configuration.machine.adversaryLimits
              configuration.rootLimitBounds.adversary .adversary nextCut.state
              nextCut.program nextCut.fuel nextCoherent
              (fullRootAdversaryReturnedContinuation configuration sample.1))
            (nextCut.remainingFresh.map Prod.snd) =
          schedulerNativePrefixCursor transitionFuel
            (exactPlainRomCursor configuration sample.1)
            (prefixes.adversary.freshQueries.map Prod.snd) := by
      rw [nextRemaining, ← stateCursorExact, aligned.cursorExact,
        ← scheduler_native_prefix_cursor_append]
      rw [← List.map_append, ← adversaryExact]
    rw [prefixCursorExact]
    change _ = seekSchedulerNativeExposure transitionFuel
      (fullRootVerifierCursor configuration sample.1
        prefixes.adversaryValue prefixes.adversary.finalState
        prefixes.adversary.finalCoherent)
    exact rootBoundary
  have targetMissing : lookupEntry verifierCut.state expectedInput = none := by
    exact projected_fresh_returned_trace_future_input_missing
      configuration.machine.verifierLimits .verifier verifierCut.fuel
      verifierCut.state verifierCut.program verifierCut.remainingFresh
      prefixes.verifier.result prefixes.verifier.finalState verifierCut.steps
      verifierCut.trace expectedInput expectedAnswer (by
        simpa [verifierCut, prefixes] using future)
  obtain ⟨verifierPrior, verifierLater, pause, verifierDecomposition, paused,
      targetAnswer, consumedAnswers, remainingAnswers, requestTable⟩ :=
    projected_fresh_trace_then_seek_aligned_trace_pauses_exact
      transitionFuel (by omega) configuration.machine.adversaryLimits
      configuration.machine.verifierLimits
      configuration.rootLimitBounds.adversary
      configuration.rootLimitBounds.verifier .adversary .verifier
      (fullRootAdversaryReturnedContinuation configuration sample.1)
      (fullRootVerifierReturnedContinuation configuration sample.1
        prefixes.adversaryValue prefixes.adversary.finalState)
      nextCoherent nextCut.trace
      (projected_fresh_returned_trace_start_coherent verifierCut.trace)
      verifierCut.trace boundaryAligned prefixes.verifier.remaining
      expectedInput expectedAnswer targetMissing (by
        simpa [verifierCut, prefixes] using future)
  refine ⟨adversaryFuture ++ verifierPrior, verifierLater, pause,
    ?_, ?_, targetAnswer, ?_, remainingAnswers, ?_⟩
  · have decomposition : prefixes.verifier.freshQueries =
        verifierPrior ++ (expectedInput, expectedAnswer) :: verifierLater := by
      simpa [verifierCut, prefixes] using verifierDecomposition
    rw [futureExact, decomposition]
    simp [List.append_assoc]
  · have verifierRemaining : verifierCut.remainingFresh =
        prefixes.verifier.freshQueries := by rfl
    rw [nextRemaining, verifierRemaining] at paused
    rw [aligned.answersExact, futureExact]
    rw [stateCursorExact]
    simpa [prefixes, List.map_append, List.append_assoc] using paused
  · simpa [nextRemaining, List.map_append, List.append_assoc] using
      consumedAnswers
  · rw [requestTable, nextTable, nextRemaining]
    simp [List.map_append, List.append_assoc]

/-- Every selected pair in an arbitrary aligned compiler future has one exact
scanner pause split.  The proof exhausts the residual-adversary,
adversary-to-verifier, and residual-verifier phases. -/
theorem exact_compiler_aligned_future_pause_split
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
  rcases exact_compiler_alignment_actor_phase_split aligned with
      ⟨adversaryFuture, adversaryExact, futureExact⟩ |
      ⟨verifierConsumed, consumedExact, verifierExact⟩
  · have joined : (expectedInput, expectedAnswer) ∈
        adversaryFuture ++
          input.package.root.full.projection.rootPrefixes.verifier.freshQueries := by
      rwa [← futureExact]
    rcases List.mem_append.mp joined with adversaryMember | verifierMember
    · exact exact_compiler_aligned_adversary_phase_pause_split transitionRoom
        input state aligned adversaryFuture adversaryExact futureExact
        expectedInput expectedAnswer adversaryMember
    · exact exact_compiler_aligned_cross_actor_pause_split transitionRoom input
        state aligned adversaryFuture adversaryExact futureExact expectedInput
        expectedAnswer verifierMember
  · exact exact_compiler_aligned_verifier_phase_pause_split transitionRoom
      input state aligned verifierConsumed consumedExact verifierExact
      expectedInput expectedAnswer future

/-- Concrete one-coordinate compiler step.  Cache hits are inert; cache
misses use the joined exact pause split above and extend all four alignment
components by the same literal fresh prefix. -/
theorem exact_compiler_actual_gamma_coordinate_step_of_transition_room
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters} {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    ∀ (kind : SchedulerNativeGammaQueryKind)
      (expectedInput : ShaInput) (expectedAnswer : Digest256)
      (state : SchedulerNativeGammaCursor
        (globalFull256OracleCallCap parameters)
        (SchedulerNativePlainRomResult TapeIdentity Statement
          Tag73K12ParsedProof Payload Result))
      (aligned : ExactCompilerRootGammaCursorAligned input state),
      tableLookup (exactOperationalTable input) expectedInput =
          some expectedAnswer →
        ∃ nextState,
          consumeSchedulerNativeGammaCoordinate transitionFuel kind
              expectedInput expectedAnswer state = .ok nextState ∧
          Nonempty (ExactCompilerRootGammaCursorAligned input nextState) := by
  intro kind expectedInput expectedAnswer state aligned found
  cases cached : lookupEntry state.oracle expectedInput with
  | some entry =>
      have answerExact := exact_compiler_aligned_cached_answer_exact input state
        aligned expectedInput expectedAnswer entry cached found
      obtain ⟨preserved, consumed, _member⟩ :=
        exact_compiler_cached_gamma_coordinate_step input state aligned kind
          expectedInput expectedAnswer entry cached answerExact
      exact ⟨state, consumed, ⟨preserved⟩⟩
  | none =>
      have future := exact_compiler_aligned_missing_coordinate_mem_future input
        state aligned expectedInput expectedAnswer cached found
      obtain ⟨prior, later, pause, futureExact, paused, targetAnswer,
          consumedAnswers, _remainingAnswers, requestTable⟩ :=
        exact_compiler_aligned_future_pause_split transitionRoom input state
          aligned expectedInput expectedAnswer future
      exact exact_compiler_aligned_future_pause_preserves_alignment input state
        aligned kind expectedInput expectedAnswer prior later futureExact cached
        pause paused targetAnswer consumedAnswers requestTable

#print axioms projected_fresh_trace_then_seek_aligned_trace_pauses_exact
#print axioms exact_compiler_aligned_cross_actor_pause_split
#print axioms exact_compiler_aligned_future_pause_split
#print axioms exact_compiler_actual_gamma_coordinate_step_of_transition_room

end

end AspisK1.V7Tag73ExactCompilerJoinedPauseSplit
