import AspisFormal.K1.V7Tag73SchedulerNativeTargetPause
import AspisFormal.K1.V7Tag73SchedulerNativePrefixTraversal
import AspisFormal.K1.V7Tag73SourceAnchoredSchedulerCut

/-!
# Scheduler-native pause/prefix alignment

The target scanner stores the cursor at the selected fresh request and the
answer/record prefix consumed before it.  This file proves that those stored
fields are exactly the deterministic scheduler prefix computations.  It is a
pure executable bridge: no protocol role or source conclusion is assumed.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73SchedulerNativePausePrefixBridge

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerNativeTargetPause
open AspisK1.V7Tag73SchedulerNativePrefixTraversal
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73SourceAnchoredSchedulerCut
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73SchedulerNativeCachedGammaReplay

noncomputable section

universe u

/-- A successful top-level target scan stores exactly the cursor and records
computed by its consumed answer prefix. -/
theorem scan_scheduler_native_to_input_paused_prefix_exact
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (target : ShaInput) :
    forall (cursor : SchedulerNativeCursor globalOracleCalls Result)
      (answers : List Digest256)
      (pause : SchedulerNativeFreshPause globalOracleCalls Result target),
      scanSchedulerNativeToInput transitionFuel target cursor answers =
          .paused pause ->
        pause.sourceTransitionFuel = transitionFuel /\
        pause.sourceCursor = schedulerNativePrefixCursor transitionFuel cursor
          pause.consumedAnswers /\
        pause.consumedTrace = schedulerNativePrefixRecords transitionFuel cursor
          pause.consumedAnswers := by
  intro cursor answers
  induction answers generalizing cursor with
  | nil =>
      intro pause found
      simp [scanSchedulerNativeToInput, scanSchedulerNativeToInputFrom] at found
  | cons answer rest ih =>
      intro pause found
      unfold scanSchedulerNativeToInput at found
      simp only [scanSchedulerNativeToInputFrom] at found
      split at found <;> rename_i requestExact
      · rename_i result
        generalize scanExact :
          scanSchedulerNativeToInputFrom transitionFuel target transitionFuel
            (.returned result : SchedulerNativeCursor globalOracleCalls Result)
            rest = scan at found
        cases scan with
        | absent run => contradiction
        | paused later =>
            cases found
            have tail := ih
              (.returned result : SchedulerNativeCursor globalOracleCalls Result)
              later scanExact
            rcases tail with ⟨fuelExact, cursorExact, traceExact⟩
            refine ⟨fuelExact, ?_, ?_⟩
            · simpa [SchedulerNativeFreshPause.prepend,
                schedulerNativePrefixCursor, schedulerNativeRequestNext,
                requestExact] using cursorExact
            · simpa [SchedulerNativeFreshPause.prepend,
                schedulerNativePrefixRecords, schedulerNativeRequestNext,
                schedulerNativeRequestRecord, requestExact] using traceExact
      · rename_i reason
        generalize scanExact :
          scanSchedulerNativeToInputFrom transitionFuel target transitionFuel
            (.failed reason : SchedulerNativeCursor globalOracleCalls Result)
            rest = scan at found
        cases scan with
        | absent run => contradiction
        | paused later =>
            cases found
            have tail := ih
              (.failed reason : SchedulerNativeCursor globalOracleCalls Result)
              later scanExact
            rcases tail with ⟨fuelExact, cursorExact, traceExact⟩
            refine ⟨fuelExact, ?_, ?_⟩
            · simpa [SchedulerNativeFreshPause.prepend,
                schedulerNativePrefixCursor, schedulerNativeRequestNext,
                requestExact] using cursorExact
            · simpa [SchedulerNativeFreshPause.prepend,
                schedulerNativePrefixRecords, schedulerNativeRequestNext,
                schedulerNativeRequestRecord, requestExact] using traceExact
      · generalize scanExact :
          scanSchedulerNativeToInputFrom transitionFuel target transitionFuel
            (.failed .transitionLimit :
              SchedulerNativeCursor globalOracleCalls Result) rest = scan at found
        cases scan with
        | absent run => contradiction
        | paused later =>
            cases found
            have tail := ih
              (.failed .transitionLimit :
                SchedulerNativeCursor globalOracleCalls Result)
              later scanExact
            rcases tail with ⟨fuelExact, cursorExact, traceExact⟩
            refine ⟨fuelExact, ?_, ?_⟩
            · simpa [SchedulerNativeFreshPause.prepend,
                schedulerNativePrefixCursor, schedulerNativeRequestNext,
                requestExact] using cursorExact
            · simpa [SchedulerNativeFreshPause.prepend,
                schedulerNativePrefixRecords, schedulerNativeRequestNext,
                schedulerNativeRequestRecord, requestExact] using traceExact
      · rename_i MachineResult limits limitBound actor requestState input
          nextProgram remainingFuel coherent totalRoom freshRoom missing
          onReturned
        split at found
        next input_eq_target =>
          cases found
          exact ⟨rfl, rfl, rfl⟩
        next input_ne_target =>
          let nextCursor : SchedulerNativeCursor globalOracleCalls Result :=
            .machine limits limitBound actor
              (freshQueryState actor requestState input answer)
              (nextProgram answer) remainingFuel
              (fresh_query_state_preserves_history_total_coherent actor
                requestState input answer coherent) onReturned
          generalize scanExact :
            scanSchedulerNativeToInputFrom transitionFuel target transitionFuel
              nextCursor rest = scan at found
          cases scan with
          | absent run => contradiction
          | paused later =>
              cases found
              have tail := ih nextCursor later scanExact
              rcases tail with ⟨fuelExact, cursorExact, traceExact⟩
              refine ⟨fuelExact, ?_, ?_⟩
              · simpa [SchedulerNativeFreshPause.prepend,
                  schedulerNativePrefixCursor, schedulerNativeRequestNext,
                  requestExact, nextCursor] using
                    cursorExact
              · simpa [SchedulerNativeFreshPause.prepend,
                  schedulerNativePrefixRecords, schedulerNativeRequestNext,
                  schedulerNativeRequestRecord, requestExact, nextCursor] using
                    traceExact
      · rename_i frozenHistory pairRoom outputInput advanceInput template next
        let nextCursor : SchedulerNativeCursor globalOracleCalls Result :=
          .forkAdvance frozenHistory pairRoom outputInput advanceInput template
            answer next
        generalize scanExact :
          scanSchedulerNativeToInputFrom transitionFuel target transitionFuel
            nextCursor rest = scan at found
        cases scan with
        | absent run => contradiction
        | paused later =>
            cases found
            have tail := ih nextCursor later scanExact
            rcases tail with ⟨fuelExact, cursorExact, traceExact⟩
            refine ⟨fuelExact, ?_, ?_⟩
            · simpa [SchedulerNativeFreshPause.prepend,
                schedulerNativePrefixCursor, schedulerNativeRequestNext,
                requestExact, nextCursor] using
                  cursorExact
            · simpa [SchedulerNativeFreshPause.prepend,
                schedulerNativePrefixRecords, schedulerNativeRequestNext,
                schedulerNativeRequestRecord, requestExact, nextCursor] using
                  traceExact
      · rename_i frozenHistory pairRoom outputInput advanceInput template
          forkOutput next
        let scheduled : ScheduledForkCoins :=
          { frozenHistory := frozenHistory
            outputInput := outputInput
            advanceInput := advanceInput
            template := template
            forkOutput := forkOutput
            forkAdvance := answer }
        generalize scanExact :
          scanSchedulerNativeToInputFrom transitionFuel target transitionFuel
            (next scheduled.configuration) rest = scan at found
        cases scan with
        | absent run => contradiction
        | paused later =>
            cases found
            have tail := ih (next scheduled.configuration) later scanExact
            rcases tail with ⟨fuelExact, cursorExact, traceExact⟩
            refine ⟨fuelExact, ?_, ?_⟩
            · simpa [SchedulerNativeFreshPause.prepend,
                schedulerNativePrefixCursor, schedulerNativeRequestNext,
                ScheduledForkCoins.configuration, requestExact, scheduled] using
                  cursorExact
            · simpa [SchedulerNativeFreshPause.prepend,
                schedulerNativePrefixRecords, schedulerNativeRequestNext,
                schedulerNativeRequestRecord, ScheduledForkCoins.configuration,
                requestExact, scheduled] using
                  traceExact

/-- Resuming the selected fresh request with any answer is exactly extending
the scanner's deterministic consumed prefix by that answer. -/
theorem scan_scheduler_native_to_input_paused_resume_cursor_with_exact
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (target : ShaInput)
    (cursor : SchedulerNativeCursor globalOracleCalls Result)
    (answers : List Digest256)
    (pause : SchedulerNativeFreshPause globalOracleCalls Result target)
    (found : scanSchedulerNativeToInput transitionFuel target cursor answers =
      .paused pause)
    (answer : Digest256) :
    pause.resumeCursorWith answer =
      schedulerNativePrefixCursor transitionFuel cursor
        (pause.consumedAnswers ++ [answer]) := by
  obtain ⟨fuelExact, cursorExact, _traceExact⟩ :=
    scan_scheduler_native_to_input_paused_prefix_exact transitionFuel target
      cursor answers pause found
  rw [scheduler_native_prefix_cursor_append]
  rw [← cursorExact]
  simp only [schedulerNativePrefixCursor]
  rw [← fuelExact, pause.requestExact]
  rfl

/-- The analogous record statement includes the selected fresh record with
the caller-supplied answer. -/
theorem scan_scheduler_native_to_input_paused_resume_records_exact
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (target : ShaInput)
    (cursor : SchedulerNativeCursor globalOracleCalls Result)
    (answers : List Digest256)
    (pause : SchedulerNativeFreshPause globalOracleCalls Result target)
    (found : scanSchedulerNativeToInput transitionFuel target cursor answers =
      .paused pause)
    (answer : Digest256) :
    schedulerNativePrefixRecords transitionFuel cursor
        (pause.consumedAnswers ++ [answer]) =
      pause.consumedTrace ++
        [.machineFresh pause.actor pause.input answer] := by
  obtain ⟨fuelExact, cursorExact, traceExact⟩ :=
    scan_scheduler_native_to_input_paused_prefix_exact transitionFuel target
      cursor answers pause found
  rw [scheduler_native_prefix_records_append, traceExact]
  rw [← cursorExact]
  simp only [schedulerNativePrefixRecords]
  rw [← fuelExact, pause.requestExact]
  rfl

/-! ## Projected fresh suffix preservation -/

/-- Scanning one literal projected machine suffix returns the chronological
split at the selected future coordinate.  In particular, the pause retains
exactly the answers before that coordinate and exactly the untouched answers
after it, even though cached calls may be normalized between fresh requests. -/
theorem projected_fresh_trace_scan_pauses_with_exact_split
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
    (suffix : List Digest256) (input : ShaInput) (answer : Digest256)
    (future : (input, answer) ∈ freshQueries) :
    ∃ (prior later : List (ShaInput × Digest256))
      (pause : SchedulerNativeFreshPause globalOracleCalls Final input),
      freshQueries = prior ++ (input, answer) :: later ∧
      scanSchedulerNativeToInput transitionFuel input
          (.machine limits limitBound actor state program fuel coherent
            onReturned)
          (freshQueries.map Prod.snd ++ suffix) = .paused pause ∧
      pause.targetAnswer = answer ∧
      pause.consumedAnswers = prior.map Prod.snd ∧
      pause.remainingAnswers = later.map Prod.snd ++ suffix ∧
      pause.requestState.table =
        state.table ++ prior.map projectedFreshEntry := by
  induction trace generalizing suffix input answer with
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
          rcases future with head | laterMember
          · rcases head with ⟨rfl, rfl⟩
            have normalized :=
              seek_scheduler_native_exposure_machine_of_fresh current limits
                limitBound actor fuel state requestState program traceCoherent
                input nextProgram remainingFuel cachedSteps requestCoherent
                totalRoom freshRoom missing onReturned sought
            have prefixTable := seek_next_fresh_oracle_table_eq limits actor
              fuel state program traceCoherent
            rw [sought] at prefixTable
            change requestState.table = state.table at prefixTable
            refine ⟨[], rest, ?_⟩
            simp only [List.map_cons, List.cons_append,
              scanSchedulerNativeToInput, scanSchedulerNativeToInputFrom]
            split <;> rename_i requestExact
            all_goals rw [normalized] at requestExact
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
            obtain ⟨prior, later, pause, decomposition, paused, answerExact,
                consumedExact, remainingExact, requestTableExact⟩ := ih
              (fresh_query_state_preserves_history_total_coherent actor
                requestState headInput headAnswer requestCoherent)
              suffix input answer laterMember
            refine ⟨(headInput, headAnswer) :: prior, later,
              pause.prepend headAnswer
                (.machineFresh actor headInput headAnswer), ?_, ?_,
              answerExact, ?_, remainingExact, ?_⟩
            · simpa [List.cons_append] using
                congrArg (List.cons (headInput, headAnswer)) decomposition
            · have normalized :=
                seek_scheduler_native_exposure_machine_of_fresh current limits
                  limitBound actor fuel state requestState program traceCoherent
                  headInput nextProgram remainingFuel cachedSteps
                  requestCoherent totalRoom freshRoom missing onReturned sought
              simp only [List.map_cons, List.cons_append,
                scanSchedulerNativeToInput, scanSchedulerNativeToInputFrom]
              split <;> rename_i requestExact
              all_goals rw [normalized] at requestExact
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

#print axioms scan_scheduler_native_to_input_paused_prefix_exact
#print axioms scan_scheduler_native_to_input_paused_resume_cursor_with_exact
#print axioms scan_scheduler_native_to_input_paused_resume_records_exact
#print axioms projected_fresh_trace_scan_pauses_with_exact_split

end

end AspisK1.V7Tag73SchedulerNativePausePrefixBridge
