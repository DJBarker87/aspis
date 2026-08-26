import AspisFormal.K1.V7Tag73SchedulerMachineFactorization

/-!
# Trace-preserving factorization of native scheduler machine segments

The earlier list interpreter retained only the terminal result.  Legal
state-restoration provenance also needs the actual chronological records.
This leaf gives the same scheduler a list semantics returning both terminal
and trace, proves equality with the fixed dependent-tape interpreter, and
factors a certified normally returned machine prefix without discarding its
machine-fresh records.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73SchedulerTraceFactorization

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73ProjectedMachinePrefix
open AspisK1.V7Tag73SchedulerMachineFactorization

noncomputable section

universe u

/-- List form of the fixed scheduler, retaining the exact exposure trace. -/
def runSchedulerNativeListRunFrom
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) :
    Nat → SchedulerNativeCursor globalOracleCalls Result →
      List Digest256 → SchedulerNativeRun Result
  | currentTransitionFuel, cursor, [] =>
      { terminal := terminalAtExposureEnd currentTransitionFuel cursor
        trace := [] }
  | currentTransitionFuel, cursor, answer :: rest =>
      match seekSchedulerNativeExposure currentTransitionFuel cursor with
      | .returned result =>
          let tail := runSchedulerNativeListRunFrom transitionFuel
            transitionFuel
            (.returned result : SchedulerNativeCursor globalOracleCalls Result)
            rest
          { terminal := tail.terminal
            trace := .padding answer :: tail.trace }
      | .failed reason =>
          let tail := runSchedulerNativeListRunFrom transitionFuel
            transitionFuel
            (.failed reason : SchedulerNativeCursor globalOracleCalls Result)
            rest
          { terminal := tail.terminal
            trace := .padding answer :: tail.trace }
      | .transitionLimit =>
          let tail := runSchedulerNativeListRunFrom transitionFuel
            transitionFuel
            (.failed .transitionLimit :
              SchedulerNativeCursor globalOracleCalls Result)
            rest
          { terminal := tail.terminal
            trace := .padding answer :: tail.trace }
      | .machineFresh limits limitBound actor state input nextProgram
          remainingFuel coherent _totalRoom _freshRoom _missing onReturned =>
          let tail := runSchedulerNativeListRunFrom transitionFuel
            transitionFuel
            (.machine limits limitBound actor
              (freshQueryState actor state input answer)
              (nextProgram answer) remainingFuel
              (fresh_query_state_preserves_history_total_coherent actor state
                input answer coherent) onReturned)
            rest
          { terminal := tail.terminal
            trace := .machineFresh actor input answer :: tail.trace }
      | .forkOutput frozenHistory pairRoom outputInput advanceInput template
          next =>
          let tail := runSchedulerNativeListRunFrom transitionFuel
            transitionFuel
            (.forkAdvance frozenHistory pairRoom outputInput advanceInput
              template answer next)
            rest
          { terminal := tail.terminal
            trace := .forkOutput frozenHistory outputInput advanceInput template
              answer :: tail.trace }
      | .forkAdvance frozenHistory pairRoom outputInput advanceInput template
          forkOutput next =>
          let scheduled : ScheduledForkCoins :=
            { frozenHistory := frozenHistory
              outputInput := outputInput
              advanceInput := advanceInput
              template := template
              forkOutput := forkOutput
              forkAdvance := answer }
          let tail := runSchedulerNativeListRunFrom transitionFuel
            transitionFuel (next scheduled.configuration) rest
          { terminal := tail.terminal
            trace := .forkAdvance scheduled :: tail.trace }

def runSchedulerNativeListRun
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat)
    (cursor : SchedulerNativeCursor globalOracleCalls Result)
    (answers : List Digest256) : SchedulerNativeRun Result :=
  runSchedulerNativeListRunFrom transitionFuel transitionFuel cursor answers

/-- Erasing the trace from the trace-retaining list semantics recovers the
existing terminal-only list interpreter. -/
theorem run_scheduler_native_list_run_terminal
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) : ∀ currentTransitionFuel
      (cursor : SchedulerNativeCursor globalOracleCalls Result)
      (answers : List Digest256),
      (runSchedulerNativeListRunFrom transitionFuel currentTransitionFuel
        cursor answers).terminal =
      runSchedulerNativeListTerminalFrom transitionFuel currentTransitionFuel
        cursor answers := by
  intro currentTransitionFuel cursor answers
  induction answers generalizing currentTransitionFuel cursor with
  | nil => rfl
  | cons answer rest ih =>
      simp only [runSchedulerNativeListRunFrom,
        runSchedulerNativeListTerminalFrom]
      cases request : seekSchedulerNativeExposure currentTransitionFuel cursor
          <;> simp only [request]
      all_goals exact ih transitionFuel _

/-- The list and length-indexed interpreters agree on the complete run, not
only on its terminal projection. -/
theorem run_scheduler_native_eq_list_run
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel remaining : Nat)
    (cursor : SchedulerNativeCursor globalOracleCalls Result)
    (tape : FreshAnswerTape Digest256 remaining) :
    runSchedulerNative transitionFuel remaining cursor tape =
      runSchedulerNativeListRun transitionFuel cursor
        (freshAnswerTapeToList tape) := by
  induction remaining generalizing cursor with
  | zero =>
      rfl
  | succ remaining ih =>
      simp only [runSchedulerNative, runSchedulerNativeListRun,
        runSchedulerNativeListRunFrom, freshAnswerTapeToList]
      cases request : seekSchedulerNativeExposure transitionFuel cursor <;>
        simp only [request]
      all_goals rw [ih]
      all_goals rfl

/-- Exact trace records emitted by one projected machine segment. -/
def projectedMachineFreshRecords
    (actor : QueryActor) :
    List (ShaInput × Digest256) → List UnifiedExposureRecord
  | [] => []
  | (input, answer) :: rest =>
      .machineFresh actor input answer :: projectedMachineFreshRecords actor rest

@[simp] theorem projected_machine_fresh_records_append
    (actor : QueryActor) (first second : List (ShaInput × Digest256)) :
    projectedMachineFreshRecords actor (first ++ second) =
      projectedMachineFreshRecords actor first ++
        projectedMachineFreshRecords actor second := by
  induction first with
  | nil => rfl
  | cons pair rest ih =>
      rcases pair with ⟨input, answer⟩
      simp [projectedMachineFreshRecords, ih]

@[simp] theorem machine_fresh_query_answers_projected_records
    (actor : QueryActor) (queries : List (ShaInput × Digest256)) :
    machineFreshQueryAnswers (projectedMachineFreshRecords actor queries) =
      queries := by
  induction queries with
  | nil => rfl
  | cons pair rest ih =>
      rcases pair with ⟨input, answer⟩
      simp [projectedMachineFreshRecords, machineFreshQueryAnswers, ih]

@[simp] theorem machine_fresh_answers_projected_records
    (actor : QueryActor) (queries : List (ShaInput × Digest256)) :
    machineFreshAnswers (projectedMachineFreshRecords actor queries) =
      queries.map Prod.snd := by
  rw [machine_fresh_answers_eq_query_answers_map,
    machine_fresh_query_answers_projected_records]

/-! ## One normally returned machine prefix with trace -/

/-- Normal return traces carry enough operational information to reconstruct
coherence of their literal final oracle. -/
theorem projected_fresh_returned_trace_final_coherent
    {MachineResult : Type u} (limits : OracleLimits) (actor : QueryActor)
    (fuel : Nat) (state : OracleState) (program : OracleMachine MachineResult)
    (freshQueries : List (ShaInput × Digest256)) (result : MachineResult)
    (finalState : OracleState) (steps : Nat)
    (_coherent : HistoryTotalCoherent state)
    (trace : ProjectedFreshReturnedTrace limits actor fuel state program
      freshQueries result finalState steps) :
    HistoryTotalCoherent finalState := by
  induction trace with
  | returned fuel state program coherent result finalState steps sought =>
      exact seek_next_fresh_returned_state_coherent limits actor fuel state
        finalState program coherent result steps sought
  | fresh fuel state requestState program coherent input next remainingFuel
      cachedSteps requestCoherent totalRoom freshRoom missing sought answer rest
      result finalState tailSteps tail ih =>
      exact ih (fresh_query_state_preserves_history_total_coherent actor
        requestState input answer requestCoherent)

/-- When the concrete normalizer returns without another fresh query, the
native scheduler continues from exactly that returned cursor.  Generalizing
the certified result before splitting it avoids an illicit dependent rewrite
between two proof terms witnessing the same oracle-history invariant. -/
theorem seek_scheduler_native_exposure_machine_of_returned
    {globalOracleCalls : Nat} {Result MachineResult : Type u}
    (current : Nat) (limits : OracleLimits)
    (limitBound : limits.totalCalls ≤ globalOracleCalls)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (program : OracleMachine MachineResult)
    (coherent : HistoryTotalCoherent state)
    (onReturned : (result : MachineResult) → (state : OracleState) →
      HistoryTotalCoherent state →
        SchedulerNativeCursor globalOracleCalls Result)
    (result : MachineResult) (finalState : OracleState) (steps : Nat)
    (sought : seekNextFresh limits actor fuel state program coherent =
      .returned result finalState steps) :
    seekSchedulerNativeExposure (current + 1)
        (.machine limits limitBound actor state program fuel coherent
          onReturned) =
      seekSchedulerNativeExposure current
        (onReturned result finalState
          (seek_next_fresh_returned_state_coherent limits actor fuel state
            finalState program coherent result steps sought)) := by
  change nativeRequestOfCoherentSeekResult limits limitBound actor onReturned
      (fun result finalState finalCoherent =>
        seekSchedulerNativeExposure current
          (onReturned result finalState finalCoherent))
      (certifiedSeekNextFresh limits actor fuel state program coherent) = _
  generalize certifiedExact :
    certifiedSeekNextFresh limits actor fuel state program coherent = certified
  rcases certified with ⟨value, valueCoherent⟩
  have valueExact : value = .returned result finalState steps := by
    have exactValue := congrArg
      (fun certified : CoherentSeekResult MachineResult limits =>
        certified.value) certifiedExact
    exact exactValue.symm.trans sought
  cases valueExact
  simp only [nativeRequestOfCoherentSeekResult]

/-- When the concrete normalizer reaches a missing query, the native scheduler
exposes that exact query and its literal continuation. -/
theorem seek_scheduler_native_exposure_machine_of_fresh
    {globalOracleCalls : Nat} {Result MachineResult : Type u}
    (current : Nat) (limits : OracleLimits)
    (limitBound : limits.totalCalls ≤ globalOracleCalls)
    (actor : QueryActor) (fuel : Nat) (state requestState : OracleState)
    (program : OracleMachine MachineResult)
    (coherent : HistoryTotalCoherent state)
    (input : ShaInput) (next : ShaOutput → OracleMachine MachineResult)
    (remainingFuel cachedSteps : Nat)
    (requestCoherent : HistoryTotalCoherent requestState)
    (totalRoom : requestState.totalCalls < limits.totalCalls)
    (freshRoom : requestState.freshCalls < limits.freshCalls)
    (missing : lookupEntry requestState input = none)
    (onReturned : (result : MachineResult) → (state : OracleState) →
      HistoryTotalCoherent state →
        SchedulerNativeCursor globalOracleCalls Result)
    (sought : seekNextFresh limits actor fuel state program coherent =
      .request requestState input next remainingFuel cachedSteps
        requestCoherent totalRoom freshRoom missing) :
    seekSchedulerNativeExposure (current + 1)
        (.machine limits limitBound actor state program fuel coherent
          onReturned) =
      .machineFresh limits limitBound actor requestState input next
        remainingFuel requestCoherent totalRoom freshRoom missing
        onReturned := by
  unfold seekSchedulerNativeExposure
  generalize certifiedExact :
    certifiedSeekNextFresh limits actor fuel state program coherent = certified
  rcases certified with ⟨value, valueCoherent⟩
  have valueExact : value =
      .request requestState input next remainingFuel cachedSteps
        requestCoherent totalRoom freshRoom missing := by
    have exactValue := congrArg
      (fun certified : CoherentSeekResult MachineResult limits =>
        certified.value) certifiedExact
    exact exactValue.symm.trans sought
  cases valueExact
  rfl

/-- A literal returned projected trace factors from the scheduler list run.
The continuation budget is the predecessor of the current budget when no
fresh coordinate was used, and the predecessor of the reset budget otherwise,
exactly as in the terminal-only factorization. -/
theorem run_scheduler_native_list_run_from_returned_trace
    {globalOracleCalls : Nat} {Result MachineResult : Type u}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (limits : OracleLimits)
    (limitBound : limits.totalCalls ≤ globalOracleCalls)
    (actor : QueryActor)
    (onReturned : (result : MachineResult) → (state : OracleState) →
      HistoryTotalCoherent state →
        SchedulerNativeCursor globalOracleCalls Result) :
    ∀ (currentTransitionFuel : Nat) (currentPositive : 0 < currentTransitionFuel)
      (fuel : Nat) (state : OracleState) (program : OracleMachine MachineResult)
      (freshQueries : List (ShaInput × Digest256))
      (result : MachineResult) (finalState : OracleState) (steps : Nat)
      (remaining : List Digest256)
      (coherent : HistoryTotalCoherent state)
      (trace : ProjectedFreshReturnedTrace limits actor fuel state program
        freshQueries result finalState steps),
      runSchedulerNativeListRunFrom transitionFuel currentTransitionFuel
          (.machine limits limitBound actor state program fuel coherent
            onReturned)
          (freshQueries.map Prod.snd ++ remaining) =
        let tail := runSchedulerNativeListRunFrom transitionFuel
          (machinePrefixContinuationTransitionFuel transitionFuel
            (currentTransitionFuel - 1) freshQueries)
          (onReturned result finalState
            (projected_fresh_returned_trace_final_coherent limits actor fuel
              state program freshQueries result finalState steps coherent trace))
          remaining
        { terminal := tail.terminal
          trace := projectedMachineFreshRecords actor freshQueries ++
            tail.trace } := by
  intro currentTransitionFuel currentPositive fuel state program freshQueries
    result finalState steps remaining coherent trace
  induction trace generalizing currentTransitionFuel remaining with
  | returned fuel state program traceCoherent result finalState steps sought =>
      have coherentExact : coherent = traceCoherent := Subsingleton.elim _ _
      cases coherentExact
      cases currentTransitionFuel with
      | zero => omega
      | succ current =>
          cases remaining <;>
            simp only [List.map_nil, List.nil_append,
              runSchedulerNativeListRunFrom, terminalAtExposureEnd,
              machinePrefixContinuationTransitionFuel,
              projectedMachineFreshRecords]
          all_goals rw [seek_scheduler_native_exposure_machine_of_returned
            current limits limitBound actor fuel state program traceCoherent
            onReturned result finalState steps sought]
          all_goals simp only [Nat.add_sub_cancel]
  | fresh fuel state requestState program traceCoherent input next
      remainingFuel cachedSteps requestCoherent totalRoom freshRoom missing
      sought answer rest result finalState tailSteps tail ih =>
      have coherentExact : coherent = traceCoherent := Subsingleton.elim _ _
      cases coherentExact
      cases currentTransitionFuel with
      | zero => omega
      | succ current =>
          simp only [List.map_cons, List.cons_append,
            runSchedulerNativeListRunFrom,
            projectedMachineFreshRecords]
          rw [seek_scheduler_native_exposure_machine_of_fresh current limits
            limitBound actor fuel state requestState program traceCoherent input
            next remainingFuel cachedSteps requestCoherent totalRoom freshRoom
            missing onReturned sought]
          simp only
          rw [ih transitionFuel positive remaining
            (fresh_query_state_preserves_history_total_coherent actor
              requestState input answer requestCoherent)]
          cases rest <;>
            simp [machinePrefixContinuationTransitionFuel]

/-- Structure-level wrapper retaining the exact untouched answer suffix. -/
theorem run_scheduler_native_list_run_from_projected_prefix
    {globalOracleCalls : Nat} {Result MachineResult : Type u}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (currentTransitionFuel : Nat) (currentPositive : 0 < currentTransitionFuel)
    (limits : OracleLimits)
    (limitBound : limits.totalCalls ≤ globalOracleCalls)
    (actor : QueryActor) (state : OracleState)
    (program : OracleMachine MachineResult) (fuel : Nat)
    (coherent : HistoryTotalCoherent state)
    (onReturned : (result : MachineResult) → (state : OracleState) →
      HistoryTotalCoherent state →
        SchedulerNativeCursor globalOracleCalls Result)
    (available : List Digest256)
    (returned : ProjectedMachinePrefixReturned limits actor fuel state program
      available) :
    runSchedulerNativeListRunFrom transitionFuel currentTransitionFuel
        (.machine limits limitBound actor state program fuel coherent onReturned)
        available =
      let tail := runSchedulerNativeListRunFrom transitionFuel
        (machinePrefixContinuationTransitionFuel transitionFuel
          (currentTransitionFuel - 1) returned.freshQueries)
        (onReturned returned.result returned.finalState returned.finalCoherent)
        returned.remaining
      { terminal := tail.terminal
        trace := projectedMachineFreshRecords actor returned.freshQueries ++
          tail.trace } := by
  calc
    _ = runSchedulerNativeListRunFrom transitionFuel currentTransitionFuel
        (.machine limits limitBound actor state program fuel coherent onReturned)
        (returned.freshQueries.map Prod.snd ++ returned.remaining) :=
      congrArg
        (fun answers => runSchedulerNativeListRunFrom transitionFuel
          currentTransitionFuel
          (.machine limits limitBound actor state program fuel coherent
            onReturned) answers)
        returned.availableExact
    _ = _ := by
      simpa using run_scheduler_native_list_run_from_returned_trace
        transitionFuel positive limits limitBound actor onReturned
          currentTransitionFuel currentPositive fuel state program
          returned.freshQueries returned.result returned.finalState returned.steps
          returned.remaining coherent returned.trace

#print axioms run_scheduler_native_eq_list_run
#print axioms run_scheduler_native_list_run_terminal
#print axioms run_scheduler_native_list_run_from_returned_trace
#print axioms run_scheduler_native_list_run_from_projected_prefix

end

end AspisK1.V7Tag73SchedulerTraceFactorization
