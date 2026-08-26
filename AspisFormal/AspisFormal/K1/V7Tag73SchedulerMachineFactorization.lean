import AspisFormal.K1.V7Tag73ProjectedMachinePrefix

/-!
# Factor one machine segment out of the native scheduler

This module gives the result-carrying scheduler a list semantics for its
terminal value and proves that a leading machine node is exactly the
proof-producing projected-prefix interpreter followed by its actual
continuation.  The list semantics is only a theorem device; the probability
experiment continues to use the fixed length-indexed uniform tape.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73SchedulerMachineFactorization

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73AtomicPairReplay
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73ProjectedMachinePrefix

noncomputable section

universe u

/-- Terminal-only list semantics of the exact scheduler step function.
`transitionFuel` is reset after every consumed exposure, exactly as in
`runSchedulerNative`; `currentTransitionFuel` is the budget for zero-exposure
normalization before the next coordinate. -/
def runSchedulerNativeListTerminalFrom
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) :
    Nat → SchedulerNativeCursor globalOracleCalls Result →
      List Digest256 → SchedulerNativeTerminal Result
  | currentTransitionFuel, cursor, [] =>
      terminalAtExposureEnd currentTransitionFuel cursor
  | currentTransitionFuel, cursor, answer :: rest =>
      match seekSchedulerNativeExposure currentTransitionFuel cursor with
      | .returned result =>
          runSchedulerNativeListTerminalFrom transitionFuel transitionFuel
            (.returned result :
              SchedulerNativeCursor globalOracleCalls Result) rest
      | .failed reason =>
          runSchedulerNativeListTerminalFrom transitionFuel transitionFuel
            (.failed reason :
              SchedulerNativeCursor globalOracleCalls Result) rest
      | .transitionLimit =>
          runSchedulerNativeListTerminalFrom transitionFuel transitionFuel
            (.failed .transitionLimit :
              SchedulerNativeCursor globalOracleCalls Result) rest
      | .machineFresh limits limitBound actor state input nextProgram
          remainingFuel coherent _totalRoom _freshRoom _missing onReturned =>
          runSchedulerNativeListTerminalFrom transitionFuel transitionFuel
            (.machine limits limitBound actor
              (freshQueryState actor state input answer)
              (nextProgram answer) remainingFuel
              (fresh_query_state_preserves_history_total_coherent actor state
                input answer coherent) onReturned) rest
      | .forkOutput frozenHistory pairRoom outputInput advanceInput template
          next =>
          runSchedulerNativeListTerminalFrom transitionFuel transitionFuel
            (.forkAdvance frozenHistory pairRoom outputInput advanceInput
              template answer next) rest
      | .forkAdvance frozenHistory pairRoom outputInput advanceInput template
          forkOutput next =>
          let scheduled : ScheduledForkCoins :=
            { frozenHistory := frozenHistory
              outputInput := outputInput
              advanceInput := advanceInput
              template := template
              forkOutput := forkOutput
              forkAdvance := answer }
          runSchedulerNativeListTerminalFrom transitionFuel transitionFuel
            (next scheduled.configuration) rest

def runSchedulerNativeListTerminal
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat)
    (cursor : SchedulerNativeCursor globalOracleCalls Result)
    (answers : List Digest256) : SchedulerNativeTerminal Result :=
  runSchedulerNativeListTerminalFrom transitionFuel transitionFuel cursor
    answers

/-- Consume a list from an already-normalized native scheduler request.  This
is exactly the request match shared by the fixed-tape and list schedulers. -/
def runSchedulerNativeListTerminalAfterRequest
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) :
    SchedulerNativeRequest globalOracleCalls Result → List Digest256 →
      SchedulerNativeTerminal Result
  | request, [] =>
      match request with
      | .returned result => .returned result
      | .failed reason => .failed reason
      | .transitionLimit => .failed .transitionLimit
      | .machineFresh .. => .failed .exposureExhausted
      | .forkOutput .. => .failed .exposureExhausted
      | .forkAdvance .. => .failed .exposureExhausted
  | request, answer :: rest =>
      match request with
      | .returned result =>
          runSchedulerNativeListTerminalFrom transitionFuel transitionFuel
            (.returned result :
              SchedulerNativeCursor globalOracleCalls Result) rest
      | .failed reason =>
          runSchedulerNativeListTerminalFrom transitionFuel transitionFuel
            (.failed reason :
              SchedulerNativeCursor globalOracleCalls Result) rest
      | .transitionLimit =>
          runSchedulerNativeListTerminalFrom transitionFuel transitionFuel
            (.failed .transitionLimit :
              SchedulerNativeCursor globalOracleCalls Result) rest
      | .machineFresh limits limitBound actor state input nextProgram
          remainingFuel coherent _totalRoom _freshRoom _missing onReturned =>
          runSchedulerNativeListTerminalFrom transitionFuel transitionFuel
            (.machine limits limitBound actor
              (freshQueryState actor state input answer)
              (nextProgram answer) remainingFuel
              (fresh_query_state_preserves_history_total_coherent actor state
                input answer coherent) onReturned) rest
      | .forkOutput frozenHistory pairRoom outputInput advanceInput template
          next =>
          runSchedulerNativeListTerminalFrom transitionFuel transitionFuel
            (.forkAdvance frozenHistory pairRoom outputInput advanceInput
              template answer next) rest
      | .forkAdvance frozenHistory pairRoom outputInput advanceInput template
          forkOutput next =>
          let scheduled : ScheduledForkCoins :=
            { frozenHistory := frozenHistory
              outputInput := outputInput
              advanceInput := advanceInput
              template := template
              forkOutput := forkOutput
              forkAdvance := answer }
          runSchedulerNativeListTerminalFrom transitionFuel transitionFuel
            (next scheduled.configuration) rest

/-- One leading machine step with the scheduler's coherence-certified
normalizer result supplied explicitly. -/
def runSchedulerNativeListTerminalFromCertifiedMachine
    {globalOracleCalls : Nat} {Result MachineResult : Type u}
    (transitionFuel currentTransitionFuel : Nat)
    (limits : OracleLimits)
    (limitBound : limits.totalCalls ≤ globalOracleCalls)
    (actor : QueryActor) (state : OracleState)
    (program : OracleMachine MachineResult) (fuel : Nat)
    (coherent : HistoryTotalCoherent state)
    (onReturned : (result : MachineResult) → (state : OracleState) →
      HistoryTotalCoherent state →
        SchedulerNativeCursor globalOracleCalls Result)
    (certified : CoherentSeekResult MachineResult limits)
    (answers : List Digest256) : SchedulerNativeTerminal Result :=
  match currentTransitionFuel with
  | 0 =>
      runSchedulerNativeListTerminalAfterRequest transitionFuel
        (.transitionLimit :
          SchedulerNativeRequest globalOracleCalls Result) answers
  | current + 1 =>
      runSchedulerNativeListTerminalAfterRequest transitionFuel
        (nativeRequestOfCoherentSeekResult limits limitBound actor onReturned
          (fun result finalState finalCoherent =>
            seekSchedulerNativeExposure current
              (onReturned result finalState finalCoherent))
          certified)
        answers

theorem run_scheduler_native_list_machine_eq_certified
    {globalOracleCalls : Nat} {Result MachineResult : Type u}
    (transitionFuel currentTransitionFuel : Nat)
    (limits : OracleLimits)
    (limitBound : limits.totalCalls ≤ globalOracleCalls)
    (actor : QueryActor) (state : OracleState)
    (program : OracleMachine MachineResult) (fuel : Nat)
    (coherent : HistoryTotalCoherent state)
    (onReturned : (result : MachineResult) → (state : OracleState) →
      HistoryTotalCoherent state →
        SchedulerNativeCursor globalOracleCalls Result)
    (answers : List Digest256) :
    runSchedulerNativeListTerminalFrom transitionFuel currentTransitionFuel
        (.machine limits limitBound actor state program fuel coherent onReturned)
        answers =
      runSchedulerNativeListTerminalFromCertifiedMachine transitionFuel
        currentTransitionFuel limits limitBound actor state program fuel
        coherent onReturned
        (certifiedSeekNextFresh limits actor fuel state program coherent)
        answers := by
  cases currentTransitionFuel <;> cases answers <;> rfl

/-- The list and length-indexed interpreters have the same terminal. -/
theorem run_scheduler_native_terminal_eq_list
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel remaining : Nat)
    (cursor : SchedulerNativeCursor globalOracleCalls Result)
    (tape : FreshAnswerTape Digest256 remaining) :
    (runSchedulerNative transitionFuel remaining cursor tape).terminal =
      runSchedulerNativeListTerminal transitionFuel cursor
        (freshAnswerTapeToList tape) := by
  induction remaining generalizing cursor with
  | zero =>
      simp [runSchedulerNative, runSchedulerNativeListTerminal,
        freshAnswerTapeToList, runSchedulerNativeListTerminalFrom]
  | succ remaining ih =>
      simp only [runSchedulerNative, runSchedulerNativeListTerminal,
        freshAnswerTapeToList, runSchedulerNativeListTerminalFrom]
      cases request : seekSchedulerNativeExposure transitionFuel cursor <;>
        simp only [request]
      all_goals exact ih _ tape.2

def prefixFailureTerminal {Result : Type u} :
    ProjectedMachinePrefixFailure → SchedulerNativeTerminal Result
  | .exposureExhausted => .failed .exposureExhausted
  | .explicitAbort reason => .failed (.explicitOracleAbort reason)
  | .resourceAbort reason => .failed (.resourceOracleAbort reason)
  | .outOfFuel => .failed .machineOutOfFuel

def machinePrefixContinuationTransitionFuel
    (transitionFuel current : Nat) : List (ShaInput × Digest256) → Nat
  | [] => current
  | _ :: _ => transitionFuel - 1

@[simp] theorem machine_prefix_continuation_transition_fuel_after_reset
    (resetCurrent : Nat) (freshQueries : List (ShaInput × Digest256)) :
    machinePrefixContinuationTransitionFuel (resetCurrent + 1) resetCurrent
      freshQueries = resetCurrent := by
  cases freshQueries <;> simp [machinePrefixContinuationTransitionFuel]

/-- Factorized terminal of a leading machine, parameterized by the scheduler's
already-certified first normalization result. -/
def terminalAfterCertifiedProjectedMachinePrefix
    {globalOracleCalls : Nat} {Result MachineResult : Type u}
    (transitionFuel currentTransitionFuel : Nat)
    (limits : OracleLimits)
    (limitBound : limits.totalCalls ≤ globalOracleCalls)
    (actor : QueryActor) (state : OracleState)
    (program : OracleMachine MachineResult) (fuel : Nat)
    (coherent : HistoryTotalCoherent state)
    (onReturned : (result : MachineResult) → (state : OracleState) →
      HistoryTotalCoherent state →
        SchedulerNativeCursor globalOracleCalls Result)
    (certified : CoherentSeekResult MachineResult limits)
    (certifiedExact :
      seekNextFresh limits actor fuel state program coherent =
        certified.value)
    (answers : List Digest256) : SchedulerNativeTerminal Result :=
  match currentTransitionFuel with
  | 0 => .failed .transitionLimit
  | current + 1 =>
      match consumeCertifiedProjectedMachinePrefix limits actor answers fuel
          state program coherent certified certifiedExact with
      | .error reason => prefixFailureTerminal reason
      | .ok returned =>
          /- A fresh coordinate resets the scheduler's normalization budget.
          Thus a zero-fresh machine return continues with the predecessor of
          the caller's current budget, while a nonempty machine segment
          continues with the predecessor of the reset budget. -/
          runSchedulerNativeListTerminalFrom transitionFuel
            (machinePrefixContinuationTransitionFuel transitionFuel current
              returned.freshQueries)
            (onReturned returned.result returned.finalState
              returned.finalCoherent)
            returned.remaining

/-- Public wrapper instantiated with the exact certified normalizer object
used by `seekSchedulerNativeExposure`. -/
def terminalAfterProjectedMachinePrefix
    {globalOracleCalls : Nat} {Result MachineResult : Type u}
    (transitionFuel currentTransitionFuel : Nat)
    (limits : OracleLimits)
    (limitBound : limits.totalCalls ≤ globalOracleCalls)
    (actor : QueryActor) (state : OracleState)
    (program : OracleMachine MachineResult) (fuel : Nat)
    (coherent : HistoryTotalCoherent state)
    (onReturned : (result : MachineResult) → (state : OracleState) →
      HistoryTotalCoherent state →
        SchedulerNativeCursor globalOracleCalls Result)
    (answers : List Digest256) : SchedulerNativeTerminal Result :=
  terminalAfterCertifiedProjectedMachinePrefix transitionFuel
    currentTransitionFuel limits limitBound actor state program fuel coherent
    onReturned (certifiedSeekNextFresh limits actor fuel state program coherent)
    rfl answers

theorem run_scheduler_native_list_failed_of_positive
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (reason : SchedulerNativeFailure) (answers : List Digest256) :
    runSchedulerNativeListTerminalFrom transitionFuel transitionFuel
        (.failed reason : SchedulerNativeCursor globalOracleCalls Result)
        answers = .failed reason := by
  induction answers with
  | nil =>
      cases transitionFuel with
      | zero => omega
      | succ transitionFuel =>
          simp [runSchedulerNativeListTerminalFrom, terminalAtExposureEnd,
            seekSchedulerNativeExposure]
  | cons answer rest ih =>
      cases transitionFuel with
      | zero => omega
      | succ transitionFuel =>
          simpa [runSchedulerNativeListTerminalFrom,
            seekSchedulerNativeExposure] using ih

theorem run_scheduler_native_list_returned_of_positive
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (result : Result) (answers : List Digest256) :
    runSchedulerNativeListTerminalFrom transitionFuel transitionFuel
        (.returned result : SchedulerNativeCursor globalOracleCalls Result)
        answers = .returned result := by
  induction answers with
  | nil =>
      cases transitionFuel with
      | zero => omega
      | succ transitionFuel =>
          simp [runSchedulerNativeListTerminalFrom, terminalAtExposureEnd,
            seekSchedulerNativeExposure]
  | cons answer rest ih =>
      cases transitionFuel with
      | zero => omega
      | succ transitionFuel =>
          simpa [runSchedulerNativeListTerminalFrom,
            seekSchedulerNativeExposure] using ih

/-! ## Certified leading-machine factorization -/

/-- Once the shared certified normalizer result is explicit, the factorization
is a structural induction on the available answers.  There is no dependent
rewrite through the raw `seekNextFresh` result. -/
theorem run_scheduler_native_list_certified_machine_factorization
    {globalOracleCalls : Nat} {Result MachineResult : Type u}
    (transitionFuel : Nat)
    (limits : OracleLimits)
    (limitBound : limits.totalCalls ≤ globalOracleCalls)
    (actor : QueryActor) (state : OracleState)
    (program : OracleMachine MachineResult) (fuel : Nat)
    (coherent : HistoryTotalCoherent state)
    (onReturned : (result : MachineResult) → (state : OracleState) →
      HistoryTotalCoherent state →
        SchedulerNativeCursor globalOracleCalls Result)
    (certified : CoherentSeekResult MachineResult limits)
    (certifiedExact :
      seekNextFresh limits actor fuel state program coherent =
        certified.value) :
    0 < transitionFuel →
    ∀ (currentTransitionFuel : Nat) (answers : List Digest256),
      runSchedulerNativeListTerminalFromCertifiedMachine transitionFuel
          currentTransitionFuel limits limitBound actor state program fuel
          coherent onReturned certified answers =
        terminalAfterCertifiedProjectedMachinePrefix transitionFuel
          currentTransitionFuel limits limitBound actor state program fuel
          coherent onReturned certified certifiedExact answers := by
  intro transitionFuelPositive
  cases transitionFuel with
  | zero => omega
  | succ resetCurrent =>
      intro currentTransitionFuel answers
      induction answers generalizing currentTransitionFuel state program fuel
          certified with
      | nil =>
          cases currentTransitionFuel with
          | zero => rfl
          | succ current =>
              rcases certified with ⟨value, valueCoherent⟩
              cases value <;> rfl
      | cons answer rest ih =>
          cases currentTransitionFuel with
          | zero =>
              unfold runSchedulerNativeListTerminalFromCertifiedMachine
              unfold runSchedulerNativeListTerminalAfterRequest
              unfold terminalAfterCertifiedProjectedMachinePrefix
              exact run_scheduler_native_list_failed_of_positive
                (resetCurrent + 1) (by omega) .transitionLimit rest
          | succ current =>
              rcases certified with ⟨value, valueCoherent⟩
              cases value with
              | returned result finalState steps => rfl
              | explicitAbort reason finalState steps =>
                  exact run_scheduler_native_list_failed_of_positive
                    (resetCurrent + 1) (by omega)
                    (.explicitOracleAbort reason) rest
              | resourceAbort reason finalState steps =>
                  exact run_scheduler_native_list_failed_of_positive
                    (resetCurrent + 1) (by omega)
                    (.resourceOracleAbort reason) rest
              | outOfFuel finalState steps =>
                  exact run_scheduler_native_list_failed_of_positive
                    (resetCurrent + 1) (by omega) .machineOutOfFuel rest
              | request requestState input next remainingFuel cachedSteps
                  requestCoherent totalRoom freshRoom missing =>
                  unfold runSchedulerNativeListTerminalFromCertifiedMachine
                  unfold runSchedulerNativeListTerminalAfterRequest
                  unfold nativeRequestOfCoherentSeekResult
                  unfold terminalAfterCertifiedProjectedMachinePrefix
                  unfold consumeCertifiedProjectedMachinePrefix
                  simp only
                  rw [run_scheduler_native_list_machine_eq_certified
                    (resetCurrent + 1) (resetCurrent + 1) limits limitBound
                    actor (freshQueryState actor requestState input answer)
                    (next answer) remainingFuel
                    (fresh_query_state_preserves_history_total_coherent actor
                      requestState input answer requestCoherent)
                    onReturned rest]
                  rw [ih
                    (freshQueryState actor requestState input answer)
                    (next answer) remainingFuel
                    (fresh_query_state_preserves_history_total_coherent actor
                      requestState input answer requestCoherent)
                    (certifiedSeekNextFresh limits actor remainingFuel
                      (freshQueryState actor requestState input answer)
                      (next answer)
                      (fresh_query_state_preserves_history_total_coherent actor
                        requestState input answer requestCoherent))
                    rfl (resetCurrent + 1)]
                  unfold terminalAfterCertifiedProjectedMachinePrefix
                  simp only
                  cases tail : consumeCertifiedProjectedMachinePrefix limits
                    actor rest remainingFuel
                    (freshQueryState actor requestState input answer)
                    (next answer)
                    (fresh_query_state_preserves_history_total_coherent actor
                      requestState input answer requestCoherent)
                    (certifiedSeekNextFresh limits actor remainingFuel
                      (freshQueryState actor requestState input answer)
                      (next answer)
                      (fresh_query_state_preserves_history_total_coherent actor
                        requestState input answer requestCoherent)) rfl with
                  | error reason => rfl
                  | ok returned =>
                      simp only
                      rw [
                        machine_prefix_continuation_transition_fuel_after_reset]
                      rfl

/-- The native scheduler's leading machine is definitionally the projected
prefix consumer followed by the same callback. -/
theorem run_scheduler_native_list_machine_factorization
    {globalOracleCalls : Nat} {Result MachineResult : Type u}
    (transitionFuel : Nat)
    (limits : OracleLimits)
    (limitBound : limits.totalCalls ≤ globalOracleCalls)
    (actor : QueryActor) (state : OracleState)
    (program : OracleMachine MachineResult) (fuel : Nat)
    (coherent : HistoryTotalCoherent state)
    (onReturned : (result : MachineResult) → (state : OracleState) →
      HistoryTotalCoherent state →
        SchedulerNativeCursor globalOracleCalls Result) :
    0 < transitionFuel →
    ∀ (currentTransitionFuel : Nat) (answers : List Digest256),
      runSchedulerNativeListTerminalFrom transitionFuel currentTransitionFuel
          (.machine limits limitBound actor state program fuel coherent
            onReturned)
          answers =
        terminalAfterProjectedMachinePrefix transitionFuel
          currentTransitionFuel limits limitBound actor state program fuel
          coherent onReturned answers := by
  intro transitionFuelPositive currentTransitionFuel answers
  rw [run_scheduler_native_list_machine_eq_certified transitionFuel
    currentTransitionFuel limits limitBound actor state program fuel coherent
    onReturned answers]
  exact run_scheduler_native_list_certified_machine_factorization transitionFuel
    limits limitBound actor state program fuel coherent onReturned
    (certifiedSeekNextFresh limits actor fuel state program coherent) rfl
    transitionFuelPositive currentTransitionFuel answers

#print axioms run_scheduler_native_terminal_eq_list
#print axioms run_scheduler_native_list_machine_factorization

end

end AspisK1.V7Tag73SchedulerMachineFactorization
