import AspisFormal.K1.V7Tag73AtomicForkUniformScheduler

/-!
# Result-carrying adaptive scheduler for the plain Tag-73 ROM game

`UnifiedExposureCursor` is the right nonanticipating object for the finite
lazy-ROM probability proof, but its terminal constructor deliberately carries
no result.  Consequently `runUnifiedExposureTrace` can prove a target bound but
cannot itself define the `ExperimentOutcome` or the concrete K1.2--K1.5 world:
all machine return values have been erased by the time the cursor halts.

This module adds the minimal missing operational primitive.  The cursor below
has exactly the machine and atomic-pair transitions of the probability
scheduler, but retains either a final result or a concrete failure.  Erasing
the result gives the existing `UnifiedExposureCursor`.  The fixed-length
interpreter consumes the same master answer tape, pads after a terminal result,
and records one existing `UnifiedExposureRecord` per tape coordinate.

There is no arbitrary outcome function, restore function, acceptance cover,
interactive-world field, or extractor conclusion in this module.  A later
Tag-73 phase dispatcher must choose the continuations from actual raw prover,
future-free verifier, and strict-replacement returns.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73SchedulerNativeResult

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AtomicPairReplay
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73AtomicForkUniformScheduler

noncomputable section

universe u

local instance historyTotalCoherentDecidable (state : OracleState) :
    Decidable (HistoryTotalCoherent state) := by
  unfold HistoryTotalCoherent
  infer_instance

/-! ## Coherence retained by zero-exposure normalization -/

/-- Every state exposed by `seekNextFresh` has the same exact
`history.length = totalCalls` invariant as its input.  The request constructor
already stores this proof; naming the uniform predicate lets terminal returns
carry it into the next scheduler phase rather than asking a caller for it. -/
def SeekResultStateCoherent
    {MachineResult : Type*} {limits : OracleLimits} :
    SeekNextFreshResult MachineResult limits → Prop
  | .returned _ state _ => HistoryTotalCoherent state
  | .explicitAbort _ state _ => HistoryTotalCoherent state
  | .resourceAbort _ state _ => HistoryTotalCoherent state
  | .outOfFuel state _ => HistoryTotalCoherent state
  | .request state _ _ _ _ _ _ _ _ => HistoryTotalCoherent state

@[simp] theorem seek_result_state_coherent_add_completed_query
    {MachineResult : Type*} {limits : OracleLimits}
    (result : SeekNextFreshResult MachineResult limits) :
    SeekResultStateCoherent result.addCompletedQuery ↔
      SeekResultStateCoherent result := by
  cases result <;> rfl

/-- Cached-query normalization cannot lose coherence.  This is proved from
the executable recursion and is not a continuation premise. -/
theorem seek_next_fresh_result_state_coherent
    {MachineResult : Type*}
    (limits : OracleLimits) (actor : QueryActor) :
    ∀ (fuel : Nat) (state : OracleState)
      (program : OracleMachine MachineResult)
      (coherent : HistoryTotalCoherent state),
      SeekResultStateCoherent
        (seekNextFresh limits actor fuel state program coherent) := by
  intro fuel
  induction fuel with
  | zero =>
      intro state program coherent
      cases program <;> exact coherent
  | succ fuel ih =>
      intro state program coherent
      cases program with
      | pure result => exact coherent
      | abort reason => exact coherent
      | query input next =>
          simp only [seekNextFresh]
          split
          next totalBlocked => exact coherent
          next totalRoom =>
            split
            next entry found =>
              rw [seek_result_state_coherent_add_completed_query]
              exact ih
                (cachedQueryState actor state input entry)
                (next entry.output)
                (cached_query_state_preserves_history_total_coherent actor
                  state input entry coherent)
            next missing =>
              split
              next freshBlocked => exact coherent
              next freshRoom => exact coherent

theorem seek_next_fresh_returned_state_coherent
    {MachineResult : Type*}
    (limits : OracleLimits) (actor : QueryActor) (fuel : Nat)
    (state finalState : OracleState)
    (program : OracleMachine MachineResult)
    (coherent : HistoryTotalCoherent state)
    (result : MachineResult) (steps : Nat)
    (returned : seekNextFresh limits actor fuel state program coherent =
      .returned result finalState steps) :
    HistoryTotalCoherent finalState := by
  have invariant := seek_next_fresh_result_state_coherent limits actor fuel
    state program coherent
  rw [returned] at invariant
  exact invariant

/-! ## A result-carrying cursor and its result-free erasure -/

/-- Concrete ways in which the scheduler can stop without a final protocol
result.  `transitionLimit` and `exposureExhausted` are scheduler resources;
the other constructors retain the exact machine failure. -/
inductive SchedulerNativeFailure where
  | transitionLimit
  | exposureExhausted
  | explicitOracleAbort (reason : OracleAbort)
  | resourceOracleAbort (reason : OracleAbort)
  | machineOutOfFuel
  deriving DecidableEq, Repr

/-- The result-carrying analogue of `UnifiedExposureCursor`.  The operational
constructors are deliberately literal copies of the result-free scheduler.
Only `returned` and `failed` refine its single `halted` constructor. -/
inductive SchedulerNativeCursor (globalOracleCalls : Nat) (Result : Type u) where
  | machine
      {MachineResult : Type u}
      (limits : OracleLimits)
      (limitBound : limits.totalCalls ≤ globalOracleCalls)
      (actor : QueryActor)
      (state : OracleState)
      (program : OracleMachine MachineResult)
      (fuel : Nat)
      (coherent : HistoryTotalCoherent state)
      (onReturned : (result : MachineResult) → (state : OracleState) →
        HistoryTotalCoherent state →
          SchedulerNativeCursor globalOracleCalls Result)
  | forkPair
      (frozenHistory : List QueryRecord)
      (pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls)
      (outputInput advanceInput : ShaInput)
      (template : AtomicPairReplayConfiguration)
      (next : AtomicPairReplayConfiguration →
        SchedulerNativeCursor globalOracleCalls Result)
  | forkAdvance
      (frozenHistory : List QueryRecord)
      (pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls)
      (outputInput advanceInput : ShaInput)
      (template : AtomicPairReplayConfiguration)
      (forkOutput : Digest256)
      (next : AtomicPairReplayConfiguration →
        SchedulerNativeCursor globalOracleCalls Result)
  | returned (result : Result)
  | failed (reason : SchedulerNativeFailure)

/-- Forget only terminal data.  Every live transition is retained literally,
including the actor, limits, oracle state, program, pair inputs and adaptive
continuation. -/
def SchedulerNativeCursor.erase
    {globalOracleCalls : Nat} {Result : Type*} :
    SchedulerNativeCursor globalOracleCalls Result →
      UnifiedExposureCursor globalOracleCalls
  | .machine limits limitBound actor state program fuel coherent onReturned =>
      .machine limits limitBound actor state program fuel coherent
        (fun result finalState =>
          if finalCoherent : HistoryTotalCoherent finalState then
            (onReturned result finalState finalCoherent).erase
          else
            .halted)
  | .forkPair frozenHistory pairRoom outputInput advanceInput template next =>
      .forkPair frozenHistory pairRoom outputInput advanceInput template
        (fun configuration => (next configuration).erase)
  | .forkAdvance frozenHistory pairRoom outputInput advanceInput template
      forkOutputValue next =>
      .forkAdvance frozenHistory pairRoom outputInput advanceInput template
        forkOutputValue (fun configuration => (next configuration).erase)
  | .returned _ => .halted
  | .failed _ => .halted

/-! ## Pause at the next exposure without erasing terminal data -/

inductive SchedulerNativeRequest (globalOracleCalls : Nat) (Result : Type u) where
  | returned (result : Result)
  | failed (reason : SchedulerNativeFailure)
  | transitionLimit
  | machineFresh
      {MachineResult : Type u}
      (limits : OracleLimits)
      (limitBound : limits.totalCalls ≤ globalOracleCalls)
      (actor : QueryActor)
      (state : OracleState) (input : ShaInput)
      (nextProgram : ShaOutput → OracleMachine MachineResult)
      (remainingFuel : Nat)
      (coherent : HistoryTotalCoherent state)
      (totalRoom : state.totalCalls < limits.totalCalls)
      (freshRoom : state.freshCalls < limits.freshCalls)
      (missing : lookupEntry state input = none)
      (onReturned : (result : MachineResult) → (state : OracleState) →
        HistoryTotalCoherent state →
          SchedulerNativeCursor globalOracleCalls Result)
  | forkOutput
      (frozenHistory : List QueryRecord)
      (pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls)
      (outputInput advanceInput : ShaInput)
      (template : AtomicPairReplayConfiguration)
      (next : AtomicPairReplayConfiguration →
        SchedulerNativeCursor globalOracleCalls Result)
  | forkAdvance
      (frozenHistory : List QueryRecord)
      (pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls)
      (outputInput advanceInput : ShaInput)
      (template : AtomicPairReplayConfiguration)
      (forkOutput : Digest256)
      (next : AtomicPairReplayConfiguration →
        SchedulerNativeCursor globalOracleCalls Result)

def SchedulerNativeRequest.erase
    {globalOracleCalls : Nat} {Result : Type*} :
    SchedulerNativeRequest globalOracleCalls Result →
      UnifiedExposureRequest globalOracleCalls
  | .returned _ => .halted
  | .failed _ => .halted
  | .transitionLimit => .transitionLimit
  | .machineFresh limits limitBound actor state input nextProgram
      remainingFuel coherent totalRoom freshRoom missing onReturned =>
      .machineFresh limits limitBound actor state input nextProgram
        remainingFuel coherent totalRoom freshRoom missing
        (fun result finalState =>
          if finalCoherent : HistoryTotalCoherent finalState then
            (onReturned result finalState finalCoherent).erase
          else
            .halted)
  | .forkOutput frozenHistory pairRoom outputInput advanceInput template next =>
      .forkOutput frozenHistory pairRoom outputInput advanceInput template
        (fun configuration => (next configuration).erase)
  | .forkAdvance frozenHistory pairRoom outputInput advanceInput template
      forkOutputValue next =>
      .forkAdvance frozenHistory pairRoom outputInput advanceInput template
        forkOutputValue (fun configuration => (next configuration).erase)

/-- One normalized machine result together with the invariant proved by the
normalizer itself.  Packaging the proof with the result is important here:
the scheduler consumes this object operationally, rather than accepting an
unrelated proof about a separately supplied result. -/
structure CoherentSeekResult
    (MachineResult : Type u) (limits : OracleLimits) where
  value : SeekNextFreshResult MachineResult limits
  coherent : SeekResultStateCoherent value

/-- Run the executable normalizer and retain its proved state invariant in one
dependent result. -/
def certifiedSeekNextFresh
    {MachineResult : Type u}
    (limits : OracleLimits) (actor : QueryActor) (fuel : Nat)
    (state : OracleState) (program : OracleMachine MachineResult)
    (coherent : HistoryTotalCoherent state) :
    CoherentSeekResult MachineResult limits :=
  { value := seekNextFresh limits actor fuel state program coherent
    coherent := seek_next_fresh_result_state_coherent limits actor fuel state
      program coherent }

@[simp] theorem certified_seek_next_fresh_value
    {MachineResult : Type u}
    (limits : OracleLimits) (actor : QueryActor) (fuel : Nat)
    (state : OracleState) (program : OracleMachine MachineResult)
    (coherent : HistoryTotalCoherent state) :
    (certifiedSeekNextFresh limits actor fuel state program coherent).value =
      seekNextFresh limits actor fuel state program coherent := by
  rfl

/-- Extract the terminal-state invariant by rewriting the invariant packaged
with a certified normalizer result.  The equality is generated by the
operational match below; callers cannot manufacture an unrelated terminal
state. -/
theorem coherentSeekReturnedState
    {MachineResult : Type u} {limits : OracleLimits}
    (certified : CoherentSeekResult MachineResult limits)
    (result : MachineResult) (finalState : OracleState) (steps : Nat)
    (returned : certified.value = .returned result finalState steps) :
    HistoryTotalCoherent finalState := by
  have invariant := certified.coherent
  rw [returned] at invariant
  exact invariant

/-- Convert one operationally certified `seekNextFresh` result to the native
request grammar.  The returned-state coherence proof comes from the packaged
normalizer result, never from a continuation premise. -/
def nativeRequestOfCoherentSeekResult
    {globalOracleCalls : Nat} {Result MachineResult : Type u}
    (limits : OracleLimits)
    (limitBound : limits.totalCalls ≤ globalOracleCalls)
    (actor : QueryActor)
    (onReturned : (result : MachineResult) → (state : OracleState) →
      HistoryTotalCoherent state →
        SchedulerNativeCursor globalOracleCalls Result)
    (continueReturned : (result : MachineResult) → (state : OracleState) →
      HistoryTotalCoherent state →
        SchedulerNativeRequest globalOracleCalls Result)
    (certified : CoherentSeekResult MachineResult limits) :
    SchedulerNativeRequest globalOracleCalls Result :=
  match returned : certified.value with
  | .returned result finalState _steps =>
      continueReturned result finalState
        (coherentSeekReturnedState certified result finalState _steps returned)
  | .request requestState input nextProgram remainingFuel _steps
      requestCoherent totalRoom freshRoom missing =>
      .machineFresh limits limitBound actor requestState input nextProgram
        remainingFuel requestCoherent totalRoom freshRoom missing onReturned
  | .explicitAbort reason _finalState _steps =>
      .failed (.explicitOracleAbort reason)
  | .resourceAbort reason _finalState _steps =>
      .failed (.resourceOracleAbort reason)
  | .outOfFuel _finalState _steps => .failed .machineOutOfFuel

/-- Erasure of a coherence-certified seek result commutes with a returned
continuation whose own erasure is aligned with the result-free scheduler. -/
theorem erase_native_request_of_coherent_seek_result
    {globalOracleCalls : Nat} {Result MachineResult : Type u}
    (limits : OracleLimits)
    (limitBound : limits.totalCalls ≤ globalOracleCalls)
    (actor : QueryActor)
    (transitionFuel : Nat)
    (onReturned : (result : MachineResult) → (state : OracleState) →
      HistoryTotalCoherent state →
        SchedulerNativeCursor globalOracleCalls Result)
    (continueReturned : (result : MachineResult) → (state : OracleState) →
      HistoryTotalCoherent state →
        SchedulerNativeRequest globalOracleCalls Result)
    (aligned : ∀ result finalState
      (finalCoherent : HistoryTotalCoherent finalState),
      (continueReturned result finalState finalCoherent).erase =
        seekUnifiedExposure transitionFuel
          (onReturned result finalState finalCoherent).erase)
    (certified : CoherentSeekResult MachineResult limits) :
    (nativeRequestOfCoherentSeekResult limits limitBound actor onReturned
        continueReturned certified).erase =
      match certified.value with
      | .returned result finalState _steps =>
          seekUnifiedExposure transitionFuel
            (if finalCoherent : HistoryTotalCoherent finalState then
              (onReturned result finalState finalCoherent).erase
            else
              .halted)
      | .request requestState input nextProgram remainingFuel _steps
          requestCoherent totalRoom freshRoom missing =>
          .machineFresh limits limitBound actor requestState input nextProgram
            remainingFuel requestCoherent totalRoom freshRoom missing
            (fun result finalState =>
              if finalCoherent : HistoryTotalCoherent finalState then
                (onReturned result finalState finalCoherent).erase
              else
                .halted)
      | .explicitAbort _reason _finalState _steps => .halted
      | .resourceAbort _reason _finalState _steps => .halted
      | .outOfFuel _finalState _steps => .halted
       := by
  rcases certified with ⟨sought, soughtCoherent⟩
  cases sought with
  | returned result finalState steps =>
      have finalCoherent : HistoryTotalCoherent finalState := soughtCoherent
      simpa [nativeRequestOfCoherentSeekResult, finalCoherent] using
        aligned result finalState finalCoherent
  | explicitAbort reason finalState steps => rfl
  | resourceAbort reason finalState steps => rfl
  | outOfFuel finalState steps => rfl
  | request requestState input nextProgram remainingFuel steps requestCoherent
      totalRoom freshRoom missing =>
      rfl

/-- Normalize cached and pure transitions exactly as `seekUnifiedExposure`,
but retain machine failures and the terminal result. -/
def seekSchedulerNativeExposure
    {globalOracleCalls : Nat} {Result : Type*} :
    Nat → SchedulerNativeCursor globalOracleCalls Result →
      SchedulerNativeRequest globalOracleCalls Result
  | 0, _cursor => .transitionLimit
  | _transitionFuel + 1, .returned result => .returned result
  | _transitionFuel + 1, .failed reason => .failed reason
  | _transitionFuel + 1,
      .forkPair frozenHistory pairRoom outputInput advanceInput template next =>
      .forkOutput frozenHistory pairRoom outputInput advanceInput template next
  | _transitionFuel + 1,
      .forkAdvance frozenHistory pairRoom outputInput advanceInput template
        forkOutput next =>
      .forkAdvance frozenHistory pairRoom outputInput advanceInput template
        forkOutput next
  | transitionFuel + 1,
      .machine limits limitBound actor state program fuel coherent onReturned =>
      nativeRequestOfCoherentSeekResult limits limitBound actor onReturned
        (fun result finalState finalCoherent =>
          seekSchedulerNativeExposure transitionFuel
            (onReturned result finalState finalCoherent))
        (certifiedSeekNextFresh limits actor fuel state program coherent)

@[simp] theorem seek_scheduler_native_returned
    {globalOracleCalls : Nat} {Result : Type*}
    (transitionFuel : Nat) (result : Result) :
    seekSchedulerNativeExposure (transitionFuel + 1)
      (.returned result : SchedulerNativeCursor globalOracleCalls Result) =
        .returned result := by
  rfl

/-- Kernel-checked alignment with the result-free cursor used by the causal
target tree. -/
theorem erase_seek_scheduler_native_exposure
    {globalOracleCalls : Nat} {Result : Type*}
    (transitionFuel : Nat)
    (cursor : SchedulerNativeCursor globalOracleCalls Result) :
    (seekSchedulerNativeExposure transitionFuel cursor).erase =
      seekUnifiedExposure transitionFuel cursor.erase := by
  induction transitionFuel generalizing cursor with
  | zero =>
      simp [seekSchedulerNativeExposure, SchedulerNativeRequest.erase,
        seekUnifiedExposure]
  | succ transitionFuel ih =>
      cases cursor with
      | returned result =>
          simp [seekSchedulerNativeExposure, SchedulerNativeCursor.erase,
            SchedulerNativeRequest.erase, seekUnifiedExposure]
      | failed reason =>
          simp [seekSchedulerNativeExposure, SchedulerNativeCursor.erase,
            SchedulerNativeRequest.erase, seekUnifiedExposure]
      | forkPair frozenHistory pairRoom outputInput advanceInput template next =>
          simp [seekSchedulerNativeExposure, SchedulerNativeCursor.erase,
            SchedulerNativeRequest.erase, seekUnifiedExposure]
      | forkAdvance frozenHistory pairRoom outputInput advanceInput template
          forkOutputValue next =>
          simp [seekSchedulerNativeExposure, SchedulerNativeCursor.erase,
            SchedulerNativeRequest.erase]
      | @machine MachineResult limits limitBound actor state program fuel
          coherent onReturned =>
          simp only [seekSchedulerNativeExposure,
            SchedulerNativeCursor.erase, seekUnifiedExposure]
          convert erase_native_request_of_coherent_seek_result
            limits limitBound actor transitionFuel onReturned
            (fun result finalState finalCoherent =>
              seekSchedulerNativeExposure transitionFuel
                (onReturned result finalState finalCoherent))
            (by
              intro result finalState finalCoherent
              exact ih (onReturned result finalState finalCoherent))
            (certifiedSeekNextFresh limits actor fuel state program coherent)
            using 1 <;>
            simp only [certified_seek_next_fresh_value]
          generalize soughtEq :
            seekNextFresh limits actor fuel state program coherent = sought
          cases sought <;> rfl

/-! ## Fixed-length result interpreter -/

inductive SchedulerNativeTerminal (Result : Type*) where
  | returned (result : Result)
  | failed (reason : SchedulerNativeFailure)

structure SchedulerNativeRun (Result : Type*) where
  terminal : SchedulerNativeTerminal Result
  trace : List UnifiedExposureRecord

def terminalAtExposureEnd
    {globalOracleCalls : Nat} {Result : Type*}
    (transitionFuel : Nat)
    (cursor : SchedulerNativeCursor globalOracleCalls Result) :
    SchedulerNativeTerminal Result :=
  match seekSchedulerNativeExposure transitionFuel cursor with
  | .returned result => .returned result
  | .failed reason => .failed reason
  | .transitionLimit => .failed .transitionLimit
  | .machineFresh .. => .failed .exposureExhausted
  | .forkOutput .. => .failed .exposureExhausted
  | .forkAdvance .. => .failed .exposureExhausted

/-- Consume the fixed master tape.  Terminal and failure states consume the
remaining coordinates as inert padding, so the probability space never
depends on early termination.  At the end of the tape, cached/pure transitions
are still normalized; needing one more fresh or fork coordinate is the exact
`exposureExhausted` failure. -/
def runSchedulerNative
    {globalOracleCalls : Nat} {Result : Type*}
    (transitionFuel : Nat) :
    (remaining : Nat) → SchedulerNativeCursor globalOracleCalls Result →
      FreshAnswerTape Digest256 remaining → SchedulerNativeRun Result
  | 0, cursor, _tape =>
      { terminal := terminalAtExposureEnd transitionFuel cursor
        trace := [] }
  | remaining + 1, cursor, tape =>
      match seekSchedulerNativeExposure transitionFuel cursor with
      | .returned result =>
          let tail := runSchedulerNative transitionFuel remaining
            (.returned result : SchedulerNativeCursor globalOracleCalls Result)
            tape.2
          { terminal := tail.terminal
            trace := .padding tape.1 :: tail.trace }
      | .failed reason =>
          let tail := runSchedulerNative transitionFuel remaining
            (.failed reason : SchedulerNativeCursor globalOracleCalls Result)
            tape.2
          { terminal := tail.terminal
            trace := .padding tape.1 :: tail.trace }
      | .transitionLimit =>
          let tail := runSchedulerNative transitionFuel remaining
            (.failed .transitionLimit :
              SchedulerNativeCursor globalOracleCalls Result) tape.2
          { terminal := tail.terminal
            trace := .padding tape.1 :: tail.trace }
      | .machineFresh limits limitBound actor state input nextProgram
          remainingFuel coherent _totalRoom _freshRoom _missing onReturned =>
          let tail := runSchedulerNative transitionFuel remaining
            (.machine limits limitBound actor
              (freshQueryState actor state input tape.1)
              (nextProgram tape.1) remainingFuel
              (fresh_query_state_preserves_history_total_coherent actor state
                input tape.1 coherent) onReturned) tape.2
          { terminal := tail.terminal
            trace := .machineFresh actor input tape.1 :: tail.trace }
      | .forkOutput frozenHistory pairRoom outputInput advanceInput template
          next =>
          let tail := runSchedulerNative transitionFuel remaining
            (.forkAdvance frozenHistory pairRoom outputInput advanceInput
              template tape.1 next) tape.2
          { terminal := tail.terminal
            trace := .forkOutput frozenHistory outputInput advanceInput template
              tape.1 :: tail.trace }
      | .forkAdvance frozenHistory _pairRoom outputInput advanceInput template
          forkOutput next =>
          let scheduled : ScheduledForkCoins :=
            { frozenHistory := frozenHistory
              outputInput := outputInput
              advanceInput := advanceInput
              template := template
              forkOutput := forkOutput
              forkAdvance := tape.1 }
          let tail := runSchedulerNative transitionFuel remaining
            (next scheduled.configuration) tape.2
          { terminal := tail.terminal
            trace := .forkAdvance scheduled :: tail.trace }

theorem run_scheduler_native_trace_length_exact
    {globalOracleCalls : Nat} {Result : Type*}
    (transitionFuel remaining : Nat)
    (cursor : SchedulerNativeCursor globalOracleCalls Result)
    (tape : FreshAnswerTape Digest256 remaining) :
    (runSchedulerNative transitionFuel remaining cursor tape).trace.length =
      remaining := by
  induction remaining generalizing cursor with
  | zero => rfl
  | succ remaining ih =>
      simp only [runSchedulerNative]
      cases request : seekSchedulerNativeExposure transitionFuel cursor <;>
        simp [ih]

/-- The result-carrying interpreter has exactly the same exposure trace as the
existing scheduler after terminal data is erased.  Hence its bad-event target
tree is not a second or independently chosen probability experiment. -/
theorem run_scheduler_native_trace_eq_erased_unified_trace
    {globalOracleCalls : Nat} {Result : Type*}
    (transitionFuel remaining : Nat)
    (cursor : SchedulerNativeCursor globalOracleCalls Result)
    (tape : FreshAnswerTape Digest256 remaining) :
    (runSchedulerNative transitionFuel remaining cursor tape).trace =
      runUnifiedExposureTrace transitionFuel remaining cursor.erase tape := by
  induction remaining generalizing cursor with
  | zero => rfl
  | succ remaining ih =>
      simp only [runSchedulerNative, runUnifiedExposureTrace]
      have aligned := erase_seek_scheduler_native_exposure transitionFuel cursor
      cases request : seekSchedulerNativeExposure transitionFuel cursor <;>
        simp only [request] at aligned ⊢ <;>
        rw [← aligned] <;>
        simp [SchedulerNativeRequest.erase, SchedulerNativeCursor.erase, ih]

theorem run_scheduler_native_answers_are_exact_tape
    {globalOracleCalls : Nat} {Result : Type*}
    (transitionFuel remaining : Nat)
    (cursor : SchedulerNativeCursor globalOracleCalls Result)
    (tape : FreshAnswerTape Digest256 remaining) :
    (runSchedulerNative transitionFuel remaining cursor tape).trace.map
        UnifiedExposureRecord.answer = freshAnswerTapeToList tape := by
  rw [run_scheduler_native_trace_eq_erased_unified_trace]
  exact run_unified_exposure_trace_answers_are_exact_tape transitionFuel
    remaining cursor.erase tape

@[simp] theorem run_scheduler_native_returned_padding
    {globalOracleCalls : Nat} {Result : Type*}
    (transitionFuel remaining : Nat) (result : Result)
    (tape : FreshAnswerTape Digest256 remaining) :
    (runSchedulerNative (transitionFuel + 1) remaining
      (.returned result : SchedulerNativeCursor globalOracleCalls Result)
      tape).terminal = .returned result := by
  induction remaining with
  | zero =>
      simp [runSchedulerNative, terminalAtExposureEnd,
        seek_scheduler_native_returned]
  | succ remaining ih =>
      simp only [runSchedulerNative, seek_scheduler_native_returned]
      exact ih tape.2

/-- A direct atomic fork uses adjacent master coordinates and delivers their
literal scheduled configuration to the result continuation. -/
theorem run_scheduler_native_direct_fork_returns_exact_configuration
    {globalOracleCalls : Nat} {Result : Type*}
    (transitionFuel : Nat)
    (frozenHistory : List QueryRecord)
    (pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls)
    (outputInput advanceInput : ShaInput)
    (template : AtomicPairReplayConfiguration)
    (observe : AtomicPairReplayConfiguration → Result)
    (forkOutput forkAdvance : Digest256) :
    (runSchedulerNative (transitionFuel + 1) 2
      (.forkPair frozenHistory pairRoom outputInput advanceInput template
        (fun configuration => .returned (observe configuration)))
      (forkOutput, (forkAdvance, PUnit.unit))).terminal =
        .returned
          (observe (scheduledForkConfiguration template forkOutput
            forkAdvance)) := by
  rfl

#print axioms erase_seek_scheduler_native_exposure
#print axioms run_scheduler_native_trace_length_exact
#print axioms run_scheduler_native_trace_eq_erased_unified_trace
#print axioms run_scheduler_native_answers_are_exact_tape
#print axioms run_scheduler_native_returned_padding
#print axioms run_scheduler_native_direct_fork_returns_exact_configuration

end

end AspisK1.V7Tag73SchedulerNativeResult
