import AspisFormal.K1.V7Tag73SchedulerTraceFactorization

/-!
# Scheduler-native pause at a selected fresh oracle input

This module scans the actual result-carrying scheduler list semantics.  It
pauses *before* consuming the answer of the first `machineFresh` request whose
input is the selected target.  The pause retains the normalized request, its
source cursor and transition budget, the already-consumed answer/trace prefix,
the answer at the target coordinate, and the untouched suffix.

The scanner is executable.  Its reconstruction theorems are proved by
induction over the same scheduler transitions as
`runSchedulerNativeListRunFrom`; no replay or source-equality premise is a
field of the paused state.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73SchedulerNativeTargetPause

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerTraceFactorization

noncomputable section

universe u

/-- Exact operational state at the first selected scheduler-native fresh
request.  `targetAnswer` has not yet been supplied to `nextProgram` or inserted
in `requestState`; `remainingAnswers` is therefore the literally unread suffix.
-/
structure SchedulerNativeFreshPause
    (globalOracleCalls : Nat) (Result : Type u) (target : ShaInput) where
  MachineResult : Type u
  limits : OracleLimits
  limitBound : limits.totalCalls ≤ globalOracleCalls
  actor : QueryActor
  requestState : OracleState
  input : ShaInput
  input_eq_target : input = target
  nextProgram : ShaOutput → OracleMachine MachineResult
  remainingFuel : Nat
  coherent : HistoryTotalCoherent requestState
  totalRoom : requestState.totalCalls < limits.totalCalls
  freshRoom : requestState.freshCalls < limits.freshCalls
  missing : lookupEntry requestState input = none
  onReturned : (result : MachineResult) → (state : OracleState) →
    HistoryTotalCoherent state →
      SchedulerNativeCursor globalOracleCalls Result
  sourceTransitionFuel : Nat
  sourceCursor : SchedulerNativeCursor globalOracleCalls Result
  requestExact :
    seekSchedulerNativeExposure sourceTransitionFuel sourceCursor =
      .machineFresh limits limitBound actor requestState input nextProgram
        remainingFuel coherent totalRoom freshRoom missing onReturned
  consumedAnswers : List Digest256
  consumedTrace : List UnifiedExposureRecord
  targetAnswer : Digest256
  remainingAnswers : List Digest256

/-- Resume immediately after supplying an arbitrary counterfactual answer to
the frozen fresh request.  This is an executable scheduler cursor, not a
postulated cross-world continuation. -/
def SchedulerNativeFreshPause.resumeCursorWith
    {globalOracleCalls : Nat} {Result : Type u} {target : ShaInput}
    (pause : SchedulerNativeFreshPause globalOracleCalls Result target)
    (answer : Digest256) :
    SchedulerNativeCursor globalOracleCalls Result :=
  .machine pause.limits pause.limitBound pause.actor
    (freshQueryState pause.actor pause.requestState pause.input
      answer)
    (pause.nextProgram answer) pause.remainingFuel
    (fresh_query_state_preserves_history_total_coherent pause.actor
      pause.requestState pause.input answer pause.coherent)
    pause.onReturned

/-- Resume with the retained real answer. -/
def SchedulerNativeFreshPause.resumeCursor
    {globalOracleCalls : Nat} {Result : Type u} {target : ShaInput}
    (pause : SchedulerNativeFreshPause globalOracleCalls Result target) :
    SchedulerNativeCursor globalOracleCalls Result :=
  pause.resumeCursorWith pause.targetAnswer

/-- Execute the frozen continuation with an arbitrary answer and arbitrary
subsequent master-tape suffix.  This total function includes terminal,
failure, machine, and atomic-fork paths through the ordinary scheduler. -/
def SchedulerNativeFreshPause.resumeRunWith
    {globalOracleCalls : Nat} {Result : Type u} {target : ShaInput}
    (transitionFuel : Nat)
    (pause : SchedulerNativeFreshPause globalOracleCalls Result target)
    (answer : Digest256) (remainingAnswers : List Digest256) :
    SchedulerNativeRun Result :=
  let tail := runSchedulerNativeListRunFrom transitionFuel transitionFuel
    (pause.resumeCursorWith answer) remainingAnswers
  { terminal := tail.terminal
    trace := pause.consumedTrace ++
      .machineFresh pause.actor pause.input answer :: tail.trace }

/-- Reconstruct the complete scheduler run represented by a pause. -/
def SchedulerNativeFreshPause.resumeRun
    {globalOracleCalls : Nat} {Result : Type u} {target : ShaInput}
    (transitionFuel : Nat)
    (pause : SchedulerNativeFreshPause globalOracleCalls Result target) :
    SchedulerNativeRun Result :=
  pause.resumeRunWith transitionFuel pause.targetAnswer pause.remainingAnswers

@[simp] theorem SchedulerNativeFreshPause.resumeCursorWith_actual
    {globalOracleCalls : Nat} {Result : Type u} {target : ShaInput}
    (pause : SchedulerNativeFreshPause globalOracleCalls Result target) :
    pause.resumeCursorWith pause.targetAnswer = pause.resumeCursor := by
  rfl

@[simp] theorem SchedulerNativeFreshPause.resumeRunWith_actual
    {globalOracleCalls : Nat} {Result : Type u} {target : ShaInput}
    (transitionFuel : Nat)
    (pause : SchedulerNativeFreshPause globalOracleCalls Result target) :
    pause.resumeRunWith transitionFuel pause.targetAnswer
        pause.remainingAnswers = pause.resumeRun transitionFuel := by
  rfl

def prependSchedulerNativeRun
    {Result : Type u} (record : UnifiedExposureRecord)
    (run : SchedulerNativeRun Result) : SchedulerNativeRun Result :=
  { terminal := run.terminal
    trace := record :: run.trace }

/-- Executable outcome of scanning for the first selected machine-fresh
request.  An absent result contains the already computed real run. -/
inductive SchedulerNativeTargetScan
    (globalOracleCalls : Nat) (Result : Type u) (target : ShaInput) where
  | paused (pause : SchedulerNativeFreshPause globalOracleCalls Result target)
  | absent (run : SchedulerNativeRun Result)

/-- Add one already executed scheduler coordinate to a later pause. -/
def SchedulerNativeFreshPause.prepend
    {globalOracleCalls : Nat} {Result : Type u} {target : ShaInput}
    (answer : Digest256) (record : UnifiedExposureRecord)
    (pause : SchedulerNativeFreshPause globalOracleCalls Result target) :
    SchedulerNativeFreshPause globalOracleCalls Result target :=
  { pause with
    consumedAnswers := answer :: pause.consumedAnswers
    consumedTrace := record :: pause.consumedTrace }

@[simp] theorem SchedulerNativeFreshPause.prepend_resumeCursor
    {globalOracleCalls : Nat} {Result : Type u} {target : ShaInput}
    (answer : Digest256) (record : UnifiedExposureRecord)
    (pause : SchedulerNativeFreshPause globalOracleCalls Result target) :
    (pause.prepend answer record).resumeCursor = pause.resumeCursor := by
  rfl

@[simp] theorem SchedulerNativeFreshPause.prepend_resumeRun
    {globalOracleCalls : Nat} {Result : Type u} {target : ShaInput}
    (transitionFuel : Nat) (answer : Digest256)
    (record : UnifiedExposureRecord)
    (pause : SchedulerNativeFreshPause globalOracleCalls Result target) :
    (pause.prepend answer record).resumeRun transitionFuel =
      prependSchedulerNativeRun record (pause.resumeRun transitionFuel) := by
  rfl

/-- Scan the actual list-tape scheduler.  A target request is recognized only
after `seekSchedulerNativeExposure` has normalized cached queries and produced
the literal `machineFresh` request.  Its answer remains unconsumed. -/
def scanSchedulerNativeToInputFrom
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (target : ShaInput) :
    (currentTransitionFuel : Nat) →
      SchedulerNativeCursor globalOracleCalls Result → List Digest256 →
        SchedulerNativeTargetScan globalOracleCalls Result target
  | currentTransitionFuel, cursor, [] =>
      .absent
        { terminal := terminalAtExposureEnd currentTransitionFuel cursor
          trace := [] }
  | currentTransitionFuel, cursor, answer :: rest =>
      match requestExact :
          seekSchedulerNativeExposure currentTransitionFuel cursor with
      | .returned result =>
          match scanSchedulerNativeToInputFrom transitionFuel target
              transitionFuel
              (.returned result : SchedulerNativeCursor globalOracleCalls Result)
              rest with
          | .absent tail =>
              .absent
                { terminal := tail.terminal
                  trace := .padding answer :: tail.trace }
          | .paused pause => .paused (pause.prepend answer (.padding answer))
      | .failed reason =>
          match scanSchedulerNativeToInputFrom transitionFuel target
              transitionFuel
              (.failed reason : SchedulerNativeCursor globalOracleCalls Result)
              rest with
          | .absent tail =>
              .absent
                { terminal := tail.terminal
                  trace := .padding answer :: tail.trace }
          | .paused pause => .paused (pause.prepend answer (.padding answer))
      | .transitionLimit =>
          match scanSchedulerNativeToInputFrom transitionFuel target
              transitionFuel
              (.failed .transitionLimit :
                SchedulerNativeCursor globalOracleCalls Result)
              rest with
          | .absent tail =>
              .absent
                { terminal := tail.terminal
                  trace := .padding answer :: tail.trace }
          | .paused pause => .paused (pause.prepend answer (.padding answer))
      | .machineFresh limits limitBound actor requestState input nextProgram
          remainingFuel coherent totalRoom freshRoom missing onReturned =>
          if input_eq_target : input = target then
            .paused
              { MachineResult := _
                limits := limits
                limitBound := limitBound
                actor := actor
                requestState := requestState
                input := input
                input_eq_target := input_eq_target
                nextProgram := nextProgram
                remainingFuel := remainingFuel
                coherent := coherent
                totalRoom := totalRoom
                freshRoom := freshRoom
                missing := missing
                onReturned := onReturned
                sourceTransitionFuel := currentTransitionFuel
                sourceCursor := cursor
                requestExact := requestExact
                consumedAnswers := []
                consumedTrace := []
                targetAnswer := answer
                remainingAnswers := rest }
          else
            let nextCursor : SchedulerNativeCursor globalOracleCalls Result :=
              .machine limits limitBound actor
                (freshQueryState actor requestState input answer)
                (nextProgram answer) remainingFuel
                (fresh_query_state_preserves_history_total_coherent actor
                  requestState input answer coherent) onReturned
            match scanSchedulerNativeToInputFrom transitionFuel target
                transitionFuel nextCursor rest with
            | .absent tail =>
                .absent
                  { terminal := tail.terminal
                    trace := .machineFresh actor input answer :: tail.trace }
            | .paused pause =>
                .paused
                  (pause.prepend answer (.machineFresh actor input answer))
      | .forkOutput frozenHistory pairRoom outputInput advanceInput template
          next =>
          let nextCursor : SchedulerNativeCursor globalOracleCalls Result :=
            .forkAdvance frozenHistory pairRoom outputInput advanceInput
              template answer next
          match scanSchedulerNativeToInputFrom transitionFuel target
              transitionFuel nextCursor rest with
          | .absent tail =>
              .absent
                { terminal := tail.terminal
                  trace := .forkOutput frozenHistory outputInput advanceInput
                    template answer :: tail.trace }
          | .paused pause =>
              .paused (pause.prepend answer
                (.forkOutput frozenHistory outputInput advanceInput template
                  answer))
      | .forkAdvance frozenHistory _pairRoom outputInput advanceInput template
          forkOutput next =>
          let scheduled : ScheduledForkCoins :=
            { frozenHistory := frozenHistory
              outputInput := outputInput
              advanceInput := advanceInput
              template := template
              forkOutput := forkOutput
              forkAdvance := answer }
          match scanSchedulerNativeToInputFrom transitionFuel target
              transitionFuel (next scheduled.configuration) rest with
          | .absent tail =>
              .absent
                { terminal := tail.terminal
                  trace := .forkAdvance scheduled :: tail.trace }
          | .paused pause =>
              .paused (pause.prepend answer (.forkAdvance scheduled))

def scanSchedulerNativeToInput
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (target : ShaInput)
    (cursor : SchedulerNativeCursor globalOracleCalls Result)
    (answers : List Digest256) :
    SchedulerNativeTargetScan globalOracleCalls Result target :=
  scanSchedulerNativeToInputFrom transitionFuel target transitionFuel cursor
    answers

/-- Interpret either scan outcome as the complete real run. -/
def SchedulerNativeTargetScan.reconstructedRun
    {globalOracleCalls : Nat} {Result : Type u} {target : ShaInput}
    (transitionFuel : Nat)
    (scan : SchedulerNativeTargetScan globalOracleCalls Result target) :
    SchedulerNativeRun Result :=
  match scan with
  | .paused pause => pause.resumeRun transitionFuel
  | .absent run => run

/-- A successful scan gives the literal master-tape split at the selected
coordinate.  In particular, `remainingAnswers` is an actual unread suffix,
not a separately supplied continuation tape. -/
theorem scan_scheduler_native_to_input_from_paused_answers_exact
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (target : ShaInput) :
    ∀ (currentTransitionFuel : Nat)
      (cursor : SchedulerNativeCursor globalOracleCalls Result)
      (answers : List Digest256)
      (pause : SchedulerNativeFreshPause globalOracleCalls Result target),
      scanSchedulerNativeToInputFrom transitionFuel target
          currentTransitionFuel cursor answers = .paused pause →
        answers = pause.consumedAnswers ++
          pause.targetAnswer :: pause.remainingAnswers := by
  intro currentTransitionFuel cursor answers
  induction answers generalizing currentTransitionFuel cursor with
  | nil =>
      intro pause found
      simp [scanSchedulerNativeToInputFrom] at found
  | cons answer rest ih =>
      intro pause found
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
            have tailExact := ih transitionFuel
              (.returned result : SchedulerNativeCursor globalOracleCalls Result)
              later scanExact
            simpa [SchedulerNativeFreshPause.prepend] using congrArg
              (List.cons answer) tailExact
      · rename_i reason
        generalize scanExact :
          scanSchedulerNativeToInputFrom transitionFuel target transitionFuel
            (.failed reason : SchedulerNativeCursor globalOracleCalls Result)
            rest = scan at found
        cases scan with
        | absent run => contradiction
        | paused later =>
            cases found
            have tailExact := ih transitionFuel
              (.failed reason : SchedulerNativeCursor globalOracleCalls Result)
              later scanExact
            simpa [SchedulerNativeFreshPause.prepend] using congrArg
              (List.cons answer) tailExact
      · generalize scanExact :
          scanSchedulerNativeToInputFrom transitionFuel target transitionFuel
            (.failed .transitionLimit :
              SchedulerNativeCursor globalOracleCalls Result) rest = scan at found
        cases scan with
        | absent run => contradiction
        | paused later =>
            cases found
            have tailExact := ih transitionFuel
              (.failed .transitionLimit :
                SchedulerNativeCursor globalOracleCalls Result) later scanExact
            simpa [SchedulerNativeFreshPause.prepend] using congrArg
              (List.cons answer) tailExact
      · rename_i MachineResult limits limitBound actor requestState input
          nextProgram remainingFuel coherent totalRoom freshRoom missing
          onReturned
        split at found
        next input_eq_target =>
          cases found
          rfl
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
              have tailExact := ih transitionFuel nextCursor later scanExact
              simpa [SchedulerNativeFreshPause.prepend] using congrArg
                (List.cons answer) tailExact
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
            have tailExact := ih transitionFuel nextCursor later scanExact
            simpa [SchedulerNativeFreshPause.prepend] using congrArg
              (List.cons answer) tailExact
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
            have tailExact := ih transitionFuel (next scheduled.configuration)
              later scanExact
            simpa [SchedulerNativeFreshPause.prepend] using congrArg
              (List.cons answer) tailExact

theorem scan_scheduler_native_to_input_paused_answers_exact
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (target : ShaInput)
    (cursor : SchedulerNativeCursor globalOracleCalls Result)
    (answers : List Digest256)
    (pause : SchedulerNativeFreshPause globalOracleCalls Result target)
    (found : scanSchedulerNativeToInput transitionFuel target cursor answers =
      .paused pause) :
    answers = pause.consumedAnswers ++
      pause.targetAnswer :: pause.remainingAnswers := by
  exact scan_scheduler_native_to_input_from_paused_answers_exact transitionFuel
    target transitionFuel cursor answers pause found

/-- The scanner neither changes nor approximates execution.  Resuming a pause
with its retained actual answer, or reading an absent result, reconstructs the
literal original list-tape scheduler run. -/
theorem scan_scheduler_native_to_input_from_reconstructs_run
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (target : ShaInput) :
    ∀ (currentTransitionFuel : Nat)
      (cursor : SchedulerNativeCursor globalOracleCalls Result)
      (answers : List Digest256),
      (scanSchedulerNativeToInputFrom transitionFuel target
        currentTransitionFuel cursor answers).reconstructedRun transitionFuel =
      runSchedulerNativeListRunFrom transitionFuel currentTransitionFuel
        cursor answers := by
  intro currentTransitionFuel cursor answers
  induction answers generalizing currentTransitionFuel cursor with
  | nil => simp [scanSchedulerNativeToInputFrom,
      SchedulerNativeTargetScan.reconstructedRun,
      runSchedulerNativeListRunFrom]
  | cons answer rest ih =>
      simp only [scanSchedulerNativeToInputFrom,
        runSchedulerNativeListRunFrom]
      split <;> rename_i requestExact
      all_goals simp only [requestExact]
      · rename_i result
        generalize scanExact :
          scanSchedulerNativeToInputFrom transitionFuel target transitionFuel
            (.returned result) rest = scan
        cases scan with
        | absent tail =>
            have resumed := ih transitionFuel
              (.returned result : SchedulerNativeCursor globalOracleCalls Result)
            rw [scanExact] at resumed
            exact congrArg (prependSchedulerNativeRun (.padding answer)) resumed
        | paused pause =>
            have resumed := ih transitionFuel
              (.returned result : SchedulerNativeCursor globalOracleCalls Result)
            rw [scanExact] at resumed
            simpa [SchedulerNativeTargetScan.reconstructedRun,
              prependSchedulerNativeRun] using congrArg
                (prependSchedulerNativeRun (.padding answer)) resumed
      · rename_i reason
        generalize scanExact :
          scanSchedulerNativeToInputFrom transitionFuel target transitionFuel
            (.failed reason) rest = scan
        cases scan with
        | absent tail =>
            have resumed := ih transitionFuel
              (.failed reason : SchedulerNativeCursor globalOracleCalls Result)
            rw [scanExact] at resumed
            exact congrArg (prependSchedulerNativeRun (.padding answer)) resumed
        | paused pause =>
            have resumed := ih transitionFuel
              (.failed reason : SchedulerNativeCursor globalOracleCalls Result)
            rw [scanExact] at resumed
            simpa [SchedulerNativeTargetScan.reconstructedRun,
              prependSchedulerNativeRun] using congrArg
                (prependSchedulerNativeRun (.padding answer)) resumed
      · generalize scanExact :
          scanSchedulerNativeToInputFrom transitionFuel target transitionFuel
            (.failed .transitionLimit :
              SchedulerNativeCursor globalOracleCalls Result) rest = scan
        cases scan with
        | absent tail =>
            have resumed := ih transitionFuel
                (.failed .transitionLimit :
                  SchedulerNativeCursor globalOracleCalls Result)
            rw [scanExact] at resumed
            exact congrArg (prependSchedulerNativeRun (.padding answer)) resumed
        | paused pause =>
            have resumed := ih transitionFuel
              (.failed .transitionLimit :
                SchedulerNativeCursor globalOracleCalls Result)
            rw [scanExact] at resumed
            simpa [SchedulerNativeTargetScan.reconstructedRun,
              prependSchedulerNativeRun] using congrArg
                (prependSchedulerNativeRun (.padding answer)) resumed
      · rename_i MachineResult limits limitBound actor requestState input
          nextProgram remainingFuel coherent totalRoom freshRoom missing
          onReturned
        split
        next input_eq_target =>
          simp [SchedulerNativeTargetScan.reconstructedRun,
            SchedulerNativeFreshPause.resumeRun,
            SchedulerNativeFreshPause.resumeRunWith,
            SchedulerNativeFreshPause.resumeCursorWith]
        next input_ne_target =>
          let nextCursor : SchedulerNativeCursor globalOracleCalls Result :=
            .machine limits limitBound actor
              (freshQueryState actor requestState input answer)
              (nextProgram answer) remainingFuel
              (fresh_query_state_preserves_history_total_coherent actor
                requestState input answer coherent) onReturned
          generalize scanExact :
            scanSchedulerNativeToInputFrom transitionFuel target transitionFuel
              nextCursor rest = scan
          cases scan with
          | absent tail =>
              have resumed := ih transitionFuel nextCursor
              rw [scanExact] at resumed
              exact congrArg
                (prependSchedulerNativeRun
                  (.machineFresh actor input answer)) resumed
          | paused pause =>
              have resumed := ih transitionFuel nextCursor
              rw [scanExact] at resumed
              simpa [SchedulerNativeTargetScan.reconstructedRun,
                prependSchedulerNativeRun] using congrArg
                  (prependSchedulerNativeRun
                    (.machineFresh actor input answer)) resumed
      · rename_i frozenHistory pairRoom outputInput advanceInput template next
        let nextCursor : SchedulerNativeCursor globalOracleCalls Result :=
          .forkAdvance frozenHistory pairRoom outputInput advanceInput template
            answer next
        generalize scanExact :
          scanSchedulerNativeToInputFrom transitionFuel target transitionFuel
            nextCursor rest = scan
        cases scan with
        | absent tail =>
            have resumed := ih transitionFuel nextCursor
            rw [scanExact] at resumed
            exact congrArg
              (prependSchedulerNativeRun
                (.forkOutput frozenHistory outputInput advanceInput template
                  answer)) resumed
        | paused pause =>
            have resumed := ih transitionFuel nextCursor
            rw [scanExact] at resumed
            simpa [SchedulerNativeTargetScan.reconstructedRun,
              prependSchedulerNativeRun] using congrArg
                (prependSchedulerNativeRun
                  (.forkOutput frozenHistory outputInput advanceInput template
                    answer)) resumed
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
            (next scheduled.configuration) rest = scan
        cases scan with
        | absent tail =>
            have resumed := ih transitionFuel (next scheduled.configuration)
            rw [scanExact] at resumed
            exact congrArg
              (prependSchedulerNativeRun (.forkAdvance scheduled)) resumed
        | paused pause =>
            have resumed := ih transitionFuel (next scheduled.configuration)
            rw [scanExact] at resumed
            simpa [SchedulerNativeTargetScan.reconstructedRun,
              prependSchedulerNativeRun] using congrArg
                (prependSchedulerNativeRun (.forkAdvance scheduled)) resumed

theorem scan_scheduler_native_to_input_reconstructs_run
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (target : ShaInput)
    (cursor : SchedulerNativeCursor globalOracleCalls Result)
    (answers : List Digest256) :
    SchedulerNativeTargetScan.reconstructedRun transitionFuel
        (scanSchedulerNativeToInput transitionFuel target cursor answers) =
      runSchedulerNativeListRun transitionFuel cursor answers := by
  exact scan_scheduler_native_to_input_from_reconstructs_run transitionFuel
    target transitionFuel cursor answers

/-- Occurrence case: the executable pause resumes on its retained original
answer and untouched suffix to the exact production scheduler run. -/
theorem scan_scheduler_native_to_input_paused_resume_exact
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (target : ShaInput)
    (cursor : SchedulerNativeCursor globalOracleCalls Result)
    (answers : List Digest256)
    (pause : SchedulerNativeFreshPause globalOracleCalls Result target)
    (found : scanSchedulerNativeToInput transitionFuel target cursor answers =
      .paused pause) :
    pause.resumeRun transitionFuel =
      runSchedulerNativeListRun transitionFuel cursor answers := by
  have exact := scan_scheduler_native_to_input_reconstructs_run
    transitionFuel target cursor answers
  rw [found] at exact
  exact exact

/-- The same occurrence theorem stated directly for the total
counterfactual-resume driver specialized to the actual answer and suffix. -/
theorem scan_scheduler_native_to_input_paused_resume_with_actual_exact
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (target : ShaInput)
    (cursor : SchedulerNativeCursor globalOracleCalls Result)
    (answers : List Digest256)
    (pause : SchedulerNativeFreshPause globalOracleCalls Result target)
    (found : scanSchedulerNativeToInput transitionFuel target cursor answers =
      .paused pause) :
    pause.resumeRunWith transitionFuel pause.targetAnswer
        pause.remainingAnswers =
      runSchedulerNativeListRun transitionFuel cursor answers := by
  simpa using scan_scheduler_native_to_input_paused_resume_exact
    transitionFuel target cursor answers pause found

/-- No-occurrence case: the run returned by the executable scan is exactly
the production scheduler run. -/
theorem scan_scheduler_native_to_input_absent_exact
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (target : ShaInput)
    (cursor : SchedulerNativeCursor globalOracleCalls Result)
    (answers : List Digest256) (run : SchedulerNativeRun Result)
    (absent : scanSchedulerNativeToInput transitionFuel target cursor answers =
      .absent run) :
    run = runSchedulerNativeListRun transitionFuel cursor answers := by
  have exact := scan_scheduler_native_to_input_reconstructs_run
    transitionFuel target cursor answers
  rw [absent] at exact
  exact exact

/-- A paused state exposes the selected target literally at the normalized
scheduler request that was saved in the state. -/
theorem scheduler_native_fresh_pause_request_is_target
    {globalOracleCalls : Nat} {Result : Type u} {target : ShaInput}
    (pause : SchedulerNativeFreshPause globalOracleCalls Result target) :
    pause.input = target :=
  pause.input_eq_target

#print axioms scan_scheduler_native_to_input_from_reconstructs_run
#print axioms scan_scheduler_native_to_input_from_paused_answers_exact
#print axioms scan_scheduler_native_to_input_paused_answers_exact
#print axioms scan_scheduler_native_to_input_reconstructs_run
#print axioms scan_scheduler_native_to_input_paused_resume_exact
#print axioms scan_scheduler_native_to_input_paused_resume_with_actual_exact
#print axioms scan_scheduler_native_to_input_absent_exact
#print axioms scheduler_native_fresh_pause_request_is_target

end

end AspisK1.V7Tag73SchedulerNativeTargetPause
