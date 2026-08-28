import AspisFormal.K1.V7Tag73SchedulerNativeTargetPause

/-!
# Counterfactual scheduler reconstruction at one fresh pause

The target scanner already proves reconstruction when its retained real answer
is replayed.  State-restoration also needs the exact counterfactual statement:
replace that answer, replace the unread suffix, and the resumed pause is the
ordinary result-carrying scheduler run on the correspondingly modified master
tape.  The prefix is unchanged because target selection occurs before the
target answer is exposed.

This theorem is generic in the scheduler result and target input.  It makes no
Tag-73 acceptance, q16, gamma, extraction, or probability claim.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73SchedulerNativeCounterfactualPause

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73SchedulerNativeTargetPause

noncomputable section

universe u

/-- Replace only the selected answer and unread suffix of a pause. -/
def replaceSchedulerNativePause
    {globalOracleCalls : Nat} {Result : Type u} {target : ShaInput}
    (pause : SchedulerNativeFreshPause globalOracleCalls Result target)
    (replacement : Digest256) (suffix : List Digest256) :
    SchedulerNativeFreshPause globalOracleCalls Result target :=
  { pause with
    targetAnswer := replacement
    remainingAnswers := suffix }

@[simp] theorem replace_scheduler_native_pause_prepend
    {globalOracleCalls : Nat} {Result : Type u} {target : ShaInput}
    (answer : Digest256) (record : UnifiedExposureRecord)
    (pause : SchedulerNativeFreshPause globalOracleCalls Result target)
    (replacement : Digest256) (suffix : List Digest256) :
    replaceSchedulerNativePause (pause.prepend answer record) replacement
        suffix =
      (replaceSchedulerNativePause pause replacement suffix).prepend answer
        record := by
  cases pause
  rfl

@[simp] theorem prepend_consumed_answers
    {globalOracleCalls : Nat} {Result : Type u} {target : ShaInput}
    (answer : Digest256) (record : UnifiedExposureRecord)
    (pause : SchedulerNativeFreshPause globalOracleCalls Result target) :
    (pause.prepend answer record).consumedAnswers =
      answer :: pause.consumedAnswers := by
  rfl

@[simp] theorem replace_scheduler_native_pause_resume_run
    {globalOracleCalls : Nat} {Result : Type u} {target : ShaInput}
    (transitionFuel : Nat)
    (pause : SchedulerNativeFreshPause globalOracleCalls Result target)
    (replacement : Digest256) (suffix : List Digest256) :
    (replaceSchedulerNativePause pause replacement suffix).resumeRun
        transitionFuel =
      pause.resumeRunWith transitionFuel replacement suffix := by
  cases pause
  rfl

@[simp] theorem prepend_resume_run_with
    {globalOracleCalls : Nat} {Result : Type u} {target : ShaInput}
    (transitionFuel : Nat) (answer : Digest256)
    (record : UnifiedExposureRecord)
    (pause : SchedulerNativeFreshPause globalOracleCalls Result target)
    (replacement : Digest256) (suffix : List Digest256) :
    (pause.prepend answer record).resumeRunWith transitionFuel replacement
        suffix =
      prependSchedulerNativeRun record
        (pause.resumeRunWith transitionFuel replacement suffix) := by
  rfl

/-- A pause at a selected fresh coordinate reconstructs the ordinary scheduler
run for any replacement answer and unread suffix.  This is the exact
same-prefix counterfactual statement needed by state restoration; it does not
compare dependent proof fields in two separately constructed pause records. -/
theorem scan_scheduler_native_to_input_from_counterfactual_exact
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (target : ShaInput) :
    ∀ (currentTransitionFuel : Nat)
      (cursor : SchedulerNativeCursor globalOracleCalls Result)
      (answers : List Digest256)
      (pause : SchedulerNativeFreshPause globalOracleCalls Result target),
      scanSchedulerNativeToInputFrom transitionFuel target
          currentTransitionFuel cursor answers = .paused pause →
      ∀ (replacement : Digest256) (suffix : List Digest256),
        pause.resumeRunWith transitionFuel replacement suffix =
          runSchedulerNativeListRunFrom transitionFuel currentTransitionFuel
            cursor (pause.consumedAnswers ++ replacement :: suffix) := by
  intro currentTransitionFuel cursor answers
  induction answers generalizing currentTransitionFuel cursor with
  | nil =>
      intro pause found replacement suffix
      simp [scanSchedulerNativeToInputFrom] at found
  | cons answer rest ih =>
      intro pause found replacement suffix
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
            have tail := ih transitionFuel
              (.returned result : SchedulerNativeCursor globalOracleCalls Result)
              later scanExact replacement suffix
            change (later.prepend answer (.padding answer)).resumeRunWith
                transitionFuel replacement suffix = _
            rw [prepend_resume_run_with, tail]
            simp [runSchedulerNativeListRunFrom, requestExact,
              prependSchedulerNativeRun]
      · rename_i reason
        generalize scanExact :
          scanSchedulerNativeToInputFrom transitionFuel target transitionFuel
            (.failed reason : SchedulerNativeCursor globalOracleCalls Result)
            rest = scan at found
        cases scan with
        | absent run => contradiction
        | paused later =>
            cases found
            have tail := ih transitionFuel
              (.failed reason : SchedulerNativeCursor globalOracleCalls Result)
              later scanExact replacement suffix
            change (later.prepend answer (.padding answer)).resumeRunWith
                transitionFuel replacement suffix = _
            rw [prepend_resume_run_with, tail]
            simp [runSchedulerNativeListRunFrom, requestExact,
              prependSchedulerNativeRun]
      · generalize scanExact :
          scanSchedulerNativeToInputFrom transitionFuel target transitionFuel
            (.failed .transitionLimit :
              SchedulerNativeCursor globalOracleCalls Result) rest = scan at found
        cases scan with
        | absent run => contradiction
        | paused later =>
            cases found
            have tail := ih transitionFuel
              (.failed .transitionLimit :
                SchedulerNativeCursor globalOracleCalls Result)
              later scanExact replacement suffix
            change (later.prepend answer (.padding answer)).resumeRunWith
                transitionFuel replacement suffix = _
            rw [prepend_resume_run_with, tail]
            simp [runSchedulerNativeListRunFrom, requestExact,
              prependSchedulerNativeRun]
      · rename_i MachineResult limits limitBound actor requestState input
          nextProgram remainingFuel coherent totalRoom freshRoom missing
          onReturned
        split at found
        next input_eq_target =>
          cases found
          simp [SchedulerNativeFreshPause.resumeRunWith,
            SchedulerNativeFreshPause.resumeCursorWith,
            runSchedulerNativeListRunFrom, requestExact]
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
              have tail := ih transitionFuel nextCursor later scanExact
                replacement suffix
              change (later.prepend answer
                  (.machineFresh actor input answer)).resumeRunWith
                    transitionFuel replacement suffix = _
              rw [prepend_resume_run_with, tail]
              simp [runSchedulerNativeListRunFrom, requestExact,
                prependSchedulerNativeRun, nextCursor]
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
            have tail := ih transitionFuel nextCursor later scanExact
              replacement suffix
            change (later.prepend answer
                (.forkOutput frozenHistory outputInput advanceInput template
                  answer)).resumeRunWith transitionFuel replacement suffix = _
            rw [prepend_resume_run_with, tail]
            simp [runSchedulerNativeListRunFrom, requestExact,
              prependSchedulerNativeRun, nextCursor]
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
            have tail := ih transitionFuel (next scheduled.configuration)
              later scanExact replacement suffix
            change (later.prepend answer
                (.forkAdvance scheduled)).resumeRunWith transitionFuel
                  replacement suffix = _
            rw [prepend_resume_run_with, tail]
            simp [runSchedulerNativeListRunFrom, requestExact,
              prependSchedulerNativeRun, scheduled]

/-- Counterfactual reconstruction theorem.  Resuming the selected pause with
an arbitrary answer and suffix is exactly the production scheduler run on the
original consumed prefix followed by that answer and suffix. -/
theorem scan_scheduler_native_to_input_paused_resume_with_replacement_exact
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (target : ShaInput)
    (cursor : SchedulerNativeCursor globalOracleCalls Result)
    (answers : List Digest256)
    (pause : SchedulerNativeFreshPause globalOracleCalls Result target)
    (found : scanSchedulerNativeToInput transitionFuel target cursor answers =
      .paused pause)
    (replacement : Digest256) (suffix : List Digest256) :
    pause.resumeRunWith transitionFuel replacement suffix =
      runSchedulerNativeListRun transitionFuel cursor
        (pause.consumedAnswers ++ replacement :: suffix) := by
  exact scan_scheduler_native_to_input_from_counterfactual_exact transitionFuel
    target transitionFuel cursor answers pause found replacement suffix

#print axioms scan_scheduler_native_to_input_from_counterfactual_exact
#print axioms
  scan_scheduler_native_to_input_paused_resume_with_replacement_exact

end

end AspisK1.V7Tag73SchedulerNativeCounterfactualPause
