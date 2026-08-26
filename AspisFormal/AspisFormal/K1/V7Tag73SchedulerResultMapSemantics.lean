import AspisFormal.K1.V7Tag73SchedulerMachineFactorization
import AspisFormal.K1.V7Tag73SchedulerNativePlainRomExperiment

/-!
# Result-map semantics for the native Tag-73 scheduler

The full plain-ROM cursor maps only the concrete restoration client's final
value into `SchedulerNativePlainRomResult.completed`.  This leaf proves that
the executable list interpreter commutes with that result-only map.  It lets
later proofs remove the map and retain the literal residual client execution;
no run equation is supplied by the caller.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73SchedulerResultMapSemantics

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SchedulerMachineFactorization

noncomputable section

universe u

/-- Map only the terminal data of a normalized scheduler request. -/
def mapSchedulerNativeRequestResult
    {globalOracleCalls : Nat} {Input Output : Type u}
    (map : Input → Output) :
    SchedulerNativeRequest globalOracleCalls Input →
      SchedulerNativeRequest globalOracleCalls Output
  | .returned result => .returned (map result)
  | .failed reason => .failed reason
  | .transitionLimit => .transitionLimit
  | .machineFresh limits limitBound actor state input nextProgram
      remainingFuel coherent totalRoom freshRoom missing onReturned =>
      .machineFresh limits limitBound actor state input nextProgram
        remainingFuel coherent totalRoom freshRoom missing
        (fun result finalState finalCoherent =>
          mapSchedulerNativeCursorResult map
            (onReturned result finalState finalCoherent))
  | .forkOutput frozenHistory pairRoom outputInput advanceInput template next =>
      .forkOutput frozenHistory pairRoom outputInput advanceInput template
        (fun configuration =>
          mapSchedulerNativeCursorResult map (next configuration))
  | .forkAdvance frozenHistory pairRoom outputInput advanceInput template
      forkOutput next =>
      .forkAdvance frozenHistory pairRoom outputInput advanceInput template
        forkOutput (fun configuration =>
          mapSchedulerNativeCursorResult map (next configuration))

/-- Cached/pure normalization commutes with changing only the eventual result
type. -/
theorem seek_scheduler_native_exposure_map
    {globalOracleCalls : Nat} {Input Output : Type u}
    (map : Input → Output) : ∀ transitionFuel
      (cursor : SchedulerNativeCursor globalOracleCalls Input),
      seekSchedulerNativeExposure transitionFuel
          (mapSchedulerNativeCursorResult map cursor) =
        mapSchedulerNativeRequestResult map
          (seekSchedulerNativeExposure transitionFuel cursor) := by
  intro transitionFuel
  induction transitionFuel with
  | zero =>
      intro cursor
      rfl
  | succ transitionFuel ih =>
      intro cursor
      cases cursor with
      | returned result => rfl
      | failed reason => rfl
      | forkPair frozenHistory pairRoom outputInput advanceInput template next =>
          rfl
      | forkAdvance frozenHistory pairRoom outputInput advanceInput template
          forkOutput next =>
          rfl
      | @machine MachineResult limits limitBound actor state program fuel
          coherent onReturned =>
          simp only [mapSchedulerNativeCursorResult,
            seekSchedulerNativeExposure]
          generalize certifiedExact :
            certifiedSeekNextFresh limits actor fuel state program coherent =
              certified
          rcases certified with ⟨sought, soughtCoherent⟩
          cases sought with
          | returned result finalState steps =>
              simpa [nativeRequestOfCoherentSeekResult,
                mapSchedulerNativeRequestResult] using
                ih (onReturned result finalState soughtCoherent)
          | explicitAbort reason finalState steps =>
              rfl
          | resourceAbort reason finalState steps =>
              rfl
          | outOfFuel finalState steps =>
              rfl
          | request requestState input nextProgram remainingFuel steps
              requestCoherent totalRoom freshRoom missing =>
              rfl

/-- Map a terminal value without changing scheduler failures. -/
def mapSchedulerNativeTerminalResult
    {Input Output : Type u} (map : Input → Output) :
    SchedulerNativeTerminal Input → SchedulerNativeTerminal Output
  | .returned result => .returned (map result)
  | .failed reason => .failed reason

/-- The exact list scheduler commutes with the result-only cursor map. -/
theorem run_scheduler_native_list_terminal_from_map
    {globalOracleCalls : Nat} {Input Output : Type u}
    (map : Input → Output) (transitionFuel : Nat) :
    ∀ (currentTransitionFuel : Nat)
      (cursor : SchedulerNativeCursor globalOracleCalls Input)
      (answers : List Digest256),
      runSchedulerNativeListTerminalFrom transitionFuel currentTransitionFuel
          (mapSchedulerNativeCursorResult map cursor) answers =
        mapSchedulerNativeTerminalResult map
          (runSchedulerNativeListTerminalFrom transitionFuel
            currentTransitionFuel cursor answers) := by
  intro currentTransitionFuel cursor answers
  induction answers generalizing currentTransitionFuel cursor with
  | nil =>
      unfold runSchedulerNativeListTerminalFrom terminalAtExposureEnd
      rw [seek_scheduler_native_exposure_map]
      cases seekSchedulerNativeExposure currentTransitionFuel cursor <;> rfl
  | cons answer rest ih =>
      unfold runSchedulerNativeListTerminalFrom
      rw [seek_scheduler_native_exposure_map]
      cases request : seekSchedulerNativeExposure currentTransitionFuel cursor with
      | returned result =>
          simpa only [mapSchedulerNativeRequestResult,
            mapSchedulerNativeCursorResult] using
            (ih transitionFuel
              (.returned result : SchedulerNativeCursor globalOracleCalls Input))
      | failed reason =>
          simpa only [mapSchedulerNativeRequestResult,
            mapSchedulerNativeCursorResult] using
            (ih transitionFuel
              (.failed reason : SchedulerNativeCursor globalOracleCalls Input))
      | transitionLimit =>
          simpa only [mapSchedulerNativeRequestResult,
            mapSchedulerNativeCursorResult] using
            (ih transitionFuel
              (.failed .transitionLimit :
                SchedulerNativeCursor globalOracleCalls Input))
      | @machineFresh MachineResult limits limitBound actor state input
          nextProgram remainingFuel coherent totalRoom freshRoom missing
          onReturned =>
          simpa only [mapSchedulerNativeRequestResult,
            mapSchedulerNativeCursorResult] using
            (ih transitionFuel
              (.machine limits limitBound actor
                (freshQueryState actor state input answer)
                (nextProgram answer) remainingFuel
                (fresh_query_state_preserves_history_total_coherent actor state
                  input answer coherent) onReturned))
      | forkOutput frozenHistory pairRoom outputInput advanceInput template next =>
          simpa only [mapSchedulerNativeRequestResult,
            mapSchedulerNativeCursorResult] using
            (ih transitionFuel
              (.forkAdvance frozenHistory pairRoom outputInput advanceInput
                template answer next))
      | forkAdvance frozenHistory pairRoom outputInput advanceInput template
          forkOutput next =>
          let scheduled : ScheduledForkCoins :=
            { frozenHistory := frozenHistory
              outputInput := outputInput
              advanceInput := advanceInput
              template := template
              forkOutput := forkOutput
              forkAdvance := answer }
          simpa only [mapSchedulerNativeRequestResult,
            mapSchedulerNativeCursorResult] using
            (ih transitionFuel (next scheduled.configuration))

/-- Injectivity specialization used by the full-run factorization.  A
completed mapped terminal determines the literal residual client terminal. -/
theorem run_scheduler_native_list_terminal_from_completed_map_reflects
    {globalOracleCalls : Nat}
    {TapeIdentity Statement Proof Payload Result : Type u}
    (expected : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (transitionFuel currentTransitionFuel : Nat)
    (cursor : SchedulerNativeCursor globalOracleCalls
      (ConcreteRestorationClientRun Statement Proof Payload Result))
    (answers : List Digest256)
    (clientRun : ConcreteRestorationClientRun Statement Proof Payload Result)
    (completed :
      runSchedulerNativeListTerminalFrom transitionFuel currentTransitionFuel
          (mapSchedulerNativeCursorResult
            (fun run => SchedulerNativePlainRomResult.completed expected run)
            cursor) answers =
        .returned (.completed expected clientRun)) :
    runSchedulerNativeListTerminalFrom transitionFuel currentTransitionFuel
        cursor answers = .returned clientRun := by
  rw [run_scheduler_native_list_terminal_from_map] at completed
  generalize terminalExact :
    runSchedulerNativeListTerminalFrom transitionFuel currentTransitionFuel
      cursor answers = terminal at completed ⊢
  cases terminal with
  | failed reason => simp [mapSchedulerNativeTerminalResult] at completed
  | returned result =>
      simp only [mapSchedulerNativeTerminalResult,
        SchedulerNativeTerminal.returned.injEq,
        SchedulerNativePlainRomResult.completed.injEq] at completed
      have resultExact : result = clientRun := completed.2
      subst result
      rfl

#print axioms seek_scheduler_native_exposure_map
#print axioms run_scheduler_native_list_terminal_from_map
#print axioms run_scheduler_native_list_terminal_from_completed_map_reflects

end

end AspisK1.V7Tag73SchedulerResultMapSemantics
