import AspisFormal.K1.V7Tag73TotalizedStageCompletion
import AspisFormal.K1.V7Tag73SchedulerResultMapSemantics

/-!
# Finite completion profiles for the native unified-exposure scheduler

This leaf lifts guarded totalized-machine completion and the literal two-coin
fork transition into a compositional bound for `SchedulerNativeCursor`.
It contains no Tag-73 dispatcher or acceptance statement.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73SchedulerCompletionCore

set_option maxRecDepth 8192

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73ProjectedMachinePrefix
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerMachineFactorization
open AspisK1.V7Tag73SchedulerResultMapSemantics
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73AtomicPairReplay
open AspisK1.V7Tag73SequentialOracleRuns
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73TotalizedStageCompletion

noncomputable section

universe u v

/-- A cursor completes from every normalization budget above `depth` and every
answer list containing at least `exposureCap` coordinates. -/
def SchedulerNativeCompletesWithin
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel depth exposureCap : Nat)
    (cursor : SchedulerNativeCursor globalOracleCalls Result) : Prop :=
  depth ≤ transitionFuel ∧
    ∀ currentTransitionFuel,
      depth ≤ currentTransitionFuel →
      ∀ answers : List Digest256,
        exposureCap ≤ answers.length →
        ∃ result,
          runSchedulerNativeListTerminalFrom transitionFuel
            currentTransitionFuel cursor answers = .returned result

theorem scheduler_native_returned_completes_within
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (result : Result) :
    SchedulerNativeCompletesWithin transitionFuel 1 0
      (.returned result : SchedulerNativeCursor globalOracleCalls Result) := by
  constructor
  · omega
  intro current currentPositive answers enough
  refine ⟨result, ?_⟩
  cases current with
  | zero => omega
  | succ current =>
      cases answers with
      | nil =>
          simp [runSchedulerNativeListTerminalFrom, terminalAtExposureEnd,
            seekSchedulerNativeExposure]
      | cons answer rest =>
          simp only [runSchedulerNativeListTerminalFrom,
            seekSchedulerNativeExposure]
          exact run_scheduler_native_list_returned_of_positive transitionFuel
            positive result rest

/-- Enlarging the depth/exposure allowance preserves completion. -/
theorem scheduler_native_completes_within_mono
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat)
    {oldDepth newDepth oldExposure newExposure : Nat}
    {cursor : SchedulerNativeCursor globalOracleCalls Result}
    (safe : SchedulerNativeCompletesWithin transitionFuel oldDepth oldExposure
      cursor)
    (depthLe : oldDepth ≤ newDepth) (newDepthLe : newDepth ≤ transitionFuel)
    (exposureLe : oldExposure ≤ newExposure) :
    SchedulerNativeCompletesWithin transitionFuel newDepth newExposure cursor := by
  constructor
  · exact newDepthLe
  intro current currentEnough answers answersEnough
  exact safe.2 current (depthLe.trans currentEnough) answers
    (exposureLe.trans answersEnough)

/-- The initial coherence proof is stored in either constructor of the exact
projected trace.  Taking the trace fields separately avoids dependent
elimination through the enclosing returned-prefix structure. -/
theorem projected_trace_entry_coherent
    {Result : Type u} (limits : OracleLimits) (actor : QueryActor)
    (fuel : Nat) (state : OracleState) (program : OracleMachine Result)
    (freshQueries : List (ShaInput × Digest256)) (result : Result)
    (finalState : OracleState) (steps : Nat)
    (trace : ProjectedFreshReturnedTrace limits actor fuel state program
      freshQueries result finalState steps) :
    HistoryTotalCoherent state := by
  cases trace <;> assumption

/-- The fresh prefix consumed by a projected normal return is bounded by the
machine query fuel. -/
theorem projected_machine_prefix_fresh_length_le_fuel
    {Result : Type u}
    (limits : OracleLimits) (actor : QueryActor)
    (fuel : Nat) (state : OracleState) (program : OracleMachine Result)
    (available : List Digest256)
    (returned : ProjectedMachinePrefixReturned limits actor fuel state program
      available) :
    returned.freshQueries.length ≤ fuel := by
  have coherent : HistoryTotalCoherent state :=
    projected_trace_entry_coherent limits actor fuel state program
      returned.freshQueries returned.result returned.finalState returned.steps
      returned.trace
  have runExact := projected_machine_prefix_returned_run_exact limits actor fuel
    state program available returned coherent
  have stepsLe := run_machine_steps_le_fuel
    (controllerFromProjectedFreshAnswers state.history
      (returned.freshQueries.map Prod.snd)) limits actor fuel state program
  rw [runExact] at stepsLe
  exact (projected_fresh_returned_trace_answer_count_le_steps limits actor fuel
    state program returned.freshQueries returned.result returned.finalState
    returned.steps returned.trace).trans stepsLe

/-- One guarded mapped-totalized machine composes with a uniformly bounded
normal-return continuation. -/
theorem mapped_totalized_machine_completes_within
    {Original : Type u} {Mapped Result : Type v}
    {globalOracleCalls : Nat}
    (transitionFuel nextDepth nextExposure : Nat)
    (limits : OracleLimits)
    (limitBound : limits.totalCalls ≤ globalOracleCalls)
    (actor : QueryActor) (state : OracleState)
    (originalProgram : OracleMachine Original) (fuel : Nat)
    (coherent : HistoryTotalCoherent state)
    (map : Except TotalizedMachineFailure Original → Mapped)
    (onReturned : (result : Mapped) → (state : OracleState) →
      HistoryTotalCoherent state →
        SchedulerNativeCursor globalOracleCalls Result)
    (stageRoom : StageHasOracleRoom limits state fuel)
    (transitionRoom : nextDepth + 1 ≤ transitionFuel)
    (continuations : ∀ result finalState finalCoherent,
      SchedulerNativeCompletesWithin transitionFuel nextDepth nextExposure
        (onReturned result finalState finalCoherent)) :
    SchedulerNativeCompletesWithin transitionFuel (nextDepth + 1)
      (fuel + nextExposure)
      (.machine limits limitBound actor state
        (mapOracleMachineResult map
          (totalizeOracleMachine fuel originalProgram)) fuel coherent
        onReturned) := by
  constructor
  · exact transitionRoom
  intro current currentRoom answers answersRoom
  have positive : 0 < transitionFuel := by omega
  rw [run_scheduler_native_list_machine_factorization transitionFuel limits
    limitBound actor state
    (mapOracleMachineResult map
      (totalizeOracleMachine fuel originalProgram)) fuel coherent onReturned
    positive current answers]
  cases current with
  | zero => omega
  | succ current =>
      unfold terminalAfterProjectedMachinePrefix
        terminalAfterCertifiedProjectedMachinePrefix
      obtain ⟨returned, returnedExact⟩ :=
        consume_mapped_totalized_stage_returns limits actor map fuel answers state
          originalProgram coherent stageRoom (by omega)
      dsimp only
      unfold consumeProjectedMachinePrefix at returnedExact
      rw [returnedExact]
      have freshBound := projected_machine_prefix_fresh_length_le_fuel limits
        actor fuel state
        (mapOracleMachineResult map
          (totalizeOracleMachine fuel originalProgram)) answers returned
      have remainingRoom : nextExposure ≤ returned.remaining.length := by
        have lengths := congrArg List.length returned.availableExact
        simp only [List.length_append, List.length_map] at lengths
        omega
      have nextCurrentRoom : nextDepth ≤
          machinePrefixContinuationTransitionFuel transitionFuel current
            returned.freshQueries := by
        cases returned.freshQueries with
        | nil =>
            simp [machinePrefixContinuationTransitionFuel]
            omega
        | cons head tail =>
            simp [machinePrefixContinuationTransitionFuel]
            omega
      exact (continuations returned.result returned.finalState
        returned.finalCoherent).2 _ nextCurrentRoom returned.remaining
          remainingRoom

/-- Mapping only a returned result consumes no coordinate and introduces no
native failure. -/
theorem scheduler_native_completes_within_map
    {globalOracleCalls : Nat} {Input Output : Type u}
    (transitionFuel depth exposure : Nat)
    (map : Input → Output)
    {cursor : SchedulerNativeCursor globalOracleCalls Input}
    (safe : SchedulerNativeCompletesWithin transitionFuel depth exposure
      cursor) :
    SchedulerNativeCompletesWithin transitionFuel depth exposure
      (mapSchedulerNativeCursorResult map cursor) := by
  constructor
  · exact safe.1
  intro current currentRoom answers answersRoom
  obtain ⟨result, returned⟩ := safe.2 current currentRoom answers answersRoom
  refine ⟨map result, ?_⟩
  rw [run_scheduler_native_list_terminal_from_map, returned]
  rfl

/-- A direct atomic pair fork consumes exactly two adjacent coordinates. -/
theorem scheduler_native_fork_pair_completes_within
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel nextDepth nextExposure : Nat)
    (frozenHistory : List QueryRecord)
    (pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls)
    (outputInput advanceInput : ShaInput)
    (template : AtomicPairReplayConfiguration)
    (next : AtomicPairReplayConfiguration →
      SchedulerNativeCursor globalOracleCalls Result)
    (positive : 0 < transitionFuel)
    (continuations : ∀ configuration,
      SchedulerNativeCompletesWithin transitionFuel nextDepth nextExposure
        (next configuration)) :
    SchedulerNativeCompletesWithin transitionFuel 1 (2 + nextExposure)
      (.forkPair frozenHistory pairRoom outputInput advanceInput template next) := by
  constructor
  · omega
  intro current currentPositive answers answersRoom
  cases current with
  | zero => omega
  | succ current =>
      cases answers with
      | nil => simp at answersRoom
      | cons forkOutput rest =>
          cases rest with
          | nil =>
              simp only [List.length_cons, List.length_nil] at answersRoom
              omega
          | cons forkAdvance tail =>
              let scheduled : ScheduledForkCoins :=
                { frozenHistory := frozenHistory
                  outputInput := outputInput
                  advanceInput := advanceInput
                  template := template
                  forkOutput := forkOutput
                  forkAdvance := forkAdvance }
              have tailRoom : nextExposure ≤ tail.length := by
                simp only [List.length_cons] at answersRoom
                omega
              have nextSafe := continuations scheduled.configuration
              cases transitionFuel with
              | zero => omega
              | succ transitionFuel =>
                  obtain ⟨result, returned⟩ := nextSafe.2
                    (transitionFuel + 1) nextSafe.1 tail tailRoom
                  refine ⟨result, ?_⟩
                  simp only [runSchedulerNativeListTerminalFrom,
                    seekSchedulerNativeExposure]
                  simpa [scheduled] using returned

#print axioms mapped_totalized_machine_completes_within
#print axioms scheduler_native_fork_pair_completes_within

end

end AspisK1.V7Tag73SchedulerCompletionCore
