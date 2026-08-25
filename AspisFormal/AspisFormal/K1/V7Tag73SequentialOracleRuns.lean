import AspisFormal.K1.V7Tag73OperationalOracleExposure

/-!
# Sequential shared-controller oracle runs

This module executes two `OracleMachine` programs sequentially with the same
fresh-answer-tape controller and the exact final `OracleState` of the first
run as the initial state of the second.  This is the operational shape needed
for an adversary run followed by a verifier run.

The results here are deterministic:

* both runs retain exact fresh-history/tape-prefix coherence;
* the first history is a prefix of the second, and the records appended by
  each run carry that run's concrete actor;
* total calls, fresh calls, and machine steps have additive fuel bounds; and
* the final fresh-call count also remains below the shared tape length.

There is no acceptance predicate, failure classification, trace-cover
assumption, probability coefficient, or extraction statement in this file.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73SequentialOracleRuns

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure

noncomputable section

/-! ## One successful query appends one actor-labelled record -/

theorem query_oracle_success_appends_actor_record
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (state nextState : OracleState)
    (input : ShaInput) (output : ShaOutput)
    (success : queryOracle controller limits actor state input =
      .ok (output, nextState)) :
    ∃ record : QueryRecord,
      nextState.history = state.history ++ [record] ∧
        record.actor = actor := by
  unfold queryOracle at success
  split at success <;> try contradiction
  next _ =>
    split at success
    next entry found =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at success
      rcases success with ⟨_, rfl⟩
      exact ⟨_, rfl, rfl⟩
    next missing =>
      split at success <;> try contradiction
      next _ =>
        split at success
        next _ => contradiction
        next _ =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at success
          rcases success with ⟨_, rfl⟩
          exact ⟨_, rfl, rfl⟩

theorem query_oracle_success_counter_step
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (state nextState : OracleState)
    (input : ShaInput) (output : ShaOutput)
    (success : queryOracle controller limits actor state input =
      .ok (output, nextState)) :
    nextState.totalCalls = state.totalCalls + 1 ∧
      nextState.freshCalls ≤ state.freshCalls + 1 := by
  unfold queryOracle at success
  split at success <;> try contradiction
  next _ =>
    split at success
    next entry found =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at success
      rcases success with ⟨_, rfl⟩
      simp
    next missing =>
      split at success <;> try contradiction
      next _ =>
        split at success
        next _ => contradiction
        next _ =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at success
          rcases success with ⟨_, rfl⟩
          simp

/-! ## Generic run suffix, actor, and additive bounds -/

/-- Every record after the supplied initial history was appended by this
concrete run and therefore carries its `actor`. -/
theorem run_machine_appended_history_has_actor
    {Result : Type*} (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (program : OracleMachine Result) :
    ∃ appended : List QueryRecord,
      (runMachine controller limits actor fuel state program).oracle.history =
          state.history ++ appended ∧
        ∀ record ∈ appended, record.actor = actor := by
  induction fuel generalizing state program with
  | zero =>
      cases program <;> exact ⟨[], by simp [runMachine], by simp⟩
  | succ fuel ih =>
      cases program with
      | pure result => exact ⟨[], by simp [runMachine], by simp⟩
      | abort reason => exact ⟨[], by simp [runMachine], by simp⟩
      | query input next =>
          simp only [runMachine]
          cases queryResult : queryOracle controller limits actor state input with
          | error reason => exact ⟨[], by simp, by simp⟩
          | ok pair =>
              rcases pair with ⟨output, nextState⟩
              obtain ⟨record, queryHistory, recordActor⟩ :=
                query_oracle_success_appends_actor_record controller limits
                  actor state nextState input output queryResult
              obtain ⟨tail, tailHistory, tailActors⟩ :=
                ih nextState (next output)
              refine ⟨record :: tail, ?_, ?_⟩
              · calc
                  (runMachine controller limits actor fuel nextState
                      (next output)).oracle.history =
                      nextState.history ++ tail := tailHistory
                  _ = (state.history ++ [record]) ++ tail := by
                    rw [queryHistory]
                  _ = state.history ++ (record :: tail) := by simp
              · intro candidate member
                simp only [List.mem_cons] at member
                rcases member with rfl | member
                · exact recordActor
                · exact tailActors candidate member

theorem run_machine_history_since_has_actor
    {Result : Type*} (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (program : OracleMachine Result) :
    ∀ record ∈ historySince state
        (runMachine controller limits actor fuel state program).oracle,
      record.actor = actor := by
  obtain ⟨appended, history, actors⟩ :=
    run_machine_appended_history_has_actor controller limits actor fuel state
      program
  simpa [historySince, history] using actors

theorem run_machine_total_calls_le_initial_add_fuel
    {Result : Type*} (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (program : OracleMachine Result) :
    (runMachine controller limits actor fuel state program).oracle.totalCalls ≤
      state.totalCalls + fuel := by
  induction fuel generalizing state program with
  | zero => cases program <;> simp [runMachine]
  | succ fuel ih =>
      cases program with
      | pure result => simp [runMachine]
      | abort reason => simp [runMachine]
      | query input next =>
          simp only [runMachine]
          cases queryResult : queryOracle controller limits actor state input with
          | error reason => simp
          | ok pair =>
              rcases pair with ⟨output, nextState⟩
              have queryStep :=
                (query_oracle_success_counter_step controller limits actor state
                  nextState input output queryResult).1
              have tail := ih nextState (next output)
              calc
                (runMachine controller limits actor fuel nextState
                    (next output)).oracle.totalCalls ≤
                    nextState.totalCalls + fuel := tail
                _ = state.totalCalls + 1 + fuel := by rw [queryStep]
                _ = state.totalCalls + (fuel + 1) := by omega

theorem run_machine_fresh_calls_le_initial_add_fuel
    {Result : Type*} (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (program : OracleMachine Result) :
    (runMachine controller limits actor fuel state program).oracle.freshCalls ≤
      state.freshCalls + fuel := by
  induction fuel generalizing state program with
  | zero => cases program <;> simp [runMachine]
  | succ fuel ih =>
      cases program with
      | pure result => simp [runMachine]
      | abort reason => simp [runMachine]
      | query input next =>
          simp only [runMachine]
          cases queryResult : queryOracle controller limits actor state input with
          | error reason => simp
          | ok pair =>
              rcases pair with ⟨output, nextState⟩
              have queryStep :=
                (query_oracle_success_counter_step controller limits actor state
                  nextState input output queryResult).2
              have tail := ih nextState (next output)
              calc
                (runMachine controller limits actor fuel nextState
                    (next output)).oracle.freshCalls ≤
                    nextState.freshCalls + fuel := tail
                _ ≤ state.freshCalls + 1 + fuel :=
                  Nat.add_le_add_right queryStep fuel
                _ = state.freshCalls + (fuel + 1) := by omega

theorem run_machine_steps_le_fuel
    {Result : Type*} (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (program : OracleMachine Result) :
    (runMachine controller limits actor fuel state program).steps ≤ fuel := by
  induction fuel generalizing state program with
  | zero => cases program <;> simp [runMachine]
  | succ fuel ih =>
      cases program with
      | pure result => simp [runMachine]
      | abort reason => simp [runMachine]
      | query input next =>
          simp only [runMachine]
          cases queryResult : queryOracle controller limits actor state input with
          | error reason => simp
          | ok pair =>
              rcases pair with ⟨output, nextState⟩
              have tail := ih nextState (next output)
              change
                (runMachine controller limits actor fuel nextState
                    (next output)).steps + 1 ≤ fuel + 1
              omega

/-! ## Two runs sharing one controller and one OracleState -/

structure SharedControllerSequentialRun (FirstResult SecondResult : Type*) where
  first : MachineRun FirstResult
  second : MachineRun SecondResult

def runSharedControllerSequential
    {FirstResult SecondResult : Type*} {steps : Nat}
    (tape : FreshAnswerTape Digest256 steps) (limits : OracleLimits)
    (firstActor secondActor : QueryActor) (firstFuel secondFuel : Nat)
    (firstProgram : OracleMachine FirstResult)
    (secondProgram : OracleMachine SecondResult) :
    SharedControllerSequentialRun FirstResult SecondResult :=
  let first := runMachine (controllerFromFreshAnswerTape tape) limits firstActor
    firstFuel emptyOracle firstProgram
  let second := runMachine (controllerFromFreshAnswerTape tape) limits secondActor
    secondFuel first.oracle secondProgram
  ⟨first, second⟩

@[simp] theorem sequential_second_uses_first_final_oracle
    {FirstResult SecondResult : Type*} {steps : Nat}
    (tape : FreshAnswerTape Digest256 steps) (limits : OracleLimits)
    (firstActor secondActor : QueryActor) (firstFuel secondFuel : Nat)
    (firstProgram : OracleMachine FirstResult)
    (secondProgram : OracleMachine SecondResult) :
    (runSharedControllerSequential tape limits firstActor secondActor firstFuel
      secondFuel firstProgram secondProgram).second =
      runMachine (controllerFromFreshAnswerTape tape) limits secondActor
        secondFuel
        (runSharedControllerSequential tape limits firstActor secondActor
          firstFuel secondFuel firstProgram secondProgram).first.oracle
        secondProgram := by
  rfl

theorem sequential_fresh_histories_are_exact_tape_prefixes
    {FirstResult SecondResult : Type*} {steps : Nat}
    (tape : FreshAnswerTape Digest256 steps) (limits : OracleLimits)
    (firstActor secondActor : QueryActor) (firstFuel secondFuel : Nat)
    (firstProgram : OracleMachine FirstResult)
    (secondProgram : OracleMachine SecondResult) :
    let runs := runSharedControllerSequential tape limits firstActor secondActor
      firstFuel secondFuel firstProgram secondProgram
    FreshHistoryMatchesTape tape runs.first.oracle ∧
      FreshHistoryMatchesTape tape runs.second.oracle := by
  dsimp only [runSharedControllerSequential]
  have firstWithin := run_machine_with_uniform_tape_preserves_exposure_bound
    tape limits firstActor firstFuel emptyOracle firstProgram
      (empty_oracle_within_fresh_answer_tape tape)
  have firstContents :=
    run_machine_with_uniform_tape_preserves_fresh_history_contents tape limits
      firstActor firstFuel emptyOracle firstProgram
        (empty_oracle_within_fresh_answer_tape tape)
        (empty_oracle_fresh_history_matches_tape tape)
  have secondContents :=
    run_machine_with_uniform_tape_preserves_fresh_history_contents tape limits
      secondActor secondFuel
        (runMachine (controllerFromFreshAnswerTape tape) limits firstActor
          firstFuel emptyOracle firstProgram).oracle
        secondProgram firstWithin firstContents
  exact ⟨firstContents, secondContents⟩

/-- Literal concatenation of the first history with the second actor's new
suffix. -/
theorem sequential_history_prefix_and_second_actor_suffix
    {FirstResult SecondResult : Type*} {steps : Nat}
    (tape : FreshAnswerTape Digest256 steps) (limits : OracleLimits)
    (firstActor secondActor : QueryActor) (firstFuel secondFuel : Nat)
    (firstProgram : OracleMachine FirstResult)
    (secondProgram : OracleMachine SecondResult) :
    let runs := runSharedControllerSequential tape limits firstActor secondActor
      firstFuel secondFuel firstProgram secondProgram
    ∃ appended : List QueryRecord,
      runs.second.oracle.history = runs.first.oracle.history ++ appended ∧
        ∀ record ∈ appended, record.actor = secondActor := by
  dsimp only [runSharedControllerSequential]
  exact run_machine_appended_history_has_actor
    (controllerFromFreshAnswerTape tape) limits secondActor secondFuel
      (runMachine (controllerFromFreshAnswerTape tape) limits firstActor
        firstFuel emptyOracle firstProgram).oracle secondProgram

theorem sequential_first_history_prefix_second_history
    {FirstResult SecondResult : Type*} {steps : Nat}
    (tape : FreshAnswerTape Digest256 steps) (limits : OracleLimits)
    (firstActor secondActor : QueryActor) (firstFuel secondFuel : Nat)
    (firstProgram : OracleMachine FirstResult)
    (secondProgram : OracleMachine SecondResult) :
    let runs := runSharedControllerSequential tape limits firstActor secondActor
      firstFuel secondFuel firstProgram secondProgram
    runs.first.oracle.history <+: runs.second.oracle.history := by
  dsimp only [runSharedControllerSequential]
  exact postfork_run_history_is_preserved
    (controllerFromFreshAnswerTape tape) limits secondActor secondFuel
      (runMachine (controllerFromFreshAnswerTape tape) limits firstActor
        firstFuel emptyOracle firstProgram).oracle secondProgram

theorem sequential_actor_partition
    {FirstResult SecondResult : Type*} {steps : Nat}
    (tape : FreshAnswerTape Digest256 steps) (limits : OracleLimits)
    (firstActor secondActor : QueryActor) (firstFuel secondFuel : Nat)
    (firstProgram : OracleMachine FirstResult)
    (secondProgram : OracleMachine SecondResult) :
    let runs := runSharedControllerSequential tape limits firstActor secondActor
      firstFuel secondFuel firstProgram secondProgram
    (∀ record ∈ runs.first.oracle.history, record.actor = firstActor) ∧
      (∀ record ∈ historySince runs.first.oracle runs.second.oracle,
        record.actor = secondActor) := by
  dsimp only [runSharedControllerSequential]
  constructor
  · simpa [historySince, emptyOracle] using
      (run_machine_history_since_has_actor
        (controllerFromFreshAnswerTape tape) limits firstActor firstFuel
          emptyOracle firstProgram)
  · exact run_machine_history_since_has_actor
      (controllerFromFreshAnswerTape tape) limits secondActor secondFuel
        (runMachine (controllerFromFreshAnswerTape tape) limits firstActor
          firstFuel emptyOracle firstProgram).oracle secondProgram

/-- Additive joint accounting from two actual runs.  The tape cap is separate
from the fuel cap: cached queries consume fuel and total calls without
consuming fresh answers. -/
theorem sequential_combined_call_and_step_bounds
    {FirstResult SecondResult : Type*} {steps : Nat}
    (tape : FreshAnswerTape Digest256 steps) (limits : OracleLimits)
    (firstActor secondActor : QueryActor) (firstFuel secondFuel : Nat)
    (firstProgram : OracleMachine FirstResult)
    (secondProgram : OracleMachine SecondResult) :
    let runs := runSharedControllerSequential tape limits firstActor secondActor
      firstFuel secondFuel firstProgram secondProgram
    runs.second.oracle.totalCalls ≤ firstFuel + secondFuel ∧
      runs.second.oracle.freshCalls ≤ firstFuel + secondFuel ∧
      runs.second.oracle.freshCalls ≤ steps ∧
      runs.first.steps + runs.second.steps ≤ firstFuel + secondFuel := by
  dsimp only [runSharedControllerSequential]
  let controller := controllerFromFreshAnswerTape tape
  let firstRun := runMachine controller limits firstActor firstFuel emptyOracle
    firstProgram
  have firstTotal : firstRun.oracle.totalCalls ≤ firstFuel := by
    simpa [firstRun, emptyOracle] using
      (run_machine_total_calls_le_initial_add_fuel controller limits firstActor
        firstFuel emptyOracle firstProgram)
  have secondTotal := run_machine_total_calls_le_initial_add_fuel controller
    limits secondActor secondFuel firstRun.oracle secondProgram
  have firstFresh : firstRun.oracle.freshCalls ≤ firstFuel := by
    simpa [firstRun, emptyOracle] using
      (run_machine_fresh_calls_le_initial_add_fuel controller limits firstActor
        firstFuel emptyOracle firstProgram)
  have secondFresh := run_machine_fresh_calls_le_initial_add_fuel controller
    limits secondActor secondFuel firstRun.oracle secondProgram
  have tapeBound := run_machine_with_uniform_tape_preserves_exposure_bound tape
    limits secondActor secondFuel firstRun.oracle secondProgram
      (run_machine_with_uniform_tape_preserves_exposure_bound tape limits
        firstActor firstFuel emptyOracle firstProgram
          (empty_oracle_within_fresh_answer_tape tape))
  have tapeFinalFreshBound :
      (runMachine controller limits secondActor secondFuel firstRun.oracle
        secondProgram).oracle.freshCalls ≤ steps := tapeBound.2
  have firstSteps : firstRun.steps ≤ firstFuel := by
    simpa [firstRun] using
      (run_machine_steps_le_fuel controller limits firstActor firstFuel
        emptyOracle firstProgram)
  have secondSteps := run_machine_steps_le_fuel controller limits secondActor
    secondFuel firstRun.oracle secondProgram
  change
    (runMachine controller limits secondActor secondFuel firstRun.oracle
        secondProgram).oracle.totalCalls ≤ firstFuel + secondFuel ∧
      (runMachine controller limits secondActor secondFuel firstRun.oracle
        secondProgram).oracle.freshCalls ≤ firstFuel + secondFuel ∧
      (runMachine controller limits secondActor secondFuel firstRun.oracle
        secondProgram).oracle.freshCalls ≤ steps ∧
      firstRun.steps +
        (runMachine controller limits secondActor secondFuel firstRun.oracle
          secondProgram).steps ≤ firstFuel + secondFuel
  omega

#print axioms query_oracle_success_appends_actor_record
#print axioms query_oracle_success_counter_step
#print axioms run_machine_appended_history_has_actor
#print axioms run_machine_history_since_has_actor
#print axioms run_machine_total_calls_le_initial_add_fuel
#print axioms run_machine_fresh_calls_le_initial_add_fuel
#print axioms run_machine_steps_le_fuel
#print axioms sequential_second_uses_first_final_oracle
#print axioms sequential_fresh_histories_are_exact_tape_prefixes
#print axioms sequential_history_prefix_and_second_actor_suffix
#print axioms sequential_first_history_prefix_second_history
#print axioms sequential_actor_partition
#print axioms sequential_combined_call_and_step_bounds

end

end AspisK1.V7Tag73SequentialOracleRuns
