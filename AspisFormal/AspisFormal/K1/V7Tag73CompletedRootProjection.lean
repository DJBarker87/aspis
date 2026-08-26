import AspisFormal.K1.V7Tag73ExactPlainRomRun
import AspisFormal.K1.V7Tag73SchedulerMachineFactorization
import AspisFormal.K1.V7Tag73TotalizedMachineReflection

/-!
# Recover the two concrete root runs from a completed scheduler terminal

The exact plain-ROM root experiment executes two totalized oracle machines:
the same-hidden-tape prover from the literal empty oracle, followed by the
future-free verifier from the prover's actual final oracle.  This file turns a
completed terminal of that one operational scheduler into the two projected
machine equations consumed by `RootProjectedTotalizedRuns`.

No controller, oracle state, trace cover, restore function, or successful run
equation is supplied by the caller.  Both projected controllers are recovered
from the shortest concrete prefixes consumed by the scheduler itself.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73CompletedRootProjection

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73UniformRawVerifierExecution
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73TotalizedMachineReflection
open AspisK1.V7Tag73ProjectedMachinePrefix
open AspisK1.V7Tag73SchedulerMachineFactorization

noncomputable section

universe u v

/-! ## Terminal padding from an already returned cursor -/

/-- A returned cursor is inert.  With a positive current normalization budget
it keeps its value while all remaining coordinates become padding; with zero
current budget the scheduler records the exact transition-limit failure. -/
theorem run_scheduler_native_list_returned_from
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (currentTransitionFuel : Nat) (result : Result)
    (answers : List Digest256) :
    runSchedulerNativeListTerminalFrom transitionFuel currentTransitionFuel
        (.returned result : SchedulerNativeCursor globalOracleCalls Result)
        answers =
      if 0 < currentTransitionFuel then .returned result
      else .failed .transitionLimit := by
  cases currentTransitionFuel with
  | zero =>
      cases answers with
      | nil => rfl
      | cons answer rest =>
          simpa [runSchedulerNativeListTerminalFrom,
            seekSchedulerNativeExposure] using
            run_scheduler_native_list_failed_of_positive
              transitionFuel positive .transitionLimit rest
  | succ current =>
      cases answers with
      | nil => rfl
      | cons answer rest =>
          simpa [runSchedulerNativeListTerminalFrom,
            seekSchedulerNativeExposure] using
            run_scheduler_native_list_returned_of_positive
              transitionFuel positive result rest

/-- Eliminate a successful terminal of one factorized leading machine.  This
is the reusable inversion step for the prover and verifier root segments. -/
theorem terminal_after_projected_machine_prefix_returned_elim
    {globalOracleCalls : Nat} {Result MachineResult : Type u}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (currentTransitionFuel : Nat)
    (limits : OracleLimits)
    (limitBound : limits.totalCalls ≤ globalOracleCalls)
    (actor : QueryActor) (state : OracleState)
    (program : OracleMachine MachineResult) (fuel : Nat)
    (coherent : HistoryTotalCoherent state)
    (onReturned : (result : MachineResult) → (state : OracleState) →
      HistoryTotalCoherent state →
        SchedulerNativeCursor globalOracleCalls Result)
    (answers : List Digest256) (finalResult : Result)
    (completed : terminalAfterProjectedMachinePrefix transitionFuel
      currentTransitionFuel limits limitBound actor state program fuel coherent
      onReturned answers = .returned finalResult) :
    ∃ returned : ProjectedMachinePrefixReturned limits actor fuel state
        program answers,
      consumeProjectedMachinePrefix limits actor answers fuel state program
          coherent = .ok returned ∧
      runSchedulerNativeListTerminalFrom transitionFuel
          (machinePrefixContinuationTransitionFuel transitionFuel
            (currentTransitionFuel - 1) returned.freshQueries)
          (onReturned returned.result returned.finalState
            returned.finalCoherent)
          returned.remaining = .returned finalResult := by
  cases currentTransitionFuel with
  | zero =>
      simp [terminalAfterProjectedMachinePrefix,
        terminalAfterCertifiedProjectedMachinePrefix] at completed
  | succ current =>
      generalize executed : consumeProjectedMachinePrefix limits actor answers
        fuel state program coherent = prefixResult
      unfold terminalAfterProjectedMachinePrefix at completed
      unfold terminalAfterCertifiedProjectedMachinePrefix at completed
      unfold consumeProjectedMachinePrefix at executed
      rw [executed] at completed
      cases prefixResult with
      | error reason =>
          cases reason <;> simp [prefixFailureTerminal] at completed
      | ok returned =>
          refine ⟨returned, rfl, ?_⟩
          simpa using completed

/-- Named-positive wrapper around the scheduler factorization theorem.  It is
convenient when rewriting a callback-dependent machine expression because all
other arguments can be inferred from that expression. -/
theorem run_scheduler_native_list_machine_factorization_of_positive
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
    (positive : 0 < transitionFuel)
    (currentTransitionFuel : Nat) (answers : List Digest256) :
    runSchedulerNativeListTerminalFrom transitionFuel currentTransitionFuel
        (.machine limits limitBound actor state program fuel coherent
          onReturned) answers =
      terminalAfterProjectedMachinePrefix transitionFuel
        currentTransitionFuel limits limitBound actor state program fuel
        coherent onReturned answers := by
  exact run_scheduler_native_list_machine_factorization transitionFuel limits
    limitBound actor state program fuel coherent onReturned positive
    currentTransitionFuel answers

/-! ## Remove the result-only scheduler-stage wrapper -/

/-- Mapping into the one-constructor scheduler-stage wrapper does not alter
queries, oracle states, or step counts.  Its constructor is visibly
injective, so a completed wrapper run reflects to the exact underlying run. -/
theorem run_machine_scheduler_stage_completed_reflects
    {Final : Type u} {Payload : Type v}
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) :
    ∀ (fuel : Nat) (state : OracleState) (program : OracleMachine Payload)
      (result : Payload) (finalState : OracleState) (steps : Nat),
      runMachine controller limits actor fuel state
          (schedulerStageProgram Final program) =
        { halt := .returned (.completed result)
          oracle := finalState
          steps := steps } →
      runMachine controller limits actor fuel state program =
        { halt := .returned result
          oracle := finalState
          steps := steps } := by
  intro fuel
  induction fuel with
  | zero =>
      intro state program result finalState steps returned
      cases program with
      | pure value =>
          simpa [schedulerStageProgram, mapOracleMachineResult, runMachine]
            using returned
      | abort reason =>
          simp [schedulerStageProgram, mapOracleMachineResult, runMachine]
            at returned
      | query input next =>
          simp [schedulerStageProgram, mapOracleMachineResult, runMachine]
            at returned
  | succ fuel ih =>
      intro state program result finalState steps returned
      cases program with
      | pure value =>
          simpa [schedulerStageProgram, mapOracleMachineResult, runMachine]
            using returned
      | abort reason =>
          simp [schedulerStageProgram, mapOracleMachineResult, runMachine]
            at returned
      | query input next =>
          simp only [schedulerStageProgram, mapOracleMachineResult,
            runMachine] at returned ⊢
          cases queried : queryOracle controller limits actor state input with
          | error reason =>
              simp [queried] at returned
          | ok outputAndState =>
              rcases outputAndState with ⟨output, nextState⟩
              simp only [queried]
              simp only [queried] at returned
              generalize tailEq :
                runMachine controller limits actor fuel nextState
                    (mapOracleMachineResult SchedulerStageResult.completed
                      (next output)) = tailRun
                at returned
              rcases tailRun with ⟨tailHalt, tailOracle, tailSteps⟩
              cases tailHalt with
              | oracleAbort reason => simp at returned
              | outOfFuel => simp at returned
              | returned stageResult =>
                  cases stageResult with
                  | completed returnedResult =>
                      simp only [MachineRun.mk.injEq,
                        MachineHalt.returned.injEq,
                        SchedulerStageResult.completed.injEq] at returned
                      have reflected := ih nextState (next output)
                        returnedResult tailOracle tailSteps (by
                          simpa [schedulerStageProgram] using tailEq)
                      rw [reflected]
                      simpa [returned.1, returned.2.1, returned.2.2]

/-! ## Plain data recovered from the two concrete scheduler segments -/

abbrev RootSchedulerResult
    (TapeIdentity Statement Proof Payload : Type u) :=
  SchedulerNativePlainRomResult TapeIdentity Statement Proof Payload PUnit

/-- The two shortest projected machine prefixes of the root scheduler.  The
second prefix starts from the first prefix's literal final oracle and uses the
first prefix's literal adversary value.  `runtimeExact` records that the
runtime returned by the scheduler callback is precisely these values, rather
than caller-provided data. -/
structure CompletedRootProjectedPrefixes
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type u}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape) (available : List Digest256)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload) where
  adversary : ProjectedMachinePrefixReturned machine.adversaryLimits
    .adversary machine.adversaryFuel emptyOracle
    (schedulerStageProgram
      (RootSchedulerResult TapeIdentity Statement Proof Payload)
      (totalizeOracleMachine machine.adversaryFuel
        (machine.blackBox.start hidden machine.observation))) available
  adversaryValue :
    CheckedRawTag73AdversaryReturnedValue Statement Proof Payload
  adversaryResult :
    adversary.result = .completed (.ok adversaryValue)
  verifier : ProjectedMachinePrefixReturned machine.verifierLimits .verifier
    machine.verifierFuel adversary.finalState
    (schedulerStageProgram
      (RootSchedulerResult TapeIdentity Statement Proof Payload)
      (totalizeOracleMachine machine.verifierFuel
        (initialRawFutureFreeProgram machine.environment
          adversaryValue.rawMessages machine.driverFuel))) adversary.remaining
  verifierFinalStateValue : FutureFreeVerifierState
  verifierResult :
    verifier.result = .completed (.ok verifierFinalStateValue)
  runtimeExact : runtime = operationalRootRuntime
    (machine.tapeIdentity hidden) adversaryValue adversary.finalState
      verifier.finalState verifierFinalStateValue

/-- Deterministically scan the answer list for the two shortest root machine
segments.  The returned runtime is built only from their literal results and
oracle boundaries.  Room checks remain in the surrounding scheduler; this
function merely reconstructs successful segments after those checks passed. -/
def recoverRootRuntimeFromProjectedPrefixes
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type u}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape) (available : List Digest256) :
    Option
      (SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
        Payload) :=
  match consumeProjectedMachinePrefix machine.adversaryLimits .adversary
      available machine.adversaryFuel emptyOracle
      (schedulerStageProgram
        (RootSchedulerResult TapeIdentity Statement Proof Payload)
        (totalizeOracleMachine machine.adversaryFuel
          (machine.blackBox.start hidden machine.observation)))
      empty_oracle_history_total_coherent with
  | .error _reason => none
  | .ok adversary =>
      match adversary.result with
      | .completed (.error _failure) => none
      | .completed (.ok adversaryValue) =>
          match consumeProjectedMachinePrefix machine.verifierLimits .verifier
              adversary.remaining machine.verifierFuel adversary.finalState
              (schedulerStageProgram
                (RootSchedulerResult TapeIdentity Statement Proof Payload)
                (totalizeOracleMachine machine.verifierFuel
                  (initialRawFutureFreeProgram machine.environment
                    adversaryValue.rawMessages machine.driverFuel)))
              adversary.finalCoherent with
          | .error _reason => none
          | .ok verifier =>
              match verifier.result with
              | .completed (.error _failure) => none
              | .completed (.ok verifierFinalState) =>
                  some (operationalRootRuntime (machine.tapeIdentity hidden)
                    adversaryValue adversary.finalState verifier.finalState
                    verifierFinalState)

/-- A successful value of the deterministic prefix scanner retains the two
dependent trace certificates used to build it. -/
def recoveredRootRuntimeProjectedPrefixes
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type u}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape) (available : List Digest256)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (recovered : recoverRootRuntimeFromProjectedPrefixes machine hidden
      available = some runtime) :
    CompletedRootProjectedPrefixes machine hidden available runtime := by
  unfold recoverRootRuntimeFromProjectedPrefixes at recovered
  generalize adversaryExecution :
    consumeProjectedMachinePrefix machine.adversaryLimits .adversary available
      machine.adversaryFuel emptyOracle
      (schedulerStageProgram
        (RootSchedulerResult TapeIdentity Statement Proof Payload)
        (totalizeOracleMachine machine.adversaryFuel
          (machine.blackBox.start hidden machine.observation)))
      empty_oracle_history_total_coherent = adversaryResult at recovered
  cases adversaryResult with
  | error reason => simp [adversaryExecution] at recovered
  | ok adversary =>
      cases adversaryStage : adversary.result with
      | completed adversaryTotalized =>
          cases adversaryTotalized with
          | error failure =>
              simp [adversaryExecution, adversaryStage] at recovered
          | ok adversaryValue =>
              generalize verifierExecution :
                consumeProjectedMachinePrefix machine.verifierLimits .verifier
                  adversary.remaining machine.verifierFuel
                  adversary.finalState
                  (schedulerStageProgram
                    (RootSchedulerResult TapeIdentity Statement Proof Payload)
                    (totalizeOracleMachine machine.verifierFuel
                      (initialRawFutureFreeProgram machine.environment
                        adversaryValue.rawMessages machine.driverFuel)))
                  adversary.finalCoherent = verifierResult at recovered
              cases verifierResult with
              | error reason =>
                  simp [adversaryExecution, adversaryStage,
                    verifierExecution] at recovered
              | ok verifier =>
                  cases verifierStage : verifier.result with
                  | completed verifierTotalized =>
                      cases verifierTotalized with
                      | error failure =>
                          simp [adversaryExecution, adversaryStage,
                            verifierExecution, verifierStage] at recovered
                      | ok verifierFinalState =>
                          have runtimeExact := Option.some.inj (by
                            simpa [adversaryExecution, adversaryStage,
                              verifierExecution, verifierStage] using recovered)
                          exact
                            { adversary := adversary
                              adversaryValue := adversaryValue
                              adversaryResult := adversaryStage
                              verifier := verifier
                              verifierFinalStateValue := verifierFinalState
                              verifierResult := verifierStage
                              runtimeExact := runtimeExact.symm }

/-! ## Invert the actual initial-only scheduler -/

/-- A completed terminal of the literal initial-only cursor is exactly the
runtime found by the deterministic two-prefix scanner.  The sole hypotheses
are the operational terminal and the scheduler's positive transition budget. -/
theorem completed_scheduler_native_plain_rom_root_recovers_runtime
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type u}
    {globalOracleCalls : Nat}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape)
    (limitBounds : SchedulerNativeRootLimitBounds machine globalOracleCalls)
    (restorationConfiguration : ConcreteRestorationConfiguration)
    (answers : List Digest256)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (clientRun : ConcreteRestorationClientRun Statement Proof Payload PUnit)
    (completed :
      runSchedulerNativeListTerminal transitionFuel
          (schedulerNativePlainRomCursor machine hidden limitBounds
            restorationConfiguration 0 (.pure PUnit.unit)) answers =
        .returned (.completed runtime clientRun)) :
    recoverRootRuntimeFromProjectedPrefixes machine hidden answers =
      some runtime := by
  unfold runSchedulerNativeListTerminal at completed
  unfold schedulerNativePlainRomCursor at completed
  split at completed
  next adversaryRoom =>
    rw [run_scheduler_native_list_machine_factorization_of_positive
      (transitionFuel := transitionFuel)
      (currentTransitionFuel := transitionFuel) (answers := answers)
      (positive := positive)] at completed
    obtain ⟨adversary, adversaryExecution, completed⟩ :=
      terminal_after_projected_machine_prefix_returned_elim
        (positive := positive) (completed := completed)
    cases adversaryStage : adversary.result with
    | completed adversaryTotalized =>
        cases adversaryTotalized with
        | error failure =>
            cases failure with
            | oracleAbort reason =>
                simp only [adversaryStage] at completed
                rw [run_scheduler_native_list_returned_from
                  transitionFuel positive] at completed
                split at completed <;> simp at completed
            | timeout =>
                simp only [adversaryStage] at completed
                rw [run_scheduler_native_list_returned_from
                  transitionFuel positive] at completed
                split at completed <;> simp at completed
        | ok adversaryValue =>
            simp only [adversaryStage] at completed
            split at completed
            next verifierRoom =>
              rw [run_scheduler_native_list_machine_factorization_of_positive
                (transitionFuel := transitionFuel)
                (positive := positive)] at completed
              obtain ⟨verifier, verifierExecution, completed⟩ :=
                terminal_after_projected_machine_prefix_returned_elim
                  (positive := positive) (completed := completed)
              cases verifierStage : verifier.result with
              | completed verifierTotalized =>
                  cases verifierTotalized with
                  | error failure =>
                      cases failure with
                      | oracleAbort reason =>
                          simp only [verifierStage] at completed
                          rw [run_scheduler_native_list_returned_from
                            transitionFuel positive] at completed
                          split at completed <;> simp at completed
                      | timeout =>
                          simp only [verifierStage] at completed
                          rw [run_scheduler_native_list_returned_from
                            transitionFuel positive] at completed
                          split at completed <;> simp at completed
                  | ok verifierFinalState =>
                      simp only [verifierStage] at completed
                      simp only [
                        start_pure_client_from_root_returns_exact_accumulator,
                        map_scheduler_native_cursor_returned] at completed
                      rw [run_scheduler_native_list_returned_from
                        transitionFuel positive] at completed
                      split at completed
                      next continuationPositive =>
                        have runtimeExact :
                            operationalRootRuntime (machine.tapeIdentity hidden)
                                adversaryValue adversary.finalState
                                verifier.finalState verifierFinalState =
                              runtime := by
                          exact SchedulerNativePlainRomResult.completed.inj
                            (SchedulerNativeTerminal.returned.inj completed) |>.1
                        unfold recoverRootRuntimeFromProjectedPrefixes
                        simp only [adversaryExecution, adversaryStage,
                          verifierExecution, verifierStage]
                        exact congrArg some runtimeExact
                      next continuationZero => simp at completed
            next verifierNoRoom =>
              rw [run_scheduler_native_list_returned_from
                transitionFuel positive] at completed
              split at completed <;> simp at completed
  next adversaryNoRoom =>
    rw [run_scheduler_native_list_returned_of_positive
      transitionFuel positive] at completed
    simp at completed

/-- The operational prefix data directly yields both projected totalized root
runs.  The projected controllers are definitionally reconstructed from the
two actual history suffixes. -/
theorem completed_root_projected_prefixes_give_totalized_runs
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type u}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape) (available : List Digest256)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (prefixes : CompletedRootProjectedPrefixes machine hidden available
      runtime) :
    RootProjectedTotalizedRuns machine hidden runtime := by
  rcases prefixes with
    ⟨adversary, adversaryValue, adversaryResult, verifier,
      verifierFinalStateValue, verifierResult, runtimeExact⟩
  subst runtime
  have adversaryWrapped := projected_machine_prefix_returned_run_exact
    machine.adversaryLimits .adversary machine.adversaryFuel emptyOracle
    (schedulerStageProgram
      (RootSchedulerResult TapeIdentity Statement Proof Payload)
      (totalizeOracleMachine machine.adversaryFuel
        (machine.blackBox.start hidden machine.observation)))
    available adversary empty_oracle_history_total_coherent
  rw [adversaryResult] at adversaryWrapped
  have adversaryRun := run_machine_scheduler_stage_completed_reflects
    (Final := RootSchedulerResult TapeIdentity Statement Proof Payload)
    (controllerFromProjectedFreshAnswers emptyOracle.history
      (adversary.freshQueries.map Prod.snd))
    machine.adversaryLimits .adversary machine.adversaryFuel emptyOracle
    (totalizeOracleMachine machine.adversaryFuel
      (machine.blackBox.start hidden machine.observation))
    (.ok adversaryValue) adversary.finalState adversary.steps adversaryWrapped
  have adversaryAnswers :=
    projected_machine_prefix_fresh_answers_are_history_suffix
      machine.adversaryLimits .adversary machine.adversaryFuel emptyOracle
      (schedulerStageProgram
        (RootSchedulerResult TapeIdentity Statement Proof Payload)
        (totalizeOracleMachine machine.adversaryFuel
          (machine.blackBox.start hidden machine.observation)))
      available adversary
  have verifierWrapped := projected_machine_prefix_returned_run_exact
    machine.verifierLimits .verifier machine.verifierFuel adversary.finalState
    (schedulerStageProgram
      (RootSchedulerResult TapeIdentity Statement Proof Payload)
      (totalizeOracleMachine machine.verifierFuel
        (initialRawFutureFreeProgram machine.environment
          adversaryValue.rawMessages machine.driverFuel)))
    adversary.remaining verifier adversary.finalCoherent
  rw [verifierResult] at verifierWrapped
  have verifierRun := run_machine_scheduler_stage_completed_reflects
    (Final := RootSchedulerResult TapeIdentity Statement Proof Payload)
    (controllerFromProjectedFreshAnswers adversary.finalState.history
      (verifier.freshQueries.map Prod.snd))
    machine.verifierLimits .verifier machine.verifierFuel adversary.finalState
    (totalizeOracleMachine machine.verifierFuel
      (initialRawFutureFreeProgram machine.environment
        adversaryValue.rawMessages machine.driverFuel))
    (.ok verifierFinalStateValue) verifier.finalState verifier.steps
    verifierWrapped
  have verifierAnswers :=
    projected_machine_prefix_fresh_answers_are_history_suffix
      machine.verifierLimits .verifier machine.verifierFuel
      adversary.finalState
      (schedulerStageProgram
        (RootSchedulerResult TapeIdentity Statement Proof Payload)
        (totalizeOracleMachine machine.verifierFuel
          (initialRawFutureFreeProgram machine.environment
            adversaryValue.rawMessages machine.driverFuel)))
      adversary.remaining verifier
  refine ⟨adversary.steps, verifier.steps, ?_, ?_⟩
  · simpa [rootAdversaryProjectedController, rootAdversaryFreshAnswers,
      operationalRootRuntime, adversaryAnswers] using adversaryRun
  · simpa [rootVerifierProjectedController, rootVerifierFreshAnswers,
      operationalRootRuntime, verifierAnswers] using verifierRun

/-! ## Exact finite experiment corollaries -/

/-- Principal bridge: an actual completed initial-only exact experiment yields
the two projected totalized machine equations.  No run equation appears as a
premise; `completed` is only the terminal observation of the executable
uniform-tape scheduler. -/
theorem completed_exact_plain_rom_root_gives_projected_totalized_runs
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (clientRun : ConcreteRestorationClientRun Statement Proof Payload PUnit)
    (completed :
      (runExactPlainRomRoot transitionFuel configuration sample).terminal =
        .returned (.completed runtime clientRun)) :
    RootProjectedTotalizedRuns configuration.machine sample.1 runtime := by
  have listCompleted :
      runSchedulerNativeListTerminal transitionFuel
          (exactPlainRomRootCursor configuration sample.1)
          (freshAnswerTapeToList sample.2) =
        .returned (.completed runtime clientRun) := by
    rw [← run_scheduler_native_terminal_eq_list]
    exact completed
  have recovered :=
    completed_scheduler_native_plain_rom_root_recovers_runtime transitionFuel
      positive configuration.machine sample.1 configuration.rootLimitBounds
      configuration.restorationConfiguration
      (freshAnswerTapeToList sample.2) runtime clientRun (by
        simpa [exactPlainRomRootCursor] using listCompleted)
  exact completed_root_projected_prefixes_give_totalized_runs
    configuration.machine sample.1 (freshAnswerTapeToList sample.2) runtime
    (recoveredRootRuntimeProjectedPrefixes configuration.machine
      sample.1 (freshAnswerTapeToList sample.2) runtime recovered)

/-- The completed exact root therefore satisfies the non-circular operational
root invariant consumed by the raw K1.2--K1.5 interface. -/
theorem completed_exact_plain_rom_root_implies_root_invariant
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (clientRun : ConcreteRestorationClientRun Statement Proof Payload PUnit)
    (completed :
      (runExactPlainRomRoot transitionFuel configuration sample).terminal =
        .returned (.completed runtime clientRun)) :
    SchedulerNativePlainRomRootInvariant runtime := by
  exact projected_root_runs_imply_root_invariant configuration.machine sample.1
    runtime
    (completed_exact_plain_rom_root_gives_projected_totalized_runs
      transitionFuel positive configuration sample runtime clientRun completed)

#print axioms run_machine_scheduler_stage_completed_reflects
#print axioms recoveredRootRuntimeProjectedPrefixes
#print axioms completed_scheduler_native_plain_rom_root_recovers_runtime
#print axioms completed_root_projected_prefixes_give_totalized_runs
#print axioms completed_exact_plain_rom_root_gives_projected_totalized_runs
#print axioms completed_exact_plain_rom_root_implies_root_invariant

end

end AspisK1.V7Tag73CompletedRootProjection
