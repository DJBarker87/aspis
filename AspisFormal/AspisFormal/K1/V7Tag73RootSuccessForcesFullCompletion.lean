import AspisFormal.K1.V7Tag73ExactPlainRomOperationalCompletion
import AspisFormal.K1.V7Tag73FullResultRootRuns
import AspisFormal.K1.V7Tag73SchedulerResultMapSemantics

/-!
# A successful Tag-73 source root forces full-scheduler completion

The initial-only and result-carrying experiments start the same hidden-tape
prover and verifier on the same master-answer tape.  The former stops after
constructing the root; the latter continues into the finite restoration
client.  This leaf proves the missing one-way operational bridge: once the
initial-only scheduler completed, the full scheduler cannot report an initial
failure, and the exact resource theorem rules out a native failure.  Hence it
returns a concrete client run under exactly the same root runtime.

No outcome, trace cover, restore function, or compiler conclusion is supplied
by a caller.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73RootSuccessForcesFullCompletion

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73ProjectedMachinePrefix
open AspisK1.V7Tag73SchedulerMachineFactorization
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73CompletedRootProjection
open AspisK1.V7Tag73FullResultRootRuns
open AspisK1.V7Tag73UniformRawVerifierExecution
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73SchedulerResultMapSemantics
open AspisK1.V7Tag73ExactPlainRomOperationalCompletion

noncomputable section

universe u

/-- Proof-relevant inversion of the actual initial-only scheduler.  Besides
the two returned projected prefixes, it retains both executable room guards
and the literal prefix-consumer equations. -/
structure CompletedRootOperationalStages
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type u}
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape)
    (limitBounds : SchedulerNativeRootLimitBounds machine globalOracleCalls)
    (restorationConfiguration : ConcreteRestorationConfiguration)
    (answers : List Digest256)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload) : Type u where
  adversaryRoom : StageHasOracleRoom machine.adversaryLimits emptyOracle
    machine.adversaryFuel
  adversary : ProjectedMachinePrefixReturned machine.adversaryLimits
    .adversary machine.adversaryFuel emptyOracle
    (schedulerStageProgram
      (RootSchedulerResult TapeIdentity Statement Proof Payload)
      (totalizeOracleMachine machine.adversaryFuel
        (machine.blackBox.start hidden machine.observation))) answers
  adversaryExecution :
    consumeProjectedMachinePrefix machine.adversaryLimits .adversary answers
        machine.adversaryFuel emptyOracle
        (schedulerStageProgram
          (RootSchedulerResult TapeIdentity Statement Proof Payload)
          (totalizeOracleMachine machine.adversaryFuel
            (machine.blackBox.start hidden machine.observation)))
        empty_oracle_history_total_coherent = .ok adversary
  adversaryValue :
    CheckedRawTag73AdversaryReturnedValue Statement Proof Payload
  adversaryResult : adversary.result = .completed (.ok adversaryValue)
  verifierRoom : StageHasOracleRoom machine.verifierLimits
    adversary.finalState machine.verifierFuel
  verifier : ProjectedMachinePrefixReturned machine.verifierLimits .verifier
    machine.verifierFuel adversary.finalState
    (schedulerStageProgram
      (RootSchedulerResult TapeIdentity Statement Proof Payload)
      (totalizeOracleMachine machine.verifierFuel
        (initialRawFutureFreeProgram machine.environment
          adversaryValue.rawMessages machine.driverFuel))) adversary.remaining
  verifierExecution :
    consumeProjectedMachinePrefix machine.verifierLimits .verifier
        adversary.remaining machine.verifierFuel adversary.finalState
        (schedulerStageProgram
          (RootSchedulerResult TapeIdentity Statement Proof Payload)
          (totalizeOracleMachine machine.verifierFuel
            (initialRawFutureFreeProgram machine.environment
              adversaryValue.rawMessages machine.driverFuel)))
        adversary.finalCoherent = .ok verifier
  verifierFinalState : FutureFreeVerifierState
  verifierResult : verifier.result = .completed (.ok verifierFinalState)
  runtimeExact : runtime = operationalRootRuntime
    (machine.tapeIdentity hidden) adversaryValue adversary.finalState
      verifier.finalState verifierFinalState

/-- A literal completed initial-only terminal constructs all stage data above;
neither guard nor projected prefix is accepted independently. -/
theorem completed_root_constructs_operational_stages_nonempty
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
    Nonempty (CompletedRootOperationalStages transitionFuel machine hidden
      limitBounds restorationConfiguration answers runtime) := by
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
                        have runtimeExact : runtime =
                            operationalRootRuntime (machine.tapeIdentity hidden)
                              adversaryValue adversary.finalState
                                verifier.finalState verifierFinalState := by
                          exact (SchedulerNativePlainRomResult.completed.inj
                            (SchedulerNativeTerminal.returned.inj completed)).1
                              |>.symm
                        exact ⟨
                          { adversaryRoom := adversaryRoom
                            adversary := adversary
                            adversaryExecution := adversaryExecution
                            adversaryValue := adversaryValue
                            adversaryResult := adversaryStage
                            verifierRoom := verifierRoom
                            verifier := verifier
                            verifierExecution := verifierExecution
                            verifierFinalState := verifierFinalState
                            verifierResult := verifierStage
                            runtimeExact := runtimeExact }⟩
                      next continuationZero => simp at completed
            next verifierNoRoom =>
              rw [run_scheduler_native_list_returned_from
                transitionFuel positive] at completed
              split at completed <;> simp at completed
  next adversaryNoRoom =>
    rw [run_scheduler_native_list_returned_of_positive transitionFuel positive]
      at completed
    simp at completed

/-- Chosen proof-relevant root-stage inversion.  Existence is established by
the literal scheduler inversion above, and standard choice only exposes the
two concrete stage values to subsequent operational composition. -/
noncomputable def completed_root_constructs_operational_stages
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
    CompletedRootOperationalStages transitionFuel machine hidden limitBounds
      restorationConfiguration answers runtime :=
  Classical.choice
    (completed_root_constructs_operational_stages_nonempty transitionFuel
      positive machine hidden limitBounds restorationConfiguration answers
      runtime clientRun completed)

/-- Forgetting executable equations recovers the stable projected-prefix
interface used by the root source theorem. -/
def CompletedRootOperationalStages.projectedPrefixes
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type u}
    {globalOracleCalls : Nat}
    {transitionFuel : Nat}
    {machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    {hidden : HiddenTape}
    {limitBounds : SchedulerNativeRootLimitBounds machine globalOracleCalls}
    {restorationConfiguration : ConcreteRestorationConfiguration}
    {answers : List Digest256}
    {runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload}
    (stages : CompletedRootOperationalStages transitionFuel machine hidden
      limitBounds restorationConfiguration answers runtime) :
    CompletedRootProjectedPrefixes machine hidden answers runtime where
  adversary := stages.adversary
  adversaryValue := stages.adversaryValue
  adversaryResult := stages.adversaryResult
  verifier := stages.verifier
  verifierFinalStateValue := stages.verifierFinalState
  verifierResult := stages.verifierResult
  runtimeExact := stages.runtimeExact

/-! ## The returned full run cannot be an initial failure -/

/-- If the root execution succeeded and the full scheduler reached any
ordinary return on the same answer list, that return is necessarily a
completed client run under the same root. -/
theorem completed_root_and_returned_full_force_same_root_completion
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type u}
    {globalOracleCalls : Nat}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape)
    (limitBounds : SchedulerNativeRootLimitBounds machine globalOracleCalls)
    (restorationConfiguration : ConcreteRestorationConfiguration)
    (restorationFuel : Nat)
    (client : ConcreteRestorationClient Result)
    (answers : List Digest256)
    (rootRuntime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement
      Proof Payload)
    (rootClientRun : ConcreteRestorationClientRun Statement Proof Payload
      PUnit)
    (rootCompleted :
      runSchedulerNativeListTerminal transitionFuel
          (schedulerNativePlainRomCursor machine hidden limitBounds
            restorationConfiguration 0 (.pure PUnit.unit)) answers =
        .returned (.completed rootRuntime rootClientRun))
    (fullReturned : ∃ fullResult,
      runSchedulerNativeListTerminal transitionFuel
          (schedulerNativePlainRomCursor machine hidden limitBounds
            restorationConfiguration restorationFuel client) answers =
        .returned fullResult) :
    ∃ clientRun : ConcreteRestorationClientRun Statement Proof Payload Result,
      runSchedulerNativeListTerminal transitionFuel
          (schedulerNativePlainRomCursor machine hidden limitBounds
            restorationConfiguration restorationFuel client) answers =
        .returned (.completed rootRuntime clientRun) := by
  let rootStages := completed_root_constructs_operational_stages transitionFuel
    positive machine hidden limitBounds restorationConfiguration answers
      rootRuntime rootClientRun rootCompleted
  obtain ⟨fullResult, fullTerminalOriginal⟩ := fullReturned
  have fullTerminal := fullTerminalOriginal
  unfold runSchedulerNativeListTerminal at fullTerminal
  unfold schedulerNativePlainRomCursor at fullTerminal
  split at fullTerminal
  next adversaryRoom =>
    rw [run_scheduler_native_list_machine_factorization_of_positive
      (transitionFuel := transitionFuel)
      (currentTransitionFuel := transitionFuel) (answers := answers)
      (positive := positive)] at fullTerminal
    obtain ⟨fullAdversary, fullAdversaryExecution, fullTerminal⟩ :=
      terminal_after_projected_machine_prefix_returned_elim
        (positive := positive) (completed := fullTerminal)
    cases fullAdversaryStage : fullAdversary.result with
    | completed fullAdversaryValue =>
      have rootAdversaryRun :=
        projected_scheduler_stage_prefix_underlying_run_exact
          (Final := RootSchedulerResult TapeIdentity Statement Proof Payload)
          machine.adversaryLimits .adversary machine.adversaryFuel emptyOracle
          (totalizeOracleMachine machine.adversaryFuel
            (machine.blackBox.start hidden machine.observation))
          answers rootStages.adversary (.ok rootStages.adversaryValue)
          rootStages.adversaryResult empty_oracle_history_total_coherent
      have fullAdversaryRun :=
        projected_scheduler_stage_prefix_underlying_run_exact
          (Final := SchedulerNativePlainRomResult TapeIdentity Statement Proof
            Payload Result)
          machine.adversaryLimits .adversary machine.adversaryFuel emptyOracle
          (totalizeOracleMachine machine.adversaryFuel
            (machine.blackBox.start hidden machine.observation))
          answers fullAdversary fullAdversaryValue fullAdversaryStage
          empty_oracle_history_total_coherent
      have adversaryOutputsEqual :=
        rootAdversaryRun.symm.trans fullAdversaryRun
      simp only [MachineRun.mk.injEq, MachineHalt.returned.injEq] at adversaryOutputsEqual
      rcases adversaryOutputsEqual with
        ⟨adversaryValueExact, adversaryOracleExact,
          _adversaryStepsExact⟩
      have fullAdversaryValueExact : fullAdversaryValue =
          (.ok rootStages.adversaryValue :
            Except TotalizedMachineFailure
              (CheckedRawTag73AdversaryReturnedValue Statement Proof
                Payload)) := adversaryValueExact.symm
      subst fullAdversaryValue
      have rootFresh :=
        projected_machine_prefix_fresh_answers_are_history_suffix
          machine.adversaryLimits .adversary machine.adversaryFuel emptyOracle
          (schedulerStageProgram
            (RootSchedulerResult TapeIdentity Statement Proof Payload)
            (totalizeOracleMachine machine.adversaryFuel
              (machine.blackBox.start hidden machine.observation)))
          answers rootStages.adversary
      have fullFresh :=
        projected_machine_prefix_fresh_answers_are_history_suffix
          machine.adversaryLimits .adversary machine.adversaryFuel emptyOracle
          (schedulerStageProgram
            (SchedulerNativePlainRomResult TapeIdentity Statement Proof Payload
              Result)
            (totalizeOracleMachine machine.adversaryFuel
              (machine.blackBox.start hidden machine.observation)))
          answers fullAdversary
      have adversaryFreshExact :
          rootStages.adversary.freshQueries.map Prod.snd =
            fullAdversary.freshQueries.map Prod.snd := by
        rw [← rootFresh, ← fullFresh, adversaryOracleExact]
      have adversaryDecomposition :=
        rootStages.adversary.availableExact.symm.trans
          fullAdversary.availableExact
      rw [adversaryFreshExact] at adversaryDecomposition
      have adversaryRemainingExact :
          rootStages.adversary.remaining = fullAdversary.remaining :=
        List.append_cancel_left adversaryDecomposition
      simp only [fullAdversaryStage] at fullTerminal
      split at fullTerminal
      next verifierRoom =>
        rw [run_scheduler_native_list_machine_factorization_of_positive
          (transitionFuel := transitionFuel)
          (positive := positive)] at fullTerminal
        obtain ⟨fullVerifier, fullVerifierExecution, fullTerminal⟩ :=
          terminal_after_projected_machine_prefix_returned_elim
            (positive := positive) (completed := fullTerminal)
        cases fullVerifierStage : fullVerifier.result with
        | completed fullVerifierValue =>
          have rootVerifierRun :=
            projected_scheduler_stage_prefix_underlying_run_exact
              (Final := RootSchedulerResult TapeIdentity Statement Proof
                Payload)
              machine.verifierLimits .verifier machine.verifierFuel
              rootStages.adversary.finalState
              (totalizeOracleMachine machine.verifierFuel
                (initialRawFutureFreeProgram machine.environment
                  rootStages.adversaryValue.rawMessages machine.driverFuel))
              rootStages.adversary.remaining rootStages.verifier
              (.ok rootStages.verifierFinalState) rootStages.verifierResult
              rootStages.adversary.finalCoherent
          have fullVerifierRunNative :=
            projected_scheduler_stage_prefix_underlying_run_exact
              (Final := SchedulerNativePlainRomResult TapeIdentity Statement
                Proof Payload Result)
              machine.verifierLimits .verifier machine.verifierFuel
              fullAdversary.finalState
              (totalizeOracleMachine machine.verifierFuel
                (initialRawFutureFreeProgram machine.environment
                  rootStages.adversaryValue.rawMessages machine.driverFuel))
              fullAdversary.remaining fullVerifier fullVerifierValue
              fullVerifierStage fullAdversary.finalCoherent
          have fullVerifierRun :
              runMachine
                  (controllerFromProjectedFreshAnswers
                    rootStages.adversary.finalState.history
                    rootStages.adversary.remaining)
                  machine.verifierLimits .verifier machine.verifierFuel
                  rootStages.adversary.finalState
                  (totalizeOracleMachine machine.verifierFuel
                    (initialRawFutureFreeProgram machine.environment
                      rootStages.adversaryValue.rawMessages
                        machine.driverFuel)) =
                { halt := .returned fullVerifierValue
                  oracle := fullVerifier.finalState
                  steps := fullVerifier.steps } := by
            simpa only [adversaryOracleExact, adversaryRemainingExact] using
              fullVerifierRunNative
          have verifierOutputsEqual :=
            rootVerifierRun.symm.trans fullVerifierRun
          simp only [MachineRun.mk.injEq, MachineHalt.returned.injEq] at verifierOutputsEqual
          rcases verifierOutputsEqual with
            ⟨verifierValueExact, verifierOracleExact,
              _verifierStepsExact⟩
          have fullVerifierValueExact : fullVerifierValue =
              (.ok rootStages.verifierFinalState :
                Except TotalizedMachineFailure FutureFreeVerifierState) :=
            verifierValueExact.symm
          subst fullVerifierValue
          simp only [fullVerifierStage] at fullTerminal
          rw [run_scheduler_native_list_terminal_from_map] at fullTerminal
          generalize clientTerminalExact :
            runSchedulerNativeListTerminalFrom transitionFuel _
              (startConcreteRestorationClientFromRoot
                (globalOracleCalls := globalOracleCalls)
                (machine.blackBox.start hidden machine.observation)
                machine.environment
                (operationalRootRuntime (machine.tapeIdentity hidden)
                  rootStages.adversaryValue fullAdversary.finalState
                  fullVerifier.finalState
                  rootStages.verifierFinalState).node
                restorationConfiguration restorationFuel client)
              fullVerifier.remaining = clientTerminal
            at fullTerminal
          cases clientTerminal with
          | failed reason =>
              simp [mapSchedulerNativeTerminalResult] at fullTerminal
          | returned clientRun =>
              have resultExact : fullResult =
                  .completed
                    (operationalRootRuntime (machine.tapeIdentity hidden)
                      rootStages.adversaryValue
                      fullAdversary.finalState
                      fullVerifier.finalState
                      rootStages.verifierFinalState)
                    clientRun := by
                exact SchedulerNativeTerminal.returned.inj fullTerminal.symm
              have runtimeExact :
                  operationalRootRuntime (machine.tapeIdentity hidden)
                      rootStages.adversaryValue fullAdversary.finalState
                      fullVerifier.finalState rootStages.verifierFinalState =
                    rootRuntime := by
                exact (congrArg₂
                  (fun adversaryState verifierState =>
                    operationalRootRuntime (machine.tapeIdentity hidden)
                      rootStages.adversaryValue adversaryState verifierState
                      rootStages.verifierFinalState)
                  adversaryOracleExact.symm verifierOracleExact.symm).trans
                    rootStages.runtimeExact.symm
              rw [runtimeExact] at resultExact
              refine ⟨clientRun, ?_⟩
              rw [fullTerminalOriginal, resultExact]
      next verifierNoRoom =>
        apply (verifierNoRoom ?_).elim
        simpa only [← adversaryOracleExact] using rootStages.verifierRoom
  next adversaryNoRoom =>
    exact (adversaryNoRoom rootStages.adversaryRoom).elim

/-! ## Exact finite experiment theorem -/

/-- Principal experiment-facing bridge.  The root observation is the only
success premise; full native completion is derived from the exact finite
resource theorem, and initial success is transferred by the operational stage
inversion above. -/
theorem completed_exact_plain_rom_root_forces_full_completion
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters)
    (rootRuntime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement
      Proof Payload)
    (rootClientRun : ConcreteRestorationClientRun Statement Proof Payload
      PUnit)
    (transitionRoom : 3 ≤ transitionFuel)
    (rootCompleted :
      (runExactPlainRomRoot transitionFuel configuration sample).terminal =
        .returned (.completed rootRuntime rootClientRun)) :
    ∃ clientRun : ConcreteRestorationClientRun Statement Proof Payload Result,
      (runExactPlainRom transitionFuel configuration sample).terminal =
        .returned (.completed rootRuntime clientRun) := by
  obtain ⟨fullResult, fullReturned⟩ :=
    run_exact_plain_rom_terminal_is_returned transitionFuel configuration sample
      transitionRoom
  have rootListCompleted :
      runSchedulerNativeListTerminal transitionFuel
          (exactPlainRomRootCursor configuration sample.1)
          (freshAnswerTapeToList sample.2) =
        .returned (.completed rootRuntime rootClientRun) := by
    rw [← run_scheduler_native_terminal_eq_list]
    exact rootCompleted
  have listCompletion :=
    completed_root_and_returned_full_force_same_root_completion transitionFuel
      (by omega) configuration.machine sample.1 configuration.rootLimitBounds
      configuration.restorationConfiguration configuration.restorationFuel
      configuration.client (freshAnswerTapeToList sample.2) rootRuntime
      rootClientRun (by simpa [exactPlainRomRootCursor] using rootListCompleted)
      ⟨fullResult, by
        rw [← run_scheduler_native_terminal_eq_list]
        exact fullReturned⟩
  obtain ⟨clientRun, listCompleted⟩ := listCompletion
  refine ⟨clientRun, ?_⟩
  rw [runExactPlainRom,
    run_scheduler_native_terminal_eq_list transitionFuel
      (exactCompilerTargetCaps parameters).length
      (exactPlainRomCursor configuration sample.1) sample.2]
  simpa [exactPlainRomCursor] using listCompleted

#print axioms completed_root_constructs_operational_stages
#print axioms completed_root_and_returned_full_force_same_root_completion
#print axioms completed_exact_plain_rom_root_forces_full_completion

end

end AspisK1.V7Tag73RootSuccessForcesFullCompletion
