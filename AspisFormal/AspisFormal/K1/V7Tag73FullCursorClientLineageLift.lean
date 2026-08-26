import AspisFormal.K1.V7Tag73RootSuccessForcesFullCompletion
import AspisFormal.K1.V7Tag73CompletedFullRunProjection
import AspisFormal.K1.V7Tag73SchedulerResultMapSemantics
import AspisFormal.K1.V7Tag73SchedulerTraceFactorization

/-!
# Exact full-cursor/root/client trace factorization for Tag-73

The deployed result-carrying cursor executes two root machines and then maps
the concrete restoration client's result into
`SchedulerNativePlainRomResult.completed`. Machine normalization consumes
transition fuel even when a projected segment has no fresh query. Therefore
the tempting statement that the full cursor and client cursor expose the same
request at the same fuel after the root prefix is false.

This leaf uses the correct operational object instead: the trace-retaining
list scheduler. It factors the actual full run through the actual projected
prover prefix, then through the dependent verifier prefix, and finally through
the unmapped concrete client at the exact continuation fuel
`machinePrefixContinuationTransitionFuel` computes. The result map changes
only terminal data and leaves the client trace literal.

No cursor alignment, root trace, continuation fuel, restore function, oracle
controller, outcome, or compiler conclusion is supplied by a caller.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73FullCursorClientLineageLift

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
open AspisK1.V7Tag73CompletedFullRunProjection
open AspisK1.V7Tag73UniformRawVerifierExecution
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73SchedulerResultMapSemantics
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73RootSuccessForcesFullCompletion

noncomputable section

universe u

local instance stageHasOracleRoomDecidable
    (limits : OracleLimits) (state : OracleState) (fuel : Nat) :
    Decidable (StageHasOracleRoom limits state fuel) := by
  unfold StageHasOracleRoom
  infer_instance

/-! ## Result mapping preserves the trace-retaining run -/

/-- Map only the terminal result of a trace-retaining native run. -/
def mapSchedulerNativeRunResult
    {Input Output : Type u} (map : Input → Output) :
    SchedulerNativeRun Input → SchedulerNativeRun Output
  | run =>
      { terminal := mapSchedulerNativeTerminalResult map run.terminal
        trace := run.trace }

/-- The trace-retaining list scheduler commutes with changing only the final
cursor result. Result mapping cannot change, add, or delete a coordinate. -/
theorem run_scheduler_native_list_run_from_map
    {globalOracleCalls : Nat} {Input Output : Type u}
    (map : Input → Output) (transitionFuel : Nat) :
    ∀ (currentTransitionFuel : Nat)
      (cursor : SchedulerNativeCursor globalOracleCalls Input)
      (answers : List Digest256),
      runSchedulerNativeListRunFrom transitionFuel currentTransitionFuel
          (mapSchedulerNativeCursorResult map cursor) answers =
        mapSchedulerNativeRunResult map
          (runSchedulerNativeListRunFrom transitionFuel currentTransitionFuel
            cursor answers) := by
  intro currentTransitionFuel cursor answers
  induction answers generalizing currentTransitionFuel cursor with
  | nil =>
      unfold runSchedulerNativeListRunFrom terminalAtExposureEnd
      rw [seek_scheduler_native_exposure_map]
      cases seekSchedulerNativeExposure currentTransitionFuel cursor <;> rfl
  | cons answer rest ih =>
      unfold runSchedulerNativeListRunFrom
      rw [seek_scheduler_native_exposure_map]
      cases request : seekSchedulerNativeExposure currentTransitionFuel cursor
          with
      | returned result =>
          simp only [mapSchedulerNativeRequestResult,
            mapSchedulerNativeCursorResult, mapSchedulerNativeRunResult]
          have h := ih transitionFuel
            (.returned result : SchedulerNativeCursor globalOracleCalls Input)
          exact congrArg (fun tail : SchedulerNativeRun Output =>
            SchedulerNativeRun.mk tail.terminal
              (.padding answer :: tail.trace)) h
      | failed reason =>
          simp only [mapSchedulerNativeRequestResult,
            mapSchedulerNativeCursorResult, mapSchedulerNativeRunResult]
          have h := ih transitionFuel
            (.failed reason : SchedulerNativeCursor globalOracleCalls Input)
          exact congrArg (fun tail : SchedulerNativeRun Output =>
            SchedulerNativeRun.mk tail.terminal
              (.padding answer :: tail.trace)) h
      | transitionLimit =>
          simp only [mapSchedulerNativeRequestResult,
            mapSchedulerNativeCursorResult, mapSchedulerNativeRunResult]
          have h := ih transitionFuel
            (.failed .transitionLimit :
              SchedulerNativeCursor globalOracleCalls Input)
          exact congrArg (fun tail : SchedulerNativeRun Output =>
            SchedulerNativeRun.mk tail.terminal
              (.padding answer :: tail.trace)) h
      | @machineFresh MachineResult limits limitBound actor state input
          nextProgram remainingFuel coherent totalRoom freshRoom missing
          onReturned =>
          simp only [mapSchedulerNativeRequestResult,
            mapSchedulerNativeCursorResult, mapSchedulerNativeRunResult]
          have h := ih transitionFuel
            (.machine limits limitBound actor
              (freshQueryState actor state input answer)
              (nextProgram answer) remainingFuel
              (fresh_query_state_preserves_history_total_coherent actor state
                input answer coherent) onReturned)
          exact congrArg (fun tail : SchedulerNativeRun Output =>
            SchedulerNativeRun.mk tail.terminal
              (.machineFresh actor input answer :: tail.trace)) h
      | forkOutput frozenHistory pairRoom outputInput advanceInput template next =>
          simp only [mapSchedulerNativeRequestResult,
            mapSchedulerNativeCursorResult, mapSchedulerNativeRunResult]
          have h := ih transitionFuel
            (.forkAdvance frozenHistory pairRoom outputInput advanceInput
              template answer next)
          exact congrArg (fun tail : SchedulerNativeRun Output =>
            SchedulerNativeRun.mk tail.terminal
              (.forkOutput frozenHistory outputInput advanceInput
                template answer :: tail.trace)) h
      | forkAdvance frozenHistory pairRoom outputInput advanceInput template
          forkOutput next =>
          let scheduled : ScheduledForkCoins :=
            { frozenHistory := frozenHistory
              outputInput := outputInput
              advanceInput := advanceInput
              template := template
              forkOutput := forkOutput
              forkAdvance := answer }
          simp only [mapSchedulerNativeRequestResult,
            mapSchedulerNativeCursorResult, mapSchedulerNativeRunResult]
          have h := ih transitionFuel (next scheduled.configuration)
          exact congrArg (fun tail : SchedulerNativeRun Output =>
            SchedulerNativeRun.mk tail.terminal
              (.forkAdvance scheduled :: tail.trace)) h

/-! ## Canonical root records, continuation fuel, and client tail -/

def fullProjectedRootRecords
    {HiddenTape TapeIdentity Observation Statement Proof Payload Final : Type u}
    {machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    {hidden : HiddenTape} {available : List Digest256}
    {runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload}
    (prefixes : FullResultRootProjectedPrefixes (Final := Final) machine hidden
      available runtime) : List UnifiedExposureRecord :=
  projectedMachineFreshRecords .adversary prefixes.adversary.freshQueries ++
    projectedMachineFreshRecords .verifier prefixes.verifier.freshQueries

def fullProjectedRootClientTransitionFuel
    {HiddenTape TapeIdentity Observation Statement Proof Payload Final : Type u}
    {machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    {hidden : HiddenTape} {available : List Digest256}
    {runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload}
    (transitionFuel : Nat)
    (prefixes : FullResultRootProjectedPrefixes (Final := Final) machine hidden
      available runtime) : Nat :=
  machinePrefixContinuationTransitionFuel transitionFuel
    (machinePrefixContinuationTransitionFuel transitionFuel
      (transitionFuel - 1) prefixes.adversary.freshQueries - 1)
    prefixes.verifier.freshQueries

def fullProjectedConcreteClientTailRun
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (prefixes : FullResultRootProjectedPrefixes
      (Final := SchedulerNativePlainRomResult TapeIdentity Statement Proof
        Payload Result)
      configuration.machine sample.1 (freshAnswerTapeToList sample.2) runtime) :
    SchedulerNativeRun
      (ConcreteRestorationClientRun Statement Proof Payload Result) :=
  runSchedulerNativeListRunFrom transitionFuel
    (fullProjectedRootClientTransitionFuel transitionFuel prefixes)
    (startConcreteRestorationClientFromRoot
      (globalOracleCalls := globalFull256OracleCallCap parameters)
      (configuration.machine.blackBox.start sample.1
        configuration.machine.observation)
      configuration.machine.environment runtime.node
      configuration.restorationConfiguration configuration.restorationFuel
      configuration.client)
    prefixes.verifier.remaining

/-! ## Named deployed callbacks -/

def mappedConcreteClientContinuation
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (hidden : HiddenTape)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload) :
    SchedulerNativeCursor (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement Proof Payload
        Result) :=
  mapSchedulerNativeCursorResult
    (fun clientRun => SchedulerNativePlainRomResult.completed runtime clientRun)
    (startConcreteRestorationClientFromRoot
      (globalOracleCalls := globalFull256OracleCallCap parameters)
      (configuration.machine.blackBox.start hidden
        configuration.machine.observation)
      configuration.machine.environment runtime.node
      configuration.restorationConfiguration configuration.restorationFuel
      configuration.client)

def fullRootVerifierReturnedContinuation
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (hidden : HiddenTape)
    (adversaryValue :
      CheckedRawTag73AdversaryReturnedValue Statement Proof Payload)
    (proverFinalOracle : OracleState)
    (verifierStage : SchedulerStageResult
      (SchedulerNativePlainRomResult TapeIdentity Statement Proof Payload
        Result)
      (Except TotalizedMachineFailure FutureFreeVerifierState))
    (verifierFinalOracle : OracleState)
    (_verifierCoherent : HistoryTotalCoherent verifierFinalOracle) :
    SchedulerNativeCursor (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement Proof Payload
        Result) :=
  match verifierStage with
  | .completed verifierResult =>
      match verifierResult with
      | .error (.oracleAbort reason) =>
          .returned (.initialFailure (.verifierOracleAbort reason))
      | .error .timeout =>
          .returned (.initialFailure .verifierTimeout)
      | .ok verifierFinalState =>
          mappedConcreteClientContinuation configuration hidden
            (operationalRootRuntime
              (configuration.machine.tapeIdentity hidden) adversaryValue
              proverFinalOracle verifierFinalOracle verifierFinalState)

def fullRootVerifierCursor
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (hidden : HiddenTape)
    (adversaryValue :
      CheckedRawTag73AdversaryReturnedValue Statement Proof Payload)
    (proverFinalOracle : OracleState)
    (proverCoherent : HistoryTotalCoherent proverFinalOracle) :
    SchedulerNativeCursor (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement Proof Payload
        Result) :=
  .machine configuration.machine.verifierLimits
    configuration.rootLimitBounds.verifier .verifier proverFinalOracle
    (schedulerStageProgram
      (SchedulerNativePlainRomResult TapeIdentity Statement Proof Payload
        Result)
      (totalizeOracleMachine configuration.machine.verifierFuel
        (initialRawFutureFreeProgram configuration.machine.environment
          adversaryValue.rawMessages configuration.machine.driverFuel)))
    configuration.machine.verifierFuel proverCoherent
    (fullRootVerifierReturnedContinuation configuration hidden adversaryValue
      proverFinalOracle)

def fullRootAdversaryReturnedContinuation
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (hidden : HiddenTape)
    (adversaryStage : SchedulerStageResult
      (SchedulerNativePlainRomResult TapeIdentity Statement Proof Payload
        Result)
      (Except TotalizedMachineFailure
        (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload)))
    (proverFinalOracle : OracleState)
    (proverCoherent : HistoryTotalCoherent proverFinalOracle) :
    SchedulerNativeCursor (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement Proof Payload
        Result) :=
  match adversaryStage with
  | .completed adversaryResult =>
      match adversaryResult with
      | .error (.oracleAbort reason) =>
          .returned (.initialFailure (.adversaryOracleAbort reason))
      | .error .timeout =>
          .returned (.initialFailure .adversaryTimeout)
      | .ok adversaryValue =>
          if StageHasOracleRoom configuration.machine.verifierLimits
              proverFinalOracle configuration.machine.verifierFuel then
            fullRootVerifierCursor configuration hidden adversaryValue
              proverFinalOracle proverCoherent
          else
            .returned (.initialFailure .verifierRoom)

theorem exact_plain_rom_cursor_eq_root_machine_of_room
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (hidden : HiddenTape)
    (room : StageHasOracleRoom configuration.machine.adversaryLimits
      emptyOracle configuration.machine.adversaryFuel) :
    exactPlainRomCursor configuration hidden =
      .machine configuration.machine.adversaryLimits
        configuration.rootLimitBounds.adversary .adversary emptyOracle
        (schedulerStageProgram
          (SchedulerNativePlainRomResult TapeIdentity Statement Proof Payload
            Result)
          (totalizeOracleMachine configuration.machine.adversaryFuel
            (configuration.machine.blackBox.start hidden
              configuration.machine.observation)))
        configuration.machine.adversaryFuel
        empty_oracle_history_total_coherent
        (fullRootAdversaryReturnedContinuation configuration hidden) := by
  unfold exactPlainRomCursor schedulerNativePlainRomCursor
  rw [dif_pos room]
  congr 1
  funext adversaryStage proverFinalOracle proverCoherent
  cases adversaryStage with
  | completed adversaryPayload =>
      unfold fullRootAdversaryReturnedContinuation
      cases adversaryPayload with
      | error failure =>
          cases failure <;> rfl
      | ok adversaryValue =>
          simp only
          by_cases verifierRoom : StageHasOracleRoom
            configuration.machine.verifierLimits proverFinalOracle
              configuration.machine.verifierFuel
          · rw [dif_pos verifierRoom, if_pos verifierRoom]
            unfold fullRootVerifierCursor
            congr 1
          · rw [dif_neg verifierRoom, if_neg verifierRoom]

/-! ## Root-only/full-prefix deterministic agreement -/

theorem completed_root_stages_and_full_prefix_adversary_exact
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type u}
    {globalOracleCalls transitionFuel : Nat}
    {machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    {hidden : HiddenTape}
    {limitBounds : SchedulerNativeRootLimitBounds machine globalOracleCalls}
    {restorationConfiguration : ConcreteRestorationConfiguration}
    {answers : List Digest256}
    {runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload}
    (stages : CompletedRootOperationalStages transitionFuel machine hidden
      limitBounds restorationConfiguration answers runtime)
    (prefixes : FullResultRootProjectedPrefixes
      (Final := SchedulerNativePlainRomResult TapeIdentity Statement Proof
        Payload Result)
      machine hidden answers runtime) :
    stages.adversaryValue = prefixes.adversaryValue ∧
      stages.adversary.finalState = prefixes.adversary.finalState := by
  have rootRun :=
    projected_scheduler_stage_prefix_underlying_run_exact
      (Final := RootSchedulerResult TapeIdentity Statement Proof Payload)
      machine.adversaryLimits .adversary machine.adversaryFuel emptyOracle
      (totalizeOracleMachine machine.adversaryFuel
        (machine.blackBox.start hidden machine.observation))
      answers stages.adversary (.ok stages.adversaryValue)
      stages.adversaryResult empty_oracle_history_total_coherent
  have fullRun :=
    projected_scheduler_stage_prefix_underlying_run_exact
      (Final := SchedulerNativePlainRomResult TapeIdentity Statement Proof
        Payload Result)
      machine.adversaryLimits .adversary machine.adversaryFuel emptyOracle
      (totalizeOracleMachine machine.adversaryFuel
        (machine.blackBox.start hidden machine.observation))
      answers prefixes.adversary (.ok prefixes.adversaryValue)
      prefixes.adversaryResult empty_oracle_history_total_coherent
  have outputsExact := rootRun.symm.trans fullRun
  simp only [MachineRun.mk.injEq, MachineHalt.returned.injEq,
    Except.ok.injEq] at outputsExact
  exact ⟨outputsExact.1, outputsExact.2.1⟩

/-! ## Principal trace factorization -/

theorem completed_root_and_full_projection_factor_full_run
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat) (transitionRoom : 3 ≤ transitionFuel)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (rootClientRun : ConcreteRestorationClientRun Statement Proof Payload
      PUnit)
    (clientRun : ConcreteRestorationClientRun Statement Proof Payload Result)
    (rootCompleted :
      (runExactPlainRomRoot transitionFuel configuration sample).terminal =
        .returned (.completed runtime rootClientRun))
    (fullProjection : CompletedExactPlainRomRootAndStoreProjection
      transitionFuel configuration sample runtime clientRun) :
    runSchedulerNativeListRunFrom transitionFuel transitionFuel
        (exactPlainRomCursor configuration sample.1)
        (freshAnswerTapeToList sample.2) =
      let tail := fullProjectedConcreteClientTailRun transitionFuel
        configuration sample runtime fullProjection.rootPrefixes
      { terminal := mapSchedulerNativeTerminalResult
          (fun clientResult =>
            SchedulerNativePlainRomResult.completed runtime clientResult)
          tail.terminal
        trace := fullProjectedRootRecords fullProjection.rootPrefixes ++
          tail.trace } := by
  have positive : 0 < transitionFuel := by omega
  have rootListCompleted :
      runSchedulerNativeListTerminal transitionFuel
          (exactPlainRomRootCursor configuration sample.1)
          (freshAnswerTapeToList sample.2) =
        .returned (.completed runtime rootClientRun) := by
    rw [← run_scheduler_native_terminal_eq_list]
    exact rootCompleted
  let stages := completed_root_constructs_operational_stages transitionFuel
    positive configuration.machine sample.1 configuration.rootLimitBounds
      configuration.restorationConfiguration
      (freshAnswerTapeToList sample.2) runtime rootClientRun (by
        simpa [exactPlainRomRootCursor] using rootListCompleted)
  have adversaryExact :=
    completed_root_stages_and_full_prefix_adversary_exact
      (Result := Result) stages fullProjection.rootPrefixes
  have verifierRoom : StageHasOracleRoom
      configuration.machine.verifierLimits
      fullProjection.rootPrefixes.adversary.finalState
      configuration.machine.verifierFuel := by
    simpa only [← adversaryExact.2] using stages.verifierRoom
  let adversaryContinuationFuel :=
    machinePrefixContinuationTransitionFuel transitionFuel
      (transitionFuel - 1)
      fullProjection.rootPrefixes.adversary.freshQueries
  have adversaryContinuationPositive : 0 < adversaryContinuationFuel := by
    unfold adversaryContinuationFuel machinePrefixContinuationTransitionFuel
    split <;> omega
  have adversaryCallbackExact :
      fullRootAdversaryReturnedContinuation configuration sample.1
          fullProjection.rootPrefixes.adversary.result
          fullProjection.rootPrefixes.adversary.finalState
          fullProjection.rootPrefixes.adversary.finalCoherent =
        fullRootVerifierCursor configuration sample.1
          fullProjection.rootPrefixes.adversaryValue
          fullProjection.rootPrefixes.adversary.finalState
          fullProjection.rootPrefixes.adversary.finalCoherent := by
    rw [fullProjection.rootPrefixes.adversaryResult]
    simp only [fullRootAdversaryReturnedContinuation, if_pos verifierRoom]
  have verifierCallbackExact :
      fullRootVerifierReturnedContinuation configuration sample.1
          fullProjection.rootPrefixes.adversaryValue
          fullProjection.rootPrefixes.adversary.finalState
          fullProjection.rootPrefixes.verifier.result
          fullProjection.rootPrefixes.verifier.finalState
          fullProjection.rootPrefixes.verifier.finalCoherent =
        mappedConcreteClientContinuation configuration sample.1 runtime := by
    rw [fullProjection.rootPrefixes.verifierResult]
    simp only [fullRootVerifierReturnedContinuation]
    exact congrArg (mappedConcreteClientContinuation configuration sample.1)
      fullProjection.rootPrefixes.runtimeExact.symm
  rw [exact_plain_rom_cursor_eq_root_machine_of_room configuration sample.1
    stages.adversaryRoom]
  rw [run_scheduler_native_list_run_from_projected_prefix transitionFuel
    positive transitionFuel positive configuration.machine.adversaryLimits
    configuration.rootLimitBounds.adversary .adversary emptyOracle
    (schedulerStageProgram
      (SchedulerNativePlainRomResult TapeIdentity Statement Proof Payload
        Result)
      (totalizeOracleMachine configuration.machine.adversaryFuel
        (configuration.machine.blackBox.start sample.1
          configuration.machine.observation)))
    configuration.machine.adversaryFuel
    empty_oracle_history_total_coherent
    (fullRootAdversaryReturnedContinuation configuration sample.1)
    (freshAnswerTapeToList sample.2)
    fullProjection.rootPrefixes.adversary]
  rw [adversaryCallbackExact]
  unfold fullRootVerifierCursor
  rw [run_scheduler_native_list_run_from_projected_prefix transitionFuel
    positive adversaryContinuationFuel adversaryContinuationPositive
    configuration.machine.verifierLimits
    configuration.rootLimitBounds.verifier .verifier
    fullProjection.rootPrefixes.adversary.finalState
    (schedulerStageProgram
      (SchedulerNativePlainRomResult TapeIdentity Statement Proof Payload
        Result)
      (totalizeOracleMachine configuration.machine.verifierFuel
        (initialRawFutureFreeProgram configuration.machine.environment
          fullProjection.rootPrefixes.adversaryValue.rawMessages
          configuration.machine.driverFuel)))
    configuration.machine.verifierFuel
    fullProjection.rootPrefixes.adversary.finalCoherent
    (fullRootVerifierReturnedContinuation configuration sample.1
      fullProjection.rootPrefixes.adversaryValue
      fullProjection.rootPrefixes.adversary.finalState)
    fullProjection.rootPrefixes.adversary.remaining
    fullProjection.rootPrefixes.verifier]
  rw [verifierCallbackExact]
  unfold mappedConcreteClientContinuation
  rw [run_scheduler_native_list_run_from_map]
  simp only [mapSchedulerNativeRunResult,
    fullProjectedConcreteClientTailRun,
    fullProjectedRootClientTransitionFuel, fullProjectedRootRecords,
    adversaryContinuationFuel, List.append_assoc]

theorem completed_full_projection_computed_client_terminal_exact
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat) (transitionRoom : 3 ≤ transitionFuel)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (rootClientRun : ConcreteRestorationClientRun Statement Proof Payload
      PUnit)
    (clientRun : ConcreteRestorationClientRun Statement Proof Payload Result)
    (rootCompleted :
      (runExactPlainRomRoot transitionFuel configuration sample).terminal =
        .returned (.completed runtime rootClientRun))
    (fullCompleted :
      (runExactPlainRom transitionFuel configuration sample).terminal =
        .returned (.completed runtime clientRun))
    (fullProjection : CompletedExactPlainRomRootAndStoreProjection
      transitionFuel configuration sample runtime clientRun) :
    (fullProjectedConcreteClientTailRun transitionFuel configuration sample
      runtime fullProjection.rootPrefixes).terminal = .returned clientRun := by
  have factor := completed_root_and_full_projection_factor_full_run
    transitionFuel transitionRoom configuration sample runtime rootClientRun
      clientRun rootCompleted fullProjection
  have fullListExact := run_scheduler_native_eq_list_run transitionFuel
    (exactCompilerTargetCaps parameters).length
    (exactPlainRomCursor configuration sample.1) sample.2
  have terminalExact :
      (runSchedulerNativeListRunFrom transitionFuel transitionFuel
        (exactPlainRomCursor configuration sample.1)
        (freshAnswerTapeToList sample.2)).terminal =
          .returned (.completed runtime clientRun) := by
    change (runSchedulerNativeListRun transitionFuel
      (exactPlainRomCursor configuration sample.1)
      (freshAnswerTapeToList sample.2)).terminal = _
    rw [← fullListExact]
    exact fullCompleted
  rw [factor] at terminalExact
  let tail := fullProjectedConcreteClientTailRun transitionFuel configuration
    sample runtime fullProjection.rootPrefixes
  change mapSchedulerNativeTerminalResult
      (fun clientResult =>
        SchedulerNativePlainRomResult.completed runtime clientResult)
      tail.terminal = .returned (.completed runtime clientRun) at terminalExact
  cases tailTerminal : tail.terminal with
  | failed reason =>
      simp [tailTerminal, mapSchedulerNativeTerminalResult] at terminalExact
  | returned result =>
      simp only [tailTerminal, mapSchedulerNativeTerminalResult,
        SchedulerNativeTerminal.returned.injEq,
        SchedulerNativePlainRomResult.completed.injEq] at terminalExact
      simpa [terminalExact.2] using tailTerminal

theorem completed_full_projection_computed_client_list_terminal_exact
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat) (transitionRoom : 3 ≤ transitionFuel)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (rootClientRun : ConcreteRestorationClientRun Statement Proof Payload
      PUnit)
    (clientRun : ConcreteRestorationClientRun Statement Proof Payload Result)
    (rootCompleted :
      (runExactPlainRomRoot transitionFuel configuration sample).terminal =
        .returned (.completed runtime rootClientRun))
    (fullCompleted :
      (runExactPlainRom transitionFuel configuration sample).terminal =
        .returned (.completed runtime clientRun))
    (fullProjection : CompletedExactPlainRomRootAndStoreProjection
      transitionFuel configuration sample runtime clientRun) :
    runSchedulerNativeListTerminalFrom transitionFuel
        (fullProjectedRootClientTransitionFuel transitionFuel
          fullProjection.rootPrefixes)
        (startConcreteRestorationClientFromRoot
          (globalOracleCalls := globalFull256OracleCallCap parameters)
          (configuration.machine.blackBox.start sample.1
            configuration.machine.observation)
          configuration.machine.environment runtime.node
          configuration.restorationConfiguration configuration.restorationFuel
          configuration.client)
        fullProjection.rootPrefixes.verifier.remaining = .returned clientRun := by
  rw [← run_scheduler_native_list_run_terminal]
  exact completed_full_projection_computed_client_terminal_exact
    transitionFuel transitionRoom configuration sample runtime rootClientRun
      clientRun rootCompleted fullCompleted fullProjection

#print axioms run_scheduler_native_list_run_from_map
#print axioms completed_root_stages_and_full_prefix_adversary_exact
#print axioms completed_root_and_full_projection_factor_full_run
#print axioms completed_full_projection_computed_client_terminal_exact
#print axioms completed_full_projection_computed_client_list_terminal_exact

end

end AspisK1.V7Tag73FullCursorClientLineageLift
