import AspisFormal.K1.V7Tag73RootForcedFullProjection
import AspisFormal.K1.V7Tag73ExactCompilerClientCaps
import AspisFormal.K1.V7Tag73ExactPlainRomTraceResourceCaps
import AspisFormal.K1.V7Tag73ActualGrindingQueryAccounting

/-!
# Exact operational resource certificate for a completed Tag-73 run

This module packages resource facts about one *actual* completed
result-carrying scheduler execution.  Every counted quantity is read from one
of three literal operational objects:

* the two projected root machine prefixes;
* the returned concrete-client accumulator and its append-only charge log; or
* the emitted scheduler trace.

In particular, no `ResourceUse` is supplied by a caller and no
`WithinBudget` conclusion is assumed.  The root prover history is the actual
Q1, the root verifier history is the actual initial verifier segment, and the
client query/restart/programming totals are the literal sums of
`ConcreteRestorationCharge`s.  Runtime means executed `OracleMachine` query
transitions, hence it is the two root step counts plus the client oracle-query
charge total.

The legacy `ResourceUse` record also asks for three stage-specific grinding
caps and a q16 candidate-branch count.  `ExactPlainRomOperationalBounds`
contains only the aggregate adversary `Q` bound.  Moreover, a failed
totalized verifier attempt retains its oracle-query charge but not its
intermediate `FutureFreeVerifierState`, so its q16 transition count cannot be
reconstructed from the terminal accumulator.  We therefore expose the three
actual root grinding counts and their proved `<= Q` bounds, but deliberately
do not manufacture a full `ResourceUse` or claim `WithinBudget`.  Closing the
35/31/34 and failed-attempt q16 fields requires a separate operational
stage-budget/instrumentation theorem.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ExactOperationalResourceCertificate

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactCompilerOperationalCaps
open AspisK1.V7Tag73ExactCompilerClientCaps
open AspisK1.V7Tag73ExactPlainRomTraceResourceCaps
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73ProjectedMachinePrefix
open AspisK1.V7Tag73SequentialOracleRuns
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73CompletedFullRunProjection
open AspisK1.V7Tag73RootForcedFullProjection
open AspisK1.V7Tag73ActualGrindingQueryAccounting

noncomputable section

/-! ## Literal completed-run quantities -/

/-- Actual initial adversary/Q1 query count. -/
def completedRootQ1QueryCount
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters}
    {sample : ExactCompilerSample HiddenTape parameters}
    {rootRuntime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement
      Proof Payload}
    (_completed : RootForcedCompletedFullProjection transitionFuel
      configuration sample rootRuntime) : Nat :=
  rootRuntime.node.proverHistory.length

/-- Actual initial verifier query count on the shared root oracle. -/
def completedRootVerifierQueryCount
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters}
    {sample : ExactCompilerSample HiddenTape parameters}
    {rootRuntime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement
      Proof Payload}
    (_completed : RootForcedCompletedFullProjection transitionFuel
      configuration sample rootRuntime) : Nat :=
  rootRuntime.node.verifierHistory.length

/-- Actual restoration-side oracle-query transitions, including synchronous
prefix replay, the complete from-start prover run, and the verifier suffix of
every attempted restoration branch that reached those stages. -/
def completedClientOracleQueryCount
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters}
    {sample : ExactCompilerSample HiddenTape parameters}
    {rootRuntime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement
      Proof Payload}
    (completed : RootForcedCompletedFullProjection transitionFuel
      configuration sample rootRuntime) : Nat :=
  completed.clientRun.accumulator.oracleQueryTotal

/-- Actual query-transition runtime.  Fork sampling and oracle programming
are deliberately not query transitions; their own counters remain separate. -/
def completedOperationalRuntimeSteps
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters}
    {sample : ExactCompilerSample HiddenTape parameters}
    {rootRuntime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement
      Proof Payload}
    (completed : RootForcedCompletedFullProjection transitionFuel
      configuration sample rootRuntime) : Nat :=
  completed.projection.rootPrefixes.adversary.steps +
    completed.projection.rootPrefixes.verifier.steps +
      completed.clientRun.accumulator.oracleQueryTotal

/-- The actual machine-fresh coordinates emitted by the completed full
scheduler, before terminal padding is discarded by the counter. -/
def completedMachineFreshCoordinateCount
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters) : Nat :=
  machineFreshCoordinateCount
    (runExactPlainRom transitionFuel configuration sample).trace

/-- The actual two-coordinate fork records emitted by the completed full
scheduler. -/
def completedForkCoordinateCount
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters) : Nat :=
  forkCoordinateCount (runExactPlainRom transitionFuel configuration sample).trace

/-- The five client totals are not estimates: they are definitionally the
five projections of the append-only charge list returned by this run. -/
theorem completed_client_charge_totals_exact
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters}
    {sample : ExactCompilerSample HiddenTape parameters}
    {rootRuntime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement
      Proof Payload}
    (completed : RootForcedCompletedFullProjection transitionFuel
      configuration sample rootRuntime) :
    completed.clientRun.accumulator.oracleQueryTotal =
        (completed.clientRun.accumulator.charges.map
          ConcreteRestorationCharge.oracleQueries).sum ∧
      completed.clientRun.accumulator.uniformForkCoordinateTotal =
        (completed.clientRun.accumulator.charges.map
          ConcreteRestorationCharge.uniformForkCoordinates).sum ∧
      completed.clientRun.accumulator.programmedPointTotal =
        (completed.clientRun.accumulator.charges.map
          ConcreteRestorationCharge.successfulProgrammingPoints).sum ∧
      completed.clientRun.accumulator.restartTotal =
        (completed.clientRun.accumulator.charges.map
          ConcreteRestorationCharge.restarts).sum ∧
      completed.clientRun.accumulator.verifierTransitionTotal =
        (completed.clientRun.accumulator.charges.map
          ConcreteRestorationCharge.protocolTransitions).sum := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## Root query and step bounds -/

/-- A normally returned projected segment's literal step count is bounded by
the exact machine fuel. -/
theorem projected_machine_prefix_steps_le_fuel
    {MachineResult : Type}
    (limits : OracleLimits) (actor : QueryActor)
    (fuel : Nat) (state : OracleState) (program : OracleMachine MachineResult)
    (available : List Digest256)
    (returned : ProjectedMachinePrefixReturned limits actor fuel state program
      available) :
    returned.steps ≤ fuel := by
  have entryCoherent : HistoryTotalCoherent state :=
    projected_returned_trace_entry_coherent limits actor fuel state program
      returned.freshQueries returned.result returned.finalState returned.steps
      returned.trace
  have runExact := projected_machine_prefix_returned_run_exact limits actor fuel
    state program available returned entryCoherent
  have stepsLe := run_machine_steps_le_fuel
    (controllerFromProjectedFreshAnswers state.history
      (returned.freshQueries.map Prod.snd)) limits actor fuel state program
  rw [runExact] at stepsLe
  exact stepsLe

/-- The two histories named by the completed operational root have their
literal stage fuel bounds. -/
theorem completed_root_query_counts_le_stage_fuels
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters)
    (rootRuntime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement
      Proof Payload)
    (completed : RootForcedCompletedFullProjection transitionFuel
      configuration sample rootRuntime) :
    completedRootQ1QueryCount completed ≤
        configuration.machine.adversaryFuel ∧
      completedRootVerifierQueryCount completed ≤
      configuration.machine.verifierFuel := by
  change rootRuntime.node.proverHistory.length ≤
      configuration.machine.adversaryFuel ∧
    rootRuntime.node.verifierHistory.length ≤
      configuration.machine.verifierFuel
  let prefixes := completed.projection.rootPrefixes
  have adversaryBound := projected_returned_history_length_le_fuel
    configuration.machine.adversaryLimits .adversary
      configuration.machine.adversaryFuel emptyOracle
      (schedulerStageProgram
        (SchedulerNativePlainRomResult TapeIdentity Statement Proof Payload
          Result)
        (totalizeOracleMachine configuration.machine.adversaryFuel
          (configuration.machine.blackBox.start sample.1
            configuration.machine.observation)))
      (freshAnswerTapeToList sample.2) prefixes.adversary
  have verifierBound := projected_returned_history_length_le_fuel
    configuration.machine.verifierLimits .verifier
      configuration.machine.verifierFuel prefixes.adversary.finalState
      (schedulerStageProgram
        (SchedulerNativePlainRomResult TapeIdentity Statement Proof Payload
          Result)
        (totalizeOracleMachine configuration.machine.verifierFuel
          (initialRawFutureFreeProgram configuration.machine.environment
            prefixes.adversaryValue.rawMessages
            configuration.machine.driverFuel)))
      prefixes.adversary.remaining prefixes.verifier
  have runtimeExact := prefixes.runtimeExact
  rw [runtimeExact]
  constructor
  · simpa [completedRootQ1QueryCount,
      SchedulerNativePlainRomRootRuntime.node,
      ConcreteRestorationNode.proverHistory, operationalRootRuntime] using
        adversaryBound
  · simpa [completedRootVerifierQueryCount,
      SchedulerNativePlainRomRootRuntime.node,
      ConcreteRestorationNode.verifierHistory, operationalRootRuntime] using
        verifierBound

/-- The root query counts satisfy the exact `Q` and deployed-1511 caps from
`ExactPlainRomOperationalBounds`. -/
theorem completed_root_query_counts_le_parameters
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters)
    (rootRuntime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement
      Proof Payload)
    (completed : RootForcedCompletedFullProjection transitionFuel
      configuration sample rootRuntime) :
    completedRootQ1QueryCount completed ≤ parameters.q1ShaCallCap ∧
      completedRootVerifierQueryCount completed ≤
        deployedFull256VerifierCallCap := by
  rcases completed_root_query_counts_le_stage_fuels configuration sample
    rootRuntime completed with ⟨adversary, verifier⟩
  exact ⟨adversary.trans configuration.bounds.rootAdversaryFuel,
    verifier.trans configuration.bounds.rootVerifierFuel⟩

theorem completed_root_steps_le_parameters
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters)
    (rootRuntime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement
      Proof Payload)
    (completed : RootForcedCompletedFullProjection transitionFuel
      configuration sample rootRuntime) :
    completed.projection.rootPrefixes.adversary.steps ≤
        parameters.q1ShaCallCap ∧
      completed.projection.rootPrefixes.verifier.steps ≤
        deployedFull256VerifierCallCap := by
  let prefixes := completed.projection.rootPrefixes
  have adversary := projected_machine_prefix_steps_le_fuel
    configuration.machine.adversaryLimits .adversary
      configuration.machine.adversaryFuel emptyOracle
      (schedulerStageProgram
        (SchedulerNativePlainRomResult TapeIdentity Statement Proof Payload
          Result)
        (totalizeOracleMachine configuration.machine.adversaryFuel
          (configuration.machine.blackBox.start sample.1
            configuration.machine.observation)))
      (freshAnswerTapeToList sample.2) prefixes.adversary
  have verifier := projected_machine_prefix_steps_le_fuel
    configuration.machine.verifierLimits .verifier
      configuration.machine.verifierFuel prefixes.adversary.finalState
      (schedulerStageProgram
        (SchedulerNativePlainRomResult TapeIdentity Statement Proof Payload
          Result)
        (totalizeOracleMachine configuration.machine.verifierFuel
          (initialRawFutureFreeProgram configuration.machine.environment
            prefixes.adversaryValue.rawMessages
            configuration.machine.driverFuel)))
      prefixes.adversary.remaining prefixes.verifier
  exact ⟨adversary.trans configuration.bounds.rootAdversaryFuel,
    verifier.trans configuration.bounds.rootVerifierFuel⟩

/-! ## Actual completed-client charge bounds -/

/-- Direct specialization of the concrete-client accumulator induction to the
literal suffix and terminal equation retained by the full projection. -/
theorem completed_full_client_accumulator_caps
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters)
    (rootRuntime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement
      Proof Payload)
    (completed : RootForcedCompletedFullProjection transitionFuel
      configuration sample rootRuntime)
    (transitionPositive : 0 < transitionFuel) :
    completed.clientRun.accumulator.oracleQueryTotal ≤
        configuration.restorationFuel *
          (2 * parameters.q1ShaCallCap + 1511) ∧
      completed.clientRun.accumulator.uniformForkCoordinateTotal ≤
        2 * configuration.restorationFuel ∧
      completed.clientRun.accumulator.programmedPointTotal ≤
        2 * configuration.restorationFuel ∧
      completed.clientRun.accumulator.restartTotal ≤
        2 * configuration.restorationFuel ∧
      completed.clientRun.accumulator.verifierTransitionTotal ≤
        configuration.restorationFuel *
          configuration.restorationConfiguration.driverFuel ∧
      AllStoredProverHistoriesWithin parameters.q1ShaCallCap
        completed.clientRun.accumulator := by
  have rootBound :=
    (completed_root_query_counts_le_parameters configuration sample rootRuntime
      completed).1
  exact completed_concrete_client_has_exact_accumulator_caps
    parameters.q1ShaCallCap
    (configuration.machine.blackBox.start sample.1
      configuration.machine.observation)
    configuration.machine.environment rootRuntime.node
    configuration.restorationConfiguration configuration.restorationFuel
    transitionFuel completed.projection.clientCurrentTransitionFuel
    transitionPositive configuration.client rootBound
    configuration.bounds.replayAdversaryFuel
    configuration.bounds.replayVerifierFuel
    completed.projection.rootPrefixes.verifier.remaining completed.clientRun
    completed.projection.clientTerminalExact

/-- Monotone closed caps in the public request parameter `R`. -/
theorem completed_full_client_accumulator_caps_at_R
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters)
    (rootRuntime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement
      Proof Payload)
    (completed : RootForcedCompletedFullProjection transitionFuel
      configuration sample rootRuntime)
    (transitionPositive : 0 < transitionFuel) :
    completed.clientRun.accumulator.oracleQueryTotal ≤
        parameters.forkRequestCap *
          (2 * parameters.q1ShaCallCap + 1511) ∧
      completed.clientRun.accumulator.uniformForkCoordinateTotal ≤
        2 * parameters.forkRequestCap ∧
      completed.clientRun.accumulator.programmedPointTotal ≤
        2 * parameters.forkRequestCap ∧
      completed.clientRun.accumulator.restartTotal ≤
        2 * parameters.forkRequestCap ∧
      completed.clientRun.accumulator.verifierTransitionTotal ≤
        parameters.forkRequestCap *
          configuration.restorationConfiguration.driverFuel ∧
      AllStoredProverHistoriesWithin parameters.q1ShaCallCap
        completed.clientRun.accumulator := by
  rcases completed_full_client_accumulator_caps transitionFuel configuration
    sample rootRuntime completed transitionPositive with
    ⟨queries, forks, programmed, restarts, transitions, stored⟩
  have requestBound := configuration.bounds.restorationRequests
  exact ⟨queries.trans (Nat.mul_le_mul_right _ requestBound),
    forks.trans (Nat.mul_le_mul_left 2 requestBound),
    programmed.trans (Nat.mul_le_mul_left 2 requestBound),
    restarts.trans (Nat.mul_le_mul_left 2 requestBound),
    transitions.trans (Nat.mul_le_mul_right _ requestBound), stored⟩

/-! ## Runtime reserves and timeout -/

/-- Lower bounds connecting the abstract runtime budget fields to the query
fuel caps that govern the literal programs.  These are componentwise reserve
facts, not a `WithinBudget` conclusion. -/
structure ExactOperationalRuntimeReserves
    (parameters : ExactCompilerResourceParameters) : Prop where
  firstRun : parameters.q1ShaCallCap ≤ parameters.firstRunRuntimeCap
  initialVerifier : deployedFull256VerifierCallCap ≤
    parameters.initialVerifierRuntimeCap
  sameTapeStart : parameters.q1ShaCallCap ≤
    parameters.sameTapeStartRuntimeCap
  replayVerifier : deployedFull256VerifierCallCap ≤
    parameters.replayVerifierRuntimeCap

theorem completed_operational_runtime_steps_le_cap
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters)
    (rootRuntime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement
      Proof Payload)
    (completed : RootForcedCompletedFullProjection transitionFuel
      configuration sample rootRuntime)
    (transitionPositive : 0 < transitionFuel)
    (reserves : ExactOperationalRuntimeReserves parameters) :
    completedOperationalRuntimeSteps completed ≤
      totalCompilerRuntimeCap parameters := by
  rcases completed_root_steps_le_parameters configuration sample rootRuntime
    completed with ⟨adversary, verifier⟩
  have client := (completed_full_client_accumulator_caps_at_R transitionFuel
    configuration sample rootRuntime completed transitionPositive).1
  have perRestoration :
      2 * parameters.q1ShaCallCap + 1511 ≤
        2 * parameters.sameTapeStartRuntimeCap +
          parameters.replayVerifierRuntimeCap := by
    simpa [deployedFull256VerifierCallCap] using
      Nat.add_le_add (Nat.mul_le_mul_left 2 reserves.sameTapeStart)
        reserves.replayVerifier
  have clientRuntime : completed.clientRun.accumulator.oracleQueryTotal ≤
      parameters.forkRequestCap *
        (2 * parameters.sameTapeStartRuntimeCap +
          parameters.replayVerifierRuntimeCap) :=
    client.trans (Nat.mul_le_mul_left _ perRestoration)
  have adversaryRuntime := adversary.trans reserves.firstRun
  have verifierRuntime := verifier.trans reserves.initialVerifier
  unfold completedOperationalRuntimeSteps totalCompilerRuntimeCap
  omega

/-- The sample-local timeout predicate is false once the literal runtime cap
lies strictly below the public cutoff. -/
theorem completed_operational_timeout_absent
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters)
    (rootRuntime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement
      Proof Payload)
    (completed : RootForcedCompletedFullProjection transitionFuel
      configuration sample rootRuntime)
    (transitionPositive : 0 < transitionFuel)
    (reserves : ExactOperationalRuntimeReserves parameters)
    (cutoffBeyondCap :
      totalCompilerRuntimeCap parameters < parameters.timeoutCutoff) :
    ¬ parameters.timeoutCutoff ≤
      completedOperationalRuntimeSteps completed := by
  intro timeout
  have runtimeBound := completed_operational_runtime_steps_le_cap
    transitionFuel configuration sample rootRuntime completed
      transitionPositive reserves
  omega

/-! ## One proof-relevant certificate -/

/-- All resource facts currently derivable for the actual completed run.
The fields mention literal runtime objects rather than a caller-selected
resource-use map. -/
structure ExactOperationalResourceCertificate
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters)
    (rootRuntime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement
      Proof Payload)
    (completed : RootForcedCompletedFullProjection transitionFuel
      configuration sample rootRuntime) : Prop where
  q1Queries : completedRootQ1QueryCount completed ≤ parameters.q1ShaCallCap
  rootVerifierQueries : completedRootVerifierQueryCount completed ≤
    deployedFull256VerifierCallCap
  restorationFuel : configuration.restorationFuel ≤ parameters.forkRequestCap
  clientOracleQueries : completedClientOracleQueryCount completed ≤
    parameters.forkRequestCap *
      (2 * parameters.q1ShaCallCap + deployedFull256VerifierCallCap)
  globalOracleQueries : completedRootQ1QueryCount completed +
      completedRootVerifierQueryCount completed +
        completedClientOracleQueryCount completed ≤
    globalFull256OracleCallCap parameters
  machineFreshCoordinates :
    completedMachineFreshCoordinateCount transitionFuel configuration sample ≤
      full256MachineFreshCap parameters
  scheduledForkCoordinates :
    completedForkCoordinateCount transitionFuel configuration sample ≤
      sameTapeStartCap parameters
  chargedForkCoordinates :
    completed.clientRun.accumulator.uniformForkCoordinateTotal ≤
      sameTapeStartCap parameters
  programmedPoints : completed.clientRun.accumulator.programmedPointTotal ≤
    2 * parameters.forkRequestCap
  restarts : completed.clientRun.accumulator.restartTotal ≤
    sameTapeStartCap parameters
  verifierTransitions :
    completed.clientRun.accumulator.verifierTransitionTotal ≤
      parameters.forkRequestCap *
        configuration.restorationConfiguration.driverFuel
  runtimeSteps : completedOperationalRuntimeSteps completed ≤
    totalCompilerRuntimeCap parameters
  timeoutAbsent : ¬ parameters.timeoutCutoff ≤
    completedOperationalRuntimeSteps completed
  batchGrindingQueries :
    (actualRootStageGrindingQueryUse rootRuntime).batch ≤
      parameters.q1ShaCallCap
  foldGrindingQueries :
    (actualRootStageGrindingQueryUse rootRuntime).fold ≤
      parameters.q1ShaCallCap
  finalGrindingQueries :
    (actualRootStageGrindingQueryUse rootRuntime).final ≤
      parameters.q1ShaCallCap

/-- Construct the certificate from the literal completed projection, the four
componentwise runtime reserves, and a cutoff strictly beyond the proved hard
runtime cap. -/
theorem completed_full_run_has_exact_operational_resource_certificate
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters)
    (rootRuntime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement
      Proof Payload)
    (completed : RootForcedCompletedFullProjection transitionFuel
      configuration sample rootRuntime)
    (transitionRoom : 3 ≤ transitionFuel)
    (reserves : ExactOperationalRuntimeReserves parameters)
    (cutoffBeyondCap :
      totalCompilerRuntimeCap parameters < parameters.timeoutCutoff) :
    ExactOperationalResourceCertificate transitionFuel configuration sample
      rootRuntime completed := by
  have rootCaps := completed_root_query_counts_le_parameters configuration
    sample rootRuntime completed
  have clientCaps := completed_full_client_accumulator_caps_at_R transitionFuel
    configuration sample rootRuntime completed (by omega)
  have traceCaps := run_exact_plain_rom_trace_has_M_and_2R_caps transitionFuel
    configuration sample transitionRoom
  have rootVerifierCap :
      completedRootVerifierQueryCount completed ≤ 1511 := by
    simpa [deployedFull256VerifierCallCap] using rootCaps.2
  have clientQueryCap : completedClientOracleQueryCount completed ≤
      parameters.forkRequestCap *
        (2 * parameters.q1ShaCallCap + 1511) := by
    simpa [completedClientOracleQueryCount] using clientCaps.1
  have globalQueries : completedRootQ1QueryCount completed +
        completedRootVerifierQueryCount completed +
          completedClientOracleQueryCount completed ≤
      globalFull256OracleCallCap parameters := by
    unfold globalFull256OracleCallCap deployedFull256VerifierCallCap
    omega
  have workCaps := actual_root_stage_grinding_counts_le_Q rootRuntime
    parameters.q1ShaCallCap rootCaps.1
  refine
    { q1Queries := rootCaps.1
      rootVerifierQueries := rootCaps.2
      restorationFuel := configuration.bounds.restorationRequests
      clientOracleQueries := by
        simpa [completedClientOracleQueryCount,
          deployedFull256VerifierCallCap] using clientCaps.1
      globalOracleQueries := globalQueries
      machineFreshCoordinates := ?_
      scheduledForkCoordinates := ?_
      chargedForkCoordinates := by
        simpa [sameTapeStartCap] using clientCaps.2.1
      programmedPoints := clientCaps.2.2.1
      restarts := by simpa [sameTapeStartCap] using clientCaps.2.2.2.1
      verifierTransitions := clientCaps.2.2.2.2.1
      runtimeSteps := completed_operational_runtime_steps_le_cap
        transitionFuel configuration sample rootRuntime completed (by omega)
          reserves
      timeoutAbsent := completed_operational_timeout_absent transitionFuel
        configuration sample rootRuntime completed (by omega) reserves
          cutoffBeyondCap
      batchGrindingQueries := workCaps.1
      foldGrindingQueries := workCaps.2.1
      finalGrindingQueries := workCaps.2.2 }
  · exact traceCaps.1
  · exact traceCaps.2

/-! ## The exact remaining legacy-budget boundary -/

/-- The stage-specific part of the legacy budget, stated only in terms of the
three actual root-history classifiers.  It is intentionally separate from the
principal certificate: the aggregate `Q` premise does not imply 35/31/34 (or
any other smaller stage caps). -/
structure ExactOperationalStageWorkCertificate
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters}
    {sample : ExactCompilerSample HiddenTape parameters}
    {rootRuntime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement
      Proof Payload}
    (_completed : RootForcedCompletedFullProjection transitionFuel
      configuration sample rootRuntime) : Prop where
  batchWork : (actualRootStageGrindingQueryUse rootRuntime).batch ≤
    parameters.batchWorkQueryCap
  foldWork : (actualRootStageGrindingQueryUse rootRuntime).fold ≤
    parameters.foldWorkQueryCap
  finalWork : (actualRootStageGrindingQueryUse rootRuntime).final ≤
    parameters.finalWorkQueryCap

/-!
There is deliberately no analogous q16 structure here.  The terminal
accumulator retains `verifierTransitions` only for normally returned verifier
suffixes.  On `.verifierSuffixAbort` and `.verifierSuffixTimeout`, it retains
the exact oracle-query charge but discards the intermediate future-free state.
Consequently an "actual q16 count" cannot be defined from this completed-run
type without changing the dispatcher to append a transient verifier-action
ledger before all three terminal branches.  The smallest missing operational
extension is precisely such an append-only per-attempt q16 ledger together
with an induction that its total is at most `64 * (restorationFuel + 1)`.
-/

#print axioms projected_machine_prefix_steps_le_fuel
#print axioms completed_client_charge_totals_exact
#print axioms completed_root_query_counts_le_stage_fuels
#print axioms completed_root_query_counts_le_parameters
#print axioms completed_root_steps_le_parameters
#print axioms completed_full_client_accumulator_caps
#print axioms completed_full_client_accumulator_caps_at_R
#print axioms completed_operational_runtime_steps_le_cap
#print axioms completed_operational_timeout_absent
#print axioms completed_full_run_has_exact_operational_resource_certificate

end

end AspisK1.V7Tag73ExactOperationalResourceCertificate
