import AspisFormal.K1.V7Tag73CompletedRootProjection
import AspisFormal.K1.V7Tag73CanonicalFutureFreeFuel
import AspisFormal.K1.V7Tag73CoupledReplayAlignment

/-!
# Operational source-acceptance model for the exact Tag-73 experiment

The compiler theorem must not obtain Fiat--Shamir acceptance from an arbitrary
Boolean or an existential `AcceptanceFacts` record: the proposition-valued
fields of such a record can be chosen by a caller.  This leaf instead fixes a
plain executable projection from the actual checked prover return to the
deployed fixed tape.  Membership in the event below then requires all of the
following computations on the root runtime that the scheduler really
returned:

* the source projection returns a tape;
* that tape contains literally the raw prover messages that returned;
* its future-free environment is literally the machine environment; and
* strict checked deterministic replay succeeds against the actual final root
  oracle table.

The projection has no proof or compiler-conclusion field.  Relating one
particular projection to the pinned Rust/SBF verifier is the separately named
source-correspondence boundary; it is not a Fiat--Shamir trace cover.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ExactSourceAcceptanceModel

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73FutureFreeCheckedRefinementBisimulation
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73CoupledReplayAlignment
open AspisK1.V7Tag73UniformRawVerifierExecution
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73TotalizedMachineReflection
open AspisK1.V7Tag73CompletedRootProjection
open AspisK1.V7Tag73CheckedRefinementFullFutureFreePath
open AspisK1.V7Tag73CanonicalFutureFreeFuel
open AspisK1.V7Tag73RawVerifierExecution
open AspisK1.V7Tag73CheckedPathActualRunAlignment

noncomputable section

/-! ## A proof-free deployed-source projection -/

/-- A fixed executable projection used by the source verifier model.  It is a
function, not a structure carrying a theorem that acceptance implies the
desired compiler conclusion. -/
abbrev AcceptedTapeProjection
    (Statement Proof Payload : Type) :=
  CheckedRawTag73AdversaryReturnedValue Statement Proof Payload →
    Option DeployedFixedTape

/-- Exact strict-refinement predicate on one root runtime.  The table is
derived from the actual root oracle at verifier halt; it is not supplied by
the projection. -/
def RootHasStrictSourceRefinement
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (projection : AcceptedTapeProjection Statement Proof Payload)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload) : Prop :=
  ∃ tape raw,
    projection runtime.adversaryValue = some tape ∧
      fixedTapeRawMessages tape = runtime.adversaryValue.rawMessages ∧
      fixedTapeFutureFreeEnvironment tape = machine.environment ∧
      checkedRefine (fixedTableOfOracleState runtime.verifierFinalOracle)
        exactDeterministicDecoders tape = some raw

/-- The fixed-instance source event is computed from the standalone initial
run, so later extractor failure cannot retroactively change whether the public
proof was accepted. -/
def exactSourceRefinementEvent
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (projection : AcceptedTapeProjection Statement Proof Payload) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | ∃ runtime clientRun,
    (runExactPlainRomRoot transitionFuel configuration sample).terminal =
      .returned (.completed runtime clientRun) ∧
    RootHasStrictSourceRefinement configuration.machine projection runtime}

/-! ## Unconditional operational consequences -/

/-! The following record exposes the ordinary, ROM-free two-phase execution
recovered from the literal scheduler root together with the exact final-oracle
boundary.  The boundary is needed below because source refinement is checked
against the scheduler's final first-hit table.  It is an output of the two
projected machine equations, not a field supplied by the experiment. -/

structure ExactProjectedRootExecution
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload) where
  execution : RawVerifierExecution
    (projectedRootSource machine hidden runtime)
  adversaryValueExact : execution.adversaryValue = runtime.adversaryValue
  environmentExact : execution.environment = machine.environment
  driverFuelExact : execution.driverFuel = machine.driverFuel
  finalStateExact : execution.finalState = runtime.verifierFinalState
  finalOracleExact : execution.verifierRun.oracle = runtime.verifierFinalOracle

/-- The exact two scheduler-root equations construct an ordinary raw
prover/verifier execution whose prover value, verifier state and final oracle
are the literal runtime fields. -/
theorem root_projected_runs_construct_exact_execution
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (runs : RootProjectedTotalizedRuns machine hidden runtime) :
    Nonempty (ExactProjectedRootExecution machine hidden runtime) := by
  rcases runs with
    ⟨adversarySteps, verifierSteps, adversaryRun, verifierRun⟩
  have reflectedAdversary := run_machine_totalized_ok_reflects
    (rootAdversaryProjectedController runtime) machine.adversaryLimits
    .adversary machine.adversaryFuel emptyOracle
    (machine.blackBox.start hidden machine.observation)
    runtime.adversaryValue runtime.proverFinalOracle adversarySteps adversaryRun
  have reflectedVerifier := run_machine_totalized_ok_reflects
    (rootVerifierProjectedController runtime) machine.verifierLimits .verifier
    machine.verifierFuel runtime.proverFinalOracle
    (initialRawFutureFreeProgram machine.environment
      runtime.adversaryValue.rawMessages machine.driverFuel)
    runtime.verifierFinalState runtime.verifierFinalOracle verifierSteps
    verifierRun
  let execution : RawVerifierExecution
      (projectedRootSource machine hidden runtime) :=
    { adversaryValue := runtime.adversaryValue
      adversaryReturned := by
        change (runMachine (rootAdversaryProjectedController runtime)
          machine.adversaryLimits .adversary machine.adversaryFuel emptyOracle
          (machine.blackBox.start hidden machine.observation)).halt =
            .returned runtime.adversaryValue
        rw [reflectedAdversary]
      environment := machine.environment
      verifierController := rootVerifierProjectedController runtime
      verifierLimits := machine.verifierLimits
      driverFuel := machine.driverFuel
      verifierFuel := machine.verifierFuel
      finalState := runtime.verifierFinalState
      verifierReturned := by
        change (runMachine (rootVerifierProjectedController runtime)
          machine.verifierLimits .verifier machine.verifierFuel
          (runMachine (rootAdversaryProjectedController runtime)
            machine.adversaryLimits .adversary machine.adversaryFuel emptyOracle
            (machine.blackBox.start hidden machine.observation)).oracle
          (initialRawFutureFreeProgram machine.environment
            runtime.adversaryValue.rawMessages machine.driverFuel)).halt =
              .returned runtime.verifierFinalState
        rw [reflectedAdversary, reflectedVerifier] }
  refine ⟨⟨execution, rfl, rfl, rfl, rfl, ?_⟩⟩
  change (runMachine (rootVerifierProjectedController runtime)
    machine.verifierLimits .verifier machine.verifierFuel
    (runMachine (rootAdversaryProjectedController runtime)
      machine.adversaryLimits .adversary machine.adversaryFuel emptyOracle
      (machine.blackBox.start hidden machine.observation)).oracle
    (initialRawFutureFreeProgram machine.environment
      runtime.adversaryValue.rawMessages machine.driverFuel)).oracle =
        runtime.verifierFinalOracle
  rw [reflectedAdversary, reflectedVerifier]

/-- Event membership exposes only computations from the actual root scheduler
and the fixed projection. -/
theorem mem_exact_source_refinement_event_iff
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (projection : AcceptedTapeProjection Statement Proof Payload)
    (sample : ExactCompilerSample HiddenTape parameters) :
    sample ∈ exactSourceRefinementEvent transitionFuel configuration
        projection ↔
      ∃ runtime clientRun tape raw,
        (runExactPlainRomRoot transitionFuel configuration sample).terminal =
          .returned (.completed runtime clientRun) ∧
        projection runtime.adversaryValue = some tape ∧
        fixedTapeRawMessages tape = runtime.adversaryValue.rawMessages ∧
        fixedTapeFutureFreeEnvironment tape = configuration.machine.environment ∧
        checkedRefine
            (fixedTableOfOracleState runtime.verifierFinalOracle)
            exactDeterministicDecoders tape = some raw := by
  simp only [exactSourceRefinementEvent, Set.mem_setOf_eq,
    RootHasStrictSourceRefinement]
  constructor
  · rintro ⟨runtime, clientRun, completed, tape, raw, projected, rawExact,
      environmentExact, refined⟩
    exact ⟨runtime, clientRun, tape, raw, completed, projected, rawExact,
      environmentExact, refined⟩
  · rintro ⟨runtime, clientRun, tape, raw, completed, projected, rawExact,
      environmentExact, refined⟩
    exact ⟨runtime, clientRun, completed, tape, raw, projected, rawExact,
      environmentExact, refined⟩

/-- A positive-budget accepted root has the literal raw verifier invariant;
this is recovered from the scheduler, not included in the source projection. -/
theorem exact_source_refinement_event_has_root_invariant
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (projection : AcceptedTapeProjection Statement Proof Payload)
    (sample : ExactCompilerSample HiddenTape parameters)
    (member : sample ∈ exactSourceRefinementEvent transitionFuel configuration
      projection) :
    ∃ runtime clientRun,
      (runExactPlainRomRoot transitionFuel configuration sample).terminal =
        .returned (.completed runtime clientRun) ∧
      SchedulerNativePlainRomRootInvariant runtime := by
  rcases member with ⟨runtime, clientRun, completed, _source⟩
  exact ⟨runtime, clientRun, completed,
    completed_exact_plain_rom_root_implies_root_invariant transitionFuel
      positive configuration sample runtime clientRun completed⟩

/-- Program, release, statement, attempt and proof-account binding is already
fixed in the checked raw return before any restart or adaptive challenge. -/
theorem exact_source_refinement_event_preserves_public_bindings
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (projection : AcceptedTapeProjection Statement Proof Payload)
    (sample : ExactCompilerSample HiddenTape parameters)
    (member : sample ∈ exactSourceRefinementEvent transitionFuel configuration
      projection) :
    ∃ runtime clientRun,
      (runExactPlainRomRoot transitionFuel configuration sample).terminal =
          .returned (.completed runtime clientRun) ∧
        let bindings :=
          FixedBindings.ofContext runtime.adversaryValue.rawMessages.context
        bindings.programId =
            runtime.adversaryValue.1.publicProof.publicInstance.context.programId ∧
          bindings.releaseBinding =
            runtime.adversaryValue.1.publicProof.publicInstance.context.releaseBinding ∧
          bindings.statementDigest =
            runtime.adversaryValue.1.publicProof.publicInstance.context.statementDigest ∧
          bindings.attemptId =
            runtime.adversaryValue.1.publicProof.publicInstance.context.attemptId ∧
          bindings.proofAccountId =
            runtime.adversaryValue.1.publicProof.publicInstance.context.attemptId := by
  rcases member with ⟨runtime, clientRun, completed, _source⟩
  exact ⟨runtime, clientRun, completed,
    checked_raw_return_preserves_public_bindings runtime.adversaryValue⟩

/-- Strict source refinement constructs the complete operational Tag-73 path
for the exact tape/table attached to the returned root.  The theorem says no
semantic, Merkle or witness conclusion; those remain the explicit K1.2--K1.5
obligations. -/
theorem exact_source_refinement_event_constructs_complete_checked_path
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (projection : AcceptedTapeProjection Statement Proof Payload)
    (sample : ExactCompilerSample HiddenTape parameters)
    (member : sample ∈ exactSourceRefinementEvent transitionFuel configuration
      projection) :
    ∃ runtime clientRun tape raw,
      (runExactPlainRomRoot transitionFuel configuration sample).terminal =
        .returned (.completed runtime clientRun) ∧
      projection runtime.adversaryValue = some tape ∧
      fixedTapeRawMessages tape = runtime.adversaryValue.rawMessages ∧
      fixedTapeFutureFreeEnvironment tape = configuration.machine.environment ∧
      checkedRefine (fixedTableOfOracleState runtime.verifierFinalOracle)
          exactDeterministicDecoders tape = some raw ∧
      Nonempty (CompleteCheckedFutureFreePath
        (fixedTableOfOracleState runtime.verifierFinalOracle) tape) := by
  rcases member with ⟨runtime, clientRun, completed, tape, raw, projected,
    rawExact, environmentExact, refined⟩
  exact ⟨runtime, clientRun, tape, raw, completed, projected, rawExact,
    environmentExact, refined,
    strict_checked_refinement_constructs_complete_future_free_path
      (fixedTableOfOracleState runtime.verifierFinalOracle) tape raw refined⟩

/-! ## Exact alignment with the operational ROM-free root -/

/-- A successful source refinement and the concrete canonical fuel reserve
identify the strict checked path with the ordinary raw verifier execution
reconstructed from the scheduler's two literal root segments.  This theorem
contains no witness or extraction conclusion. -/
theorem exact_source_refinement_event_aligns_actual_root
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (projection : AcceptedTapeProjection Statement Proof Payload)
    (driverCoversProtocol :
      tag73CanonicalDriverFuelCap ≤ configuration.machine.driverFuel)
    (sample : ExactCompilerSample HiddenTape parameters)
    (member : sample ∈ exactSourceRefinementEvent transitionFuel configuration
      projection) :
    ∃ runtime clientRun tape raw,
      (runExactPlainRomRoot transitionFuel configuration sample).terminal =
          .returned (.completed runtime clientRun) ∧
      projection runtime.adversaryValue = some tape ∧
      fixedTapeRawMessages tape = runtime.adversaryValue.rawMessages ∧
      fixedTapeFutureFreeEnvironment tape =
        configuration.machine.environment ∧
      checkedRefine (fixedTableOfOracleState runtime.verifierFinalOracle)
          exactDeterministicDecoders tape = some raw ∧
      ∃ projected : ExactProjectedRootExecution configuration.machine
          sample.1 runtime,
        ∃ canonical : CanonicalCappedCheckedFutureFreePath
            projected.execution.finalTable tape,
          CheckedPathActualRunAlignment projected.execution tape
            canonical.construction.complete := by
  rcases member with ⟨runtime, clientRun, completed, tape, raw, projectedTape,
    rawExact, environmentExact, refined⟩
  have runs := completed_exact_plain_rom_root_gives_projected_totalized_runs
    transitionFuel positive configuration sample runtime clientRun completed
  obtain ⟨projected⟩ :=
    root_projected_runs_construct_exact_execution configuration.machine
      sample.1 runtime runs
  have executionTableExact :
      projected.execution.finalTable =
        fixedTableOfOracleState runtime.verifierFinalOracle := by
    unfold RawVerifierExecution.finalTable
    exact congrArg fixedTableOfOracleState projected.finalOracleExact
  have executionEnvironmentExact :
      projected.execution.environment =
        fixedTapeFutureFreeEnvironment tape := by
    exact projected.environmentExact.trans environmentExact.symm
  have executionRawExact :
      projected.execution.adversaryValue.rawMessages =
        fixedTapeRawMessages tape := by
    rw [projected.adversaryValueExact, ← rawExact]
  have executionFuelCovered :
      tag73CanonicalDriverFuelCap ≤ projected.execution.driverFuel := by
    simpa [projected.driverFuelExact] using driverCoversProtocol
  have executionRefined :
      checkedRefine projected.execution.finalTable exactDeterministicDecoders
          tape = some raw := by
    rw [executionTableExact]
    exact refined
  obtain ⟨canonical, aligned⟩ :=
    strict_checked_refinement_aligns_with_cap_covered_actual_run
      projected.execution tape raw executionEnvironmentExact executionRawExact
      executionFuelCovered executionRefined
  exact ⟨runtime, clientRun, tape, raw, completed, projectedTape, rawExact,
    environmentExact, refined, projected, canonical, aligned⟩

#print axioms root_projected_runs_construct_exact_execution
#print axioms mem_exact_source_refinement_event_iff
#print axioms exact_source_refinement_event_has_root_invariant
#print axioms exact_source_refinement_event_preserves_public_bindings
#print axioms exact_source_refinement_event_constructs_complete_checked_path
#print axioms exact_source_refinement_event_aligns_actual_root

end

end AspisK1.V7Tag73ExactSourceAcceptanceModel
