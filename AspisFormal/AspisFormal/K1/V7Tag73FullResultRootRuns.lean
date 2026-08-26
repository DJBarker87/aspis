import AspisFormal.K1.V7Tag73CompletedRootProjection

/-!
# Reflect Tag-73 root prefixes with an arbitrary scheduler result type

The initial-only root scanner fixes the scheduler's phantom final result to
`PUnit`.  A full plain-ROM run uses the extractor client's actual result type.
The phantom parameter does not affect either oracle program.  This leaf
reflects the two concrete projected prefixes directly, avoiding an artificial
conversion through the initial-only scanner.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73FullResultRootRuns

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73ProjectedMachinePrefix
open AspisK1.V7Tag73CompletedRootProjection
open AspisK1.V7Tag73TotalizedMachineReflection
open AspisK1.V7Tag73UniformRawVerifierExecution
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73FutureFreeFullControl

noncomputable section

universe u v

/-- The two concrete root machine prefixes recovered from a scheduler whose
final result type is arbitrary.  Unlike the initial-only scanner, this
structure retains the literal untouched answer suffix after the verifier;
that suffix is the chronological input to the restoration client. -/
structure FullResultRootProjectedPrefixes
    {HiddenTape TapeIdentity Observation Statement Proof Payload Final :
      Type u}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape) (available : List Digest256)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload) where
  adversary : ProjectedMachinePrefixReturned machine.adversaryLimits
    .adversary machine.adversaryFuel emptyOracle
    (schedulerStageProgram Final
      (totalizeOracleMachine machine.adversaryFuel
        (machine.blackBox.start hidden machine.observation))) available
  adversaryValue :
    CheckedRawTag73AdversaryReturnedValue Statement Proof Payload
  adversaryResult : adversary.result = .completed (.ok adversaryValue)
  verifier : ProjectedMachinePrefixReturned machine.verifierLimits .verifier
    machine.verifierFuel adversary.finalState
    (schedulerStageProgram Final
      (totalizeOracleMachine machine.verifierFuel
        (initialRawFutureFreeProgram machine.environment
          adversaryValue.rawMessages machine.driverFuel))) adversary.remaining
  verifierFinalStateValue : FutureFreeVerifierState
  verifierResult :
    verifier.result = .completed (.ok verifierFinalStateValue)
  runtimeExact : runtime = operationalRootRuntime
    (machine.tapeIdentity hidden) adversaryValue adversary.finalState
      verifier.finalState verifierFinalStateValue

/-- A returned projected trace is insensitive to unused answer suffixes.  The
interpreter stops at the certified normal return before consulting `unused`.
-/
theorem projected_fresh_returned_trace_interpreter_exact_with_suffix
    {Result : Type u} (limits : OracleLimits) (actor : QueryActor)
    (fuel : Nat) (state : OracleState) (program : OracleMachine Result)
    (freshQueries : List (ShaInput × Digest256)) (unused : List Digest256)
    (result : Result) (finalState : OracleState) (steps : Nat)
    (coherent : HistoryTotalCoherent state)
    (trace : ProjectedFreshReturnedTrace limits actor fuel state program
      freshQueries result finalState steps) :
    runProjectedFreshSegment limits actor
        (freshQueries.map Prod.snd ++ unused) fuel state program coherent =
      { halt := .returned result, oracle := finalState, steps := steps } := by
  induction trace with
  | returned fuel state program traceCoherent result finalState steps sought =>
      rw [runProjectedFreshSegment, sought]
  | fresh fuel state requestState program traceCoherent input next
      remainingFuel cachedSteps requestCoherent totalRoom freshRoom missing
      sought answer rest result finalState tailSteps tail ih =>
      simp only [List.map_cons, List.cons_append]
      rw [runProjectedFreshSegment, sought]
      change addMachineRunSteps
          (runProjectedFreshSegment limits actor
            (rest.map Prod.snd ++ unused) remainingFuel
            (freshQueryState actor requestState input answer) (next answer)
            (fresh_query_state_preserves_history_total_coherent actor
              requestState input answer requestCoherent))
          (cachedSteps + 1) =
        { halt := .returned result
          oracle := finalState
          steps := tailSteps + (cachedSteps + 1) }
      rw [ih]
      rfl

/-- A successful scheduler-stage prefix, replayed against the whole available
answer list, reflects to the underlying program.  The scheduler result type is
only a universe-raising phantom and cannot affect the oracle path. -/
theorem projected_scheduler_stage_prefix_underlying_run_exact
    {Final : Type u} {Payload : Type v}
    (limits : OracleLimits) (actor : QueryActor)
    (fuel : Nat) (state : OracleState) (program : OracleMachine Payload)
    (available : List Digest256)
    (returned : ProjectedMachinePrefixReturned limits actor fuel state
      (schedulerStageProgram Final program) available)
    (payload : Payload)
    (returnedExact : returned.result = .completed payload)
    (coherent : HistoryTotalCoherent state) :
    runMachine
        (controllerFromProjectedFreshAnswers state.history available)
        limits actor fuel state program =
      { halt := .returned payload
        oracle := returned.finalState
        steps := returned.steps } := by
  have wrappedProjected :=
    projected_fresh_returned_trace_interpreter_exact_with_suffix limits actor
      fuel state (schedulerStageProgram Final program) returned.freshQueries
      returned.remaining returned.result returned.finalState returned.steps
      coherent returned.trace
  have wrappedRun :
      runMachine
          (controllerFromProjectedFreshAnswers state.history available)
          limits actor fuel state (schedulerStageProgram Final program) =
        { halt := .returned returned.result
          oracle := returned.finalState
          steps := returned.steps } := by
    have interpreterExact :=
      run_projected_fresh_segment_eq_run_machine limits actor
        state.history [] available fuel state
        (schedulerStageProgram Final program) coherent
        (projected_fresh_suffix_initial state)
    simp only [List.nil_append] at interpreterExact
    rw [← interpreterExact]
    simpa [returned.availableExact] using wrappedProjected
  rw [returnedExact] at wrappedRun
  exact run_machine_scheduler_stage_completed_reflects
    (Final := Final)
    (controllerFromProjectedFreshAnswers state.history available)
    limits actor fuel state program payload returned.finalState returned.steps
    wrappedRun

/-- Two actual successful root prefixes reflect to the ordinary totalized
prover and verifier equations for every phantom scheduler result type. -/
theorem full_result_projected_prefixes_give_totalized_runs
    {HiddenTape TapeIdentity Observation Statement Proof Payload Final :
      Type u}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape) (available : List Digest256)
    (adversary : ProjectedMachinePrefixReturned machine.adversaryLimits
      .adversary machine.adversaryFuel emptyOracle
      (schedulerStageProgram Final
        (totalizeOracleMachine machine.adversaryFuel
          (machine.blackBox.start hidden machine.observation))) available)
    (adversaryValue :
      CheckedRawTag73AdversaryReturnedValue Statement Proof Payload)
    (adversaryResult : adversary.result = .completed (.ok adversaryValue))
    (verifier : ProjectedMachinePrefixReturned machine.verifierLimits
      .verifier machine.verifierFuel adversary.finalState
      (schedulerStageProgram Final
        (totalizeOracleMachine machine.verifierFuel
          (initialRawFutureFreeProgram machine.environment
            adversaryValue.rawMessages machine.driverFuel)))
      adversary.remaining)
    (verifierFinalState : FutureFreeVerifierState)
    (verifierResult : verifier.result = .completed (.ok verifierFinalState)) :
    RootProjectedTotalizedRuns machine hidden
      (operationalRootRuntime (machine.tapeIdentity hidden) adversaryValue
        adversary.finalState verifier.finalState verifierFinalState) := by
  have adversaryWrapped := projected_machine_prefix_returned_run_exact
    machine.adversaryLimits .adversary machine.adversaryFuel emptyOracle
    (schedulerStageProgram Final
      (totalizeOracleMachine machine.adversaryFuel
        (machine.blackBox.start hidden machine.observation)))
    available adversary empty_oracle_history_total_coherent
  rw [adversaryResult] at adversaryWrapped
  have adversaryRun := run_machine_scheduler_stage_completed_reflects
    (Final := Final)
    (controllerFromProjectedFreshAnswers emptyOracle.history
      (adversary.freshQueries.map Prod.snd))
    machine.adversaryLimits .adversary machine.adversaryFuel emptyOracle
    (totalizeOracleMachine machine.adversaryFuel
      (machine.blackBox.start hidden machine.observation))
    (.ok adversaryValue) adversary.finalState adversary.steps adversaryWrapped
  have adversaryAnswers :=
    projected_machine_prefix_fresh_answers_are_history_suffix
      machine.adversaryLimits .adversary machine.adversaryFuel emptyOracle
      (schedulerStageProgram Final
        (totalizeOracleMachine machine.adversaryFuel
          (machine.blackBox.start hidden machine.observation)))
      available adversary
  have verifierWrapped := projected_machine_prefix_returned_run_exact
    machine.verifierLimits .verifier machine.verifierFuel adversary.finalState
    (schedulerStageProgram Final
      (totalizeOracleMachine machine.verifierFuel
        (initialRawFutureFreeProgram machine.environment
          adversaryValue.rawMessages machine.driverFuel)))
    adversary.remaining verifier adversary.finalCoherent
  rw [verifierResult] at verifierWrapped
  have verifierRun := run_machine_scheduler_stage_completed_reflects
    (Final := Final)
    (controllerFromProjectedFreshAnswers adversary.finalState.history
      (verifier.freshQueries.map Prod.snd))
    machine.verifierLimits .verifier machine.verifierFuel adversary.finalState
    (totalizeOracleMachine machine.verifierFuel
      (initialRawFutureFreeProgram machine.environment
        adversaryValue.rawMessages machine.driverFuel))
    (.ok verifierFinalState) verifier.finalState verifier.steps verifierWrapped
  have verifierAnswers :=
    projected_machine_prefix_fresh_answers_are_history_suffix
      machine.verifierLimits .verifier machine.verifierFuel
      adversary.finalState
      (schedulerStageProgram Final
        (totalizeOracleMachine machine.verifierFuel
          (initialRawFutureFreeProgram machine.environment
            adversaryValue.rawMessages machine.driverFuel)))
      adversary.remaining verifier
  refine ⟨adversary.steps, verifier.steps, ?_, ?_⟩
  · simpa [rootAdversaryProjectedController, rootAdversaryFreshAnswers,
      operationalRootRuntime, adversaryAnswers] using adversaryRun
  · simpa [rootVerifierProjectedController, rootVerifierFreshAnswers,
      operationalRootRuntime, verifierAnswers] using verifierRun

/-- Structure-valued wrapper for the ordinary root-run reflection. -/
theorem FullResultRootProjectedPrefixes.totalizedRuns
    {HiddenTape TapeIdentity Observation Statement Proof Payload Final :
      Type u}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape) (available : List Digest256)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (prefixes : FullResultRootProjectedPrefixes
      (Final := Final) machine hidden available runtime) :
    RootProjectedTotalizedRuns machine hidden runtime := by
  rcases prefixes with
    ⟨adversary, adversaryValue, adversaryResult, verifier,
      verifierFinalStateValue, verifierResult, runtimeExact⟩
  subst runtime
  exact full_result_projected_prefixes_give_totalized_runs
    (Final := Final) machine hidden available adversary adversaryValue
      adversaryResult verifier verifierFinalStateValue verifierResult

/-- The initial-only and result-carrying cursors have the same operational
root when both complete on the same hidden tape and the same master-answer
list.  The proof compares the two literal underlying prover runs, derives the
identical untouched suffix, and then compares the dependent verifier runs.
No root-alignment equation is accepted from the caller. -/
theorem root_and_full_projected_prefixes_runtime_eq
    {HiddenTape TapeIdentity Observation Statement Proof Payload Final :
      Type u}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape) (available : List Digest256)
    (rootRuntime fullRuntime : SchedulerNativePlainRomRootRuntime TapeIdentity
      Statement Proof Payload)
    (root : CompletedRootProjectedPrefixes machine hidden available
      rootRuntime)
    (full : FullResultRootProjectedPrefixes
      (Final := Final) machine hidden available fullRuntime) :
    rootRuntime = fullRuntime := by
  have rootAdversaryRun :=
    projected_scheduler_stage_prefix_underlying_run_exact
      (Final := RootSchedulerResult TapeIdentity Statement Proof Payload)
      machine.adversaryLimits .adversary machine.adversaryFuel emptyOracle
      (totalizeOracleMachine machine.adversaryFuel
        (machine.blackBox.start hidden machine.observation))
      available root.adversary (.ok root.adversaryValue) root.adversaryResult
      empty_oracle_history_total_coherent
  have fullAdversaryRun :=
    projected_scheduler_stage_prefix_underlying_run_exact
      (Final := Final) machine.adversaryLimits .adversary
      machine.adversaryFuel emptyOracle
      (totalizeOracleMachine machine.adversaryFuel
        (machine.blackBox.start hidden machine.observation))
      available full.adversary (.ok full.adversaryValue) full.adversaryResult
      empty_oracle_history_total_coherent
  have adversaryOutputsEqual := rootAdversaryRun.symm.trans fullAdversaryRun
  simp only [MachineRun.mk.injEq, MachineHalt.returned.injEq,
    Except.ok.injEq] at adversaryOutputsEqual
  rcases adversaryOutputsEqual with
    ⟨adversaryValueExact, adversaryOracleExact, _adversaryStepsExact⟩
  have rootFresh :=
    projected_machine_prefix_fresh_answers_are_history_suffix
      machine.adversaryLimits .adversary machine.adversaryFuel emptyOracle
      (schedulerStageProgram
        (RootSchedulerResult TapeIdentity Statement Proof Payload)
        (totalizeOracleMachine machine.adversaryFuel
          (machine.blackBox.start hidden machine.observation)))
      available root.adversary
  have fullFresh :=
    projected_machine_prefix_fresh_answers_are_history_suffix
      machine.adversaryLimits .adversary machine.adversaryFuel emptyOracle
      (schedulerStageProgram Final
        (totalizeOracleMachine machine.adversaryFuel
          (machine.blackBox.start hidden machine.observation)))
      available full.adversary
  have adversaryFreshExact :
      root.adversary.freshQueries.map Prod.snd =
        full.adversary.freshQueries.map Prod.snd := by
    rw [← rootFresh, ← fullFresh, adversaryOracleExact]
  have adversaryDecomposition :=
    root.adversary.availableExact.symm.trans full.adversary.availableExact
  rw [adversaryFreshExact] at adversaryDecomposition
  have adversaryRemainingExact :
      root.adversary.remaining = full.adversary.remaining :=
    List.append_cancel_left adversaryDecomposition
  let rootVerifierProgram :
      OracleMachine (Except TotalizedMachineFailure FutureFreeVerifierState) :=
    totalizeOracleMachine machine.verifierFuel
      (initialRawFutureFreeProgram machine.environment
        root.adversaryValue.rawMessages machine.driverFuel)
  let fullVerifierProgram :
      OracleMachine (Except TotalizedMachineFailure FutureFreeVerifierState) :=
    totalizeOracleMachine machine.verifierFuel
      (initialRawFutureFreeProgram machine.environment
        full.adversaryValue.rawMessages machine.driverFuel)
  have rootVerifierRun :=
    projected_scheduler_stage_prefix_underlying_run_exact
      (Final := RootSchedulerResult TapeIdentity Statement Proof Payload)
      (limits := machine.verifierLimits) (actor := .verifier)
      (fuel := machine.verifierFuel) (state := root.adversary.finalState)
      (program := rootVerifierProgram)
      (available := root.adversary.remaining) (returned := root.verifier)
      (payload := (Except.ok root.verifierFinalStateValue :
        Except TotalizedMachineFailure FutureFreeVerifierState))
      (returnedExact := root.verifierResult)
      (coherent := root.adversary.finalCoherent)
  have fullVerifierRunNative :=
    projected_scheduler_stage_prefix_underlying_run_exact
      (Final := Final) (limits := machine.verifierLimits) (actor := .verifier)
      (fuel := machine.verifierFuel) (state := full.adversary.finalState)
      (program := fullVerifierProgram)
      (available := full.adversary.remaining) (returned := full.verifier)
      (payload := (Except.ok full.verifierFinalStateValue :
        Except TotalizedMachineFailure FutureFreeVerifierState))
      (returnedExact := full.verifierResult)
      (coherent := full.adversary.finalCoherent)
  have fullVerifierRun :
      runMachine
          (controllerFromProjectedFreshAnswers
            root.adversary.finalState.history root.adversary.remaining)
          machine.verifierLimits .verifier machine.verifierFuel
          root.adversary.finalState
          rootVerifierProgram =
        { halt := .returned (.ok full.verifierFinalStateValue)
          oracle := full.verifier.finalState
          steps := full.verifier.steps } := by
    simpa only [rootVerifierProgram, fullVerifierProgram,
      adversaryValueExact, adversaryOracleExact,
      adversaryRemainingExact] using fullVerifierRunNative
  have verifierOutputsEqual := rootVerifierRun.symm.trans fullVerifierRun
  simp only [MachineRun.mk.injEq, MachineHalt.returned.injEq,
    Except.ok.injEq] at verifierOutputsEqual
  rcases verifierOutputsEqual with
    ⟨verifierValueExact, verifierOracleExact, _verifierStepsExact⟩
  rw [root.runtimeExact, full.runtimeExact]
  simp only [operationalRootRuntime]
  simpa only [adversaryValueExact, adversaryOracleExact,
    verifierValueExact, verifierOracleExact]

#print axioms full_result_projected_prefixes_give_totalized_runs
#print axioms FullResultRootProjectedPrefixes.totalizedRuns
#print axioms root_and_full_projected_prefixes_runtime_eq

end

end AspisK1.V7Tag73FullResultRootRuns
