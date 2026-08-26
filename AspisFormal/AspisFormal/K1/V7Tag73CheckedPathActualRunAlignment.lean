import AspisFormal.K1.V7Tag73CheckedRefinementFullFutureFreePath
import AspisFormal.K1.V7Tag73RawDriverFuelMonotonicity
import AspisFormal.K1.V7Tag73RawFixedPathAlignment

/-!
# Align a complete checked Tag-73 path with one actual raw verifier run

The checked-refinement bridge constructs a complete future-free path over the
first-hit table left by a verifier run.  If the actual run uses the same raw
messages and deterministic environment and its configured driver fuel covers
that concrete path, fixed-table path uniqueness identifies the two executions
exactly.

The fuel premise is deliberately attached to one concrete path.  It cannot be
replaced by an upper bound on every value of `CompleteCheckedFutureFreePath`:
after a path reaches `.done`, arbitrary extra fuel stutters at that same state.
The final section kernel-checks this obstruction.  A separately fuel-accounted
canonical constructor is therefore the correct place for a protocol-wide cap.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73CheckedPathActualRunAlignment

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73RawProverMessages
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73SharedOracleVerifierRunner
open AspisK1.V7Tag73RawVerifierExecution
open AspisK1.V7Tag73FutureFreeCheckedRefinementBisimulation
open AspisK1.V7Tag73CheckedRefinementFullFutureFreePath
open AspisK1.V7Tag73RawDriverFuelMonotonicity
open AspisK1.V7Tag73RawFixedPathAlignment

noncomputable section

/-! ## Exact covered-fuel alignment -/

/-- Arithmetic form of strict driver-fuel coverage.  The slack is explicit;
it is the exact amount of harmless post-halt fuel used in the alignment. -/
theorem driver_fuel_coverage_has_exact_slack
    (pathFuel driverFuel : Nat) (covered : pathFuel ≤ driverFuel) :
    ∃ slack, pathFuel + slack = driverFuel := by
  exact ⟨driverFuel - pathFuel, Nat.add_sub_of_le covered⟩

/-- The operational conclusion of aligning one checked path with the actual
two-phase same-tape execution.  This is output data, not an interface premise:
the normally returned run and its final table are fields of `execution`, and
the exact path is supplied by the checked-refinement construction. -/
structure CheckedPathActualRunAlignment
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    (execution : RawVerifierExecution source) (tape : DeployedFixedTape)
    (path : CompleteCheckedFutureFreePath execution.finalTable tape) where
  verifierPath : MachineQueryPath
    (initialRawFutureFreeProgram execution.environment
      execution.adversaryValue.rawMessages execution.driverFuel)
    path.pairs path.final
  verifierHistoryExact :
    queryAnswerTrace execution.verifierHistory = path.pairs
  finalStateExact : execution.finalState = path.final
  scheduleExhausted :
    FutureFreeScheduleExhausted execution.finalState.current
  runInvariant : FutureFreeRunInvariant
    (FixedBindings.ofContext execution.adversaryValue.rawMessages.context)
    execution.finalState

/-- A concrete checked path, run with the actual final first-hit table and
covered by the actual driver fuel, is literally the verifier's chronological
query history and final complete state.  No acceptance cover, arbitrary run
equation, or extraction statement is an input. -/
theorem align_complete_checked_path_with_actual_run
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    (execution : RawVerifierExecution source) (tape : DeployedFixedTape)
    (path : CompleteCheckedFutureFreePath execution.finalTable tape)
    (environmentExact : execution.environment =
      fixedTapeFutureFreeEnvironment tape)
    (rawExact : execution.adversaryValue.rawMessages =
      fixedTapeRawMessages tape)
    (fuelCovered : path.fuel ≤ execution.driverFuel) :
    CheckedPathActualRunAlignment execution tape path := by
  obtain ⟨slack, fuelExact⟩ := driver_fuel_coverage_has_exact_slack
    path.fuel execution.driverFuel fuelCovered
  have halted : isDriverHalt path.final.current.control = true := by
    have done := path.exhausted
    change path.final.current.control = .done at done
    rw [done]
    rfl
  have extended := initial_raw_future_free_path_extend_fuel
    (fixedTapeFutureFreeEnvironment tape) (fixedTapeRawMessages tape)
    path.fuel slack path.pairs path.final path.path halted
  have actualPath : MachineQueryPath
      (initialRawFutureFreeProgram execution.environment
        execution.adversaryValue.rawMessages execution.driverFuel)
      path.pairs path.final := by
    simpa [environmentExact, rawExact, fuelExact] using extended
  have exactRun := raw_verifier_execution_fixed_table_path_is_exact execution
    path.pairs path.final actualPath path.tableBacked
  have exhausted := raw_verifier_execution_exhausted_of_fixed_table_path
    execution path.pairs path.final actualPath path.tableBacked path.exhausted
  exact ⟨actualPath, exactRun.1, exactRun.2, exhausted,
    raw_verifier_execution_has_exact_run_invariant execution⟩

/-! ## Why the unconstrained complete-path type has no finite fuel cap -/

/-- Once a checked path is complete, arbitrary extra driver fuel gives another
value of the same complete-path type with the identical transcript, state,
table evidence, schedule exhaustion and external-obligation boundary. -/
theorem complete_checked_path_extends_by_arbitrary_halt_fuel
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (path : CompleteCheckedFutureFreePath table tape) (extra : Nat) :
    ∃ extended : CompleteCheckedFutureFreePath table tape,
      extended.fuel = path.fuel + extra ∧
      extended.pairs = path.pairs ∧
      extended.final = path.final := by
  have halted : isDriverHalt path.final.current.control = true := by
    have done := path.exhausted
    change path.final.current.control = .done at done
    rw [done]
    rfl
  have extendedPath := initial_raw_future_free_path_extend_fuel
    (fixedTapeFutureFreeEnvironment tape) (fixedTapeRawMessages tape)
    path.fuel extra path.pairs path.final path.path halted
  let extended : CompleteCheckedFutureFreePath table tape :=
    { fuel := path.fuel + extra
      pairs := path.pairs
      final := path.final
      path := extendedPath
      tableBacked := path.tableBacked
      exhausted := path.exhausted
      invariant := path.invariant
      externalObligations := path.externalObligations
      externalObligationsExact := path.externalObligationsExact }
  exact ⟨extended, rfl, rfl, rfl⟩

/-- Consequently, every proposed numeric bound is exceeded by another padded
representation of the same halted checked execution. -/
theorem complete_checked_path_fuel_is_representation_unbounded
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (path : CompleteCheckedFutureFreePath table tape) (bound : Nat) :
    ∃ extended : CompleteCheckedFutureFreePath table tape,
      bound < extended.fuel := by
  obtain ⟨extended, fuelExact, _pairs, _final⟩ :=
    complete_checked_path_extends_by_arbitrary_halt_fuel table tape path
      (bound + 1)
  refine ⟨extended, ?_⟩
  rw [fuelExact]
  omega

#print axioms driver_fuel_coverage_has_exact_slack
#print axioms align_complete_checked_path_with_actual_run
#print axioms complete_checked_path_extends_by_arbitrary_halt_fuel
#print axioms complete_checked_path_fuel_is_representation_unbounded

end

end AspisK1.V7Tag73CheckedPathActualRunAlignment
