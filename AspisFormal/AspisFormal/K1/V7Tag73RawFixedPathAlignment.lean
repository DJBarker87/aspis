import AspisFormal.K1.V7Tag73RawVerifierExecution
import AspisFormal.K1.V7Tag73FixedTablePathUniqueness

/-!
# Align an actual raw Tag-73 run with a fixed-table path

The scheduler/root layer reconstructs an actual `RawVerifierExecution`; the
checked-transcript layer reconstructs a `MachineQueryPath`.  When the latter
uses the exact same future-free program and the actual run's final first-hit
table, path uniqueness forces the histories and final verifier states to be
identical.  No caller can choose a convenient final state.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73RawFixedPathAlignment

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73SharedOracleVerifierRunner
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73RawVerifierExecution
open AspisK1.V7Tag73CheckedRefinementFutureFreePath
open AspisK1.V7Tag73FixedTablePathUniqueness

noncomputable section

/-- Any table-backed path for the literal program run by an actual raw
execution is its exact chronological verifier history and final state. -/
theorem raw_verifier_execution_fixed_table_path_is_exact
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    (execution : RawVerifierExecution source)
    (pairs : List (ShaInput × ShaOutput))
    (final : FutureFreeVerifierState)
    (path : MachineQueryPath
      (initialRawFutureFreeProgram execution.environment
        execution.adversaryValue.rawMessages execution.driverFuel)
      pairs final)
    (backed : PathUsesFixedTable execution.finalTable pairs) :
    queryAnswerTrace execution.verifierHistory = pairs ∧
      execution.finalState = final := by
  obtain ⟨actualPairs, actualPath, history, _actors, actualBackedPointwise⟩ :=
    raw_verifier_execution_has_exact_query_path execution
  have actualBacked : PathUsesFixedTable execution.finalTable actualPairs :=
    actualBackedPointwise
  have unique := machine_query_path_fixed_table_unique execution.finalTable
    (initialRawFutureFreeProgram execution.environment
      execution.adversaryValue.rawMessages execution.driverFuel)
    actualPairs pairs execution.finalState final actualPath path actualBacked
      backed
  exact ⟨history.trans unique.1, unique.2⟩

/-- Schedule exhaustion proved on the fixed-table path is therefore schedule
exhaustion of the actual raw verifier execution. -/
theorem raw_verifier_execution_exhausted_of_fixed_table_path
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    (execution : RawVerifierExecution source)
    (pairs : List (ShaInput × ShaOutput))
    (final : FutureFreeVerifierState)
    (path : MachineQueryPath
      (initialRawFutureFreeProgram execution.environment
        execution.adversaryValue.rawMessages execution.driverFuel)
      pairs final)
    (backed : PathUsesFixedTable execution.finalTable pairs)
    (exhausted : FutureFreeScheduleExhausted final.current) :
    FutureFreeScheduleExhausted execution.finalState.current := by
  have finalExact :=
    (raw_verifier_execution_fixed_table_path_is_exact execution pairs final
      path backed).2
  rw [finalExact]
  exact exhausted

#print axioms raw_verifier_execution_fixed_table_path_is_exact
#print axioms raw_verifier_execution_exhausted_of_fixed_table_path

end

end AspisK1.V7Tag73RawFixedPathAlignment
