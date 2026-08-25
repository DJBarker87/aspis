import AspisFormal.K1.V7Tag73ScheduledStrictReplacement
import AspisFormal.K1.V7Tag73SequentialOracleRuns

/-!
# Resource accounting for scheduled strict replacement

The two uniformly drawn fork coordinates are installed by programming calls,
not by lazy-oracle queries.  This leaf records the exact operational
consequence: successful programming adds two table/ledger entries but changes
neither oracle-call counter.  Only the subsequently replayed residual consumes
query fuel.  Thus the global exposure scheduler must count the two uniform
fork coordinates separately even though `OracleState.freshCalls` does not.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ScheduledReplacementAccounting

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AtomicPairReplay
open AspisK1.V7Tag73PausedRecursiveReplay
open AspisK1.V7Tag73StrictAncestorReplacementLineage
open AspisK1.V7Tag73ScheduledStrictReplacement
open AspisK1.V7Tag73SequentialOracleRuns

noncomputable section

theorem successful_program_oracle_preserves_call_counters
    (limits : OracleLimits) (actor : QueryActor)
    (state nextState : OracleState) (point : Programming)
    (success : programOracle limits actor state point = .ok nextState) :
    nextState.totalCalls = state.totalCalls ∧
      nextState.freshCalls = state.freshCalls := by
  unfold programOracle at success
  split at success
  · contradiction
  · split at success
    · contradiction
    · simp only [Except.ok.injEq] at success
      subst nextState
      exact ⟨rfl, rfl⟩

/-- The real two-point programming operation adds exactly two table entries
while preserving the query and fresh-answer counters. -/
theorem scheduled_pair_programming_exact_resource_delta
    (outputInput advanceInput : ShaInput)
    (base : OracleState)
    (configuration : AtomicPairReplayConfiguration)
    (programming : ExactScheduledPairProgramming outputInput advanceInput base
      configuration) :
    programming.operations.afterBoth.totalCalls = base.totalCalls ∧
      programming.operations.afterBoth.freshCalls = base.freshCalls ∧
      programming.operations.afterBoth.table.length = base.table.length + 2 ∧
      programming.operations.afterBoth.programmingHistory.length =
        base.programmingHistory.length + 2 := by
  have firstCounters := successful_program_oracle_preserves_call_counters
    configuration.oracleLimits .extractorReplay base
    programming.operations.afterFirst programming.operations.firstPoint
    programming.operations.firstExact
  have secondCounters := successful_program_oracle_preserves_call_counters
    configuration.oracleLimits .extractorReplay
    programming.operations.afterFirst programming.operations.afterBoth
    programming.operations.secondPoint programming.operations.secondExact
  have firstFacts := program_oracle_success_exact configuration.oracleLimits
    .extractorReplay base programming.operations.afterFirst
    programming.operations.firstPoint programming.operations.firstExact
  have secondFacts := program_oracle_success_exact configuration.oracleLimits
    .extractorReplay programming.operations.afterFirst
    programming.operations.afterBoth programming.operations.secondPoint
    programming.operations.secondExact
  refine ⟨secondCounters.1.trans firstCounters.1,
    secondCounters.2.trans firstCounters.2, ?_,
    scheduled_pair_programming_appends_exactly_two_records outputInput
      advanceInput base configuration programming⟩
  rw [secondFacts.2.2.1, firstFacts.2.2.1]
  simp

/-- In a normally returned scheduled replacement, only the residual machine
can increase the oracle-call counters.  Its increment is bounded by the exact
replay fuel; the two scheduled uniform coordinates remain separately counted
programming exposures. -/
theorem scheduled_completed_replacement_call_bounds
    {Result : Type*} {start : OracleMachine Result}
    {selected : OperationalReturnedSegment start}
    {outputInput advanceInput : ShaInput}
    {location : LocatedOperationalPair selected outputInput advanceInput}
    {configuration : AtomicPairReplayConfiguration}
    (replacement : ScheduledCompletedStrictReplacement location
      configuration) :
    replacement.continuationRun.oracle.totalCalls ≤
        (locatedReplayPrefix location).oracle.totalCalls +
          configuration.replayFuel ∧
      replacement.continuationRun.oracle.freshCalls ≤
        (locatedReplayPrefix location).oracle.freshCalls +
          configuration.replayFuel := by
  have delta := scheduled_pair_programming_exact_resource_delta outputInput
    advanceInput (locatedReplayPrefix location).oracle configuration
    replacement.exactProgramming
  have totalBound := run_machine_total_calls_le_initial_add_fuel
    configuration.postForkController configuration.oracleLimits
    .extractorReplay configuration.replayFuel
    replacement.exactProgramming.operations.afterBoth
    replacement.paused.residualProgram
  have freshBound := run_machine_fresh_calls_le_initial_add_fuel
    configuration.postForkController configuration.oracleLimits
    .extractorReplay configuration.replayFuel
    replacement.exactProgramming.operations.afterBoth
    replacement.paused.residualProgram
  rw [← replacement.runExact] at totalBound freshBound
  exact ⟨by simpa [delta.1] using totalBound,
    by simpa [delta.2.1] using freshBound⟩

#print axioms successful_program_oracle_preserves_call_counters
#print axioms scheduled_pair_programming_exact_resource_delta
#print axioms scheduled_completed_replacement_call_bounds

end

end AspisK1.V7Tag73ScheduledReplacementAccounting
