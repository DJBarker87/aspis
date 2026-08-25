import AspisFormal.K1.V7Tag73AtomicForkUniformScheduler
import AspisFormal.K1.V7Tag73StrictAncestorReplacementLineage

/-!
# Scheduled pair programming and strict replacement

This module connects the two adjacent uniformly scheduled fork coordinates to
the strict-ancestor replacement lineage.  It remains generic in the residual
machine result, so a later specialization may use raw Tag-73 prover messages
without storing a parsed child DAG or future tape.

The construction executes the real `programOracle` operation twice in the
configuration's declared order and then executes the already-paused residual
under the configuration's replay controller.  Programming conflict, oracle
abort and timeout are returned as data.  A normal return constructs
`CompletedStrictReplacement` and, when a path location is supplied by the
executable scan, the complete `StrictAncestorReplacementLineage`.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ScheduledStrictReplacement

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73ConcreteQueryDag
open AspisK1.V7Tag73AtomicPairReplay
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73PausedRecursiveReplay
open AspisK1.V7Tag73StrictAncestorReplacementLineage
open AspisK1.V7Tag73CumulativeReplayHistory

noncomputable section

def literalPairProgrammingPoint
    (outputInput advanceInput : ShaInput)
    (configuration : AtomicPairReplayConfiguration) :
    SqueezeHalf -> Programming
  | .output =>
      { input := outputInput
        output := configuration.forkOutput }
  | .advance =>
      { input := advanceInput
        output := configuration.forkAdvance }

/-- The two real programming calls, tied to the exact scheduled inputs,
outputs and declared order. -/
structure ExactScheduledPairProgramming
    (outputInput advanceInput : ShaInput)
    (base : OracleState)
    (configuration : AtomicPairReplayConfiguration) where
  operations : ExactTwoPointProgramming configuration.oracleLimits
    .extractorReplay base
  orderExact :
    match configuration.programmingOrder with
    | .outputThenAdvance =>
        operations.firstPoint = literalPairProgrammingPoint outputInput
            advanceInput configuration .output ∧
          operations.secondPoint = literalPairProgrammingPoint outputInput
            advanceInput configuration .advance
    | .advanceThenOutput =>
        operations.firstPoint = literalPairProgrammingPoint outputInput
            advanceInput configuration .advance ∧
          operations.secondPoint = literalPairProgrammingPoint outputInput
            advanceInput configuration .output

/-- Execute the exact ordered pair programming. -/
noncomputable def executeScheduledPairProgramming
    (outputInput advanceInput : ShaInput)
    (base : OracleState)
    (configuration : AtomicPairReplayConfiguration) :
    Except OracleAbort
      (ExactScheduledPairProgramming outputInput advanceInput base
        configuration) :=
  match order : configuration.programmingOrder with
  | .outputThenAdvance =>
      let outputPoint := literalPairProgrammingPoint outputInput advanceInput
        configuration .output
      let advancePoint := literalPairProgrammingPoint outputInput advanceInput
        configuration .advance
      match firstResult : programOracle configuration.oracleLimits
          .extractorReplay base outputPoint with
      | .error reason => .error reason
      | .ok afterFirst =>
          match secondResult : programOracle configuration.oracleLimits
              .extractorReplay afterFirst advancePoint with
          | .error reason => .error reason
          | .ok afterBoth => .ok
              { operations :=
                  { firstPoint := outputPoint
                    secondPoint := advancePoint
                    afterFirst := afterFirst
                    afterBoth := afterBoth
                    firstExact := firstResult
                    secondExact := secondResult }
                orderExact := by rw [order]; exact ⟨rfl, rfl⟩ }
  | .advanceThenOutput =>
      let advancePoint := literalPairProgrammingPoint outputInput advanceInput
        configuration .advance
      let outputPoint := literalPairProgrammingPoint outputInput advanceInput
        configuration .output
      match firstResult : programOracle configuration.oracleLimits
          .extractorReplay base advancePoint with
      | .error reason => .error reason
      | .ok afterFirst =>
          match secondResult : programOracle configuration.oracleLimits
              .extractorReplay afterFirst outputPoint with
          | .error reason => .error reason
          | .ok afterBoth => .ok
              { operations :=
                  { firstPoint := advancePoint
                    secondPoint := outputPoint
                    afterFirst := afterFirst
                    afterBoth := afterBoth
                    firstExact := firstResult
                    secondExact := secondResult }
                orderExact := by rw [order]; exact ⟨rfl, rfl⟩ }

theorem scheduled_pair_programming_preserves_query_history
    (outputInput advanceInput : ShaInput)
    (base : OracleState)
    (configuration : AtomicPairReplayConfiguration)
    (programming : ExactScheduledPairProgramming outputInput advanceInput base
      configuration) :
    programming.operations.afterBoth.history = base.history :=
  (exact_two_point_programming_preserves_query_history
    configuration.oracleLimits .extractorReplay base
    programming.operations).2

theorem scheduled_pair_programming_appends_exactly_two_records
    (outputInput advanceInput : ShaInput)
    (base : OracleState)
    (configuration : AtomicPairReplayConfiguration)
    (programming : ExactScheduledPairProgramming outputInput advanceInput base
      configuration) :
    programming.operations.afterBoth.programmingHistory.length =
      base.programmingHistory.length + 2 := by
  rw [exact_two_point_programming_appends_exact_ledger
    configuration.oracleLimits .extractorReplay base programming.operations]
  simp

/-- Both exact inputs resolve to the two scheduled coordinates after a
successful ordered programming operation. -/
theorem scheduled_pair_programming_installs_both_coordinates
    (outputInput advanceInput : ShaInput)
    (base : OracleState)
    (configuration : AtomicPairReplayConfiguration)
    (programming : ExactScheduledPairProgramming outputInput advanceInput base
      configuration) :
    (lookupEntry programming.operations.afterBoth outputInput).map
        TableEntry.output = some configuration.forkOutput ∧
      (lookupEntry programming.operations.afterBoth advanceInput).map
        TableEntry.output = some configuration.forkAdvance := by
  have firstFacts := program_oracle_success_exact configuration.oracleLimits
    .extractorReplay base programming.operations.afterFirst
    programming.operations.firstPoint programming.operations.firstExact
  have secondFacts := program_oracle_success_exact configuration.oracleLimits
    .extractorReplay programming.operations.afterFirst
    programming.operations.afterBoth programming.operations.secondPoint
    programming.operations.secondExact
  cases order : configuration.programmingOrder with
  | outputThenAdvance =>
      have exactOrder := programming.orderExact
      rw [order] at exactOrder
      have outputAtFirst :
          (lookupEntry programming.operations.afterFirst outputInput).map
              TableEntry.output = some configuration.forkOutput := by
        simpa [exactOrder.1, literalPairProgrammingPoint] using
          firstFacts.2.2.2
      have outputAtEnd := program_oracle_success_preserves_lookup_answer
        configuration.oracleLimits .extractorReplay
        programming.operations.afterFirst programming.operations.afterBoth
        programming.operations.secondPoint programming.operations.secondExact
        outputInput configuration.forkOutput outputAtFirst
      have advanceAtEnd :
          (lookupEntry programming.operations.afterBoth advanceInput).map
              TableEntry.output = some configuration.forkAdvance := by
        simpa [exactOrder.2, literalPairProgrammingPoint] using
          secondFacts.2.2.2
      exact ⟨outputAtEnd, advanceAtEnd⟩
  | advanceThenOutput =>
      have exactOrder := programming.orderExact
      rw [order] at exactOrder
      have advanceAtFirst :
          (lookupEntry programming.operations.afterFirst advanceInput).map
              TableEntry.output = some configuration.forkAdvance := by
        simpa [exactOrder.1, literalPairProgrammingPoint] using
          firstFacts.2.2.2
      have advanceAtEnd := program_oracle_success_preserves_lookup_answer
        configuration.oracleLimits .extractorReplay
        programming.operations.afterFirst programming.operations.afterBoth
        programming.operations.secondPoint programming.operations.secondExact
        advanceInput configuration.forkAdvance advanceAtFirst
      have outputAtEnd :
          (lookupEntry programming.operations.afterBoth outputInput).map
              TableEntry.output = some configuration.forkOutput := by
        simpa [exactOrder.2, literalPairProgrammingPoint] using
          secondFacts.2.2.2
      exact ⟨outputAtEnd, advanceAtEnd⟩

/-! ## Execute the scheduled residual -/

inductive ScheduledStrictReplacementFailure where
  | programming (reason : OracleAbort)
  | replayAbort (reason : OracleAbort)
  | timeout
  deriving DecidableEq, Repr

/-- A completed replacement together with the exact scheduled programming
witness from which it was built. -/
structure ScheduledCompletedStrictReplacement
    {Result : Type*} {start : OracleMachine Result}
    {selected : OperationalReturnedSegment start}
    {outputInput advanceInput : ShaInput}
    (location : LocatedOperationalPair selected outputInput advanceInput)
    (configuration : AtomicPairReplayConfiguration) where
  exactProgramming : ExactScheduledPairProgramming outputInput advanceInput
    (locatedReplayPrefix location).oracle configuration
  paused : PausedReplayAtPair location
  continuationRun : MachineRun Result
  returnedValue : Result
  runExact : continuationRun = runMachine configuration.postForkController
    configuration.oracleLimits .extractorReplay configuration.replayFuel
    exactProgramming.operations.afterBoth paused.residualProgram
  normallyReturned : continuationRun.halt = .returned returnedValue

/-- Forget the scheduler witness while retaining the literal completed strict
replacement operation.  Defining this projection from the fields avoids any
dependent equality between independently packaged oracle limits. -/
def ScheduledCompletedStrictReplacement.completed
    {Result : Type*} {start : OracleMachine Result}
    {selected : OperationalReturnedSegment start}
    {outputInput advanceInput : ShaInput}
    {location : LocatedOperationalPair selected outputInput advanceInput}
    {configuration : AtomicPairReplayConfiguration}
    (replacement : ScheduledCompletedStrictReplacement location
      configuration) :
    CompletedStrictReplacement location where
  paused := replacement.paused
  programmingLimits := configuration.oracleLimits
  programming := replacement.exactProgramming.operations
  continuationController := configuration.postForkController
  continuationLimits := configuration.oracleLimits
  continuationFuel := configuration.replayFuel
  continuationRun := replacement.continuationRun
  returnedValue := replacement.returnedValue
  runExact := replacement.runExact
  normallyReturned := replacement.normallyReturned

/-- Execute pair programming and then the actual paused residual.  A normal
return constructs the chronology/provenance object; it is not supplied as a
premise. -/
noncomputable def constructScheduledStrictReplacement
    {Result : Type*} {start : OracleMachine Result}
    {selected : OperationalReturnedSegment start}
    {outputInput advanceInput : ShaInput}
    (location : LocatedOperationalPair selected outputInput advanceInput)
    (configuration : AtomicPairReplayConfiguration) :
    Except ScheduledStrictReplacementFailure
      (ScheduledCompletedStrictReplacement location configuration) :=
  let paused := pauseReplayAtPair location
  match executeScheduledPairProgramming outputInput advanceInput
      (locatedReplayPrefix location).oracle configuration with
  | .error reason => .error (.programming reason)
  | .ok exactProgramming =>
      let replay := runMachine configuration.postForkController
        configuration.oracleLimits .extractorReplay configuration.replayFuel
        exactProgramming.operations.afterBoth paused.residualProgram
      match returned : replay.halt with
      | .oracleAbort reason => .error (.replayAbort reason)
      | .outOfFuel => .error .timeout
      | .returned result =>
          .ok
            { exactProgramming := exactProgramming
              paused := paused
              continuationRun := replay
              returnedValue := result
              runExact := rfl
              normallyReturned := returned }

theorem constructed_scheduled_replacement_uses_exact_coordinates
    {Result : Type*} {start : OracleMachine Result}
    {selected : OperationalReturnedSegment start}
    {outputInput advanceInput : ShaInput}
    (location : LocatedOperationalPair selected outputInput advanceInput)
    (configuration : AtomicPairReplayConfiguration)
    (replacement : ScheduledCompletedStrictReplacement location configuration) :
    (lookupEntry replacement.completed.programming.afterBoth outputInput).map
        TableEntry.output = some configuration.forkOutput ∧
      (lookupEntry replacement.completed.programming.afterBoth advanceInput).map
        TableEntry.output = some configuration.forkAdvance := by
  exact scheduled_pair_programming_installs_both_coordinates
    outputInput advanceInput (locatedReplayPrefix location).oracle
    configuration replacement.exactProgramming

/-- The scheduler's adjacent coordinates are definitionally the values used
by the replacement constructor. -/
theorem scheduled_configuration_replacement_coordinates
    (template : AtomicPairReplayConfiguration)
    (forkOutput forkAdvance : Digest256) :
    let configuration :=
      scheduledForkConfiguration template forkOutput forkAdvance
    configuration.forkOutput = forkOutput ∧
      configuration.forkAdvance = forkAdvance := by
  exact scheduled_fork_configuration_coordinates template forkOutput
    forkAdvance

/-! ## Package the strict lineage -/

structure ScheduledStrictReplacementLineage
    {Result : Type*} {start : OracleMachine Result}
    {final : OperationalReturnedSegment start}
    {outputInput advanceInput : ShaInput}
    {path : SequentialReplayPath start final}
    (location : StrictReplacementLocation outputInput advanceInput path)
    (configuration : AtomicPairReplayConfiguration) where
  scheduled : ScheduledCompletedStrictReplacement location.selectedLocation
    configuration

def ScheduledStrictReplacementLineage.lineage
    {Result : Type*} {start : OracleMachine Result}
    {final : OperationalReturnedSegment start}
    {outputInput advanceInput : ShaInput}
    {path : SequentialReplayPath start final}
    {location : StrictReplacementLocation outputInput advanceInput path}
    {configuration : AtomicPairReplayConfiguration}
    (scheduledLineage : ScheduledStrictReplacementLineage location
      configuration) :
    StrictAncestorReplacementLineage
      (outputInput := outputInput) (advanceInput := advanceInput) path where
  location := location
  replacement := scheduledLineage.scheduled.completed

noncomputable def constructScheduledReplacementLineage
    {Result : Type*} {start : OracleMachine Result}
    {final : OperationalReturnedSegment start}
    {outputInput advanceInput : ShaInput}
    {path : SequentialReplayPath start final}
    (location : StrictReplacementLocation outputInput advanceInput path)
    (configuration : AtomicPairReplayConfiguration) :
    Except ScheduledStrictReplacementFailure
      (ScheduledStrictReplacementLineage location configuration) :=
  match constructScheduledStrictReplacement location.selectedLocation
      configuration with
  | .error reason => .error reason
  | .ok scheduled => .ok { scheduled := scheduled }

theorem constructed_scheduled_lineage_replaces_nonempty_stale_suffix
    {Result : Type*} {start : OracleMachine Result}
    {final : OperationalReturnedSegment start}
    {outputInput advanceInput : ShaInput}
    {path : SequentialReplayPath start final}
    (location : StrictReplacementLocation outputInput advanceInput path)
    (configuration : AtomicPairReplayConfiguration)
    (scheduledLineage : ScheduledStrictReplacementLineage location
      configuration) :
    scheduledLineage.lineage.oldSegments =
        scheduledLineage.lineage.location.earlier ++
          scheduledLineage.lineage.staleHistorySegments ∧
      scheduledLineage.lineage.staleHistorySegments ≠ [] ∧
      HistoryLinkedSegments scheduledLineage.lineage.newHistorySegments := by
  exact ⟨strict_replacement_old_path_splits_retained_and_stale
      scheduledLineage.lineage,
    strict_replacement_stale_suffix_is_nonempty scheduledLineage.lineage,
    strict_replacement_new_history_is_linked scheduledLineage.lineage⟩

#print axioms scheduled_pair_programming_preserves_query_history
#print axioms scheduled_pair_programming_appends_exactly_two_records
#print axioms scheduled_pair_programming_installs_both_coordinates
#print axioms constructed_scheduled_replacement_uses_exact_coordinates
#print axioms scheduled_configuration_replacement_coordinates
#print axioms constructed_scheduled_lineage_replaces_nonempty_stale_suffix

end

end AspisK1.V7Tag73ScheduledStrictReplacement
