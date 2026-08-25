import AspisFormal.K1.V7Tag73PausedRecursiveReplay

/-!
# Strict-ancestor suffix replacement for recursive Tag-73 replay

A rewind at an ancestor query is not a sequential append to the parent final
oracle history.  The old selected query and every record after it are stale.
The correct lineage keeps the segments strictly before the selected segment,
replays the selected segment only to the chosen query, programs the pair, and
uses the normally returned residual run as the replacement suffix.

This module implements that operation generically in the oracle-machine result
type.  It neither parses a child proof nor stores a future `DeployedFixedTape`.
It proves chronology from actual `runPrefix`, `programOracle`, and `runMachine`
equations.  The remaining Tag-73 boundary is to feed a returned raw prover
message object through the future-free verifier controller and then choose the
next generated checkpoint from that live state.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73StrictAncestorReplacementLineage

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73AtomicPairFork
open AspisK1.V7Tag73AtomicPairReplay
open AspisK1.V7Tag73CumulativeReplayHistory
open AspisK1.V7Tag73PausedRecursiveReplay
open AspisK1.V7Tag73SequentialOracleRuns

noncomputable section

/-! ## A direct operational scan of returned segments -/

/-- Scan operational segments directly.  Unlike scanning a mapped history
projection, this retains the selected entry program and provenance. -/
def firstPairInOperationalSegments {Result : Type*}
    {start : OracleMachine Result} (outputInput advanceInput : ShaInput) :
    List (OperationalReturnedSegment start) -> Option SegmentedPairOccurrence
  | [] => none
  | segment :: rest =>
      match firstEitherInputOccurrence outputInput advanceInput segment.records with
      | some occurrence =>
          some { segmentIndex := 0, withinSegment := occurrence }
      | none =>
          match firstPairInOperationalSegments outputInput advanceInput rest with
          | none => none
          | some location => some
              { segmentIndex := location.segmentIndex + 1
                withinSegment := location.withinSegment }

def firstPairInOperationalPath {Result : Type*}
    {start : OracleMachine Result}
    {final : OperationalReturnedSegment start}
    (outputInput advanceInput : ShaInput)
    (path : SequentialReplayPath start final) :
    Option SegmentedPairOccurrence :=
  firstPairInOperationalSegments outputInput advanceInput path.segments

/-- Direct scan inversion retains the literal selected operational segment. -/
theorem first_pair_in_operational_segments_spec
    {Result : Type*} {start : OracleMachine Result}
    (outputInput advanceInput : ShaInput)
    (segments : List (OperationalReturnedSegment start))
    (location : SegmentedPairOccurrence)
    (found : firstPairInOperationalSegments outputInput advanceInput segments =
      some location) :
    ∃ earlier selected later,
      segments = earlier ++ selected :: later ∧
      earlier.length = location.segmentIndex ∧
      firstEitherInputOccurrence outputInput advanceInput selected.records =
        some location.withinSegment ∧
      ∀ segment ∈ earlier,
        firstEitherInputOccurrence outputInput advanceInput segment.records =
          none := by
  induction segments generalizing location with
  | nil => simp [firstPairInOperationalSegments] at found
  | cons segment rest ih =>
      cases localFound : firstEitherInputOccurrence outputInput advanceInput
          segment.records with
      | some occurrence =>
          simp only [firstPairInOperationalSegments, localFound,
            Option.some.injEq] at found
          cases found
          exact ⟨[], segment, rest, rfl, rfl, localFound, by simp⟩
      | none =>
          cases recursive : firstPairInOperationalSegments outputInput
              advanceInput rest with
          | none =>
              simp [firstPairInOperationalSegments, localFound, recursive]
                at found
          | some tailLocation =>
              simp only [firstPairInOperationalSegments, localFound, recursive,
                Option.some.injEq] at found
              cases found
              obtain ⟨earlier, selected, later, split, index, selectedFound,
                  earlierNone⟩ := ih tailLocation recursive
              refine ⟨segment :: earlier, selected, later, ?_, ?_,
                selectedFound, ?_⟩
              · simp [split]
              · simp [index]
              · intro candidate member
                simp only [List.mem_cons] at member
                rcases member with rfl | member
                · exact localFound
                · exact earlierNone candidate member

/-- Exact path location selected by the direct executable scan. -/
structure StrictReplacementLocation {Result : Type*}
    {start : OracleMachine Result}
    {final : OperationalReturnedSegment start}
    (outputInput advanceInput : ShaInput)
    (path : SequentialReplayPath start final) where
  scanLocation : SegmentedPairOccurrence
  earlier : List (OperationalReturnedSegment start)
  selected : OperationalReturnedSegment start
  later : List (OperationalReturnedSegment start)
  pathExact : path.segments = earlier ++ selected :: later
  indexExact : earlier.length = scanLocation.segmentIndex
  selectedLocation : LocatedOperationalPair selected outputInput advanceInput
  occurrenceExact : selectedLocation.occurrence = scanLocation.withinSegment
  earlierHaveNoPair : ∀ segment ∈ earlier,
    firstEitherInputOccurrence outputInput advanceInput segment.records = none

/-- A successful direct path scan constructs the strict replacement location;
there is no caller-supplied segment or history projection inverse. -/
theorem strict_replacement_location_exists
    {Result : Type*} {start : OracleMachine Result}
    {final : OperationalReturnedSegment start}
    (outputInput advanceInput : ShaInput)
    (path : SequentialReplayPath start final)
    (scanLocation : SegmentedPairOccurrence)
    (found : firstPairInOperationalPath outputInput advanceInput path =
      some scanLocation) :
    Nonempty (StrictReplacementLocation outputInput advanceInput path) := by
  obtain ⟨earlier, selected, later, split, index, selectedFound, earlierNone⟩ :=
    first_pair_in_operational_segments_spec outputInput advanceInput
      path.segments scanLocation
      (by simpa [firstPairInOperationalPath] using found)
  exact Nonempty.intro
    { scanLocation := scanLocation
      earlier := earlier
      selected := selected
      later := later
      pathExact := split
      indexExact := index
      selectedLocation :=
        { occurrence := scanLocation.withinSegment
          found := selectedFound }
      occurrenceExact := rfl
      earlierHaveNoPair := earlierNone }

/-! ## Two actual programming calls -/

/-- Two successful calls to the real oracle programmer.  This records the
operations used to install a fork pair without pretending that programmed
values are ordinary lazy-oracle fresh answers. -/
structure ExactTwoPointProgramming
    (limits : OracleLimits) (actor : QueryActor) (base : OracleState) where
  firstPoint : Programming
  secondPoint : Programming
  afterFirst : OracleState
  afterBoth : OracleState
  firstExact : programOracle limits actor base firstPoint = .ok afterFirst
  secondExact : programOracle limits actor afterFirst secondPoint = .ok afterBoth

/-- Execute exactly two programming calls, stopping at their real failure. -/
noncomputable def executeTwoPointProgramming
    (limits : OracleLimits) (actor : QueryActor) (base : OracleState)
    (firstPoint secondPoint : Programming) :
    Except OracleAbort (ExactTwoPointProgramming limits actor base) :=
  match firstResult : programOracle limits actor base firstPoint with
  | .error reason => .error reason
  | .ok afterFirst =>
      match secondResult : programOracle limits actor afterFirst secondPoint with
      | .error reason => .error reason
      | .ok afterBoth => .ok
          { firstPoint := firstPoint
            secondPoint := secondPoint
            afterFirst := afterFirst
            afterBoth := afterBoth
            firstExact := firstResult
            secondExact := secondResult }

theorem exact_two_point_programming_preserves_query_history
    (limits : OracleLimits) (actor : QueryActor) (base : OracleState)
    (programming : ExactTwoPointProgramming limits actor base) :
    programming.afterFirst.history = base.history ∧
      programming.afterBoth.history = base.history := by
  have firstFacts := program_oracle_success_exact limits actor base
    programming.afterFirst programming.firstPoint programming.firstExact
  have secondFacts := program_oracle_success_exact limits actor
    programming.afterFirst programming.afterBoth programming.secondPoint
    programming.secondExact
  exact ⟨firstFacts.1, secondFacts.1.trans firstFacts.1⟩

def pointProgrammingRecord (actor : QueryActor)
    (point : Programming) : ProgrammingRecord where
  input := point.input
  output := point.output
  actor := actor

theorem exact_two_point_programming_appends_exact_ledger
    (limits : OracleLimits) (actor : QueryActor) (base : OracleState)
    (programming : ExactTwoPointProgramming limits actor base) :
    programming.afterBoth.programmingHistory =
      base.programmingHistory ++
        [pointProgrammingRecord actor programming.firstPoint,
          pointProgrammingRecord actor programming.secondPoint] := by
  have firstFacts := program_oracle_success_exact limits actor base
    programming.afterFirst programming.firstPoint programming.firstExact
  have secondFacts := program_oracle_success_exact limits actor
    programming.afterFirst programming.afterBoth programming.secondPoint
    programming.secondExact
  rw [secondFacts.2.1, firstFacts.2.1]
  simp [List.append_assoc, pointProgrammingRecord]

/-! ## A completed replacement segment -/

/-- The actual result of replacing one selected ancestor suffix.  Prefix
replay, the two programming operations, and the returned residual run are all
stored by exact equations. -/
structure CompletedStrictReplacement {Result : Type*}
    {start : OracleMachine Result}
    {selected : OperationalReturnedSegment start}
    {outputInput advanceInput : ShaInput}
    (location : LocatedOperationalPair selected outputInput advanceInput) where
  paused : PausedReplayAtPair location
  programmingLimits : OracleLimits
  programming : ExactTwoPointProgramming programmingLimits .extractorReplay
    (locatedReplayPrefix location).oracle
  continuationController : AdaptiveController
  continuationLimits : OracleLimits
  continuationFuel : Nat
  continuationRun : MachineRun Result
  returnedValue : Result
  runExact : continuationRun = runMachine continuationController
    continuationLimits .extractorReplay continuationFuel
    programming.afterBoth paused.residualProgram
  normallyReturned : continuationRun.halt = .returned returnedValue

theorem completed_replacement_has_same_start_program_provenance
    {Result : Type*} {start : OracleMachine Result}
    {selected : OperationalReturnedSegment start}
    {outputInput advanceInput : ShaInput}
    {location : LocatedOperationalPair selected outputInput advanceInput}
    (replacement : CompletedStrictReplacement location) :
    SameStartProgramProvenance start replacement.paused.residualProgram :=
  replacement.paused.programProvenance

/-- The final history is the ancestor entry history followed by the replayed
prefix records and then the new returned continuation records. -/
theorem completed_replacement_history_decomposition
    {Result : Type*} {start : OracleMachine Result}
    {selected : OperationalReturnedSegment start}
    {outputInput advanceInput : ShaInput}
    {location : LocatedOperationalPair selected outputInput advanceInput}
    (replacement : CompletedStrictReplacement location) :
    ∃ prefixRecords childRecords,
      (locatedReplayPrefix location).oracle.history =
        selected.entryOracle.history ++ prefixRecords ∧
      replacement.continuationRun.oracle.history =
        replacement.programming.afterBoth.history ++ childRecords ∧
      replacement.continuationRun.oracle.history =
        selected.entryOracle.history ++ (prefixRecords ++ childRecords) ∧
      (∀ record ∈ prefixRecords, record.actor = selected.actor) ∧
      (∀ record ∈ childRecords, record.actor = .extractorReplay) := by
  obtain ⟨prefixRecords, prefixHistory, prefixActors⟩ :=
    run_prefix_appended_history_exact
      (recordedPrefixController selected.entryOracle.history.length
        location.occurrence.before)
      selected.limits selected.actor location.occurrence.before.length
      selected.entryOracle selected.entryProgram
  obtain ⟨childRecords, childHistory, childActors⟩ :=
    run_machine_appended_history_exact replacement.continuationController
      replacement.continuationLimits .extractorReplay
      replacement.continuationFuel replacement.programming.afterBoth
      replacement.paused.residualProgram
  have prefixHistory' : (locatedReplayPrefix location).oracle.history =
      selected.entryOracle.history ++ prefixRecords := by
    simpa [locatedReplayPrefix] using prefixHistory
  have childHistory' : replacement.continuationRun.oracle.history =
      replacement.programming.afterBoth.history ++ childRecords := by
    rw [replacement.runExact]
    exact childHistory
  have programmedHistory :=
    (exact_two_point_programming_preserves_query_history
      replacement.programmingLimits .extractorReplay
      (locatedReplayPrefix location).oracle replacement.programming).2
  refine ⟨prefixRecords, childRecords, prefixHistory', childHistory', ?_,
    prefixActors, childActors⟩
  calc
    replacement.continuationRun.oracle.history =
        replacement.programming.afterBoth.history ++ childRecords :=
      childHistory'
    _ = (locatedReplayPrefix location).oracle.history ++ childRecords := by
      rw [programmedHistory]
    _ = (selected.entryOracle.history ++ prefixRecords) ++ childRecords := by
      rw [prefixHistory']
    _ = selected.entryOracle.history ++ (prefixRecords ++ childRecords) := by
      simp [List.append_assoc]

/-- Project the complete composite operation to its literal chronological
prover-history segment. -/
noncomputable def CompletedStrictReplacement.toActualHistory
    {Result : Type*} {start : OracleMachine Result}
    {selected : OperationalReturnedSegment start}
    {outputInput advanceInput : ShaInput}
    {location : LocatedOperationalPair selected outputInput advanceInput}
    (replacement : CompletedStrictReplacement location) :
    ActualProverHistorySegment where
  entryOracle := selected.entryOracle
  finalOracle := replacement.continuationRun.oracle
  historyPrefix := by
    obtain ⟨prefixRecords, childRecords, _prefixHistory, _childHistory,
        combined, _prefixActors, _childActors⟩ :=
      completed_replacement_history_decomposition replacement
    rw [combined]
    exact List.prefix_append _ _
  records := historySince selected.entryOracle
    replacement.continuationRun.oracle
  recordsExact := rfl
  proverActors := by
    obtain ⟨prefixRecords, childRecords, _prefixHistory, _childHistory,
        combined, prefixActors, childActors⟩ :=
      completed_replacement_history_decomposition replacement
    have sinceExact : historySince selected.entryOracle
        replacement.continuationRun.oracle = prefixRecords ++ childRecords :=
      history_since_eq_of_exact_append selected.entryOracle
        replacement.continuationRun.oracle (prefixRecords ++ childRecords)
        combined
    intro record member
    rw [sinceExact, List.mem_append] at member
    rcases member with prefixMember | childMember
    · have actorExact := prefixActors record prefixMember
      rcases selected.proverActor with adversary | replay
      · exact Or.inl (actorExact.trans adversary)
      · exact Or.inr (actorExact.trans replay)
    · exact Or.inr (childActors record childMember)

theorem replacement_retains_exact_ancestor_prefix_trace
    {Result : Type*} {start : OracleMachine Result}
    {selected : OperationalReturnedSegment start}
    {outputInput advanceInput : ShaInput}
    {location : LocatedOperationalPair selected outputInput advanceInput}
    (replacement : CompletedStrictReplacement location) :
    queryAnswerTrace
        (historySince selected.entryOracle
          (locatedReplayPrefix location).oracle) =
      queryAnswerTrace location.occurrence.before :=
  replacement.paused.traceExact

/-! ## Replace the stale suffix -/

/-- A strict replacement keeps only `earlier`; `selected :: later` is the
stale parent suffix. -/
structure StrictAncestorReplacementLineage {Result : Type*}
    {start : OracleMachine Result}
    {final : OperationalReturnedSegment start}
    {outputInput advanceInput : ShaInput}
    (path : SequentialReplayPath start final) where
  location : StrictReplacementLocation outputInput advanceInput path
  replacement : CompletedStrictReplacement location.selectedLocation

def StrictAncestorReplacementLineage.oldSegments
    {Result : Type*} {start : OracleMachine Result}
    {final : OperationalReturnedSegment start}
    {outputInput advanceInput : ShaInput}
    {path : SequentialReplayPath start final}
    (_lineage : StrictAncestorReplacementLineage
      (outputInput := outputInput) (advanceInput := advanceInput) path) :
    List (OperationalReturnedSegment start) :=
  path.segments

noncomputable def StrictAncestorReplacementLineage.newHistorySegments
    {Result : Type*} {start : OracleMachine Result}
    {final : OperationalReturnedSegment start}
    {outputInput advanceInput : ShaInput}
    {path : SequentialReplayPath start final}
    (lineage : StrictAncestorReplacementLineage
      (outputInput := outputInput) (advanceInput := advanceInput) path) :
    List ActualProverHistorySegment :=
  lineage.location.earlier.map OperationalReturnedSegment.toActualHistory ++
    [lineage.replacement.toActualHistory]

def StrictAncestorReplacementLineage.staleHistorySegments
    {Result : Type*} {start : OracleMachine Result}
    {final : OperationalReturnedSegment start}
    {outputInput advanceInput : ShaInput}
    {path : SequentialReplayPath start final}
    (lineage : StrictAncestorReplacementLineage
      (outputInput := outputInput) (advanceInput := advanceInput) path) :
    List (OperationalReturnedSegment start) :=
  lineage.location.selected :: lineage.location.later

theorem strict_replacement_old_path_splits_retained_and_stale
    {Result : Type*} {start : OracleMachine Result}
    {final : OperationalReturnedSegment start}
    {outputInput advanceInput : ShaInput}
    {path : SequentialReplayPath start final}
    (lineage : StrictAncestorReplacementLineage
      (outputInput := outputInput) (advanceInput := advanceInput) path) :
    lineage.oldSegments = lineage.location.earlier ++
      lineage.staleHistorySegments := by
  exact lineage.location.pathExact

theorem strict_replacement_stale_suffix_is_nonempty
    {Result : Type*} {start : OracleMachine Result}
    {final : OperationalReturnedSegment start}
    {outputInput advanceInput : ShaInput}
    {path : SequentialReplayPath start final}
    (lineage : StrictAncestorReplacementLineage
      (outputInput := outputInput) (advanceInput := advanceInput) path) :
    lineage.staleHistorySegments ≠ [] := by
  simp [StrictAncestorReplacementLineage.staleHistorySegments]

/-! ## Chronological linkage after replacement -/

private theorem history_linked_append_last
    (initialSegments : List ActualProverHistorySegment)
    (last next : ActualProverHistorySegment)
    (linked : HistoryLinkedSegments (initialSegments ++ [last]))
    (boundary : last.finalOracle.history = next.entryOracle.history) :
    HistoryLinkedSegments (initialSegments ++ [last, next]) := by
  induction initialSegments generalizing last next with
  | nil => simpa [HistoryLinkedSegments] using boundary
  | cons head tail ih =>
      cases tail with
      | nil =>
          have headLast : head.finalOracle.history = last.entryOracle.history := by
            simpa [HistoryLinkedSegments] using linked
          exact ⟨headLast, by simpa [HistoryLinkedSegments] using boundary⟩
      | cons second rest =>
          have headSecond :
              head.finalOracle.history = second.entryOracle.history := linked.1
          have linkedTail : HistoryLinkedSegments
              ((second :: rest) ++ [last]) := by
            exact linked.2
          have extendedTail := ih last next linkedTail boundary
          exact ⟨headSecond, extendedTail⟩

private theorem sequential_path_histories_linked
    {Result : Type*} {start : OracleMachine Result}
    {final : OperationalReturnedSegment start}
    (path : SequentialReplayPath start final) :
    HistoryLinkedSegments
      (path.segments.map OperationalReturnedSegment.toActualHistory) := by
  induction path with
  | root segment => simp [SequentialReplayPath.segments, HistoryLinkedSegments]
  | @append previous parent segment boundary ih =>
      have endsAt : ∃ initialSegments,
          parent.segments = initialSegments ++ [previous] := by
        induction parent with
        | root rootSegment => exact ⟨[], rfl⟩
        | append earlier current link inner =>
            exact ⟨earlier.segments, rfl⟩
      obtain ⟨initialSegments, parentExact⟩ := endsAt
      have priorLinked : HistoryLinkedSegments
          (initialSegments.map OperationalReturnedSegment.toActualHistory ++
            [previous.toActualHistory]) := by
        simpa [parentExact, List.map_append] using ih
      have endpoint : previous.toActualHistory.finalOracle.history =
          segment.toActualHistory.entryOracle.history := by
        exact boundary
      have extended := history_linked_append_last
        (initialSegments.map OperationalReturnedSegment.toActualHistory)
        previous.toActualHistory segment.toActualHistory priorLinked endpoint
      simpa [SequentialReplayPath.segments, parentExact, List.map_append,
        List.append_assoc] using extended

private theorem history_linked_replace_suffix
    (earlier : List ActualProverHistorySegment)
    (selected : ActualProverHistorySegment)
    (later : List ActualProverHistorySegment)
    (replacement : ActualProverHistorySegment)
    (linked : HistoryLinkedSegments (earlier ++ selected :: later))
    (sameEntry : selected.entryOracle.history =
      replacement.entryOracle.history) :
    HistoryLinkedSegments (earlier ++ [replacement]) := by
  induction earlier generalizing selected later replacement with
  | nil => simp [HistoryLinkedSegments]
  | cons head tail ih =>
      cases tail with
      | nil =>
          have boundary : head.finalOracle.history = selected.entryOracle.history :=
            linked.1
          exact ⟨boundary.trans sameEntry, by simp [HistoryLinkedSegments]⟩
      | cons second rest =>
          have headSecond :
              head.finalOracle.history = second.entryOracle.history := linked.1
          have linkedTail : HistoryLinkedSegments
              ((second :: rest) ++ selected :: later) := by
            exact linked.2
          have replacedTail := ih selected later replacement linkedTail sameEntry
          exact ⟨headSecond, replacedTail⟩

/-- The retained prefix plus the new composite replacement is a chronological
history.  This is derived from the old linked path and the fact that the
replacement begins at the selected ancestor entry; no append-to-old-final
equation is assumed. -/
theorem strict_replacement_new_history_is_linked
    {Result : Type*} {start : OracleMachine Result}
    {final : OperationalReturnedSegment start}
    {outputInput advanceInput : ShaInput}
    {path : SequentialReplayPath start final}
    (lineage : StrictAncestorReplacementLineage
      (outputInput := outputInput) (advanceInput := advanceInput) path) :
    HistoryLinkedSegments lineage.newHistorySegments := by
  have oldLinked := sequential_path_histories_linked path
  have oldSplit : path.segments.map OperationalReturnedSegment.toActualHistory =
      lineage.location.earlier.map OperationalReturnedSegment.toActualHistory ++
        lineage.location.selected.toActualHistory ::
          lineage.location.later.map
            OperationalReturnedSegment.toActualHistory := by
    rw [lineage.location.pathExact, List.map_append]
    rfl
  rw [oldSplit] at oldLinked
  apply history_linked_replace_suffix
    (lineage.location.earlier.map OperationalReturnedSegment.toActualHistory)
    lineage.location.selected.toActualHistory
    (lineage.location.later.map OperationalReturnedSegment.toActualHistory)
    lineage.replacement.toActualHistory oldLinked
  rfl

#print axioms first_pair_in_operational_segments_spec
#print axioms strict_replacement_location_exists
#print axioms exact_two_point_programming_preserves_query_history
#print axioms exact_two_point_programming_appends_exact_ledger
#print axioms completed_replacement_has_same_start_program_provenance
#print axioms completed_replacement_history_decomposition
#print axioms replacement_retains_exact_ancestor_prefix_trace
#print axioms strict_replacement_old_path_splits_retained_and_stale
#print axioms strict_replacement_stale_suffix_is_nonempty
#print axioms strict_replacement_new_history_is_linked

end

end AspisK1.V7Tag73StrictAncestorReplacementLineage
