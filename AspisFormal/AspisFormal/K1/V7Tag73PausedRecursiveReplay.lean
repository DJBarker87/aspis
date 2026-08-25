import AspisFormal.K1.V7Tag73CumulativeReplayHistory
import AspisFormal.K1.V7Tag73ResumeDerivedReplayNode

/-!
# A future-free pause before a recursive Tag-73 replay

The eager replay dispatcher computes an entire child before returning it.  It
therefore cannot be used directly by the adaptive uniform-exposure scheduler:
the scheduler must see the residual oracle machine *before* it supplies fresh
answers to that machine.

This file factors out the required operational pause.  The core construction
is generic in the machine result.  Its recursive state contains no parsed
child proof, `ConcreteDagInstance`, `DeployedFixedTape`, or verifier state
indexed by a future proof.  A fixed start closure represents the immutable
hidden adversary tape; every later entry program carries an inductive proof
that it is either that exact closure or a residual obtained by a real
`runPrefix` pause.

The construction locates an actual pair occurrence in the chronological
history of an actually returned ancestor run, replays the literal prefix, and
returns the residual query without executing it.  Programming the two pair
coordinates and running the residual are deliberately subsequent operations.

The final section gives a genuine arbitrary-depth *sequential* linked path.
A rewind to a strict ancestor prefix is not a sequential append: the old
suffix must be replaced.  This distinction is stated as the remaining
future-free suffix-splice boundary rather than hidden in an interface field.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73PausedRecursiveReplay

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73AtomicPairFork
open AspisK1.V7Tag73CumulativeReplayHistory
open AspisK1.V7Tag73SequentialOracleRuns
open AspisK1.V7Tag73OperationalKnowledgeInput
open AspisK1.V7Tag73ResumeDerivedReplayNode
open AspisK1.V7Tag73ConcreteKnowledgeInsertion

noncomputable section

/-! ## Same-start program provenance -/

/-- A residual program can only be obtained from the one fixed start closure
by a finite chain of actual prefix pauses.  When the fixed closure captures a
hidden adversary tape, this is the operational same-tape invariant. -/
inductive SameStartProgramProvenance {Result : Type*}
    (start : OracleMachine Result) : OracleMachine Result -> Prop where
  | start : SameStartProgramProvenance start start
  | paused
      {parent residual : OracleMachine Result}
      (parentProvenance : SameStartProgramProvenance start parent)
      (controller : AdaptiveController) (limits : OracleLimits)
      (actor : QueryActor) (fuel : Nat) (initialOracle : OracleState)
      (pauseExact :
        (runPrefix controller limits actor fuel initialOracle parent).halt =
          .paused residual) :
      SameStartProgramProvenance start residual

/-! ## Exact Tag-73 same-tape specialization -/

/-- The older Tag-73 provenance object is a specialization of the generic
same-start relation above.  In particular, translating it does not inspect a
returned proof or its parsed DAG. -/
theorem same_tape_program_provenance_to_same_start
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : Tag73SameTapeSource HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    {program : OracleMachine
      (CheckedTag73AdversaryReturnedValue Statement Proof Payload)}
    (provenance : SameTapeProgramProvenance source program) :
    SameStartProgramProvenance
      (source.toSameTapeSource.origin.capability.start
        source.toSameTapeSource.observation) program := by
  induction provenance with
  | start => exact SameStartProgramProvenance.start
  | paused parentProvenance controller limits fuel initialOracle pauseExact ih =>
      exact SameStartProgramProvenance.paused ih controller limits
        .extractorReplay fuel initialOracle pauseExact

/-- One actually returned machine segment.  It is generic in `Result` and
retains the exact entry program, controller, actor, resource limits and
same-start derivation. -/
structure OperationalReturnedSegment {Result : Type*}
    (start : OracleMachine Result) where
  entryOracle : OracleState
  entryProgram : OracleMachine Result
  programProvenance : SameStartProgramProvenance start entryProgram
  controller : AdaptiveController
  limits : OracleLimits
  actor : QueryActor
  proverActor : actor = .adversary ∨ actor = .extractorReplay
  fuel : Nat
  run : MachineRun Result
  returnedValue : Result
  exactRun : run = runMachine controller limits actor fuel entryOracle
    entryProgram
  normallyReturned : run.halt = .returned returnedValue

/-- Every dispatcher-derived continuation becomes one generic returned
segment whose start closure is definitionally the original Tag-73 adversary
closure on the original observation. -/
def operationalReturnedSegmentOfContinuation
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : Tag73SameTapeSource HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (continuation : ResumeDerivedContinuation source) :
    OperationalReturnedSegment
      (source.toSameTapeSource.origin.capability.start
        source.toSameTapeSource.observation) where
  entryOracle := continuation.entryOracle
  entryProgram := continuation.entryProgram
  programProvenance :=
    same_tape_program_provenance_to_same_start continuation.programProvenance
  controller := continuation.controller
  limits := continuation.limits
  actor := .extractorReplay
  proverActor := Or.inr rfl
  fuel := continuation.fuel
  run := continuation.run
  returnedValue := continuation.returnedValue
  exactRun := continuation.exactRun
  normallyReturned := continuation.normallyReturned

/-- The fixed generic start above is exactly the black-box closure applied to
the same hidden tape. -/
theorem continuation_segment_start_is_exact_hidden_tape
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : Tag73SameTapeSource HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (_continuation : ResumeDerivedContinuation source) :
    source.toSameTapeSource.origin.capability.start
        source.toSameTapeSource.observation =
      source.toSameTapeSource.blackBox.start
        source.toSameTapeSource.hiddenTape source.toSameTapeSource.observation := by
  exact source_origin_capability_uses_same_hidden_tape source.toSameTapeSource

def OperationalReturnedSegment.records {Result : Type*}
    {start : OracleMachine Result}
    (segment : OperationalReturnedSegment start) : List QueryRecord :=
  historySince segment.entryOracle segment.run.oracle

/-- Forget only the operational program/controller data, retaining the exact
chronological history segment. -/
def OperationalReturnedSegment.toActualHistory {Result : Type*}
    {start : OracleMachine Result}
    (segment : OperationalReturnedSegment start) :
    ActualProverHistorySegment where
  entryOracle := segment.entryOracle
  finalOracle := segment.run.oracle
  historyPrefix := by
    rw [segment.exactRun]
    exact postfork_run_history_is_preserved segment.controller segment.limits
      segment.actor segment.fuel segment.entryOracle segment.entryProgram
  records := segment.records
  recordsExact := rfl
  proverActors := by
    intro record member
    rw [OperationalReturnedSegment.records, segment.exactRun] at member
    have actorExact := run_machine_history_since_has_actor segment.controller
      segment.limits segment.actor segment.fuel segment.entryOracle
      segment.entryProgram record member
    rcases segment.proverActor with adversary | replay
    · exact Or.inl (actorExact.trans adversary)
    · exact Or.inr (actorExact.trans replay)

@[simp] theorem operational_history_records_are_exact {Result : Type*}
    {start : OracleMachine Result}
    (segment : OperationalReturnedSegment start) :
    segment.toActualHistory.records = segment.records := by
  rfl

/-! ## A located occurrence and its exact pause -/

/-- A checked location is not a trace-cover premise.  Its `found` field is the
result of the executable first-occurrence scan on the literal records of one
actual returned segment. -/
structure LocatedOperationalPair {Result : Type*}
    {start : OracleMachine Result}
    (segment : OperationalReturnedSegment start)
    (outputInput advanceInput : ShaInput) where
  occurrence : PairOccurrenceSplit
  found : firstEitherInputOccurrence outputInput advanceInput segment.records =
    some occurrence

def locatedReplayPrefix {Result : Type*}
    {start : OracleMachine Result}
    {segment : OperationalReturnedSegment start}
    {outputInput advanceInput : ShaInput}
    (location : LocatedOperationalPair segment outputInput advanceInput) :
    PrefixRun Result :=
  runPrefix
    (recordedPrefixController segment.entryOracle.history.length
      location.occurrence.before)
    segment.limits segment.actor location.occurrence.before.length
    segment.entryOracle segment.entryProgram

/-- The exact operational object required by a scheduler: execution has
stopped immediately before the selected pair query.  In particular, no
post-fork query and no verifier action has yet run. -/
structure PausedReplayAtPair {Result : Type*}
    {start : OracleMachine Result}
    {segment : OperationalReturnedSegment start}
    {outputInput advanceInput : ShaInput}
    (location : LocatedOperationalPair segment outputInput advanceInput) where
  residualProgram : OracleMachine Result
  pendingInput : ShaInput
  pendingContinuation : ShaOutput -> OracleMachine Result
  pauseExact : (locatedReplayPrefix location).halt =
    .paused residualProgram
  residualIsQuery : residualProgram =
    .query pendingInput pendingContinuation
  pendingIsChosen : pendingInput = location.occurrence.chosen.input
  traceExact : queryAnswerTrace
      (historySince segment.entryOracle
        (locatedReplayPrefix location).oracle) =
    queryAnswerTrace location.occurrence.before

/-- Construct the pause solely by inverting the actual normal return and the
literal first-occurrence decomposition. -/
theorem paused_replay_at_pair_exists {Result : Type*}
    {start : OracleMachine Result}
    {segment : OperationalReturnedSegment start}
    {outputInput advanceInput : ShaInput}
    (location : LocatedOperationalPair segment outputInput advanceInput) :
    Nonempty (PausedReplayAtPair location) := by
  have occurrenceSpec := first_either_input_occurrence_spec outputInput
    advanceInput segment.records location.occurrence location.found
  have returnedRun :
      (runMachine segment.controller segment.limits segment.actor segment.fuel
        segment.entryOracle segment.entryProgram).halt =
          .returned segment.returnedValue := by
    rw [← segment.exactRun]
    exact segment.normallyReturned
  have decomposition :
      historySince segment.entryOracle
          (runMachine segment.controller segment.limits segment.actor
            segment.fuel segment.entryOracle segment.entryProgram).oracle =
        location.occurrence.before ++
          location.occurrence.chosen :: location.occurrence.after := by
    rw [← segment.exactRun]
    rw [← OperationalReturnedSegment.records]
    exact occurrenceSpec.1
  obtain ⟨residual, pendingInput, pendingContinuation, paused, residualQuery,
      pendingChosen, trace⟩ :=
    returned_run_first_occurrence_replays_to_exact_pause segment.controller
      segment.limits segment.actor segment.fuel segment.entryOracle
      segment.entryProgram segment.returnedValue location.occurrence returnedRun
      decomposition
  exact Nonempty.intro
    { residualProgram := residual
      pendingInput := pendingInput
      pendingContinuation := pendingContinuation
      pauseExact := by simpa [locatedReplayPrefix] using paused
      residualIsQuery := residualQuery
      pendingIsChosen := pendingChosen
      traceExact := by simpa [locatedReplayPrefix] using trace }

/-- Canonical noncomputable choice of the proved operational pause.  The
choice is over `paused_replay_at_pair_exists`; no caller supplies a restore
function or a desired property. -/
noncomputable def pauseReplayAtPair {Result : Type*}
    {start : OracleMachine Result}
    {segment : OperationalReturnedSegment start}
    {outputInput advanceInput : ShaInput}
    (location : LocatedOperationalPair segment outputInput advanceInput) :
    PausedReplayAtPair location :=
  Classical.choice (paused_replay_at_pair_exists location)

/-- The returned residual is tied inductively to the identical fixed start
program. -/
theorem PausedReplayAtPair.programProvenance {Result : Type*}
    {start : OracleMachine Result}
    {segment : OperationalReturnedSegment start}
    {outputInput advanceInput : ShaInput}
    {location : LocatedOperationalPair segment outputInput advanceInput}
    (paused : PausedReplayAtPair location) :
    SameStartProgramProvenance start paused.residualProgram :=
  SameStartProgramProvenance.paused segment.programProvenance
    (recordedPrefixController segment.entryOracle.history.length
      location.occurrence.before)
    segment.limits segment.actor location.occurrence.before.length
    segment.entryOracle (by simpa [locatedReplayPrefix] using paused.pauseExact)

theorem paused_replay_retains_exact_ancestor_program_and_controller
    {Result : Type*} {start : OracleMachine Result}
    {segment : OperationalReturnedSegment start}
    {outputInput advanceInput : ShaInput}
    {location : LocatedOperationalPair segment outputInput advanceInput}
    (paused : PausedReplayAtPair location) :
    (locatedReplayPrefix location =
      runPrefix
        (recordedPrefixController segment.entryOracle.history.length
          location.occurrence.before)
        segment.limits segment.actor location.occurrence.before.length
        segment.entryOracle segment.entryProgram) /\
      SameStartProgramProvenance start paused.residualProgram := by
  exact And.intro rfl paused.programProvenance

theorem paused_replay_pending_input_is_literal_pair_half
    {Result : Type*} {start : OracleMachine Result}
    {segment : OperationalReturnedSegment start}
    {outputInput advanceInput : ShaInput}
    {location : LocatedOperationalPair segment outputInput advanceInput}
    (paused : PausedReplayAtPair location) :
    paused.pendingInput = outputInput \/ paused.pendingInput = advanceInput := by
  have occurrenceSpec := first_either_input_occurrence_spec outputInput
    advanceInput segment.records location.occurrence location.found
  rw [paused.pendingIsChosen]
  exact occurrenceSpec.2.2

theorem paused_replay_prefix_history_is_cumulative
    {Result : Type*} {start : OracleMachine Result}
    {segment : OperationalReturnedSegment start}
    {outputInput advanceInput : ShaInput}
    (location : LocatedOperationalPair segment outputInput advanceInput) :
    segment.entryOracle.history <+:
      (locatedReplayPrefix location).oracle.history := by
  unfold locatedReplayPrefix
  exact prefix_run_history_is_preserved
    (recordedPrefixController segment.entryOracle.history.length
      location.occurrence.before)
    segment.limits segment.actor location.occurrence.before.length
    segment.entryOracle segment.entryProgram

/-! ## Arbitrary-depth sequential linkage -/

/-- A nonempty path built only by exact history-linked appends.  This type is
inductive, so no finite depth is baked into the replay model. -/
inductive SequentialReplayPath {Result : Type*}
    (start : OracleMachine Result) :
    OperationalReturnedSegment start -> Type _ where
  | root (segment : OperationalReturnedSegment start) :
      SequentialReplayPath start segment
  | append {previous : OperationalReturnedSegment start}
      (parent : SequentialReplayPath start previous)
      (segment : OperationalReturnedSegment start)
      (historyLink : previous.run.oracle.history = segment.entryOracle.history) :
      SequentialReplayPath start segment

def SequentialReplayPath.segments {Result : Type*}
    {start : OracleMachine Result} {final : OperationalReturnedSegment start} :
      SequentialReplayPath start final ->
      List (OperationalReturnedSegment start)
  | .root segment => [segment]
  | .append parent segment _ => parent.segments ++ [segment]

def SequentialReplayPath.depth {Result : Type*}
    {start : OracleMachine Result} {final : OperationalReturnedSegment start} :
      SequentialReplayPath start final -> Nat
  | .root _ => 1
  | .append parent _ _ => parent.depth + 1

/-- Executable first-pair search over every chronological returned segment in
an arbitrary-depth sequential path. -/
def firstPairInSequentialReplayPath {Result : Type*}
    {start : OracleMachine Result}
    {final : OperationalReturnedSegment start}
    (outputInput advanceInput : ShaInput)
    (path : SequentialReplayPath start final) :
    Option SegmentedPairOccurrence :=
  firstEitherInputOccurrenceInSegments outputInput advanceInput
    (path.segments.map OperationalReturnedSegment.toActualHistory)

/-- A successful executable path scan identifies an actual operational
segment, not merely its history projection. -/
theorem sequential_path_scan_some_has_operational_location
    {Result : Type*} {start : OracleMachine Result}
    {final : OperationalReturnedSegment start}
    (outputInput advanceInput : ShaInput)
    (path : SequentialReplayPath start final)
    (scanLocation : SegmentedPairOccurrence)
    (found : firstPairInSequentialReplayPath outputInput advanceInput path =
      some scanLocation) :
    ∃ segment : OperationalReturnedSegment start,
      segment ∈ path.segments ∧
        firstEitherInputOccurrence outputInput advanceInput segment.records =
          some scanLocation.withinSegment := by
  obtain ⟨earlier, currentHistory, later, segmentsExact, _indexExact,
      currentFound, _earlierNone⟩ :=
    first_either_input_occurrence_in_segments_spec outputInput advanceInput
      (path.segments.map OperationalReturnedSegment.toActualHistory)
      scanLocation (by
        simpa [firstPairInSequentialReplayPath] using found)
  have currentMember : currentHistory ∈
      path.segments.map OperationalReturnedSegment.toActualHistory := by
    rw [segmentsExact]
    simp
  obtain ⟨segment, segmentMember, segmentHistory⟩ :=
    List.mem_map.mp currentMember
  refine ⟨segment, segmentMember, ?_⟩
  subst currentHistory
  simpa only [operational_history_records_are_exact] using currentFound

/-- Consequently, a successful path scan constructs the real pause at that
ancestor.  The only premise is the equality returned by the executable scan;
there is no acceptance, compiler-failure, or trace-cover predicate. -/
theorem sequential_path_scan_constructs_operational_pause
    {Result : Type*} {start : OracleMachine Result}
    {final : OperationalReturnedSegment start}
    (outputInput advanceInput : ShaInput)
    (path : SequentialReplayPath start final)
    (scanLocation : SegmentedPairOccurrence)
    (found : firstPairInSequentialReplayPath outputInput advanceInput path =
      some scanLocation) :
    ∃ segment : OperationalReturnedSegment start,
      segment ∈ path.segments ∧
        ∃ location : LocatedOperationalPair segment outputInput advanceInput,
          Nonempty (PausedReplayAtPair location) := by
  obtain ⟨segment, member, localFound⟩ :=
    sequential_path_scan_some_has_operational_location outputInput advanceInput
      path scanLocation found
  let location : LocatedOperationalPair segment outputInput advanceInput :=
    { occurrence := scanLocation.withinSegment
      found := localFound }
  exact ⟨segment, member, location, paused_replay_at_pair_exists location⟩

@[simp] theorem sequential_append_depth {Result : Type*}
    {start : OracleMachine Result}
    {previous : OperationalReturnedSegment start}
    (parent : SequentialReplayPath start previous)
    (segment : OperationalReturnedSegment start)
    (historyLink : previous.run.oracle.history = segment.entryOracle.history) :
    (SequentialReplayPath.append parent segment historyLink).depth =
      parent.depth + 1 := by
  rfl

@[simp] theorem sequential_segments_length_eq_depth {Result : Type*}
    {start : OracleMachine Result}
    {final : OperationalReturnedSegment start}
    (path : SequentialReplayPath start final) :
    path.segments.length = path.depth := by
  induction path with
  | root segment => rfl
  | append parent segment link ih =>
      simp [SequentialReplayPath.segments, SequentialReplayPath.depth, ih]

/-- Recursive statement of every endpoint equation retained by a path.  It
does not reconstruct links from a projected query list; each equation is the
one supplied by the operational append that created that edge. -/
def SequentialReplayPath.AllLinksExact {Result : Type*}
    {start : OracleMachine Result} {final : OperationalReturnedSegment start} :
      SequentialReplayPath start final -> Prop
  | .root _ => True
  | .append parent segment _ =>
      parent.AllLinksExact

theorem sequential_append_endpoint_exact {Result : Type*}
    {start : OracleMachine Result}
    {previous : OperationalReturnedSegment start}
    (_parent : SequentialReplayPath start previous)
    (segment : OperationalReturnedSegment start)
    (historyLink : previous.run.oracle.history = segment.entryOracle.history) :
    previous.run.oracle.history = segment.entryOracle.history := by
  exact historyLink

theorem sequential_path_all_links_exact {Result : Type*}
    {start : OracleMachine Result}
    {final : OperationalReturnedSegment start}
    (path : SequentialReplayPath start final) : path.AllLinksExact := by
  induction path with
  | root segment => trivial
  | append parent segment historyLink ih => exact ih

/-- One actual dispatcher continuation initializes the generic linked path. -/
def singletonSequentialPathOfContinuation
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : Tag73SameTapeSource HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (continuation : ResumeDerivedContinuation source) :
    SequentialReplayPath
      (source.toSameTapeSource.origin.capability.start
        source.toSameTapeSource.observation)
      (operationalReturnedSegmentOfContinuation continuation) :=
  SequentialReplayPath.root _

/-- A later actual continuation can extend the path at every finite depth
when its entry history is literally the previous returned history.  The
endpoint equality is the necessary operational linkage, not a compiler
conclusion. -/
def appendContinuationToSequentialPath
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : Tag73SameTapeSource HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    {previous : OperationalReturnedSegment
      (source.toSameTapeSource.origin.capability.start
        source.toSameTapeSource.observation)}
    (path : SequentialReplayPath
      (source.toSameTapeSource.origin.capability.start
        source.toSameTapeSource.observation) previous)
    (continuation : ResumeDerivedContinuation source)
    (historyLink : previous.run.oracle.history = continuation.entryOracle.history) :
    SequentialReplayPath
      (source.toSameTapeSource.origin.capability.start
        source.toSameTapeSource.observation)
      (operationalReturnedSegmentOfContinuation continuation) :=
  SequentialReplayPath.append path
    (operationalReturnedSegmentOfContinuation continuation) historyLink

/-!
`SequentialReplayPath.append` is the exact arbitrary-depth append operation
for a suffix that really begins at the preceding final history.  A fork from
a strict ancestor does not satisfy that endpoint equation: its paused prefix
ends before the old ancestor run ended.  The remaining protocol-specific
constructor must therefore splice the normally returned child into a
future-free verifier state while replacing the stale ancestor suffix.  It
must also rederive the new Tag-73 DAG from raw prover messages.  Neither a
whole future tape nor a parsed child DAG is a field of the pause above.
-/

#print axioms paused_replay_at_pair_exists
#print axioms same_tape_program_provenance_to_same_start
#print axioms continuation_segment_start_is_exact_hidden_tape
#print axioms paused_replay_retains_exact_ancestor_program_and_controller
#print axioms paused_replay_pending_input_is_literal_pair_half
#print axioms paused_replay_prefix_history_is_cumulative
#print axioms sequential_append_depth
#print axioms sequential_segments_length_eq_depth
#print axioms sequential_append_endpoint_exact
#print axioms sequential_path_all_links_exact
#print axioms sequential_path_scan_some_has_operational_location
#print axioms sequential_path_scan_constructs_operational_pause

end

end AspisK1.V7Tag73PausedRecursiveReplay
