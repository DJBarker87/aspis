import AspisFormal.K1.V7Tag73NoPairReplay
import AspisFormal.K1.V7Tag73PausedRecursiveReplay

/-!
# Operational output-oblivious replay for an unqueried squeeze half

This is the causal alternative to charging a decoder-completion fiber.  A
normally returned same-start machine segment determines a literal
`MachineQueryPath`.  If the squeeze-output input is absent from that path and
is still fresh in the final shared table, programming *any* answer at that
point cannot change the replay: every answer the machine actually reads is
already fixed in the table, so the same entry program follows the identical
path and returns the identical value.

The theorem additionally requires and preserves an actual later query to the
paired advance input.  Thus it covers the deployed two-query squeeze case
without pretending the two halves are one singleton prediction.  There is no
decoder, acceptance, probability, trace-cover, or abstract restore premise.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73UnqueriedOutputObliviousReplay

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73AtomicPairFork
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73NoPairReplay
open AspisK1.V7Tag73PausedRecursiveReplay
open AspisK1.V7Tag73SharedOracleVerifierRunner
open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling

noncomputable section

def PathAvoidsInput (pairs : List (ShaInput × ShaOutput))
    (input : ShaInput) : Prop :=
  ∀ pair ∈ pairs, pair.1 ≠ input

def PathQueriesInput (pairs : List (ShaInput × ShaOutput))
    (input : ShaInput) : Prop :=
  ∃ output, (input, output) ∈ pairs

def outputObliviousReplayLimits (state : OracleState) (pathLength : Nat) :
    OracleLimits where
  totalCalls := state.totalCalls + pathLength
  freshCalls := state.freshCalls
  programmedPoints := state.programmingHistory.length + 1

/-- Programming a point absent from a syntactic machine path preserves every
preloaded answer on that path. -/
theorem append_unqueried_programming_preserves_preloaded_path
    (state : OracleState) (actor : QueryActor)
    (pairs : List (ShaInput × ShaOutput))
    (programming : Programming)
    (answers : PreloadedPathAnswers state pairs)
    (avoids : PathAvoidsInput pairs programming.input) :
    PreloadedPathAnswers
      (appendProgrammedPoint actor state programming) pairs := by
  intro pair member
  have different : programming.input ≠ pair.1 := by
    exact fun equal => avoids pair member equal.symm
  exact append_programmed_point_preserves_answer actor state programming
    pair.1 pair.2 (answers pair member)

/-- Generic deterministic noninterference: every assigned value at the
unqueried fresh point yields the same literal path and return.  The controller
is immaterial because all path answers are cached, but is retained explicitly
in the operational statement. -/
theorem machine_path_replay_is_oblivious_to_unqueried_programmed_output
    {Result : Type*} (program : OracleMachine Result)
    (result : Result) (pairs : List (ShaInput × ShaOutput))
    (path : MachineQueryPath program pairs result)
    (state : OracleState) (outputInput : ShaInput)
    (answers : PreloadedPathAnswers state pairs)
    (avoids : PathAvoidsInput pairs outputInput)
    (fresh : lookupEntry state outputInput = none)
    (controller : AdaptiveController) (actor : QueryActor) :
    ∀ assignedOutput : ShaOutput,
      let programming : Programming :=
        { input := outputInput, output := assignedOutput }
      let programmed := appendProgrammedPoint actor state programming
      let limits := outputObliviousReplayLimits state pairs.length
      programOracle limits actor state programming = .ok programmed ∧
      let replay := runMachine controller limits actor pairs.length programmed
        program
      replay.halt = .returned result ∧
      queryAnswerTrace (historySince programmed replay.oracle) = pairs ∧
      replay.oracle.table = programmed.table ∧
      replay.oracle.programmingHistory = programmed.programmingHistory ∧
      replay.oracle.totalCalls = state.totalCalls + pairs.length ∧
      replay.oracle.freshCalls = state.freshCalls ∧
      replay.steps = pairs.length := by
  intro assignedOutput
  let programming : Programming :=
    { input := outputInput, output := assignedOutput }
  let programmed := appendProgrammedPoint actor state programming
  let limits := outputObliviousReplayLimits state pairs.length
  have programmingRoom : state.programmingHistory.length <
      limits.programmedPoints := by
    simp [limits, outputObliviousReplayLimits]
  have programmedExact :
      programOracle limits actor state programming = .ok programmed :=
    program_oracle_fresh_point_exact limits actor state programming
      programmingRoom fresh
  have programmedAnswers : PreloadedPathAnswers programmed pairs :=
    append_unqueried_programming_preserves_preloaded_path state actor pairs
      programming answers avoids
  have totalRoom : programmed.totalCalls + pairs.length ≤
      limits.totalCalls := by
    simp [programmed, appendProgrammedPoint, limits,
      outputObliviousReplayLimits]
  obtain ⟨halt, trace, replayActors, table, programmingHistory, total,
      freshCalls, steps⟩ :=
    run_machine_preloaded_replay_history_since_exact controller limits actor
      pairs.length programmed program pairs result path programmedAnswers
      totalRoom (le_refl _)
  exact ⟨programmedExact, halt, trace, table, programmingHistory,
    by simpa [programmed, appendProgrammedPoint] using total,
    by simpa [programmed, appendProgrammedPoint] using freshCalls, steps⟩

/-! ## Specialization to one actual same-start returned segment -/

/-- The exact path extracted from an actual returned segment avoids an input
whenever its chronological records avoid that input. -/
theorem operational_segment_path_avoids
    {Result : Type*} {start : OracleMachine Result}
    (segment : OperationalReturnedSegment start)
    (outputInput : ShaInput)
    (recordsAvoid : ∀ record ∈ segment.records,
      record.input ≠ outputInput) :
    ∃ pairs : List (ShaInput × ShaOutput),
      MachineQueryPath segment.entryProgram pairs segment.returnedValue ∧
      queryAnswerTrace segment.records = pairs ∧
      PathAvoidsInput pairs outputInput ∧
      PreloadedPathAnswers segment.run.oracle pairs := by
  have returnedRun :
      (runMachine segment.controller segment.limits segment.actor segment.fuel
        segment.entryOracle segment.entryProgram).halt =
          .returned segment.returnedValue := by
    rw [← segment.exactRun]
    exact segment.normallyReturned
  obtain ⟨pairs, path, trace, actors, finalAnswers⟩ :=
    run_machine_returned_has_exact_query_path segment.controller
      segment.limits segment.actor segment.fuel segment.entryOracle
      segment.entryProgram segment.returnedValue returnedRun
  have segmentTrace : queryAnswerTrace segment.records = pairs := by
    rw [OperationalReturnedSegment.records, segment.exactRun]
    exact trace
  have avoids : PathAvoidsInput pairs outputInput := by
    intro pair member
    have traceMember : pair ∈ queryAnswerTrace segment.records := by
      rw [segmentTrace]
      exact member
    obtain ⟨record, recordMember, recordPair⟩ := List.mem_map.mp traceMember
    have inputEq : record.input = pair.1 := congrArg Prod.fst recordPair
    exact fun pairEq => recordsAvoid record recordMember
      (inputEq.trans pairEq)
  have answers : PreloadedPathAnswers segment.run.oracle pairs := by
    intro pair member
    rw [segment.exactRun]
    rw [← fixed_table_lookup_eq_lookup_entry_output]
    exact finalAnswers pair member
  exact ⟨pairs, path, segmentTrace, avoids, answers⟩

/-- Main causal dichotomy branch for K1.6.  The hypotheses are literal facts
about one actual returned same-start segment: the output input is absent, the
advance input is present, and the output point is fresh in the frozen final
table.  For every programmed output value, replay uses the same entry program
(hence the same hidden tape by `programProvenance`), follows the same complete
query path through the advance, and returns the same value. -/
theorem operational_segment_unqueried_output_is_oblivious_through_advance
    {Result : Type*} {start : OracleMachine Result}
    (segment : OperationalReturnedSegment start)
    (outputInput advanceInput : ShaInput)
    (recordsAvoid : ∀ record ∈ segment.records,
      record.input ≠ outputInput)
    (advanceQueried : ∃ record ∈ segment.records,
      record.input = advanceInput)
    (fresh : lookupEntry segment.run.oracle outputInput = none) :
    ∃ pairs : List (ShaInput × ShaOutput),
      MachineQueryPath segment.entryProgram pairs segment.returnedValue ∧
      queryAnswerTrace segment.records = pairs ∧
      PathAvoidsInput pairs outputInput ∧
      PathQueriesInput pairs advanceInput ∧
      ∀ assignedOutput : ShaOutput,
        let programming : Programming :=
          { input := outputInput, output := assignedOutput }
        let programmed := appendProgrammedPoint .extractorReplay
          segment.run.oracle programming
        let limits := outputObliviousReplayLimits segment.run.oracle
          pairs.length
        programOracle limits .extractorReplay segment.run.oracle programming =
            .ok programmed ∧
        let replay := runMachine
          (recordedPrefixController segment.run.oracle.history.length
            segment.records)
          limits .extractorReplay pairs.length programmed segment.entryProgram
        replay.halt = .returned segment.returnedValue ∧
        queryAnswerTrace (historySince programmed replay.oracle) = pairs ∧
        replay.oracle.table = programmed.table ∧
        replay.oracle.programmingHistory = programmed.programmingHistory ∧
        replay.oracle.totalCalls = segment.run.oracle.totalCalls + pairs.length ∧
        replay.oracle.freshCalls = segment.run.oracle.freshCalls ∧
        replay.steps = pairs.length := by
  obtain ⟨pairs, path, trace, avoids, answers⟩ :=
    operational_segment_path_avoids segment outputInput recordsAvoid
  have advanceInPath : PathQueriesInput pairs advanceInput := by
    obtain ⟨record, member, inputEq⟩ := advanceQueried
    have pairMember : (record.input, record.output) ∈ pairs := by
      rw [← trace]
      exact List.mem_map.mpr ⟨record, member, rfl⟩
    exact ⟨record.output, by simpa [inputEq] using pairMember⟩
  refine ⟨pairs, path, trace, avoids, advanceInPath, ?_⟩
  exact machine_path_replay_is_oblivious_to_unqueried_programmed_output
    segment.entryProgram segment.returnedValue pairs path segment.run.oracle
    outputInput answers avoids fresh
    (recordedPrefixController segment.run.oracle.history.length
      segment.records) .extractorReplay

/-- Executable-scan form of the main theorem.  Reusing the existing
first-either scan with the same input in both positions is exactly a
single-input absence test; no caller supplies the universal avoidance
predicate. -/
theorem operational_segment_scanned_unqueried_output_is_oblivious_through_advance
    {Result : Type*} {start : OracleMachine Result}
    (segment : OperationalReturnedSegment start)
    (outputInput advanceInput : ShaInput)
    (outputScan : firstEitherInputOccurrence outputInput outputInput
      segment.records = none)
    (advanceQueried : ∃ record ∈ segment.records,
      record.input = advanceInput)
    (fresh : lookupEntry segment.run.oracle outputInput = none) :
    ∃ pairs : List (ShaInput × ShaOutput),
      MachineQueryPath segment.entryProgram pairs segment.returnedValue ∧
      queryAnswerTrace segment.records = pairs ∧
      PathAvoidsInput pairs outputInput ∧
      PathQueriesInput pairs advanceInput ∧
      ∀ assignedOutput : ShaOutput,
        let programming : Programming :=
          { input := outputInput, output := assignedOutput }
        let programmed := appendProgrammedPoint .extractorReplay
          segment.run.oracle programming
        let limits := outputObliviousReplayLimits segment.run.oracle
          pairs.length
        programOracle limits .extractorReplay segment.run.oracle programming =
            .ok programmed ∧
        let replay := runMachine
          (recordedPrefixController segment.run.oracle.history.length
            segment.records)
          limits .extractorReplay pairs.length programmed segment.entryProgram
        replay.halt = .returned segment.returnedValue ∧
        queryAnswerTrace (historySince programmed replay.oracle) = pairs ∧
        replay.oracle.table = programmed.table ∧
        replay.oracle.programmingHistory = programmed.programmingHistory ∧
        replay.oracle.totalCalls = segment.run.oracle.totalCalls + pairs.length ∧
        replay.oracle.freshCalls = segment.run.oracle.freshCalls ∧
        replay.steps = pairs.length := by
  have absent := (first_either_input_occurrence_none_iff outputInput
    outputInput segment.records).mp outputScan
  apply operational_segment_unqueried_output_is_oblivious_through_advance
    segment outputInput advanceInput
  · intro record member
    exact (absent record member).1
  · exact advanceQueried
  · exact fresh

#print axioms machine_path_replay_is_oblivious_to_unqueried_programmed_output
#print axioms operational_segment_path_avoids
#print axioms operational_segment_unqueried_output_is_oblivious_through_advance
#print axioms operational_segment_scanned_unqueried_output_is_oblivious_through_advance

end

end AspisK1.V7Tag73UnqueriedOutputObliviousReplay
