import AspisFormal.K1.V7Tag73SchedulerNativeCachedGammaReplay
import AspisFormal.K1.V7Tag73OperationalOracleExposure

/-!
# Source provenance for cached K1.5 sampler coordinates

The scheduler-native cache observer records calls skipped by the fresh-answer
normalizer, but intentionally erases the source of the selected table entry.
That erasure matters for K1.5: a cached answer can either be the value of an
earlier genuinely fresh master-tape coordinate or a value installed by a
restoration programming step.

This file retains the source tag and proves the exact operational split.  A
cached call backed by a fresh table entry has a matching earlier fresh query
record and therefore occurs in the consumed prefix of the compiler master
tape.  A cached call backed by a programmed entry has a matching programming
record and consumes no fresh coordinate.  The split is deterministic and
does not select an earlier coordinate from completed future context.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73K15CachedCoordinateProvenance

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73SchedulerNativeCachedGammaReplay
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

universe u

/-! ## Source-exact table coverage -/

/-- Every table entry is witnessed at the operational source indicated by its
source tag.  Unlike source-erased table coverage, this invariant is strong
enough to recover the original fresh master-tape coordinate of a cached call.
-/
def TableSourceCovered (state : OracleState) : Prop :=
  ∀ entry ∈ state.table,
    (entry.source = .fresh →
      ∃ record ∈ state.history,
        record.origin = .fresh ∧ record.input = entry.input ∧
          record.output = entry.output) ∧
    (entry.source = .programmed →
      ∃ record ∈ state.programmingHistory,
        record.input = entry.input ∧ record.output = entry.output)

theorem empty_oracle_table_source_covered :
    TableSourceCovered emptyOracle := by
  simp [TableSourceCovered, emptyOracle]

/-- A successful lazy-oracle query preserves source-exact coverage.  The
cached branch changes no table entry; the missing branch appends one fresh
entry together with its literal fresh record. -/
theorem query_oracle_preserves_table_source_covered
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (state nextState : OracleState)
    (input : ShaInput) (output : ShaOutput)
    (covered : TableSourceCovered state)
    (success : queryOracle controller limits actor state input =
      .ok (output, nextState)) :
    TableSourceCovered nextState := by
  unfold queryOracle at success
  split at success <;> try contradiction
  next _ =>
    split at success
    next entry found =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at success
      rcases success with ⟨rfl, rfl⟩
      intro candidate member
      obtain ⟨freshCovered, programmedCovered⟩ := covered candidate member
      constructor
      · intro sourceFresh
        obtain ⟨record, recordMember, originFresh, inputExact,
            outputExact⟩ := freshCovered sourceFresh
        exact ⟨record, List.mem_append_left _ recordMember, originFresh,
          inputExact, outputExact⟩
      · exact programmedCovered
    next missing =>
      split at success <;> try contradiction
      next _ =>
        split at success
        next _ => contradiction
        next answer answered =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at success
          rcases success with ⟨rfl, rfl⟩
          intro candidate member
          simp only [List.mem_append, List.mem_singleton] at member
          rcases member with old | rfl
          · obtain ⟨freshCovered, programmedCovered⟩ := covered candidate old
            constructor
            · intro sourceFresh
              obtain ⟨record, recordMember, originFresh, inputExact,
                  outputExact⟩ := freshCovered sourceFresh
              exact ⟨record, List.mem_append_left _ recordMember,
                originFresh, inputExact, outputExact⟩
            · exact programmedCovered
          · constructor
            · intro _sourceFresh
              let record : QueryRecord :=
                { input := input
                  output := answer
                  actor := actor
                  origin := .fresh }
              exact ⟨record, List.mem_append_right _ (by simp [record]),
                rfl, rfl, rfl⟩
            · intro impossible
              cases impossible

/-- A successful programming operation appends a programmed entry together
with its exact programming record and leaves all fresh witnesses intact. -/
theorem program_oracle_preserves_table_source_covered
    (limits : OracleLimits) (actor : QueryActor)
    (state nextState : OracleState) (point : Programming)
    (covered : TableSourceCovered state)
    (success : programOracle limits actor state point = .ok nextState) :
    TableSourceCovered nextState := by
  unfold programOracle at success
  split at success <;> try contradiction
  next _ =>
    split at success
    next _ => contradiction
    next fresh =>
      simp only [Except.ok.injEq] at success
      subst nextState
      intro candidate member
      simp only [List.mem_append, List.mem_singleton] at member
      rcases member with old | rfl
      · obtain ⟨freshCovered, programmedCovered⟩ := covered candidate old
        constructor
        · exact freshCovered
        · intro sourceProgrammed
          obtain ⟨record, recordMember, inputExact, outputExact⟩ :=
            programmedCovered sourceProgrammed
          exact ⟨record, List.mem_append_left _ recordMember,
            inputExact, outputExact⟩
      · constructor
        · intro impossible
          cases impossible
        · intro _sourceProgrammed
          let record : ProgrammingRecord :=
            { input := point.input
              output := point.output
              actor := actor }
          exact ⟨record, List.mem_append_right _ (by simp [record]), rfl, rfl⟩

/-- A fuel-bounded machine preserves source-exact coverage. -/
theorem run_machine_preserves_table_source_covered
    {Result : Type*} (controller : AdaptiveController)
    (limits : OracleLimits) (actor : QueryActor) (fuel : Nat)
    (state : OracleState) (program : OracleMachine Result)
    (covered : TableSourceCovered state) :
    TableSourceCovered
      (runMachine controller limits actor fuel state program).oracle := by
  induction fuel generalizing state program with
  | zero =>
      cases program <;> simpa [runMachine] using covered
  | succ fuel ih =>
      cases program with
      | pure result => simpa [runMachine] using covered
      | abort reason => simpa [runMachine] using covered
      | query input next =>
          simp only [runMachine]
          cases queryResult : queryOracle controller limits actor state input with
          | error reason => simpa using covered
          | ok pair =>
              rcases pair with ⟨output, nextState⟩
              exact ih nextState (next output)
                (query_oracle_preserves_table_source_covered controller limits
                  actor state nextState input output covered queryResult)

/-! ## Source-aware cached normalization -/

/-- One cached query together with the exact source tag selected from the
table. -/
structure SourceAwareCachedObservation where
  record : QueryRecord
  source : TableSource
  originExact : record.origin = cachedOrigin source

/-- Source-aware analogue of `cachedRecordsBeforeNextFresh`.  It executes no
new semantics and only retains the source tag erased by the older observer.
-/
def sourceAwareCachedRecordsBeforeNextFresh {Result : Type u}
    (limits : OracleLimits) (actor : QueryActor) :
    Nat → OracleState → OracleMachine Result →
      List SourceAwareCachedObservation
  | _, _, .pure _ => []
  | _, _, .abort _ => []
  | 0, _, .query _ _ => []
  | fuel + 1, state, .query input next =>
      if state.totalCalls ≥ limits.totalCalls then
        []
      else
        match lookupEntry state input with
        | some entry =>
            { record :=
                { input := input
                  output := entry.output
                  actor := actor
                  origin := cachedOrigin entry.source }
              source := entry.source
              originExact := rfl } ::
              sourceAwareCachedRecordsBeforeNextFresh limits actor fuel
                (cachedQueryState actor state input entry)
                (next entry.output)
        | none => []

@[simp] theorem source_aware_cached_records_map
    {Result : Type u} (limits : OracleLimits) (actor : QueryActor) :
    ∀ (fuel : Nat) (state : OracleState) (program : OracleMachine Result),
      (sourceAwareCachedRecordsBeforeNextFresh limits actor fuel state
          program).map SourceAwareCachedObservation.record =
        (cachedRecordsBeforeNextFresh limits actor fuel state program).map
          CachedQueryObservation.record := by
  intro fuel
  induction fuel with
  | zero =>
      intro state program
      cases program <;> rfl
  | succ fuel ih =>
      intro state program
      cases program with
      | pure result => rfl
      | abort reason => rfl
      | query input next =>
          by_cases blocked : state.totalCalls ≥ limits.totalCalls
          · simp [sourceAwareCachedRecordsBeforeNextFresh,
              cachedRecordsBeforeNextFresh, blocked]
          · cases found : lookupEntry state input with
            | none =>
                simp [sourceAwareCachedRecordsBeforeNextFresh,
                  cachedRecordsBeforeNextFresh, blocked, found]
            | some entry =>
                simp [sourceAwareCachedRecordsBeforeNextFresh,
                  cachedRecordsBeforeNextFresh, blocked, found,
                  ih (cachedQueryState actor state input entry)
                    (next entry.output)]

theorem cached_query_state_table_eq
    (actor : QueryActor) (state : OracleState) (input : ShaInput)
    (entry : TableEntry) :
    (cachedQueryState actor state input entry).table = state.table := by
  rfl

theorem cached_query_state_programming_history_eq
    (actor : QueryActor) (state : OracleState) (input : ShaInput)
    (entry : TableEntry) :
    (cachedQueryState actor state input entry).programmingHistory =
      state.programmingHistory := by
  rfl

/-- Exact source split for every cached call normalized before the next fresh
request.  A fresh-backed hit names an earlier fresh query record.  A
programmed-backed hit names an earlier programming record instead. -/
theorem source_aware_cached_record_provenance
    {Result : Type u} (limits : OracleLimits) (actor : QueryActor) :
    ∀ (fuel : Nat) (state : OracleState) (program : OracleMachine Result)
      (covered : TableSourceCovered state)
      (observation : SourceAwareCachedObservation),
      observation ∈
          sourceAwareCachedRecordsBeforeNextFresh limits actor fuel state
            program →
        ((observation.source = .fresh ∧
            ∃ record ∈ state.history,
              record.origin = .fresh ∧
                record.input = observation.record.input ∧
                record.output = observation.record.output) ∨
          (observation.source = .programmed ∧
            ∃ record ∈ state.programmingHistory,
              record.input = observation.record.input ∧
                record.output = observation.record.output)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro state program covered observation member
      cases program <;> simp [sourceAwareCachedRecordsBeforeNextFresh] at member
  | succ fuel ih =>
      intro state program covered observation member
      cases program with
      | pure result => simp [sourceAwareCachedRecordsBeforeNextFresh] at member
      | abort reason => simp [sourceAwareCachedRecordsBeforeNextFresh] at member
      | query input next =>
          by_cases blocked : state.totalCalls ≥ limits.totalCalls
          · simp [sourceAwareCachedRecordsBeforeNextFresh, blocked] at member
          · cases found : lookupEntry state input with
            | none =>
                simp [sourceAwareCachedRecordsBeforeNextFresh, blocked,
                  found] at member
            | some entry =>
              rw [show sourceAwareCachedRecordsBeforeNextFresh limits actor
                    (fuel + 1) state (.query input next) =
                    ({ record :=
                        { input := input
                          output := entry.output
                          actor := actor
                          origin := cachedOrigin entry.source }
                       source := entry.source
                       originExact := rfl } : SourceAwareCachedObservation) ::
                      sourceAwareCachedRecordsBeforeNextFresh limits actor fuel
                        (cachedQueryState actor state input entry)
                        (next entry.output) by
                    simp [sourceAwareCachedRecordsBeforeNextFresh, blocked,
                      found]] at member
              simp only [List.mem_cons] at member
              rcases member with rfl | tailMember
              · have entryMember : entry ∈ state.table := by
                  unfold lookupEntry at found
                  exact List.mem_of_find?_eq_some found
                obtain ⟨freshCovered, programmedCovered⟩ :=
                  covered entry entryMember
                have selectedInput : entry.input = input := by
                  unfold lookupEntry at found
                  have predicate := List.find?_some found
                  exact of_decide_eq_true predicate
                by_cases sourceFresh : entry.source = .fresh
                · left
                  obtain ⟨record, recordMember, originFresh, inputExact,
                      outputExact⟩ := freshCovered sourceFresh
                  exact ⟨sourceFresh, record, recordMember, originFresh,
                    inputExact.trans selectedInput, outputExact⟩
                · right
                  have sourceProgrammed : entry.source = .programmed := by
                    cases source : entry.source with
                    | fresh => exact (sourceFresh source).elim
                    | programmed => exact rfl
                  obtain ⟨record, recordMember, inputExact, outputExact⟩ :=
                    programmedCovered sourceProgrammed
                  exact ⟨sourceProgrammed, record, recordMember,
                    inputExact.trans selectedInput, outputExact⟩
              · have nextCovered : TableSourceCovered
                    (cachedQueryState actor state input entry) := by
                  intro candidate candidateMember
                  obtain ⟨freshCovered, programmedCovered⟩ :=
                    covered candidate candidateMember
                  constructor
                  · intro sourceFresh
                    obtain ⟨record, recordMember, originFresh, inputExact,
                        outputExact⟩ := freshCovered sourceFresh
                    exact ⟨record, List.mem_append_left _ recordMember,
                      originFresh, inputExact, outputExact⟩
                  · exact programmedCovered
                have tail := ih (cachedQueryState actor state input entry)
                  (next entry.output) nextCovered observation tailMember
                rcases tail with fresh | programmed
                · left
                  rcases fresh with ⟨sourceFresh, record, recordMember,
                    originFresh, inputExact, outputExact⟩
                  refine ⟨sourceFresh, record, ?_, originFresh, inputExact,
                    outputExact⟩
                  simp only [cachedQueryState, List.mem_append,
                    List.mem_singleton] at recordMember
                  rcases recordMember with old | rfl
                  · exact old
                  · have impossible : cachedOrigin entry.source ≠ .fresh := by
                      cases entry.source <;> simp [cachedOrigin]
                    exact (impossible originFresh).elim
                · right
                  rcases programmed with ⟨sourceProgrammed, record,
                    recordMember, inputExact, outputExact⟩
                  exact ⟨sourceProgrammed, record, recordMember, inputExact,
                    outputExact⟩

/-! ## From a fresh source witness to the literal master tape -/

theorem fresh_record_output_mem_enumeration
    (history : List QueryRecord) (record : QueryRecord)
    (member : record ∈ history) (fresh : record.origin = .fresh) :
    record.output ∈ freshAnswerEnumeration history := by
  induction history with
  | nil => simp at member
  | cons head tail ih =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · simp [freshAnswerEnumeration, fresh]
      · cases origin : head.origin with
        | fresh =>
            rw [show freshAnswerEnumeration (head :: tail) =
                head.output :: freshAnswerEnumeration tail by
              simp [freshAnswerEnumeration, origin]]
            exact List.mem_cons_of_mem head.output (ih member)
        | programmed =>
            rw [show freshAnswerEnumeration (head :: tail) =
                freshAnswerEnumeration tail by
              simp [freshAnswerEnumeration, origin]]
            exact ih member
        | cached =>
            rw [show freshAnswerEnumeration (head :: tail) =
                freshAnswerEnumeration tail by
              simp [freshAnswerEnumeration, origin]]
            exact ih member

/-- Any fresh source witness in a tape-coherent state is literally one of the
consumed master-tape values. -/
theorem fresh_record_output_mem_master_tape
    {steps : Nat} (tape : FreshAnswerTape Digest256 steps)
    (state : OracleState) (coherent : FreshHistoryMatchesTape tape state)
    (record : QueryRecord) (member : record ∈ state.history)
    (fresh : record.origin = .fresh) :
    record.output ∈ freshAnswerTapeToList tape := by
  have inEnumeration := fresh_record_output_mem_enumeration state.history
    record member fresh
  unfold FreshHistoryMatchesTape at coherent
  rw [coherent] at inEnumeration
  exact List.mem_of_mem_take inEnumeration

/-- Final operational classification.  A source-aware cached call is either
an actual earlier master-tape value or a programmed value.  The second branch
is intentionally not converted into a fresh coordinate. -/
theorem source_aware_cached_record_master_tape_or_programmed
    {Result : Type u} {steps : Nat}
    (limits : OracleLimits) (actor : QueryActor)
    (fuel : Nat) (state : OracleState) (program : OracleMachine Result)
    (tape : FreshAnswerTape Digest256 steps)
    (covered : TableSourceCovered state)
    (coherent : FreshHistoryMatchesTape tape state)
    (observation : SourceAwareCachedObservation)
    (member : observation ∈
      sourceAwareCachedRecordsBeforeNextFresh limits actor fuel state
        program) :
    (observation.record.output ∈ freshAnswerTapeToList tape) ∨
      ∃ record ∈ state.programmingHistory,
        record.input = observation.record.input ∧
          record.output = observation.record.output := by
  rcases source_aware_cached_record_provenance limits actor fuel state program
      covered observation member with fresh | programmed
  · left
    rcases fresh with ⟨_sourceFresh, record, recordMember, originFresh,
      _inputExact, outputExact⟩
    rw [← outputExact]
    exact fresh_record_output_mem_master_tape tape state coherent record
      recordMember originFresh
  · right
    exact programmed.2

#print axioms empty_oracle_table_source_covered
#print axioms query_oracle_preserves_table_source_covered
#print axioms program_oracle_preserves_table_source_covered
#print axioms run_machine_preserves_table_source_covered
#print axioms source_aware_cached_records_map
#print axioms source_aware_cached_record_provenance
#print axioms fresh_record_output_mem_master_tape
#print axioms source_aware_cached_record_master_tape_or_programmed

end

end AspisK1.V7Tag73K15CachedCoordinateProvenance
