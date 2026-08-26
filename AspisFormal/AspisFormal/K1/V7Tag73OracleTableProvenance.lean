import AspisFormal.K1.V7Tag73NoPairOccurrenceTrichotomy

/-!
# Operational provenance of Tag-73 lazy-oracle table entries

The concrete restoration client checks that both inputs of a squeeze pair are
absent from its programming base before installing fresh fork coordinates.
Absence of the pair from the recorded prover-query history is not, by itself,
enough: an earlier restoration can have inserted an entry through
`programOracle`, which changes the table and programming history but not the
query history.

This leaf proves the exact invariant needed to separate those cases.  Every
table entry produced from the empty oracle by successful queries and
programming operations is witnessed by either an actual query record or an
actual programming record.  Consequently, when neither squeeze input occurs
in the complete cumulative history, any lookup conflict has to be a reuse of
a prior programmed input.  A one-entry executable counterexample proves that
this last case cannot be eliminated from query-history absence alone.

There is no acceptance, probability, trace-cover, compiler, or extraction
premise here.  The concrete client scans only the node-local
`historySince proverEntryOracle proverFinalOracle`, not the complete cumulative
history.  Its remaining protocol-specific obligation is therefore slightly
broader: prove that the requested pair is absent from the node's entry table,
or causally charge reuse of an ancestor queried or programmed input.  This
module deliberately does not collapse that segmented-history obligation into
the full-history result below.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73OracleTableProvenance

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73AtomicPairFork
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy

/-! ## Table coverage by observable operational records -/

/-- Every table entry is justified by a matching query or programming record.
Actors and origins are intentionally retained in the witnesses rather than
erased from the underlying histories. -/
def TableCoveredByQueryOrProgramming (state : OracleState) : Prop :=
  ∀ entry ∈ state.table,
    (∃ record ∈ state.history,
      record.input = entry.input ∧ record.output = entry.output) ∨
    (∃ record ∈ state.programmingHistory,
      record.input = entry.input ∧ record.output = entry.output)

theorem empty_oracle_table_covered_by_query_or_programming :
    TableCoveredByQueryOrProgramming emptyOracle := by
  simp [TableCoveredByQueryOrProgramming, emptyOracle]

/-- A successful query preserves coverage.  A cached call only appends its
history record; a fresh call appends a matching table and query record. -/
theorem query_oracle_preserves_table_covered_by_query_or_programming
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (state nextState : OracleState)
    (input : ShaInput) (output : ShaOutput)
    (covered : TableCoveredByQueryOrProgramming state)
    (success : queryOracle controller limits actor state input =
      .ok (output, nextState)) :
    TableCoveredByQueryOrProgramming nextState := by
  unfold queryOracle at success
  split at success <;> try contradiction
  next _ =>
    split at success
    next entry found =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at success
      rcases success with ⟨rfl, rfl⟩
      intro candidate member
      rcases covered candidate member with queryWitness | programmingWitness
      · rcases queryWitness with ⟨record, recordMember, inputEq, outputEq⟩
        exact Or.inl ⟨record, List.mem_append_left _ recordMember,
          inputEq, outputEq⟩
      · exact Or.inr programmingWitness
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
          · rcases covered candidate old with
                queryWitness | programmingWitness
            · rcases queryWitness with
                ⟨record, recordMember, inputEq, outputEq⟩
              exact Or.inl ⟨record,
                List.mem_append_left _ recordMember, inputEq, outputEq⟩
            · exact Or.inr programmingWitness
          · let newRecord : QueryRecord :=
              { input := input
                output := answer
                actor := actor
                origin := .fresh }
            exact Or.inl ⟨newRecord,
              List.mem_append_right _ (by simp [newRecord]), rfl, rfl⟩

/-- A successful programming operation preserves coverage and witnesses its
new table entry in the programming history, without pretending that it was an
oracle query. -/
theorem program_oracle_preserves_table_covered_by_query_or_programming
    (limits : OracleLimits) (actor : QueryActor)
    (state nextState : OracleState) (point : Programming)
    (covered : TableCoveredByQueryOrProgramming state)
    (success : programOracle limits actor state point = .ok nextState) :
    TableCoveredByQueryOrProgramming nextState := by
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
      · rcases covered candidate old with queryWitness | programmingWitness
        · exact Or.inl queryWitness
        · rcases programmingWitness with
            ⟨record, recordMember, inputEq, outputEq⟩
          exact Or.inr ⟨record, List.mem_append_left _ recordMember,
            inputEq, outputEq⟩
      · let newRecord : ProgrammingRecord :=
          { input := point.input
            output := point.output
            actor := actor }
        exact Or.inr ⟨newRecord,
          List.mem_append_right _ (by simp [newRecord]), rfl, rfl⟩

/-- A complete fuel-bounded machine run preserves the invariant on return,
oracle abort, and timeout. -/
theorem run_machine_preserves_table_covered_by_query_or_programming
    {Result : Type*} (controller : AdaptiveController)
    (limits : OracleLimits) (actor : QueryActor) (fuel : Nat)
    (state : OracleState) (program : OracleMachine Result)
    (covered : TableCoveredByQueryOrProgramming state) :
    TableCoveredByQueryOrProgramming
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
                (query_oracle_preserves_table_covered_by_query_or_programming
                  controller limits actor state nextState input output covered
                    queryResult)

/-! ## Exact segment-relative table provenance -/

/-- Relative coverage used while proving a single machine segment.  Entries
already present at segment entry remain classified separately from entries
created by the segment's chronological query records. -/
def TableCoveredByInitialOrRecords
    (initialTable : List TableEntry) (records : List QueryRecord)
    (currentTable : List TableEntry) : Prop :=
  ∀ entry ∈ currentTable,
    entry ∈ initialTable ∨
      ∃ record ∈ records,
        record.input = entry.input ∧ record.output = entry.output

theorem initial_table_covered_by_initial_or_empty_records
    (table : List TableEntry) :
    TableCoveredByInitialOrRecords table [] table := by
  intro entry member
  exact Or.inl member

/-- One successful query has one exact appended history record and preserves
relative table coverage. -/
theorem query_oracle_success_extends_relative_table_coverage
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (initialTable : List TableEntry)
    (priorRecords : List QueryRecord) (state nextState : OracleState)
    (input : ShaInput) (output : ShaOutput)
    (covered : TableCoveredByInitialOrRecords initialTable priorRecords
      state.table)
    (success : queryOracle controller limits actor state input =
      .ok (output, nextState)) :
    ∃ record : QueryRecord,
      nextState.history = state.history ++ [record] ∧
      TableCoveredByInitialOrRecords initialTable
        (priorRecords ++ [record]) nextState.table := by
  unfold queryOracle at success
  split at success <;> try contradiction
  next _ =>
    split at success
    next entry found =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at success
      rcases success with ⟨rfl, rfl⟩
      let record : QueryRecord :=
        { input := input
          output := entry.output
          actor := actor
          origin := cachedOrigin entry.source }
      refine ⟨record, rfl, ?_⟩
      intro candidate member
      rcases covered candidate member with initialMember | queryWitness
      · exact Or.inl initialMember
      · rcases queryWitness with ⟨prior, priorMember, inputEq, outputEq⟩
        exact Or.inr ⟨prior, List.mem_append_left _ priorMember,
          inputEq, outputEq⟩
    next missing =>
      split at success <;> try contradiction
      next _ =>
        split at success
        next _ => contradiction
        next answer answered =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at success
          rcases success with ⟨rfl, rfl⟩
          let record : QueryRecord :=
            { input := input
              output := answer
              actor := actor
              origin := .fresh }
          refine ⟨record, rfl, ?_⟩
          intro candidate member
          simp only [List.mem_append, List.mem_singleton] at member
          rcases member with old | rfl
          · rcases covered candidate old with initialMember | queryWitness
            · exact Or.inl initialMember
            · rcases queryWitness with
                ⟨prior, priorMember, inputEq, outputEq⟩
              exact Or.inr ⟨prior,
                List.mem_append_left _ priorMember, inputEq, outputEq⟩
          · exact Or.inr ⟨record,
              List.mem_append_right _ (by simp [record]), rfl, rfl⟩

/-- Exact chronological decomposition and table provenance for an arbitrary
fuel-bounded machine segment. -/
theorem run_machine_appended_history_and_table_provenance
    {Result : Type*} (controller : AdaptiveController)
    (limits : OracleLimits) (actor : QueryActor) (fuel : Nat)
    (initialTable : List TableEntry) (priorRecords : List QueryRecord)
    (state : OracleState) (program : OracleMachine Result)
    (covered : TableCoveredByInitialOrRecords initialTable priorRecords
      state.table) :
    ∃ appended : List QueryRecord,
      (runMachine controller limits actor fuel state program).oracle.history =
          state.history ++ appended ∧
        TableCoveredByInitialOrRecords initialTable
          (priorRecords ++ appended)
          (runMachine controller limits actor fuel state program).oracle.table := by
  induction fuel generalizing state program priorRecords with
  | zero =>
      cases program <;>
        change ∃ appended,
          state.history = state.history ++ appended ∧
            TableCoveredByInitialOrRecords initialTable
              (priorRecords ++ appended) state.table <;>
        exact ⟨[], by simp, by simpa using covered⟩
  | succ fuel ih =>
      cases program with
      | pure result =>
          change ∃ appended,
            state.history = state.history ++ appended ∧
              TableCoveredByInitialOrRecords initialTable
                (priorRecords ++ appended) state.table
          exact ⟨[], by simp, by simpa using covered⟩
      | abort reason =>
          change ∃ appended,
            state.history = state.history ++ appended ∧
              TableCoveredByInitialOrRecords initialTable
                (priorRecords ++ appended) state.table
          exact ⟨[], by simp, by simpa using covered⟩
      | query input next =>
          cases queryResult : queryOracle controller limits actor state input with
          | error reason =>
              simp only [runMachine, queryResult]
              exact ⟨[], by simp, by simpa using covered⟩
          | ok pair =>
              rcases pair with ⟨output, nextState⟩
              simp only [runMachine, queryResult]
              obtain ⟨headRecord, headHistory, headCovered⟩ :=
                query_oracle_success_extends_relative_table_coverage
                  controller limits actor initialTable priorRecords state
                    nextState input output covered queryResult
              obtain ⟨tail, tailHistory, tailCovered⟩ :=
                ih (priorRecords := priorRecords ++ [headRecord]) nextState
                  (next output) headCovered
              refine ⟨headRecord :: tail, ?_, ?_⟩
              · calc
                  (runMachine controller limits actor fuel nextState
                      (next output)).oracle.history =
                      nextState.history ++ tail := tailHistory
                  _ = (state.history ++ [headRecord]) ++ tail := by
                    rw [headHistory]
                  _ = state.history ++ (headRecord :: tail) := by simp
              · simpa [List.append_assoc] using tailCovered

/-- Specialization with the actual entry table and no prior segment records.
It produces coverage by exactly the `historySince` list exported by the
machine run. -/
theorem run_machine_table_covered_by_entry_or_history_since
    {Result : Type*} (controller : AdaptiveController)
    (limits : OracleLimits) (actor : QueryActor) (fuel : Nat)
    (entryState : OracleState) (program : OracleMachine Result) :
    let final := (runMachine controller limits actor fuel entryState
      program).oracle
    ∀ entry ∈ final.table,
      entry ∈ entryState.table ∨
        ∃ record ∈ historySince entryState final,
          record.input = entry.input ∧ record.output = entry.output := by
  let final := (runMachine controller limits actor fuel entryState
    program).oracle
  obtain ⟨appended, exactHistory, covered⟩ :=
    run_machine_appended_history_and_table_provenance controller limits actor
      fuel entryState.table [] entryState program
        (initial_table_covered_by_initial_or_empty_records entryState.table)
  have exactSince : historySince entryState final = appended := by
    unfold historySince
    rw [exactHistory]
    simp
  change ∀ entry ∈ final.table,
    entry ∈ entryState.table ∨
      ∃ record ∈ historySince entryState final,
        record.input = entry.input ∧ record.output = entry.output
  intro entry member
  rcases covered entry member with initialMember | queryWitness
  · exact Or.inl initialMember
  · rcases queryWitness with ⟨record, recordMember, inputEq, outputEq⟩
    refine Or.inr ⟨record, ?_, inputEq, outputEq⟩
    rw [exactSince]
    exact recordMember

/-- This is the exact ancestor-table classification required by the concrete
client's node-local occurrence scan.  If neither pair input occurs in this
machine segment, a final lookup conflict must already have existed in the
segment's entry table. -/
theorem no_pair_segment_lookup_conflict_is_in_entry_table
    {Result : Type*} (controller : AdaptiveController)
    (limits : OracleLimits) (actor : QueryActor) (fuel : Nat)
    (entryState : OracleState) (program : OracleMachine Result)
    (outputInput advanceInput input : ShaInput) (entry : TableEntry)
    (noPair : firstEitherInputOccurrence outputInput advanceInput
      (historySince entryState
        (runMachine controller limits actor fuel entryState program).oracle) =
          none)
    (isPairInput : input = outputInput ∨ input = advanceInput)
    (found : lookupEntry
      (runMachine controller limits actor fuel entryState program).oracle
        input = some entry) :
    entry ∈ entryState.table := by
  let final := (runMachine controller limits actor fuel entryState
    program).oracle
  have covered := run_machine_table_covered_by_entry_or_history_since
    controller limits actor fuel entryState program
  unfold lookupEntry at found
  have foundSpec := List.find?_eq_some_iff_append.mp found
  have entryInput : entry.input = input :=
    of_decide_eq_true foundSpec.1
  have entryMember : entry ∈ final.table :=
    List.mem_of_find?_eq_some found
  rcases covered entry entryMember with initialMember | queryWitness
  · exact initialMember
  · rcases queryWitness with ⟨record, member, inputEq, _outputEq⟩
    have absent := (first_either_input_occurrence_none_iff outputInput
      advanceInput (historySince entryState final)).mp noPair record member
    have recordInput : record.input = input := inputEq.trans entryInput
    rcases isPairInput with rfl | rfl
    · exact (absent.1 recordInput).elim
    · exact (absent.2 recordInput).elim

/-- Iterated explicit programming preserves the same invariant. -/
theorem program_many_preserves_table_covered_by_query_or_programming
    (limits : OracleLimits) (actor : QueryActor)
    (points : List Programming) (state nextState : OracleState)
    (covered : TableCoveredByQueryOrProgramming state)
    (success : programMany limits actor state points = .ok nextState) :
    TableCoveredByQueryOrProgramming nextState := by
  induction points generalizing state with
  | nil =>
      simp only [programMany, Except.ok.injEq] at success
      subst nextState
      exact covered
  | cons point rest ih =>
      simp only [programMany] at success
      cases firstResult : programOracle limits actor state point with
      | error reason => simp [firstResult] at success
      | ok afterFirst =>
          rw [firstResult] at success
          exact ih afterFirst
            (program_oracle_preserves_table_covered_by_query_or_programming
              limits actor state afterFirst point covered firstResult)
            success

/-! ## Lookup provenance and the exact no-pair residual case -/

theorem lookup_entry_some_has_query_or_programming_provenance
    (state : OracleState) (input : ShaInput)
    (entry : TableEntry)
    (covered : TableCoveredByQueryOrProgramming state)
    (found : lookupEntry state input = some entry) :
    entry.input = input ∧
      ((∃ record ∈ state.history,
          record.input = input ∧ record.output = entry.output) ∨
        (∃ record ∈ state.programmingHistory,
          record.input = input ∧ record.output = entry.output)) := by
  unfold lookupEntry at found
  have foundSpec := List.find?_eq_some_iff_append.mp found
  have entryInput : entry.input = input :=
    of_decide_eq_true foundSpec.1
  have entryMember : entry ∈ state.table :=
    List.mem_of_find?_eq_some found
  refine ⟨entryInput, ?_⟩
  rcases covered entry entryMember with queryWitness | programmingWitness
  · rcases queryWitness with ⟨record, member, inputEq, outputEq⟩
    exact Or.inl ⟨record, member, inputEq.trans entryInput, outputEq⟩
  · rcases programmingWitness with ⟨record, member, inputEq, outputEq⟩
    exact Or.inr ⟨record, member, inputEq.trans entryInput, outputEq⟩

/-- If neither member of the pair occurred in the complete query history, a
lookup conflict at either input can only be an earlier programming record. -/
theorem no_pair_lookup_conflict_is_prior_programming
    (state : OracleState) (outputInput advanceInput input : ShaInput)
    (entry : TableEntry)
    (covered : TableCoveredByQueryOrProgramming state)
    (noPair : firstEitherInputOccurrence outputInput advanceInput
      state.history = none)
    (isPairInput : input = outputInput ∨ input = advanceInput)
    (found : lookupEntry state input = some entry) :
    ∃ record ∈ state.programmingHistory,
      record.input = input ∧ record.output = entry.output := by
  have absent := (first_either_input_occurrence_none_iff outputInput
    advanceInput state.history).mp noPair
  rcases (lookup_entry_some_has_query_or_programming_provenance state input
    entry covered found).2 with queryWitness | programmingWitness
  · rcases queryWitness with ⟨record, member, inputEq, outputEq⟩
    have pairAbsent := absent record member
    rcases isPairInput with rfl | rfl
    · exact (pairAbsent.1 inputEq).elim
    · exact (pairAbsent.2 inputEq).elim
  · exact programmingWitness

theorem no_pair_output_lookup_conflict_is_prior_programming
    (state : OracleState) (outputInput advanceInput : ShaInput)
    (entry : TableEntry)
    (covered : TableCoveredByQueryOrProgramming state)
    (noPair : firstEitherInputOccurrence outputInput advanceInput
      state.history = none)
    (found : lookupEntry state outputInput = some entry) :
    ∃ record ∈ state.programmingHistory,
      record.input = outputInput ∧ record.output = entry.output := by
  exact no_pair_lookup_conflict_is_prior_programming state outputInput
    advanceInput outputInput entry covered noPair (Or.inl rfl) found

theorem no_pair_advance_lookup_conflict_is_prior_programming
    (state : OracleState) (outputInput advanceInput : ShaInput)
    (entry : TableEntry)
    (covered : TableCoveredByQueryOrProgramming state)
    (noPair : firstEitherInputOccurrence outputInput advanceInput
      state.history = none)
    (found : lookupEntry state advanceInput = some entry) :
    ∃ record ∈ state.programmingHistory,
      record.input = advanceInput ∧ record.output = entry.output := by
  exact no_pair_lookup_conflict_is_prior_programming state outputInput
    advanceInput advanceInput entry covered noPair (Or.inr rfl) found

/-- This form matches the executable `.isSome` checks made immediately before
pair programming. -/
theorem no_pair_defined_input_has_prior_programming_record
    (state : OracleState) (outputInput advanceInput input : ShaInput)
    (covered : TableCoveredByQueryOrProgramming state)
    (noPair : firstEitherInputOccurrence outputInput advanceInput
      state.history = none)
    (isPairInput : input = outputInput ∨ input = advanceInput)
    (defined : (lookupEntry state input).isSome = true) :
    ∃ entry : TableEntry, ∃ record ∈ state.programmingHistory,
      record.input = input ∧ record.output = entry.output ∧
        lookupEntry state input = some entry := by
  cases found : lookupEntry state input with
  | none => simp [found] at defined
  | some entry =>
      obtain ⟨record, member, recordInput, recordOutput⟩ :=
        no_pair_lookup_conflict_is_prior_programming state outputInput
          advanceInput input entry covered noPair isPairInput found
      exact ⟨entry, record, member, recordInput, recordOutput, rfl⟩

/-! ## Executable obstruction to a query-history-only freshness proof -/

def singletonProgrammedOracle (actor : QueryActor)
    (input : ShaInput) (output : ShaOutput) : OracleState where
  table := [{ input := input, output := output, source := .programmed }]
  history := []
  programmingHistory := [{ input := input, output := output, actor := actor }]
  totalCalls := 0
  freshCalls := 0

theorem singleton_programmed_oracle_is_operationally_covered
    (actor : QueryActor) (input : ShaInput) (output : ShaOutput) :
    TableCoveredByQueryOrProgramming
      (singletonProgrammedOracle actor input output) := by
  simp [TableCoveredByQueryOrProgramming, singletonProgrammedOracle]

/-- Even an empty query history can coexist with a defined pair input.  The
witness is not malformed hidden table state: it carries the exact matching
programming record required by the operational invariant. -/
theorem query_history_pair_absence_does_not_imply_lookup_freshness
    (actor : QueryActor) (outputInput advanceInput : ShaInput)
    (output : ShaOutput) :
    let state := singletonProgrammedOracle actor outputInput output
    firstEitherInputOccurrence outputInput advanceInput state.history = none ∧
      (lookupEntry state outputInput).isSome = true ∧
      TableCoveredByQueryOrProgramming state := by
  dsimp [singletonProgrammedOracle]
  exact ⟨rfl, by simp [lookupEntry],
    singleton_programmed_oracle_is_operationally_covered actor outputInput
      output⟩

/-- A queried entry can likewise predate the node-local segment scanned by the
restoration client.  Taking the same operational state as both segment
boundaries gives an empty `historySince` even though the entry table still
contains the queried pair input. -/
def singletonQueriedOracle (actor : QueryActor)
    (input : ShaInput) (output : ShaOutput) : OracleState where
  table := [{ input := input, output := output, source := .fresh }]
  history :=
    [{ input := input, output := output, actor := actor, origin := .fresh }]
  programmingHistory := []
  totalCalls := 1
  freshCalls := 1

theorem singleton_queried_oracle_is_operationally_covered
    (actor : QueryActor) (input : ShaInput) (output : ShaOutput) :
    TableCoveredByQueryOrProgramming
      (singletonQueriedOracle actor input output) := by
  simp [TableCoveredByQueryOrProgramming, singletonQueriedOracle]

theorem node_local_pair_absence_does_not_exclude_ancestor_query
    (actor : QueryActor) (outputInput advanceInput : ShaInput)
    (output : ShaOutput) :
    let state := singletonQueriedOracle actor outputInput output
    firstEitherInputOccurrence outputInput advanceInput
        (historySince state state) = none ∧
      (lookupEntry state outputInput).isSome = true ∧
      TableCoveredByQueryOrProgramming state := by
  simp [singletonQueriedOracle, historySince, lookupEntry,
    TableCoveredByQueryOrProgramming, firstEitherInputOccurrence]

def twoPointProgrammingLimits : OracleLimits where
  totalCalls := 0
  freshCalls := 0
  programmedPoints := 2

/-- Reusing a previously programmed input is a deterministic programming
conflict, regardless of the replacement output.  In particular, blindly
requesting the same `(node, transition)` restoration twice cannot be charged
to a random-oracle collision event.  The concrete extractor schedule must
prove that successful restoration targets are unique (or handle the second
request as an ordinary deterministic failure). -/
theorem duplicate_programmed_input_aborts_deterministically
    (actor : QueryActor) (input : ShaInput)
    (oldOutput replacementOutput : ShaOutput) :
    programOracle twoPointProgrammingLimits actor
      (singletonProgrammedOracle actor input oldOutput)
      { input := input, output := replacementOutput } =
        .error .programmingConflict := by
  apply programming_an_existing_point_aborts
  · simp [twoPointProgrammingLimits, singletonProgrammedOracle]
  · simp [singletonProgrammedOracle, lookupEntry]

#print axioms empty_oracle_table_covered_by_query_or_programming
#print axioms query_oracle_preserves_table_covered_by_query_or_programming
#print axioms program_oracle_preserves_table_covered_by_query_or_programming
#print axioms run_machine_preserves_table_covered_by_query_or_programming
#print axioms query_oracle_success_extends_relative_table_coverage
#print axioms run_machine_appended_history_and_table_provenance
#print axioms run_machine_table_covered_by_entry_or_history_since
#print axioms no_pair_segment_lookup_conflict_is_in_entry_table
#print axioms program_many_preserves_table_covered_by_query_or_programming
#print axioms lookup_entry_some_has_query_or_programming_provenance
#print axioms no_pair_lookup_conflict_is_prior_programming
#print axioms no_pair_defined_input_has_prior_programming_record
#print axioms query_history_pair_absence_does_not_imply_lookup_freshness
#print axioms node_local_pair_absence_does_not_exclude_ancestor_query
#print axioms duplicate_programmed_input_aborts_deterministically

end AspisK1.V7Tag73OracleTableProvenance
