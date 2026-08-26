import AspisFormal.K1.V7Tag73OracleTableProvenance

/-!
# Table provenance for paused Tag-73 prefix executions

The concrete restoration client may pause a same-tape replay immediately
before the first occurrence of a selected squeeze input.  Existing table
provenance covered complete `runMachine` executions, but the client's
programming base in this branch is the oracle returned by `runPrefix`.

This leaf proves the matching relative-table invariant for `runPrefix` and
the exact consequence used by restoration: if neither member of a pair occurs
in the executed prefix, any lookup conflict at either member was already in
the immutable entry table.  No acceptance, randomness, target event, restore
function, or compiler conclusion is assumed.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73PrefixTableProvenance

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73AtomicPairFork
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73OracleTableProvenance

noncomputable section

/-! ## Relative coverage for the prefix interpreter -/

/-- Prefix execution uses only ordinary oracle queries, so the global
query-or-programming provenance invariant is preserved on every halt branch. -/
theorem run_prefix_preserves_table_covered_by_query_or_programming
    {Result : Type*} (controller : AdaptiveController)
    (limits : OracleLimits) (actor : QueryActor) (fuel : Nat)
    (state : OracleState) (program : OracleMachine Result)
    (covered : TableCoveredByQueryOrProgramming state) :
    TableCoveredByQueryOrProgramming
      (runPrefix controller limits actor fuel state program).oracle := by
  induction fuel generalizing state program with
  | zero =>
      cases program <;> simpa [runPrefix] using covered
  | succ fuel ih =>
      cases program with
      | pure result => simpa [runPrefix] using covered
      | abort reason => simpa [runPrefix] using covered
      | query input next =>
          simp only [runPrefix]
          cases queryResult : queryOracle controller limits actor state input with
          | error reason => simpa using covered
          | ok pair =>
              rcases pair with ⟨output, nextState⟩
              exact ih nextState (next output)
                (query_oracle_preserves_table_covered_by_query_or_programming
                  controller limits actor state nextState input output covered
                    queryResult)

theorem run_prefix_appended_history_and_table_provenance
    {Result : Type*} (controller : AdaptiveController)
    (limits : OracleLimits) (actor : QueryActor) (fuel : Nat)
    (initialTable : List TableEntry) (priorRecords : List QueryRecord)
    (state : OracleState) (program : OracleMachine Result)
    (covered : TableCoveredByInitialOrRecords initialTable priorRecords
      state.table) :
    ∃ appended : List QueryRecord,
      (runPrefix controller limits actor fuel state program).oracle.history =
          state.history ++ appended ∧
        TableCoveredByInitialOrRecords initialTable
          (priorRecords ++ appended)
          (runPrefix controller limits actor fuel state program).oracle.table := by
  induction fuel generalizing state program priorRecords with
  | zero =>
      exact ⟨[], by simp [runPrefix], by simpa [runPrefix] using covered⟩
  | succ fuel ih =>
      cases program with
      | pure result =>
          exact ⟨[], by simp [runPrefix], by simpa [runPrefix] using covered⟩
      | abort reason =>
          exact ⟨[], by simp [runPrefix], by simpa [runPrefix] using covered⟩
      | query input next =>
          cases queryResult : queryOracle controller limits actor state input with
          | error reason =>
              exact ⟨[], by simp [runPrefix, queryResult],
                by simpa [runPrefix, queryResult] using covered⟩
          | ok pair =>
              rcases pair with ⟨output, nextState⟩
              obtain ⟨headRecord, headHistory, headCovered⟩ :=
                query_oracle_success_extends_relative_table_coverage
                  controller limits actor initialTable priorRecords state
                    nextState input output covered queryResult
              obtain ⟨tail, tailHistory, tailCovered⟩ :=
                ih (priorRecords := priorRecords ++ [headRecord]) nextState
                  (next output) headCovered
              refine ⟨headRecord :: tail, ?_, ?_⟩
              · simpa [runPrefix, queryResult, headHistory,
                  List.append_assoc] using tailHistory
              · simpa [runPrefix, queryResult, List.append_assoc] using
                  tailCovered

theorem run_prefix_table_covered_by_entry_or_history_since
    {Result : Type*} (controller : AdaptiveController)
    (limits : OracleLimits) (actor : QueryActor) (fuel : Nat)
    (entryState : OracleState) (program : OracleMachine Result) :
    let final := (runPrefix controller limits actor fuel entryState
      program).oracle
    ∀ entry ∈ final.table,
      entry ∈ entryState.table ∨
        ∃ record ∈ historySince entryState final,
          record.input = entry.input ∧ record.output = entry.output := by
  let final := (runPrefix controller limits actor fuel entryState
    program).oracle
  obtain ⟨appended, exactHistory, covered⟩ :=
    run_prefix_appended_history_and_table_provenance controller limits actor
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

/-! ## A pair absent from the prefix can conflict only at entry -/

theorem no_pair_prefix_lookup_conflict_is_in_entry_table
    {Result : Type*} (controller : AdaptiveController)
    (limits : OracleLimits) (actor : QueryActor) (fuel : Nat)
    (entryState : OracleState) (program : OracleMachine Result)
    (outputInput advanceInput input : ShaInput) (entry : TableEntry)
    (noPair : firstEitherInputOccurrence outputInput advanceInput
      (historySince entryState
        (runPrefix controller limits actor fuel entryState program).oracle) =
          none)
    (isPairInput : input = outputInput ∨ input = advanceInput)
    (found : lookupEntry
      (runPrefix controller limits actor fuel entryState program).oracle
        input = some entry) :
    entry ∈ entryState.table := by
  let final := (runPrefix controller limits actor fuel entryState
    program).oracle
  have covered := run_prefix_table_covered_by_entry_or_history_since
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

#print axioms run_prefix_appended_history_and_table_provenance
#print axioms run_prefix_preserves_table_covered_by_query_or_programming
#print axioms run_prefix_table_covered_by_entry_or_history_since
#print axioms no_pair_prefix_lookup_conflict_is_in_entry_table

end

end AspisK1.V7Tag73PrefixTableProvenance
