import AspisFormal.K1.V7Tag73SharedOracleVerifierRunner
import AspisFormal.K1.V7Tag73SequentialOracleRuns

/-!
# Deterministic shared-oracle stability for the Tag-73 verifier phase

This module studies one concrete adversary-first, verifier-second execution.
The verifier receives both the frozen adversary state used as grinding evidence
and that same state's lazy-oracle table as its initial shared state.

The deterministic result is intentionally two-sided:

* table stability is exactly the absence of verifier records tagged `fresh`;
* when stability fails, every appended table entry is paired, in order, with
  a verifier history record tagged `fresh`, and its input was absent from the
  frozen adversary table.

The `1511` corollary is a concrete machine-fuel bound for the full-256 Tag-73
verifier runner.  The separately typed 208-bit Merkle work is not part of this
runner or bound.  Nothing here says acceptance implies stability, classifies a
protocol failure as this event, or supplies a probabilistic/compiler premise.
In particular, a fresh verifier entry at `H(S || 0x01)` is not identified with
a singleton 256-bit prediction event: the distinct `H(S || 0x02)` call and the
bounded decoder remain separate operational facts.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73VerifierOracleStability

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73ResourceLazyOracle
open AspisK1.V7Tag73SharedOracleVerifierRunner
open AspisK1.V7Tag73SequentialOracleRuns
open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling

noncomputable section

abbrev OracleTableEntry := AspisK1.V7FsAokExperiment.TableEntry

/-! ## Exact fresh suffixes -/

/-- Turn a history record known to be fresh into the table entry created by
that call.  The definition itself sets the source tag; the theorems below
prove that this is exactly the entry appended by `queryOracle`. -/
def freshTableEntryOfRecord (record : QueryRecord) : OracleTableEntry where
  input := record.input
  output := record.output
  source := .fresh

/-- Fresh verifier records, retaining their original call order. -/
def verifierFreshRecords (before after : OracleState) : List QueryRecord :=
  (historySince before after).filter fun record => record.origin = .fresh

/-- The table suffix predicted by the fresh verifier records. -/
def verifierFreshTableEntries (before after : OracleState) :
    List OracleTableEntry :=
  (verifierFreshRecords before after).map freshTableEntryOfRecord

/-- The verifier phase is table-stable precisely when it appends no lazy-ROM
entry to the table frozen at adversary halt. -/
def VerifierPhaseTableStable (before after : OracleState) : Prop :=
  after.table = before.table

/-- The deterministic bad event complementary to table stability.  It is an
observable machine event, not an assertion about accepting transcripts. -/
def VerifierPhaseFreshnessFailure (before after : OracleState) : Prop :=
  ∃ record ∈ historySince before after, record.origin = .fresh

private theorem table_find_none_of_append_none
    (initialTable suffix : List OracleTableEntry) (input : ShaInput)
    (missing :
      (initialTable ++ suffix).find?
          (fun entry => entry.input = input) = none) :
    initialTable.find? (fun entry => entry.input = input) = none := by
  induction initialTable with
  | nil => rfl
  | cons entry rest ih =>
      by_cases hit : entry.input = input
      · simp [hit] at missing
      · simp only [List.cons_append, List.find?_cons, hit, ↓reduceIte] at missing ⊢
        exact ih missing

private theorem lookup_entry_none_of_table_extension
    (before after : OracleState) (suffix : List OracleTableEntry)
    (extension : after.table = before.table ++ suffix) (input : ShaInput)
    (missing : lookupEntry after input = none) :
    lookupEntry before input = none := by
  unfold lookupEntry at missing ⊢
  rw [extension] at missing
  exact table_find_none_of_append_none before.table suffix input missing

/-- One successful lazy-oracle call either reuses the table or appends exactly
one fresh entry.  In the latter case its history record carries the same input
and output and the queried input was absent immediately before the call. -/
theorem query_oracle_success_table_history_cases
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (state nextState : OracleState)
    (input : ShaInput) (output : ShaOutput)
    (success : queryOracle controller limits actor state input =
      .ok (output, nextState)) :
    ∃ record : QueryRecord,
      nextState.history = state.history ++ [record] ∧
      record.input = input ∧ record.output = output ∧ record.actor = actor ∧
      ((record.origin = .fresh ∧
          nextState.table = state.table ++ [freshTableEntryOfRecord record] ∧
          lookupEntry state input = none) ∨
        (record.origin ≠ .fresh ∧ nextState.table = state.table)) := by
  unfold queryOracle at success
  split at success <;> try contradiction
  next _ =>
    split at success
    next entry found =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at success
      rcases success with ⟨rfl, rfl⟩
      refine ⟨
        { input := input, output := entry.output, actor := actor,
          origin := cachedOrigin entry.source },
        rfl, rfl, rfl, rfl, Or.inr ⟨?_, rfl⟩⟩
      cases entry.source <;> simp [cachedOrigin]
    next missing =>
      split at success <;> try contradiction
      next _ =>
        split at success
        next _ => contradiction
        next answer answered =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at success
          rcases success with ⟨rfl, rfl⟩
          refine ⟨
            { input := input, output := answer, actor := actor,
              origin := .fresh },
            rfl, rfl, rfl, rfl, Or.inl ⟨rfl, ?_, missing⟩⟩
          rfl

/-! ## Generic run invariant used by the concrete two-phase execution -/

/-- Exact operational invariant for an arbitrary `OracleMachine` run.  The
fresh table suffix is the ordered projection of precisely the fresh records;
all records carry the concrete run actor; every fresh input was absent from
the supplied initial table; and successful records cannot outnumber steps. -/
theorem run_machine_fresh_extension_data
    {Result : Type*} (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (program : OracleMachine Result) :
    ∃ appended : List QueryRecord,
      (runMachine controller limits actor fuel state program).oracle.history =
          state.history ++ appended ∧
      (runMachine controller limits actor fuel state program).oracle.table =
          state.table ++
            ((appended.filter fun record => record.origin = .fresh).map
              freshTableEntryOfRecord) ∧
      (∀ record ∈ appended,
        record.actor = actor ∧
          (record.origin = .fresh →
            lookupEntry state record.input = none)) ∧
      appended.length ≤
        (runMachine controller limits actor fuel state program).steps := by
  induction fuel generalizing state program with
  | zero =>
      cases program <;> exact ⟨[], by simp [runMachine], by simp [runMachine],
        by simp, by simp [runMachine]⟩
  | succ fuel ih =>
      cases program with
      | pure result =>
          exact ⟨[], by simp [runMachine], by simp [runMachine], by simp,
            by simp [runMachine]⟩
      | abort reason =>
          exact ⟨[], by simp [runMachine], by simp [runMachine], by simp,
            by simp [runMachine]⟩
      | query input next =>
          cases queryResult : queryOracle controller limits actor state input with
          | error reason =>
              exact ⟨[], by simp [runMachine, queryResult],
                by simp [runMachine, queryResult], by simp,
                by simp [runMachine, queryResult]⟩
          | ok pair =>
              rcases pair with ⟨output, nextState⟩
              obtain ⟨head, headHistory, headInput, headOutput, headActor,
                  headCase⟩ :=
                query_oracle_success_table_history_cases controller limits actor
                  state nextState input output queryResult
              obtain ⟨tail, tailHistory, tailTable, tailProperties, tailLength⟩ :=
                ih nextState (next output)
              refine ⟨head :: tail, ?_, ?_, ?_, ?_⟩
              · calc
                  (runMachine controller limits actor (fuel + 1) state
                      (.query input next)).oracle.history =
                      (runMachine controller limits actor fuel nextState
                        (next output)).oracle.history := by
                    simp [runMachine, queryResult]
                  _ = nextState.history ++ tail := tailHistory
                  _ = (state.history ++ [head]) ++ tail := by rw [headHistory]
                  _ = state.history ++ (head :: tail) := by simp
              · rcases headCase with fresh | cached
                · rcases fresh with ⟨headFresh, headTable, headMissing⟩
                  calc
                    (runMachine controller limits actor (fuel + 1) state
                        (.query input next)).oracle.table =
                        (runMachine controller limits actor fuel nextState
                          (next output)).oracle.table := by
                      simp [runMachine, queryResult]
                    _ = nextState.table ++
                        ((tail.filter fun record => record.origin = .fresh).map
                          freshTableEntryOfRecord) := tailTable
                    _ = (state.table ++ [freshTableEntryOfRecord head]) ++
                        ((tail.filter fun record => record.origin = .fresh).map
                          freshTableEntryOfRecord) := by rw [headTable]
                    _ = state.table ++
                        (((head :: tail).filter fun record =>
                            record.origin = .fresh).map
                          freshTableEntryOfRecord) := by
                      simp [headFresh, List.append_assoc]
                · rcases cached with ⟨headNotFresh, headTable⟩
                  calc
                    (runMachine controller limits actor (fuel + 1) state
                        (.query input next)).oracle.table =
                        (runMachine controller limits actor fuel nextState
                          (next output)).oracle.table := by
                      simp [runMachine, queryResult]
                    _ = nextState.table ++
                        ((tail.filter fun record => record.origin = .fresh).map
                          freshTableEntryOfRecord) := tailTable
                    _ = state.table ++
                        ((tail.filter fun record => record.origin = .fresh).map
                          freshTableEntryOfRecord) := by rw [headTable]
                    _ = state.table ++
                        (((head :: tail).filter fun record =>
                            record.origin = .fresh).map
                          freshTableEntryOfRecord) := by simp [headNotFresh]
              · intro record member
                simp only [List.mem_cons] at member
                rcases member with rfl | member
                · exact ⟨headActor, fun fresh => by
                    rcases headCase with headCase | headCase
                    · simpa [headInput] using headCase.2.2
                    · exact (headCase.1 fresh).elim⟩
                · have tailProperty := tailProperties record member
                  refine ⟨tailProperty.1, fun fresh => ?_⟩
                  have nextMissing := tailProperty.2 fresh
                  rcases headCase with headCase | headCase
                  · exact lookup_entry_none_of_table_extension state nextState
                      [freshTableEntryOfRecord head] headCase.2.1 record.input
                        nextMissing
                  · exact lookup_entry_none_of_table_extension state nextState
                      [] (by simpa using headCase.2) record.input nextMissing
              · have tailStep :
                    (runMachine controller limits actor fuel nextState
                      (next output)).steps + 1 =
                    (runMachine controller limits actor (fuel + 1) state
                      (.query input next)).steps := by
                    simp [runMachine, queryResult]
                simp only [List.length_cons]
                omega

/-- Exact table, history, actor, freshness, and step invariant phrased using
the public `historySince` and fresh-suffix definitions. -/
theorem run_machine_exact_fresh_extension
    {Result : Type*} (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (program : OracleMachine Result) :
    let final := (runMachine controller limits actor fuel state program).oracle
    final.table = state.table ++ verifierFreshTableEntries state final ∧
      (∀ record ∈ historySince state final,
        record.actor = actor ∧
          (record.origin = .fresh →
            lookupEntry state record.input = none)) ∧
      (historySince state final).length ≤
        (runMachine controller limits actor fuel state program).steps := by
  dsimp only
  obtain ⟨appended, history, table, properties, length⟩ :=
    run_machine_fresh_extension_data controller limits actor fuel state program
  have since :
      historySince state
          (runMachine controller limits actor fuel state program).oracle =
        appended := by
    simp [historySince, history]
  rw [since]
  exact ⟨by simpa [verifierFreshTableEntries, verifierFreshRecords, since] using table,
    properties, length⟩

/-! ## Stability and failure are exact complements -/

theorem run_machine_table_stable_iff_no_fresh_records
    {Result : Type*} (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (program : OracleMachine Result) :
    let final := (runMachine controller limits actor fuel state program).oracle
    VerifierPhaseTableStable state final ↔
      ∀ record ∈ historySince state final, record.origin ≠ .fresh := by
  dsimp only
  have exactExtension :=
    (run_machine_exact_fresh_extension controller limits actor fuel state
      program).1
  let final := (runMachine controller limits actor fuel state program).oracle
  let entries := verifierFreshTableEntries state final
  have extension : final.table = state.table ++ entries := exactExtension
  have stableIffEntries :
      VerifierPhaseTableStable state final ↔ entries = [] := by
    constructor
    · intro stable
      have lengths := congrArg List.length (extension.symm.trans stable)
      simp only [List.length_append] at lengths
      have zero : entries.length = 0 := by omega
      exact List.length_eq_zero_iff.mp zero
    · intro empty
      unfold VerifierPhaseTableStable
      simpa [empty] using extension
  rw [stableIffEntries]
  change entries = [] ↔
    ∀ record ∈ historySince state final, record.origin ≠ .fresh
  simp [entries, verifierFreshTableEntries, verifierFreshRecords]

theorem run_machine_freshness_failure_iff_not_stable
    {Result : Type*} (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (program : OracleMachine Result) :
    let final := (runMachine controller limits actor fuel state program).oracle
    VerifierPhaseFreshnessFailure state final ↔
      ¬ VerifierPhaseTableStable state final := by
  dsimp only
  have stableIff := run_machine_table_stable_iff_no_fresh_records controller
    limits actor fuel state program
  constructor
  · rintro ⟨record, member, fresh⟩ stable
    exact (stableIff.mp stable record member) fresh
  · intro notStable
    by_contra noFailure
    apply notStable
    apply stableIff.mpr
    intro record member fresh
    apply noFailure
    exact ⟨record, member, fresh⟩

theorem run_machine_new_table_entries_exact
    {Result : Type*} (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (program : OracleMachine Result) :
    let final := (runMachine controller limits actor fuel state program).oracle
    final.table.drop state.table.length =
      verifierFreshTableEntries state final := by
  dsimp only
  have extension :=
    (run_machine_exact_fresh_extension controller limits actor fuel state
      program).1
  rw [extension]
  simp

/-- Every actual new table entry has a matching same-order history record from
this run.  Its source and record origin are both fresh, and its input was
absent from the table supplied at the beginning of the run. -/
theorem run_machine_new_entry_is_fresh_and_initially_absent
    {Result : Type*} (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (program : OracleMachine Result) (entry : OracleTableEntry)
    (member : entry ∈
      (runMachine controller limits actor fuel state program).oracle.table.drop
        state.table.length) :
    entry.source = .fresh ∧ lookupEntry state entry.input = none ∧
      ∃ record ∈ historySince state
          (runMachine controller limits actor fuel state program).oracle,
        record.actor = actor ∧ record.origin = .fresh ∧
          record.input = entry.input ∧ record.output = entry.output ∧
          entry = freshTableEntryOfRecord record := by
  have exactRun :=
    run_machine_exact_fresh_extension controller limits actor fuel state program
  have freshEntries :=
    run_machine_new_table_entries_exact controller limits actor fuel state program
  rw [freshEntries] at member
  unfold verifierFreshTableEntries verifierFreshRecords at member
  obtain ⟨record, recordFiltered, rfl⟩ := List.mem_map.mp member
  have filtered := List.mem_filter.mp recordFiltered
  have recordFresh : record.origin = .fresh :=
    of_decide_eq_true filtered.2
  have recordProperty := exactRun.2.1 record filtered.1
  exact ⟨rfl, recordProperty.2 recordFresh,
    ⟨record, filtered.1, recordProperty.1, recordFresh, rfl, rfl, rfl⟩⟩

theorem run_machine_new_entry_count_le_steps
    {Result : Type*} (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (program : OracleMachine Result) :
    ((runMachine controller limits actor fuel state program).oracle.table.drop
      state.table.length).length ≤
      (runMachine controller limits actor fuel state program).steps := by
  rw [run_machine_new_table_entries_exact]
  have exactRun :=
    run_machine_exact_fresh_extension controller limits actor fuel state program
  exact le_trans (by
    unfold verifierFreshTableEntries verifierFreshRecords
    simp only [List.length_map]
    exact List.length_filter_le _ _)
    exactRun.2.2

/-! ## Concrete adversary-first / verifier-second run -/

structure AdversaryThenTag73VerifierRun (AdversaryResult : Type*) where
  adversary : MachineRun AdversaryResult
  verifier : MachineRun VerifierPlanResult

/-- Both phases use one explicit fresh-answer controller and one shared table.
The exact post-adversary state is simultaneously frozen as grinding evidence
and supplied as the verifier's starting oracle state. -/
def runAdversaryThenTag73Verifier
    {AdversaryResult : Type*} {freshAnswerCount : Nat}
    (freshTape : FreshAnswerTape Digest256 freshAnswerCount)
    (limits : OracleLimits) (adversaryFuel verifierFuel : Nat)
    (adversaryProgram : OracleMachine AdversaryResult)
    (transcriptTape : DeployedFixedTape) :
    AdversaryThenTag73VerifierRun AdversaryResult :=
  let adversary := runMachine (controllerFromFreshAnswerTape freshTape) limits
    .adversary adversaryFuel emptyOracle adversaryProgram
  let verifier := runFullVerifierPlan (controllerFromFreshAnswerTape freshTape)
    limits verifierFuel adversary.oracle adversary.oracle transcriptTape
  { adversary, verifier }

@[simp] theorem concrete_verifier_starts_from_frozen_adversary_state
    {AdversaryResult : Type*} {freshAnswerCount : Nat}
    (freshTape : FreshAnswerTape Digest256 freshAnswerCount)
    (limits : OracleLimits) (adversaryFuel verifierFuel : Nat)
    (adversaryProgram : OracleMachine AdversaryResult)
    (transcriptTape : DeployedFixedTape) :
    let run := runAdversaryThenTag73Verifier freshTape limits adversaryFuel
      verifierFuel adversaryProgram transcriptTape
    run.verifier =
      runFullVerifierPlan (controllerFromFreshAnswerTape freshTape) limits
        verifierFuel run.adversary.oracle run.adversary.oracle transcriptTape := by
  rfl

/-- Exact history order, verifier actor tags, fresh-entry projection and
initial-table absence for the concrete second phase. -/
theorem concrete_shared_verifier_exact_fresh_extension
    {AdversaryResult : Type*} {freshAnswerCount : Nat}
    (freshTape : FreshAnswerTape Digest256 freshAnswerCount)
    (limits : OracleLimits) (adversaryFuel verifierFuel : Nat)
    (adversaryProgram : OracleMachine AdversaryResult)
    (transcriptTape : DeployedFixedTape) :
    let run := runAdversaryThenTag73Verifier freshTape limits adversaryFuel
      verifierFuel adversaryProgram transcriptTape
    run.verifier.oracle.table = run.adversary.oracle.table ++
        verifierFreshTableEntries run.adversary.oracle run.verifier.oracle ∧
      (∀ record ∈ historySince run.adversary.oracle run.verifier.oracle,
        record.actor = .verifier ∧
          (record.origin = .fresh →
            lookupEntry run.adversary.oracle record.input = none)) ∧
      (historySince run.adversary.oracle run.verifier.oracle).length ≤
        run.verifier.steps := by
  dsimp only [runAdversaryThenTag73Verifier, runFullVerifierPlan,
    runVerifierPlan]
  exact run_machine_exact_fresh_extension
    (controllerFromFreshAnswerTape freshTape) limits .verifier verifierFuel
      (runMachine (controllerFromFreshAnswerTape freshTape) limits .adversary
        adversaryFuel emptyOracle adversaryProgram).oracle
      (verifierPlanProgram
        (runMachine (controllerFromFreshAnswerTape freshTape) limits .adversary
          adversaryFuel emptyOracle adversaryProgram).oracle
        (FixedBindings.ofContext transcriptTape.messages.context) initialCore
          (fullPlan transcriptTape))

/-- The exact deterministic stability characterization for the concrete
shared run. -/
theorem concrete_shared_verifier_stable_iff_no_fresh_records
    {AdversaryResult : Type*} {freshAnswerCount : Nat}
    (freshTape : FreshAnswerTape Digest256 freshAnswerCount)
    (limits : OracleLimits) (adversaryFuel verifierFuel : Nat)
    (adversaryProgram : OracleMachine AdversaryResult)
    (transcriptTape : DeployedFixedTape) :
    let run := runAdversaryThenTag73Verifier freshTape limits adversaryFuel
      verifierFuel adversaryProgram transcriptTape
    VerifierPhaseTableStable run.adversary.oracle run.verifier.oracle ↔
      ∀ record ∈ historySince run.adversary.oracle run.verifier.oracle,
        record.origin ≠ .fresh := by
  dsimp only [runAdversaryThenTag73Verifier, runFullVerifierPlan,
    runVerifierPlan]
  exact run_machine_table_stable_iff_no_fresh_records
    (controllerFromFreshAnswerTape freshTape) limits .verifier verifierFuel
      (runMachine (controllerFromFreshAnswerTape freshTape) limits .adversary
        adversaryFuel emptyOracle adversaryProgram).oracle
      (verifierPlanProgram
        (runMachine (controllerFromFreshAnswerTape freshTape) limits .adversary
          adversaryFuel emptyOracle adversaryProgram).oracle
        (FixedBindings.ofContext transcriptTape.messages.context) initialCore
          (fullPlan transcriptTape))

theorem concrete_shared_verifier_freshness_failure_iff_not_stable
    {AdversaryResult : Type*} {freshAnswerCount : Nat}
    (freshTape : FreshAnswerTape Digest256 freshAnswerCount)
    (limits : OracleLimits) (adversaryFuel verifierFuel : Nat)
    (adversaryProgram : OracleMachine AdversaryResult)
    (transcriptTape : DeployedFixedTape) :
    let run := runAdversaryThenTag73Verifier freshTape limits adversaryFuel
      verifierFuel adversaryProgram transcriptTape
    VerifierPhaseFreshnessFailure run.adversary.oracle run.verifier.oracle ↔
      ¬ VerifierPhaseTableStable run.adversary.oracle run.verifier.oracle := by
  dsimp only [runAdversaryThenTag73Verifier, runFullVerifierPlan,
    runVerifierPlan]
  exact run_machine_freshness_failure_iff_not_stable
    (controllerFromFreshAnswerTape freshTape) limits .verifier verifierFuel
      (runMachine (controllerFromFreshAnswerTape freshTape) limits .adversary
        adversaryFuel emptyOracle adversaryProgram).oracle
      (verifierPlanProgram
        (runMachine (controllerFromFreshAnswerTape freshTape) limits .adversary
          adversaryFuel emptyOracle adversaryProgram).oracle
        (FixedBindings.ofContext transcriptTape.messages.context) initialCore
          (fullPlan transcriptTape))

/-- The concrete form of the new-entry witness: every table entry beyond the
frozen post-adversary prefix is a verifier-created fresh answer at an input
that did not occur in that frozen table. -/
theorem concrete_shared_verifier_new_entry_is_fresh_and_adversary_absent
    {AdversaryResult : Type*} {freshAnswerCount : Nat}
    (freshTape : FreshAnswerTape Digest256 freshAnswerCount)
    (limits : OracleLimits) (adversaryFuel verifierFuel : Nat)
    (adversaryProgram : OracleMachine AdversaryResult)
    (transcriptTape : DeployedFixedTape) (entry : OracleTableEntry) :
    let run := runAdversaryThenTag73Verifier freshTape limits adversaryFuel
      verifierFuel adversaryProgram transcriptTape
    entry ∈ run.verifier.oracle.table.drop run.adversary.oracle.table.length →
      entry.source = .fresh ∧
        lookupEntry run.adversary.oracle entry.input = none ∧
        ∃ record ∈ historySince run.adversary.oracle run.verifier.oracle,
          record.actor = .verifier ∧ record.origin = .fresh ∧
            record.input = entry.input ∧ record.output = entry.output ∧
            entry = freshTableEntryOfRecord record := by
  dsimp only [runAdversaryThenTag73Verifier, runFullVerifierPlan,
    runVerifierPlan]
  exact run_machine_new_entry_is_fresh_and_initially_absent
    (controllerFromFreshAnswerTape freshTape) limits .verifier verifierFuel
      (runMachine (controllerFromFreshAnswerTape freshTape) limits .adversary
        adversaryFuel emptyOracle adversaryProgram).oracle
      (verifierPlanProgram
        (runMachine (controllerFromFreshAnswerTape freshTape) limits .adversary
          adversaryFuel emptyOracle adversaryProgram).oracle
        (FixedBindings.ofContext transcriptTape.messages.context) initialCore
          (fullPlan transcriptTape)) entry

/-- With verifier fuel fixed to the independently audited full-256 ceiling,
both successful verifier records and genuinely new verifier table entries are
bounded by `1511`.  This theorem does not assert that a run with this fuel
returns or accepts. -/
theorem concrete_full256_verifier_history_and_new_entries_le_1511
    {AdversaryResult : Type*} {freshAnswerCount : Nat}
    (freshTape : FreshAnswerTape Digest256 freshAnswerCount)
    (limits : OracleLimits) (adversaryFuel : Nat)
    (adversaryProgram : OracleMachine AdversaryResult)
    (transcriptTape : DeployedFixedTape) :
    let run := runAdversaryThenTag73Verifier freshTape limits adversaryFuel 1511
      adversaryProgram transcriptTape
    (historySince run.adversary.oracle run.verifier.oracle).length ≤ 1511 ∧
      (run.verifier.oracle.table.drop run.adversary.oracle.table.length).length ≤
        1511 := by
  dsimp only [runAdversaryThenTag73Verifier, runFullVerifierPlan,
    runVerifierPlan]
  let state :=
    (runMachine (controllerFromFreshAnswerTape freshTape) limits .adversary
      adversaryFuel emptyOracle adversaryProgram).oracle
  let program := verifierPlanProgram state
    (FixedBindings.ofContext transcriptTape.messages.context) initialCore
      (fullPlan transcriptTape)
  have exactRun := run_machine_exact_fresh_extension
    (controllerFromFreshAnswerTape freshTape) limits .verifier 1511 state program
  have stepBound := run_machine_steps_le_fuel
    (controllerFromFreshAnswerTape freshTape) limits .verifier 1511 state program
  have entryBound := run_machine_new_entry_count_le_steps
    (controllerFromFreshAnswerTape freshTape) limits .verifier 1511 state program
  change
    (historySince state
      (runMachine (controllerFromFreshAnswerTape freshTape) limits .verifier
        1511 state program).oracle).length ≤ 1511 ∧
    ((runMachine (controllerFromFreshAnswerTape freshTape) limits .verifier
      1511 state program).oracle.table.drop state.table.length).length ≤ 1511
  exact ⟨le_trans exactRun.2.2 stepBound, le_trans entryBound stepBound⟩

/-- The independently audited schedule expression is also bounded by `1511`.
It is kept separate from the fuel theorem above: connecting termination of a
particular adversarial run to the complete plan is not smuggled into this
stability interface. -/
theorem concrete_transcript_schedule_full256_cap
    (transcriptTape : DeployedFixedTape) :
    tag73Full256VerifierOracleCalls transcriptTape.messages
      transcriptTape.search ≤ 1511 :=
  shared_runner_full256_verifier_call_cap transcriptTape.messages
    transcriptTape.search

#print axioms query_oracle_success_table_history_cases
#print axioms run_machine_fresh_extension_data
#print axioms run_machine_exact_fresh_extension
#print axioms run_machine_table_stable_iff_no_fresh_records
#print axioms run_machine_freshness_failure_iff_not_stable
#print axioms run_machine_new_table_entries_exact
#print axioms run_machine_new_entry_is_fresh_and_initially_absent
#print axioms run_machine_new_entry_count_le_steps
#print axioms concrete_shared_verifier_exact_fresh_extension
#print axioms concrete_shared_verifier_stable_iff_no_fresh_records
#print axioms concrete_shared_verifier_freshness_failure_iff_not_stable
#print axioms concrete_shared_verifier_new_entry_is_fresh_and_adversary_absent
#print axioms concrete_full256_verifier_history_and_new_entries_le_1511
#print axioms concrete_transcript_schedule_full256_cap

end

end AspisK1.V7Tag73VerifierOracleStability
