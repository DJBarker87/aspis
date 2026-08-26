import AspisFormal.K1.V7Tag73SharedOracleVerifierRunner
import AspisFormal.K1.V7Tag73ConcreteKnowledgeInsertion
import AspisFormal.K1.V7Tag73ReturnedPlanSemantics

/-!
# Stable shared-oracle first run for Tag 73

This module closes one deterministic gap between the generic same-tape
experiment and the concrete Tag-73 interactive input.  The adversary is run
once from `emptyOracle` with a fixed hidden tape.  Its complete post-adversary
oracle state and adversary-only `Q1` are then frozen.  The literal Tag-73
verifier plan starts from that *same* state, while historical grinding probes
are read only from the frozen `Q1` evidence.

In the stable case, the verifier run returns normally and its final fixed
table is exactly the post-adversary fixed table: every verifier-driving query
was already present after the adversary run.  This condition does not say that
Rust accepted a proof.  In particular, it supplies neither deterministic
decoder well-formedness nor the semantic terminal, typed two-tree Merkle, and
final relation checks omitted by the work-erased action machine.  Those source
facts remain separate data and are not premises of the principal theorem in
this file.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73StableFirstRunBridge

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73InteractiveExecution
open AspisK1.V7Tag73ConcreteQueryDag
open AspisK1.V7Tag73CoupledReplayAlignment
open AspisK1.V7Tag73SharedOracleVerifierRunner
open AspisK1.V7Tag73ReturnedPlanSemantics
open AspisK1.V7Tag73ConcreteKnowledgeInsertion
open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling

/-! ## One actual empty-oracle adversary run -/

/-- Inputs for one first execution of a fixed-hidden-tape adversary.  Unlike
`SameTapeOriginSource`, there is no caller-selectable initial oracle: the
construction below starts literally from `emptyOracle`. -/
structure EmptyOracleFirstRunSource
    (HiddenTape TapeIdentity Observation Statement Proof Result : Type*) where
  blackBox : SameTapeBlackBox HiddenTape Observation Result
  hiddenTape : HiddenTape
  tapeIdentity : TapeIdentity
  observation : Observation
  adversaryController : AdaptiveController
  oracleLimits : OracleLimits
  adversaryFuel : Nat
  forgeryOf : Result → Option (PublicProof Statement Proof)

/-- Forget only the enforced empty-oracle choice, yielding the already audited
same-tape source object used by the K1.2--K1.5 insertion layer. -/
def EmptyOracleFirstRunSource.toSameTapeSource
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    (source : EmptyOracleFirstRunSource HiddenTape TapeIdentity Observation
      Statement Proof Result) :
    SameTapeOriginSource HiddenTape TapeIdentity Observation Statement Proof
      Result where
  blackBox := source.blackBox
  hiddenTape := source.hiddenTape
  tapeIdentity := source.tapeIdentity
  observation := source.observation
  controller := source.adversaryController
  oracleLimits := source.oracleLimits
  firstRunFuel := source.adversaryFuel
  initialOracle := emptyOracle
  forgeryOf := source.forgeryOf

def EmptyOracleFirstRunSource.origin
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    (source : EmptyOracleFirstRunSource HiddenTape TapeIdentity Observation
      Statement Proof Result) :
    SameTapeExperimentOrigin TapeIdentity Observation Statement Proof Result :=
  source.toSameTapeSource.origin

/-- The complete shared-oracle state frozen exactly when the adversary's first
execution halts (whether by return, oracle abort, or fuel exhaustion). -/
def EmptyOracleFirstRunSource.postAdversaryState
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    (source : EmptyOracleFirstRunSource HiddenTape TapeIdentity Observation
      Statement Proof Result) : OracleState :=
  source.origin.firstRun.stateAtAdversaryHalt

/-- Ganesh-style `Q1`, frozen before any verifier calls are made. -/
def EmptyOracleFirstRunSource.q1
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    (source : EmptyOracleFirstRunSource HiddenTape TapeIdentity Observation
      Statement Proof Result) : List QueryRecord :=
  freezeAdversaryQ1 source.postAdversaryState

@[simp] theorem empty_first_run_initial_oracle
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    (source : EmptyOracleFirstRunSource HiddenTape TapeIdentity Observation
      Statement Proof Result) :
    source.origin.initialOracle = emptyOracle := by
  rfl

theorem empty_first_run_is_fixed_hidden_tape_start
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    (source : EmptyOracleFirstRunSource HiddenTape TapeIdentity Observation
      Statement Proof Result) :
    source.origin.firstExecution =
      runMachine source.adversaryController source.oracleLimits .adversary
        source.adversaryFuel emptyOracle
        (source.blackBox.start source.hiddenTape source.observation) := by
  rfl

@[simp] theorem empty_first_run_post_state_is_execution_oracle
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    (source : EmptyOracleFirstRunSource HiddenTape TapeIdentity Observation
      Statement Proof Result) :
    source.postAdversaryState = source.origin.firstExecution.oracle := by
  rfl

@[simp] theorem empty_first_run_q1_is_frozen_at_adversary_halt
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    (source : EmptyOracleFirstRunSource HiddenTape TapeIdentity Observation
      Statement Proof Result) :
    source.q1 = source.origin.firstRun.q1 := by
  rfl

theorem empty_first_run_capability_restarts_same_hidden_tape
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    (source : EmptyOracleFirstRunSource HiddenTape TapeIdentity Observation
      Statement Proof Result) :
    source.origin.capability.start source.observation =
      source.blackBox.start source.hiddenTape source.observation := by
  rfl

/-! ## Every post-adversary table entry came from adversary Q1 -/

/-- Each fixed-table entry has a matching call record by the one actor that
has run so far.  This invariant is useful only because the source below starts
from the genuinely empty oracle; it would be false for an arbitrary
preprogrammed initial state. -/
def TableCoveredByActorHistory (actor : QueryActor)
    (state : OracleState) : Prop :=
  ∀ entry ∈ state.table,
    ∃ record ∈ state.history,
      record.actor = actor ∧
        record.input = entry.input ∧ record.output = entry.output

theorem empty_oracle_table_is_covered_by_actor_history
    (actor : QueryActor) :
    TableCoveredByActorHistory actor emptyOracle := by
  simp [TableCoveredByActorHistory, emptyOracle]

/-- A successful query by the same actor preserves table/history coverage.
Cached queries leave the table unchanged; fresh queries append the matching
table entry and history record together. -/
theorem query_oracle_preserves_table_covered_by_actor_history
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (state nextState : OracleState)
    (input : ShaInput) (output : ShaOutput)
    (covered : TableCoveredByActorHistory actor state)
    (success : queryOracle controller limits actor state input =
      .ok (output, nextState)) :
    TableCoveredByActorHistory actor nextState := by
  unfold queryOracle at success
  split at success <;> try contradiction
  next _ =>
    split at success
    next entry found =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at success
      rcases success with ⟨rfl, rfl⟩
      intro candidate member
      obtain ⟨record, recordMember, actorEq, inputEq, outputEq⟩ :=
        covered candidate member
      exact ⟨record, List.mem_append_left _ recordMember,
        actorEq, inputEq, outputEq⟩
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
          · obtain ⟨record, recordMember, actorEq, inputEq, outputEq⟩ :=
              covered candidate old
            exact ⟨record, List.mem_append_left _ recordMember,
              actorEq, inputEq, outputEq⟩
          · let newRecord : QueryRecord :=
              { input := input
                output := answer
                actor := actor
                origin := .fresh }
            refine ⟨newRecord, ?_, rfl, rfl, rfl⟩
            exact List.mem_append_right _ (by simp [newRecord])

/-- A fuel-bounded oracle program preserves coverage on normal return, abort,
and timeout.  No programming operation exists in `OracleMachine`. -/
theorem run_machine_preserves_table_covered_by_actor_history
    {RunResult : Type*} (controller : AdaptiveController)
    (limits : OracleLimits) (actor : QueryActor) (fuel : Nat)
    (state : OracleState) (program : OracleMachine RunResult)
    (covered : TableCoveredByActorHistory actor state) :
    TableCoveredByActorHistory actor
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
              have nextCovered :=
                query_oracle_preserves_table_covered_by_actor_history
                  controller limits actor state nextState input output covered
                    queryResult
              simpa using ih nextState (next output) nextCovered

theorem post_adversary_table_is_covered_by_q1_history
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    (source : EmptyOracleFirstRunSource HiddenTape TapeIdentity Observation
      Statement Proof Result) :
    TableCoveredByActorHistory .adversary source.postAdversaryState := by
  change TableCoveredByActorHistory .adversary
    (runMachine source.adversaryController source.oracleLimits .adversary
      source.adversaryFuel emptyOracle
        (source.blackBox.start source.hiddenTape source.observation)).oracle
  exact run_machine_preserves_table_covered_by_actor_history
    source.adversaryController source.oracleLimits .adversary
      source.adversaryFuel emptyOracle
        (source.blackBox.start source.hiddenTape source.observation)
          (empty_oracle_table_is_covered_by_actor_history .adversary)

private theorem lookup_entry_some_has_requested_input
    (state : OracleState) (input : ShaInput)
    (entry : AspisK1.V7FsAokExperiment.TableEntry)
    (selected : lookupEntry state input = some entry) :
    entry.input = input := by
  unfold lookupEntry at selected
  have predicate := List.find?_some selected
  exact of_decide_eq_true predicate

/-- A lookup in the frozen post-adversary fixed table has an exact matching
record in frozen Q1. -/
theorem post_adversary_fixed_table_answer_has_q1_record
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    (source : EmptyOracleFirstRunSource HiddenTape TapeIdentity Observation
      Statement Proof Result)
    (input : ShaInput) (output : ShaOutput)
    (found : tableLookup (fixedTableOfOracleState source.postAdversaryState)
      input = some output) :
    ∃ record ∈ source.q1,
      record.actor = .adversary ∧ record.input = input ∧
        record.output = output := by
  change tableLookup (fixedTableOfOracleState source.postAdversaryState)
    input = some output at found
  rw [fixed_table_lookup_eq_lookup_entry_output] at found
  cases selected : lookupEntry source.postAdversaryState input with
  | none =>
      rw [selected] at found
      cases found
  | some entry =>
      have outputEq : entry.output = output := by
        simpa only [selected, Option.map_some, Option.some.injEq] using found
      have entryMember : entry ∈ source.postAdversaryState.table := by
        unfold lookupEntry at selected
        exact List.mem_of_find?_eq_some selected
      have entryInput : entry.input = input := by
        exact lookup_entry_some_has_requested_input
          source.postAdversaryState input entry selected
      obtain ⟨record, recordMember, actorEq, recordInput, recordOutput⟩ :=
        post_adversary_table_is_covered_by_q1_history source entry entryMember
      refine ⟨record, ?_, actorEq, recordInput.trans entryInput, ?_⟩
      · change record ∈ actorHistory .adversary source.postAdversaryState
        exact List.mem_filter.mpr
          ⟨recordMember, by simpa [actorEq]⟩
      · exact recordOutput.trans outputEq

/-! ## Verifier continuation on the very same shared oracle -/

/-- Execute the literal full Tag-73 verifier plan with both its immutable Q1
evidence and its evolving shared oracle initialized to the exact state frozen
at adversary halt. -/
def runVerifierAfterFirstRun
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    (source : EmptyOracleFirstRunSource HiddenTape TapeIdentity Observation
      Statement Proof Result)
    (verifierController : AdaptiveController) (verifierLimits : OracleLimits)
    (verifierFuel : Nat) (tape : DeployedFixedTape) :
    MachineRun VerifierPlanResult :=
  runFullVerifierPlan verifierController verifierLimits verifierFuel
    source.postAdversaryState source.postAdversaryState tape

/-- Operational data for the stable case.  `returned` is the result of the
literal verifier runner, not an acceptance assumption.  `noNewFixedEntries`
states exactly that the verifier did not extend the fixed table; its call
history may still grow with cached verifier calls. -/
structure StableVerifierContinuation
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    (source : EmptyOracleFirstRunSource HiddenTape TapeIdentity Observation
      Statement Proof Result)
    (verifierController : AdaptiveController) (verifierLimits : OracleLimits)
    (verifierFuel : Nat) (tape : DeployedFixedTape) where
  result : VerifierPlanResult
  returned :
    (runVerifierAfterFirstRun source verifierController verifierLimits
      verifierFuel tape).halt = .returned result
  noNewFixedEntries :
    fixedTableOfOracleState
        (runVerifierAfterFirstRun source verifierController verifierLimits
          verifierFuel tape).oracle =
      fixedTableOfOracleState source.postAdversaryState

theorem stable_continuation_freezes_q1_before_verifier_history
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    {source : EmptyOracleFirstRunSource HiddenTape TapeIdentity Observation
      Statement Proof Result}
    {verifierController : AdaptiveController} {verifierLimits : OracleLimits}
    {verifierFuel : Nat} {tape : DeployedFixedTape}
    (stable : StableVerifierContinuation source verifierController
      verifierLimits verifierFuel tape) :
    source.q1 = freezeAdversaryQ1 source.postAdversaryState ∧
      (runVerifierAfterFirstRun source verifierController verifierLimits
        verifierFuel tape).halt = .returned stable.result := by
  exact ⟨rfl, stable.returned⟩

/-- A stable continuation exposes the verifier's literal ordered query path,
and every answer on that path was already present in the table frozen at
adversary halt.  The history records are still appended with actor
`.verifier`; table stability does not erase or relabel those calls. -/
theorem stable_continuation_has_exact_preexisting_query_answers
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    {source : EmptyOracleFirstRunSource HiddenTape TapeIdentity Observation
      Statement Proof Result}
    {verifierController : AdaptiveController} {verifierLimits : OracleLimits}
    {verifierFuel : Nat} {tape : DeployedFixedTape}
    (stable : StableVerifierContinuation source verifierController
      verifierLimits verifierFuel tape) :
    ∃ pairs : List (ShaInput × ShaOutput),
      queryAnswerTrace
          (historySince source.postAdversaryState
            (runVerifierAfterFirstRun source verifierController verifierLimits
              verifierFuel tape).oracle) = pairs ∧
      (historySince source.postAdversaryState
          (runVerifierAfterFirstRun source verifierController verifierLimits
            verifierFuel tape).oracle).length = pairs.length ∧
      (∀ record ∈ historySince source.postAdversaryState
          (runVerifierAfterFirstRun source verifierController verifierLimits
            verifierFuel tape).oracle,
        record.actor = .verifier) ∧
      ∀ pair ∈ pairs,
        tableLookup (fixedTableOfOracleState source.postAdversaryState)
          pair.1 = some pair.2 := by
  have returned :
      (runFullVerifierPlan verifierController verifierLimits verifierFuel
        source.postAdversaryState source.postAdversaryState tape).halt =
          .returned stable.result := by
    simpa [runVerifierAfterFirstRun] using stable.returned
  obtain ⟨pairs, _path, history, length, actors, answers⟩ :=
    returned_full_verifier_plan_has_exact_ordered_history verifierController
      verifierLimits verifierFuel source.postAdversaryState
        source.postAdversaryState tape stable.result returned
  refine ⟨pairs, ?_, ?_, ?_, ?_⟩
  · simpa [runVerifierAfterFirstRun] using history
  · simpa [runVerifierAfterFirstRun] using length
  · simpa [runVerifierAfterFirstRun] using actors
  · intro pair member
    have answer := answers pair member
    rw [← stable.noNewFixedEntries]
    simpa [runVerifierAfterFirstRun] using answer

/-- Consequently every actual verifier query in a stable continuation has a
matching adversary record in the Q1 frozen *before* the verifier began. -/
theorem stable_continuation_verifier_queries_have_first_run_q1_records
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    {source : EmptyOracleFirstRunSource HiddenTape TapeIdentity Observation
      Statement Proof Result}
    {verifierController : AdaptiveController} {verifierLimits : OracleLimits}
    {verifierFuel : Nat} {tape : DeployedFixedTape}
    (stable : StableVerifierContinuation source verifierController
      verifierLimits verifierFuel tape) :
    ∃ pairs : List (ShaInput × ShaOutput),
      queryAnswerTrace
          (historySince source.postAdversaryState
            (runVerifierAfterFirstRun source verifierController verifierLimits
              verifierFuel tape).oracle) = pairs ∧
      ∀ pair ∈ pairs,
        ∃ record ∈ source.q1,
          record.actor = .adversary ∧ record.input = pair.1 ∧
            record.output = pair.2 := by
  obtain ⟨pairs, history, _length, _actors, answers⟩ :=
    stable_continuation_has_exact_preexisting_query_answers stable
  refine ⟨pairs, history, ?_⟩
  intro pair member
  exact post_adversary_fixed_table_answer_has_q1_record source pair.1 pair.2
    (answers pair member)

/-!
## Stable table transport into K1.2--K1.5

The bridge below consumes only the operational returned-plan semantics and
`noNewFixedEntries`; no parser, acceptance, transcript-cover, or extraction
proposition is introduced.
-/

/-- A normally returned verifier plan already constructs a concrete execution
over its final table.  Stability transports that execution back to the table
frozen exactly at adversary halt. -/
theorem stable_continuation_constructs_concrete_first_execution
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    {source : EmptyOracleFirstRunSource HiddenTape TapeIdentity Observation
      Statement Proof Result}
    {verifierController : AdaptiveController} {verifierLimits : OracleLimits}
    {verifierFuel : Nat} {tape : DeployedFixedTape}
    (stable : StableVerifierContinuation source verifierController
      verifierLimits verifierFuel tape) :
    Nonempty (ConcreteFirstExecution
      (fixedTableOfOracleState source.postAdversaryState) tape) := by
  have returned :
      (runFullVerifierPlan verifierController verifierLimits verifierFuel
        source.postAdversaryState source.postAdversaryState tape).halt =
          .returned stable.result := by
    simpa [runVerifierAfterFirstRun] using stable.returned
  obtain ⟨execution, _exactReplies⟩ :=
    returned_full_plan_from_frozen_state_gives_concrete_first_execution
      verifierController verifierLimits verifierFuel source.postAdversaryState
        tape stable.result returned
  have tableStable :
      fixedTableOfOracleState
          (runFullVerifierPlan verifierController verifierLimits verifierFuel
            source.postAdversaryState source.postAdversaryState tape).oracle =
        fixedTableOfOracleState source.postAdversaryState := by
    simpa [runVerifierAfterFirstRun] using stable.noNewFixedEntries
  exact ⟨tableStable ▸ execution⟩

/-- This is the exact concrete object accepted by the K1.2--K1.5 insertion
interface.  Its source is definitionally the fixed-hidden-tape run from
`emptyOracle`, and its execution is indexed by the table frozen before any
verifier call. -/
theorem stable_continuation_constructs_concrete_k12_to_k15_input
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    {source : EmptyOracleFirstRunSource HiddenTape TapeIdentity Observation
      Statement Proof Result}
    {verifierController : AdaptiveController} {verifierLimits : OracleLimits}
    {verifierFuel : Nat} {dag : ConcreteDagInstance}
    (stable : StableVerifierContinuation source verifierController
      verifierLimits verifierFuel dag.tape) :
    Nonempty (ConcreteK12ToK15Input HiddenTape TapeIdentity Observation
      Statement Proof Result) := by
  obtain ⟨execution⟩ :=
    stable_continuation_constructs_concrete_first_execution stable
  exact ⟨
    { source := source.toSameTapeSource
      dag := dag
      execution := execution }⟩

/-- The stable first run therefore supplies the whole concrete restoration
family expected upstream: complete, previously seen, nonempty verifier states
with fixed bindings and the exact next atomic squeeze.  All facts are computed
from the resulting execution. -/
theorem stable_continuation_constructs_legal_k12_to_k15_restoration_family
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    {source : EmptyOracleFirstRunSource HiddenTape TapeIdentity Observation
      Statement Proof Result}
    {verifierController : AdaptiveController} {verifierLimits : OracleLimits}
    {verifierFuel : Nat} {dag : ConcreteDagInstance}
    (stable : StableVerifierContinuation source verifierController
      verifierLimits verifierFuel dag.tape) :
    ∃ input : ConcreteK12ToK15Input HiddenTape TapeIdentity Observation
        Statement Proof Result,
      input.source = source.toSameTapeSource ∧ input.dag = dag ∧
      ∀ generated : GeneratedReplayPrefix input.dag,
        let restoration := input.restorationFamily generated
        IsComplete restoration.snapshot ∧
          PreviouslySeen restoration.snapshot
            input.execution.interactiveState ∧
          NonemptyVerifierHistory input.execution.interactiveState ∧
          restoration.snapshot.bindings =
            FixedBindings.ofContext input.dag.tape.messages.context ∧
          (fullPlan input.dag.tape).get restoration.actionCursor =
            .squeezePair restoration.checkpoint.owner
              restoration.checkpoint.block ∧
          restoration.oracleTable =
            fixedTableOfOracleState
              input.source.origin.firstRun.stateAtAdversaryHalt ∧
          restoration.deployedTape = input.dag.tape := by
  obtain ⟨execution⟩ :=
    stable_continuation_constructs_concrete_first_execution stable
  let input : ConcreteK12ToK15Input HiddenTape TapeIdentity Observation
      Statement Proof Result :=
    { source := source.toSameTapeSource
      dag := dag
      execution := execution }
  refine ⟨input, rfl, rfl, ?_⟩
  intro generated
  exact concrete_input_restoration_family_is_legal input generated

/-!
`stable_continuation_constructs_concrete_k12_to_k15_input` is deliberately
the strongest unconditional conclusion here.  It does **not** derive
`checkedRefine`: the shared runner uses `applyActionWorkErased`, and its tape
already contains typed sampler values.  A checked refinement additionally
needs an independently proved `TraceWellFormed` decoder correspondence.
Deployed acceptance needs the still larger `SourceAcceptanceRemainder` from
`V7Tag73SourceAcceptanceBoundary` (semantic terminal, typed Merkle checks,
frontier equality, batched residual, and final relations).  Neither missing
source datum is smuggled into this stable-run theorem.
-/

#print axioms empty_first_run_initial_oracle
#print axioms empty_first_run_is_fixed_hidden_tape_start
#print axioms empty_first_run_post_state_is_execution_oracle
#print axioms empty_first_run_q1_is_frozen_at_adversary_halt
#print axioms empty_first_run_capability_restarts_same_hidden_tape
#print axioms empty_oracle_table_is_covered_by_actor_history
#print axioms query_oracle_preserves_table_covered_by_actor_history
#print axioms run_machine_preserves_table_covered_by_actor_history
#print axioms post_adversary_table_is_covered_by_q1_history
#print axioms post_adversary_fixed_table_answer_has_q1_record
#print axioms stable_continuation_freezes_q1_before_verifier_history
#print axioms stable_continuation_has_exact_preexisting_query_answers
#print axioms stable_continuation_verifier_queries_have_first_run_q1_records
#print axioms stable_continuation_constructs_concrete_first_execution
#print axioms stable_continuation_constructs_concrete_k12_to_k15_input
#print axioms stable_continuation_constructs_legal_k12_to_k15_restoration_family

end AspisK1.V7Tag73StableFirstRunBridge
