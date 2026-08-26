import AspisFormal.K1.V7Tag73ConcreteKnowledgeInsertion
import AspisFormal.K1.V7Tag73ReturnedPlanSemantics
import AspisFormal.K1.V7Tag73VerifierOracleStability
import AspisFormal.K1.V7Tag73AtomicPairFork

/-!
# Operational two-table input for Tag-73 knowledge extraction

The adversary's frozen Q1 table and the verifier's final shared table are not
the same object in general.  A verifier query missing from Q1 extends the lazy
oracle table.  Nevertheless the concrete Tag-73 execution is interpreted over
the final table, while start-only replay and historical grinding evidence must
remain tied to the state frozen at adversary halt.

This module makes that separation explicit.  It constructs the final-table
`ConcreteFirstExecution` from an actual normally returned shared-oracle
verifier run, proves that the final table extends the frozen table and
preserves all of its answers, and derives the complete restoration family over
the final table.  It assumes neither table stability nor verifier acceptance.

The operational atomic-replay layer follows below using the concrete pair
constructor.  Replay controls are inputs to that algorithm; callers do not
supply an arbitrary replay or restoration function.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73OperationalKnowledgeInput

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73InteractiveExecution
open AspisK1.V7Tag73ConcreteQueryDag
open AspisK1.V7Tag73ConcreteStateRestoration
open AspisK1.V7Tag73CoupledReplayAlignment
open AspisK1.V7Tag73SharedOracleVerifierRunner
open AspisK1.V7Tag73ReturnedPlanSemantics
open AspisK1.V7Tag73VerifierOracleStability
open AspisK1.V7Tag73AtomicPairFork
open AspisK1.V7Tag73ConcreteKnowledgeInsertion
open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling

noncomputable section

/-! ## An actual adversary-first, verifier-second source -/

/-- The proof payload consumed by this bridge is already a parsed Tag-73 proof
view.  Its raw proof, auxiliary payload, and exact query DAG are one proof
value, so no later interface can pair the public proof with a convenient
independent DAG. -/
structure ParsedTag73Proof (Proof Payload : Type*) where
  rawProof : Proof
  payload : Payload
  dag : ConcreteDagInstance

/-- The fixed concrete value returned by the Tag-73 adversary first run. -/
structure Tag73AdversaryReturnedValue
    (Statement Proof Payload : Type*) where
  publicProof : PublicProof Statement (ParsedTag73Proof Proof Payload)

def Tag73AdversaryReturnedValue.dag
    {Statement Proof Payload : Type*}
    (value : Tag73AdversaryReturnedValue Statement Proof Payload) :
    ConcreteDagInstance :=
  value.publicProof.proof.dag

/-- Deterministic context check joining the parsed DAG to the public instance
inside the same returned value. -/
noncomputable def returnedValueContextMatches
    {Statement Proof Payload : Type*}
    (value : Tag73AdversaryReturnedValue Statement Proof Payload) : Bool :=
  by
    classical
    exact if value.publicProof.proof.dag.tape.messages.context =
        value.publicProof.publicInstance.context then true else false

/-- A context-checked returned value.  The proof is produced by the concrete
checker above, rather than being a caller-supplied equality field. -/
abbrev CheckedTag73AdversaryReturnedValue
    (Statement Proof Payload : Type*) :=
  {value : Tag73AdversaryReturnedValue Statement Proof Payload //
    returnedValueContextMatches value = true}

/-- The fixed-hidden-tape first-run source for the concrete return type.
`forgeryOf` is not caller-selectable: it is the public-proof projection of the
same checked returned value that contains the parsed DAG. -/
structure Tag73SameTapeSource
    (HiddenTape TapeIdentity Observation Statement Proof Payload : Type*) where
  blackBox : SameTapeBlackBox HiddenTape Observation
    (CheckedTag73AdversaryReturnedValue Statement Proof Payload)
  hiddenTape : HiddenTape
  tapeIdentity : TapeIdentity
  observation : Observation
  controller : AdaptiveController
  oracleLimits : OracleLimits
  firstRunFuel : Nat
  initialOracle : OracleState

def Tag73SameTapeSource.toSameTapeSource
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (source : Tag73SameTapeSource HiddenTape TapeIdentity Observation Statement
      Proof Payload) :
    SameTapeOriginSource HiddenTape TapeIdentity Observation Statement
      (ParsedTag73Proof Proof Payload)
      (CheckedTag73AdversaryReturnedValue Statement Proof Payload) where
  blackBox := source.blackBox
  hiddenTape := source.hiddenTape
  tapeIdentity := source.tapeIdentity
  observation := source.observation
  controller := source.controller
  oracleLimits := source.oracleLimits
  firstRunFuel := source.firstRunFuel
  initialOracle := source.initialOracle
  forgeryOf value := some value.1.publicProof

def Tag73SameTapeSource.origin
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (source : Tag73SameTapeSource HiddenTape TapeIdentity Observation Statement
      Proof Payload) : SameTapeExperimentOrigin TapeIdentity Observation
        Statement (ParsedTag73Proof Proof Payload)
        (CheckedTag73AdversaryReturnedValue Statement Proof Payload) :=
  source.toSameTapeSource.origin

/-- Inputs and normal-return output of the concrete shared-oracle verifier.
The verifier starts from the exact state frozen at adversary halt both as its
immutable Q1 evidence and as its evolving shared state.  `returned` is an
operational equation; it is not a deployed acceptance or extraction field. -/
structure ReturnedVerifierKnowledgeSource
    (HiddenTape TapeIdentity Observation Statement Proof Payload : Type*) where
  sameTape : Tag73SameTapeSource HiddenTape TapeIdentity Observation Statement
    Proof Payload
  /-- The actual normally returned first-run result. -/
  adversaryResult : CheckedTag73AdversaryReturnedValue Statement Proof Payload
  adversaryReturned :
    sameTape.origin.firstExecution.halt = .returned adversaryResult
  verifierController : AdaptiveController
  verifierLimits : OracleLimits
  verifierFuel : Nat
  result : VerifierPlanResult
  returned :
    (runFullVerifierPlan verifierController verifierLimits verifierFuel
      sameTape.origin.firstRun.stateAtAdversaryHalt
      sameTape.origin.firstRun.stateAtAdversaryHalt
      adversaryResult.1.publicProof.proof.dag.tape).halt =
        .returned result

def ReturnedVerifierKnowledgeSource.dag
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (source : ReturnedVerifierKnowledgeSource HiddenTape TapeIdentity
      Observation Statement Proof Payload) : ConcreteDagInstance :=
  source.adversaryResult.1.publicProof.proof.dag

def ReturnedVerifierKnowledgeSource.publicProof
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (source : ReturnedVerifierKnowledgeSource HiddenTape TapeIdentity
      Observation Statement Proof Payload) :
    PublicProof Statement (ParsedTag73Proof Proof Payload) :=
  source.adversaryResult.1.publicProof

theorem returned_source_first_run_forgery_is_public_proof
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (source : ReturnedVerifierKnowledgeSource HiddenTape TapeIdentity
      Observation Statement Proof Payload) :
    source.sameTape.origin.firstRun.forgery = some source.publicProof := by
  change returnedForgery (fun value => some value.1.publicProof)
      source.sameTape.origin.firstExecution.halt = some source.publicProof
  rw [source.adversaryReturned]
  rfl

theorem returned_source_dag_context_matches_public_instance
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (source : ReturnedVerifierKnowledgeSource HiddenTape TapeIdentity
      Observation Statement Proof Payload) :
    source.dag.tape.messages.context =
      source.publicProof.publicInstance.context := by
  have checked := source.adversaryResult.2
  unfold returnedValueContextMatches at checked
  split at checked
  next equal => exact equal
  next _ => simp at checked

/-- Program, release, statement, attempt, and proof-account bindings all come
from the checked public instance context. -/
theorem returned_source_preserves_public_instance_bindings
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (source : ReturnedVerifierKnowledgeSource HiddenTape TapeIdentity
      Observation Statement Proof Payload) :
    let bindings := FixedBindings.ofContext source.dag.tape.messages.context
    bindings.programId = source.publicProof.publicInstance.context.programId ∧
      bindings.releaseBinding =
        source.publicProof.publicInstance.context.releaseBinding ∧
      bindings.statementDigest =
        source.publicProof.publicInstance.context.statementDigest ∧
      bindings.attemptId =
        source.publicProof.publicInstance.context.attemptId ∧
      bindings.proofAccountId =
        source.publicProof.publicInstance.context.attemptId := by
  rw [returned_source_dag_context_matches_public_instance source]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

def ReturnedVerifierKnowledgeSource.frozenOracle
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    (source : ReturnedVerifierKnowledgeSource HiddenTape TapeIdentity
      Observation Statement Proof Result) : OracleState :=
  source.sameTape.origin.firstRun.stateAtAdversaryHalt

def ReturnedVerifierKnowledgeSource.verifierRun
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    (source : ReturnedVerifierKnowledgeSource HiddenTape TapeIdentity
      Observation Statement Proof Result) : MachineRun VerifierPlanResult :=
  runFullVerifierPlan source.verifierController source.verifierLimits
    source.verifierFuel source.frozenOracle source.frozenOracle source.dag.tape

def ReturnedVerifierKnowledgeSource.finalOracle
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    (source : ReturnedVerifierKnowledgeSource HiddenTape TapeIdentity
      Observation Statement Proof Result) : OracleState :=
  source.verifierRun.oracle

def ReturnedVerifierKnowledgeSource.frozenTable
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    (source : ReturnedVerifierKnowledgeSource HiddenTape TapeIdentity
      Observation Statement Proof Result) : FixedOracleTable :=
  fixedTableOfOracleState source.frozenOracle

def ReturnedVerifierKnowledgeSource.finalTable
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    (source : ReturnedVerifierKnowledgeSource HiddenTape TapeIdentity
      Observation Statement Proof Result) : FixedOracleTable :=
  fixedTableOfOracleState source.finalOracle

def projectOracleEntries
    (entries : List AspisK1.V7FsAokExperiment.TableEntry) :
    FixedOracleTable :=
  entries.map fun entry =>
    ({ input := entry.input, output := entry.output } :
      AspisK1.V7Tag73DeterministicRefinement.TableEntry)

@[simp] theorem source_q1_is_frozen_before_verifier
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    (source : ReturnedVerifierKnowledgeSource HiddenTape TapeIdentity
      Observation Statement Proof Result) :
    source.sameTape.origin.firstRun.q1 =
      freezeAdversaryQ1 source.frozenOracle := by
  rfl

theorem source_verifier_normally_returned
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    (source : ReturnedVerifierKnowledgeSource HiddenTape TapeIdentity
      Observation Statement Proof Result) :
    source.verifierRun.halt = .returned source.result := by
  exact source.returned

/-! ## The final verifier table extends the frozen Q1 table -/

theorem final_oracle_table_is_exact_fresh_extension
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    (source : ReturnedVerifierKnowledgeSource HiddenTape TapeIdentity
      Observation Statement Proof Result) :
    source.finalOracle.table = source.frozenOracle.table ++
      verifierFreshTableEntries source.frozenOracle source.finalOracle := by
  simpa [ReturnedVerifierKnowledgeSource.finalOracle,
    ReturnedVerifierKnowledgeSource.verifierRun, runFullVerifierPlan,
    runVerifierPlan] using
      (run_machine_exact_fresh_extension source.verifierController
        source.verifierLimits .verifier source.verifierFuel source.frozenOracle
          (verifierPlanProgram source.frozenOracle
            (FixedBindings.ofContext source.dag.tape.messages.context)
              initialCore (fullPlan source.dag.tape))).1

/-- Exact projected-table extension.  The suffix contains only verifier-fresh
entries and can be nonempty; no stability assumption is made. -/
theorem final_fixed_table_extends_frozen_fixed_table
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    (source : ReturnedVerifierKnowledgeSource HiddenTape TapeIdentity
      Observation Statement Proof Result) :
    source.finalTable = source.frozenTable ++
      projectOracleEntries
        (verifierFreshTableEntries source.frozenOracle source.finalOracle) := by
  unfold ReturnedVerifierKnowledgeSource.finalTable
    ReturnedVerifierKnowledgeSource.frozenTable fixedTableOfOracleState
    projectOracleEntries
  rw [final_oracle_table_is_exact_fresh_extension source]
  exact List.map_append

/-- Every answer defined at adversary halt remains the first-hit answer in the
final verifier table, even when the verifier appends other fresh entries. -/
theorem final_fixed_table_preserves_frozen_answer
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    (source : ReturnedVerifierKnowledgeSource HiddenTape TapeIdentity
      Observation Statement Proof Result)
    (input : ShaInput) (output : ShaOutput)
    (found : tableLookup source.frozenTable input = some output) :
    tableLookup source.finalTable input = some output := by
  simpa [ReturnedVerifierKnowledgeSource.finalTable,
    ReturnedVerifierKnowledgeSource.finalOracle,
    ReturnedVerifierKnowledgeSource.verifierRun, runFullVerifierPlan,
    runVerifierPlan, ReturnedVerifierKnowledgeSource.frozenTable] using
      run_machine_preserves_fixed_table_answer source.verifierController
        source.verifierLimits .verifier source.verifierFuel source.frozenOracle
          (verifierPlanProgram source.frozenOracle
            (FixedBindings.ofContext source.dag.tape.messages.context)
              initialCore (fullPlan source.dag.tape)) input output found

/-- Every Q1 record validated by the runner's frozen-evidence predicate keeps
the same answer in the final table.  We do not claim this for arbitrary
malformed adversary-tagged records that a caller may have placed in a
nonempty initial oracle history. -/
theorem final_table_covers_validated_frozen_q1_evidence
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    (source : ReturnedVerifierKnowledgeSource HiddenTape TapeIdentity
      Observation Statement Proof Result) :
    FrozenEvidenceCoveredByTable source.frozenOracle source.finalTable := by
  simpa [ReturnedVerifierKnowledgeSource.finalTable,
    ReturnedVerifierKnowledgeSource.finalOracle,
    ReturnedVerifierKnowledgeSource.verifierRun, runFullVerifierPlan] using
      same_start_final_table_covers_frozen_evidence
        source.verifierController source.verifierLimits source.verifierFuel
          source.frozenOracle
            (FixedBindings.ofContext source.dag.tape.messages.context)
              initialCore (fullPlan source.dag.tape)

/-! ## The final-table concrete execution and restoration family -/

theorem returned_source_constructs_final_table_execution
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    (source : ReturnedVerifierKnowledgeSource HiddenTape TapeIdentity
      Observation Statement Proof Result) :
    ∃ execution : ConcreteFirstExecution source.finalTable source.dag.tape,
      execution.trace.actionReplies = source.result.actionReplies := by
  simpa [ReturnedVerifierKnowledgeSource.finalTable,
    ReturnedVerifierKnowledgeSource.finalOracle,
    ReturnedVerifierKnowledgeSource.verifierRun] using
      returned_full_plan_from_frozen_state_gives_concrete_first_execution
        source.verifierController source.verifierLimits source.verifierFuel
          source.frozenOracle source.dag.tape source.result source.returned

/-- The exact two-table interactive object offered to K1.2--K1.5.  Its
execution is over `run.finalTable`; its same-tape origin and Q1 remain frozen
inside `run.sameTape`.  This is operational trace data, not an extractor or an
acceptance conclusion. -/
structure TwoTableConcreteK12ToK15Input
    (HiddenTape TapeIdentity Observation Statement Proof Result : Type*) where
  run : ReturnedVerifierKnowledgeSource HiddenTape TapeIdentity Observation
    Statement Proof Result
  execution : ConcreteFirstExecution run.finalTable run.dag.tape
  exactActionReplies :
    execution.trace.actionReplies = run.result.actionReplies

theorem returned_source_constructs_two_table_k12_to_k15_input
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    (source : ReturnedVerifierKnowledgeSource HiddenTape TapeIdentity
      Observation Statement Proof Result) :
    Nonempty (TwoTableConcreteK12ToK15Input HiddenTape TapeIdentity
      Observation Statement Proof Result) := by
  obtain ⟨execution, replies⟩ :=
    returned_source_constructs_final_table_execution source
  exact ⟨⟨source, execution, replies⟩⟩

def TwoTableConcreteK12ToK15Input.restorationAt
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    (input : TwoTableConcreteK12ToK15Input HiddenTape TapeIdentity Observation
      Statement Proof Result)
    (generated : GeneratedReplayPrefix input.run.dag) :
    ConcreteRestorationRecord input.run.finalTable input.run.dag :=
  concreteRestoration input.execution generated

theorem two_table_restoration_is_complete_seen_and_final_table_bound
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    (input : TwoTableConcreteK12ToK15Input HiddenTape TapeIdentity Observation
      Statement Proof Result)
    (generated : GeneratedReplayPrefix input.run.dag) :
    let restoration := input.restorationAt generated
    IsComplete restoration.snapshot ∧
      PreviouslySeen restoration.snapshot input.execution.interactiveState ∧
      NonemptyVerifierHistory input.execution.interactiveState ∧
      restoration.snapshot.bindings =
        FixedBindings.ofContext input.run.dag.tape.messages.context ∧
      (fullPlan input.run.dag.tape).get restoration.actionCursor =
        .squeezePair restoration.checkpoint.owner restoration.checkpoint.block ∧
      restoration.oracleTable = input.run.finalTable ∧
      restoration.deployedTape = input.run.dag.tape := by
  let restoration := input.restorationAt generated
  exact ⟨restoration_snapshot_is_complete restoration,
    restoration_snapshot_is_previously_seen restoration,
    restoration_first_run_history_is_nonempty restoration,
    restoration_preserves_fixed_bindings restoration,
    restoration_next_action_is_exact_squeeze_pair restoration,
    restoration_retains_same_oracle_table restoration,
    restoration_retains_same_deployed_tape restoration⟩

/-- The two tables are retained side by side at every restoration: the state
map uses the final table, while the replay evidence remains the original Q1. -/
theorem two_table_input_keeps_frozen_q1_and_final_execution_table_separate
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    (input : TwoTableConcreteK12ToK15Input HiddenTape TapeIdentity Observation
      Statement Proof Result)
    (generated : GeneratedReplayPrefix input.run.dag) :
    input.run.sameTape.origin.firstRun.q1 =
        freezeAdversaryQ1 input.run.frozenOracle ∧
      (input.restorationAt generated).oracleTable = input.run.finalTable ∧
      ∃ suffix : FixedOracleTable,
        input.run.finalTable = input.run.frozenTable ++ suffix := by
  refine ⟨rfl, restoration_retains_same_oracle_table _, ?_⟩
  exact ⟨projectOracleEntries
      (verifierFreshTableEntries input.run.frozenOracle input.run.finalOracle),
    final_fixed_table_extends_frozen_fixed_table input.run⟩

/-!
The atomic replay constructor is integrated after its executable paired
programming output is available.  Its source/Q1 arguments will be
`input.run.sameTape.origin` and `input.run.frozenOracle`; its concrete state
argument will be `input.execution`, indexed by `input.run.finalTable`.
No equality between those two tables is required or asserted.
-/

#print axioms source_q1_is_frozen_before_verifier
#print axioms returned_source_first_run_forgery_is_public_proof
#print axioms returned_source_dag_context_matches_public_instance
#print axioms returned_source_preserves_public_instance_bindings
#print axioms source_verifier_normally_returned
#print axioms final_oracle_table_is_exact_fresh_extension
#print axioms final_fixed_table_extends_frozen_fixed_table
#print axioms final_fixed_table_preserves_frozen_answer
#print axioms final_table_covers_validated_frozen_q1_evidence
#print axioms returned_source_constructs_final_table_execution
#print axioms returned_source_constructs_two_table_k12_to_k15_input
#print axioms two_table_restoration_is_complete_seen_and_final_table_bound
#print axioms two_table_input_keeps_frozen_q1_and_final_execution_table_separate

end

end AspisK1.V7Tag73OperationalKnowledgeInput
