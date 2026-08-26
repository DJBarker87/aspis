import AspisFormal.K1.V7Tag73ReplayBranchDispatcher
import AspisFormal.K1.V7Tag73ReplayReturnedVerifier

/-!
# A finite restricted replay forest for deployed Tag 73

This module packages the concrete first execution as the root of a finite
depth-one replay forest.  Every child is produced by the executable replay
branch dispatcher at one actual `GeneratedReplayPrefix`.  A child stores the
dispatcher equation, its exact resource use, and the checked parsed proof
returned by that replay.  Its DAG is projected from that returned proof; it is
not equated with the root DAG.  In particular, rewinding lambda or chi may
produce a different challenge-dependent C2 commitment and hence a different
DAG.

The restored verifier state belongs to the root execution: it is complete,
previously seen, and its history contains the explicit dummy round.  The
child's returned-DAG verifier computation is defined, but no premise or field
asserts that this new verifier returns or accepts.

Recursive extension below a child needs a new concrete execution indexed by
the child's returned DAG.  The final section gives the exact dependent sigma
type for that datum.  It is intentionally not manufactured from a replay
return alone.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73RestrictedReplayForest

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73InteractiveExecution
open AspisK1.V7Tag73ConcreteQueryDag
open AspisK1.V7Tag73ConcreteStateRestoration
open AspisK1.V7Tag73AtomicPairFork
open AspisK1.V7Tag73AtomicPairReplay
open AspisK1.V7Tag73ReplayBranchDispatcher
open AspisK1.V7Tag73ReplayReturnedVerifier
open AspisK1.V7Tag73OperationalKnowledgeInput
open AspisK1.V7Tag73ConcreteKnowledgeInsertion
open AspisK1.V7Tag73SharedOracleVerifierRunner
open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling

noncomputable section

/-! ## The operational root -/

/-- The root contains a concrete first execution indexed by the exact parsed
DAG in the actual checked adversary return.  Its execution table is explicit
and may differ from the table frozen at adversary halt.  No verifier-run
normal-return equation is stored. -/
structure RestrictedReplayRoot
    (HiddenTape TapeIdentity Observation Statement Proof Payload : Type*) where
  source : Tag73SameTapeSource HiddenTape TapeIdentity Observation Statement
    Proof Payload
  returnedValue : CheckedTag73AdversaryReturnedValue Statement Proof Payload
  adversaryReturned :
    source.origin.firstExecution.halt = .returned returnedValue
  table : FixedOracleTable
  execution : ConcreteFirstExecution table
    returnedValue.1.publicProof.proof.dag.tape

def RestrictedReplayRoot.dag
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload) : ConcreteDagInstance :=
  root.returnedValue.1.publicProof.proof.dag

def RestrictedReplayRoot.dummySnapshot
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload) : CompleteSnapshot root.dag.tape :=
  dummyRestorationSnapshot root.execution

/-- Root legality contains only operational return/binding/history facts.  It
does not contain verifier acceptance or a knowledge conclusion. -/
def RestrictedReplayRoot.IsOperational
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload) : Prop :=
  root.source.origin.firstExecution.halt = .returned root.returnedValue ∧
  root.dag.tape.messages.context =
    root.returnedValue.1.publicProof.publicInstance.context ∧
  root.source.origin.firstRun.q1 =
    freezeAdversaryQ1 root.source.origin.firstRun.stateAtAdversaryHalt ∧
  root.dummySnapshot.cursor.val = 0 ∧
  root.dummySnapshot.phase = .dummyNonempty ∧
  IsComplete root.dummySnapshot ∧
  PreviouslySeen root.dummySnapshot root.execution.interactiveState ∧
  NonemptyVerifierHistory root.execution.interactiveState

theorem restricted_replay_root_is_operational
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload) :
    root.IsOperational := by
  have dummy := dummy_cursor_zero_is_legal_restoration_state root.execution
  exact ⟨root.adversaryReturned,
    checked_returned_value_context_is_exact root.returnedValue,
    rfl,
    dummy.1, dummy.2.1, dummy.2.2.1, dummy.2.2.2.1, dummy.2.2.2.2⟩

/-! ## One dispatcher-produced child -/

/-- Specialize the generic branch outcome's returned result to the checked
parsed Tag-73 value used by this forest. -/
def checkedReplayReturned
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    {source : Tag73SameTapeSource HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    {execution : ConcreteFirstExecution table dag.tape}
    {generated : GeneratedReplayPrefix dag}
    {configuration : AtomicPairReplayConfiguration}
    (outcome : ReplayBranchOutcome source.toSameTapeSource execution generated
      configuration) :
    CheckedTag73AdversaryReturnedValue Statement Proof Payload :=
  match outcome with
  | .atomic output _ => output.returned
  | .noPair output _ => output.returned

/-- The concrete replay run selected by the dispatcher. -/
def checkedReplayRun
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    {source : Tag73SameTapeSource HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    {execution : ConcreteFirstExecution table dag.tape}
    {generated : GeneratedReplayPrefix dag}
    {configuration : AtomicPairReplayConfiguration}
    (outcome : ReplayBranchOutcome source.toSameTapeSource execution generated
      configuration) :
    MachineRun (CheckedTag73AdversaryReturnedValue Statement Proof Payload) :=
  match outcome with
  | .atomic output _ => output.replayRun
  | .noPair output _ => output.replay

theorem checked_replay_run_normally_returns_its_actual_value
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    {source : Tag73SameTapeSource HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    {execution : ConcreteFirstExecution table dag.tape}
    {generated : GeneratedReplayPrefix dag}
    {configuration : AtomicPairReplayConfiguration}
    (outcome : ReplayBranchOutcome source.toSameTapeSource execution generated
      configuration) :
    (checkedReplayRun outcome).halt =
      .returned (checkedReplayReturned outcome) := by
  cases outcome with
  | atomic output operational =>
      rcases operational with
        ⟨_tape, _identity, _q1, _occurrenceFound, _split, _beforeFresh,
          _chosenInput, _actor, _pendingChosen, _halfClassification,
          _pendingHalf, _assigned, _prefixDefinition, _paused, _residual,
          _trace, _freshOutput, _freshAdvance, _distinct, _programmingOrder,
          _programmed, _replayDefinition, _pendingQuery, returned,
          _initialHistory, _replayHistory, _prefixSteps, _replaySteps,
          _replayFuelBound, _resources, _withinBudget⟩
      exact returned
  | noPair output operational =>
      rcases operational with ⟨exactReplay, _withinBudget⟩
      rcases exactReplay with
        ⟨_tape, _identity, _q1, _noPair, _firstReturned, _outputMissing,
          _advanceMissing, _replayDefinition, returned, _rest⟩
      exact returned

/-- A child carries the exact successful dispatcher equation.  The generated
prefix is indexed by the root DAG, while the returned DAG below is projected
from the child result and may differ. -/
structure RestrictedReplayChild
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload) where
  generated : GeneratedReplayPrefix root.dag
  configuration : AtomicPairReplayConfiguration
  outcome : ReplayBranchOutcome root.source.toSameTapeSource root.execution
    generated configuration
  dispatched : dispatchGeneratedReplayBranch root.source.toSameTapeSource
    root.execution generated configuration = .ok outcome

def RestrictedReplayChild.returnedValue
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (child : RestrictedReplayChild root) :
    CheckedTag73AdversaryReturnedValue Statement Proof Payload :=
  checkedReplayReturned child.outcome

def RestrictedReplayChild.returnedPublicProof
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (child : RestrictedReplayChild root) :
    PublicProof Statement (ParsedTag73Proof Proof Payload) :=
  child.returnedValue.1.publicProof

def RestrictedReplayChild.returnedDag
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (child : RestrictedReplayChild root) : ConcreteDagInstance :=
  child.returnedPublicProof.proof.dag

def RestrictedReplayChild.replayRun
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (child : RestrictedReplayChild root) :
    MachineRun (CheckedTag73AdversaryReturnedValue Statement Proof Payload) :=
  checkedReplayRun child.outcome

def RestrictedReplayChild.restoration
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (child : RestrictedReplayChild root) :
    ConcreteRestorationRecord root.table root.dag :=
  concreteRestoration root.execution child.generated

/-- The literal verifier computation for the child starts at the replay-final
oracle and consumes the child result's own reparsed tape.  No normal-return or
acceptance field is added. -/
def RestrictedReplayChild.returnedVerifierRun
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (child : RestrictedReplayChild root)
    (controller : AdaptiveController) (limits : OracleLimits) (fuel : Nat) :
    MachineRun VerifierPlanResult :=
  runFullVerifierPlan controller limits fuel child.replayRun.oracle
    child.replayRun.oracle child.returnedDag.tape

/-- Complete one-step invariant.  Notice that it binds the restoration to the
root DAG and separately binds the returned proof to the child DAG; it never
asserts that those DAGs are equal. -/
def RestrictedReplayChild.IsOperational
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (child : RestrictedReplayChild root) : Prop :=
  child.outcome.tapeIdentity = root.source.origin.capability.tapeIdentity ∧
  root.source.origin.capability.tapeIdentity =
    root.source.origin.firstRun.tapeIdentity ∧
  child.outcome.q1 = root.source.origin.firstRun.q1 ∧
  WithinBudget child.outcome.resources child.configuration.budget ∧
  child.replayRun.halt = .returned child.returnedValue ∧
  child.returnedDag.tape.messages.context =
    child.returnedPublicProof.publicInstance.context ∧
  IsComplete child.restoration.snapshot ∧
  PreviouslySeen child.restoration.snapshot root.execution.interactiveState ∧
  NonemptyVerifierHistory root.execution.interactiveState ∧
  child.restoration.snapshot.bindings =
    FixedBindings.ofContext root.dag.tape.messages.context ∧
  child.restoration.oracleTable = root.table ∧
  child.restoration.deployedTape = root.dag.tape ∧
  root.source.origin.capability.start root.source.observation =
    root.source.blackBox.start root.source.hiddenTape root.source.observation

theorem restricted_replay_child_is_operational
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (child : RestrictedReplayChild root) : child.IsOperational := by
  have preserved := dispatch_success_preserves_same_tape_q1_and_budget
    root.source.toSameTapeSource root.execution child.generated
      child.configuration child.outcome child.dispatched
  have restored := dispatch_success_relates_complete_seen_bound_state
    root.source.toSameTapeSource root.execution child.generated
      child.configuration child.outcome child.dispatched
  exact ⟨preserved.1, preserved.2.1, preserved.2.2.1, preserved.2.2.2,
    checked_replay_run_normally_returns_its_actual_value child.outcome,
    checked_returned_value_context_is_exact child.returnedValue,
    restored.1, restored.2.1, restored.2.2.1, restored.2.2.2.1,
    restored.2.2.2.2.1, restored.2.2.2.2.2,
    source_origin_capability_uses_same_hidden_tape
      root.source.toSameTapeSource⟩

/-- Compute one child.  A caller supplies branch controls and programmed
answers, but never supplies a restore function or an operationality proof. -/
noncomputable def dispatchRestrictedReplayChild
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload)
    (generated : GeneratedReplayPrefix root.dag)
    (configuration : AtomicPairReplayConfiguration) :
    Except ReplayBranchFailure (RestrictedReplayChild root) :=
  match dispatched : dispatchGeneratedReplayBranch root.source.toSameTapeSource
      root.execution generated configuration with
  | .error reason => .error reason
  | .ok outcome => .ok
      { generated := generated
        configuration := configuration
        outcome := outcome
        dispatched := dispatched }

theorem dispatched_restricted_child_is_operational
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload)
    (generated : GeneratedReplayPrefix root.dag)
    (configuration : AtomicPairReplayConfiguration)
    (child : RestrictedReplayChild root)
    (_success : dispatchRestrictedReplayChild root generated configuration =
      .ok child) :
    child.IsOperational :=
  restricted_replay_child_is_operational child

/-! ## Finite root-star forest and induction -/

inductive RestrictedReplayNode
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload) where
  | root
  | child (branch : RestrictedReplayChild root)

def RestrictedReplayNode.dag
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload} : RestrictedReplayNode root → ConcreteDagInstance
  | .root => root.dag
  | .child branch => branch.returnedDag

def RestrictedReplayNode.IsOperational
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload} : RestrictedReplayNode root → Prop
  | .root => root.IsOperational
  | .child branch => branch.IsOperational

theorem every_restricted_replay_node_is_operational
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (node : RestrictedReplayNode root) : node.IsOperational := by
  cases node with
  | root => exact restricted_replay_root_is_operational root
  | child branch => exact restricted_replay_child_is_operational branch

/-- A finite forest is a root plus a finite list of independently dispatched
children.  The dependent child DAG is hidden inside each list element through
its checked returned value. -/
structure RestrictedReplayForest
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload) where
  children : List (RestrictedReplayChild root)

def RestrictedReplayForest.nodeCount
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (forest : RestrictedReplayForest root) : Nat :=
  forest.children.length + 1

def RestrictedReplayForest.addChild
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (forest : RestrictedReplayForest root) (child : RestrictedReplayChild root) :
    RestrictedReplayForest root where
  children := child :: forest.children

@[simp] theorem add_child_increases_node_count_by_one
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (forest : RestrictedReplayForest root) (child : RestrictedReplayChild root) :
    (forest.addChild child).nodeCount = forest.nodeCount + 1 := by
  simp [RestrictedReplayForest.addChild, RestrictedReplayForest.nodeCount]

def RestrictedReplayForest.AllOperational
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (forest : RestrictedReplayForest root) : Prop :=
  root.IsOperational ∧ ∀ child ∈ forest.children, child.IsOperational

theorem child_list_is_operational_by_induction
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload} :
    ∀ children : List (RestrictedReplayChild root),
      ∀ child ∈ children, child.IsOperational := by
  intro children
  induction children with
  | nil => simp
  | cons head tail ih =>
      intro child member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact restricted_replay_child_is_operational child
      · exact ih child member

theorem every_restricted_replay_forest_is_operational
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (forest : RestrictedReplayForest root) : forest.AllOperational := by
  exact ⟨restricted_replay_root_is_operational root,
    child_list_is_operational_by_induction forest.children⟩

theorem add_child_preserves_all_operational_invariants
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (forest : RestrictedReplayForest root) (child : RestrictedReplayChild root)
    (_before : forest.AllOperational) :
    (forest.addChild child).AllOperational :=
  every_restricted_replay_forest_is_operational _

/-! ## Exact dependent datum needed for recursive extension -/

/-- This is the sigma package required before a returned child can itself be
used as the parent of generated replay prefixes.  The concrete execution is
indexed by the returned value's own parsed DAG.  A replay normal return alone
does not construct this package because the returned verifier run has not
been proved to return. -/
structure ReparsedDagExecution
    {Statement Proof Payload : Type*}
    (returned : CheckedTag73AdversaryReturnedValue Statement Proof Payload) where
  table : FixedOracleTable
  execution : ConcreteFirstExecution table
    returned.1.publicProof.proof.dag.tape

/-- Once the sigma package exists, a next generated prefix is necessarily
indexed by the same returned DAG. -/
structure ReparsedDagReplayCursor
    {Statement Proof Payload : Type*}
    (returned : CheckedTag73AdversaryReturnedValue Statement Proof Payload) where
  run : ReparsedDagExecution returned
  generated : GeneratedReplayPrefix returned.1.publicProof.proof.dag

def RestrictedReplayChild.CanExtendRecursively
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (child : RestrictedReplayChild root) : Prop :=
  Nonempty (ReparsedDagExecution child.returnedValue)

theorem reparsed_execution_uses_exact_child_dag_and_nonempty_history
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (child : RestrictedReplayChild root)
    (next : ReparsedDagExecution child.returnedValue) :
    next.execution.tape = child.returnedDag.tape ∧
      NonemptyVerifierHistory next.execution.interactiveState := by
  exact ⟨first_execution_retains_same_tape next.execution,
    by
      simpa [NonemptyVerifierHistory,
        ConcreteFirstExecution.interactiveState] using
          first_execution_history_is_nonempty next.execution⟩

/-- Directly transporting a root-indexed prefix to a changed child DAG is
legal only after an explicit equality proof.  The sigma cursor above avoids
inventing such an equality. -/
def transportGeneratedPrefixToReturnedDag
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (child : RestrictedReplayChild root)
    (sameDag : root.dag = child.returnedDag)
    (generated : GeneratedReplayPrefix root.dag) :
    GeneratedReplayPrefix child.returnedDag := by
  exact Eq.mp (congrArg GeneratedReplayPrefix sameDag) generated

#print axioms restricted_replay_root_is_operational
#print axioms checked_replay_run_normally_returns_its_actual_value
#print axioms restricted_replay_child_is_operational
#print axioms dispatched_restricted_child_is_operational
#print axioms every_restricted_replay_node_is_operational
#print axioms child_list_is_operational_by_induction
#print axioms every_restricted_replay_forest_is_operational
#print axioms add_child_preserves_all_operational_invariants
#print axioms reparsed_execution_uses_exact_child_dag_and_nonempty_history

end

end AspisK1.V7Tag73RestrictedReplayForest
