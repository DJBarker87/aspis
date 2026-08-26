import AspisFormal.K1.V7Tag73RestrictedReplayForest
import AspisFormal.K1.V7Tag73ProverHistoryReturnedPlan

/-!
# Construct restricted replay roots from concrete verifier runs

The ordinary root constructor below is definitionally tied to the actual
checked adversary return and the final-table `ConcreteFirstExecution` already
produced by `ReturnedVerifierKnowledgeSource`.  It adds no acceptance or
knowledge premise.

The second half handles the actor-preserving prover-history runner.  A normal
return from that literal runner produces a concrete execution over the
returned child's own reparsed DAG.  It deliberately stops at that graph node:
a verifier return cannot manufacture a new same-tape black-box first run.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ReplayRootFromVerifier

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73InteractiveExecution
open AspisK1.V7Tag73ConcreteQueryDag
open AspisK1.V7Tag73ConcreteStateRestoration
open AspisK1.V7Tag73OperationalKnowledgeInput
open AspisK1.V7Tag73RestrictedReplayForest
open AspisK1.V7Tag73SharedOracleVerifierRunner
open AspisK1.V7Tag73CoupledReplayAlignment
open AspisK1.V7Tag73ReturnedPlanSemantics
open AspisK1.V7Tag73ReplayWorkEvidenceBridge
open AspisK1.V7Tag73ProverHistoryReturnedPlan
open AspisK1.V7FsAokExperiment

noncomputable section

/-! ## Ordinary returned verifier to root -/

/-- The two-table operational input already contains every field of a
restricted root.  The root DAG is definitionally the DAG parsed from the
actual checked adversary return. -/
def restrictedReplayRootOfTwoTable
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (input : TwoTableConcreteK12ToK15Input HiddenTape TapeIdentity Observation
      Statement Proof Payload) :
    RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement Proof
      Payload where
  source := input.run.sameTape
  returnedValue := input.run.adversaryResult
  adversaryReturned := input.run.adversaryReturned
  table := input.run.finalTable
  execution := input.execution

@[simp] theorem two_table_root_retains_actual_returned_value
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (input : TwoTableConcreteK12ToK15Input HiddenTape TapeIdentity Observation
      Statement Proof Payload) :
    (restrictedReplayRootOfTwoTable input).returnedValue =
      input.run.adversaryResult := by
  rfl

@[simp] theorem two_table_root_retains_final_table
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (input : TwoTableConcreteK12ToK15Input HiddenTape TapeIdentity Observation
      Statement Proof Payload) :
    (restrictedReplayRootOfTwoTable input).table = input.run.finalTable := by
  rfl

@[simp] theorem two_table_root_dag_is_actual_parsed_dag
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (input : TwoTableConcreteK12ToK15Input HiddenTape TapeIdentity Observation
      Statement Proof Payload) :
    (restrictedReplayRootOfTwoTable input).dag = input.run.dag := by
  rfl

theorem two_table_constructs_operational_restricted_root
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (input : TwoTableConcreteK12ToK15Input HiddenTape TapeIdentity Observation
      Statement Proof Payload) :
    (restrictedReplayRootOfTwoTable input).IsOperational :=
  restricted_replay_root_is_operational _

/-- Every generated root cursor restores a complete, previously seen state in
the nonempty dummy-retaining history and preserves the exact fixed bindings.
-/
theorem two_table_root_every_generated_prefix_is_complete_seen_nonempty_bound
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (input : TwoTableConcreteK12ToK15Input HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (generated : GeneratedReplayPrefix
      (restrictedReplayRootOfTwoTable input).dag) :
    let root := restrictedReplayRootOfTwoTable input
    let restoration := concreteRestoration root.execution generated
    IsComplete restoration.snapshot ∧
      PreviouslySeen restoration.snapshot root.execution.interactiveState ∧
      NonemptyVerifierHistory root.execution.interactiveState ∧
      restoration.snapshot.bindings =
        FixedBindings.ofContext root.dag.tape.messages.context ∧
      restoration.oracleTable = root.table ∧
      restoration.deployedTape = root.dag.tape := by
  let root := restrictedReplayRootOfTwoTable input
  let restoration := concreteRestoration root.execution generated
  exact ⟨restoration_snapshot_is_complete restoration,
    restoration_snapshot_is_previously_seen restoration,
    restoration_first_run_history_is_nonempty restoration,
    restoration_preserves_fixed_bindings restoration,
    restoration_retains_same_oracle_table restoration,
    restoration_retains_same_deployed_tape restoration⟩

/-- Choose the final-table execution proved by an actual normally returned
ordinary verifier and package it as a root.  The choice is over a proved
existential concrete trace, not over a restore function. -/
noncomputable def restrictedReplayRootOfReturnedVerifier
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (source : ReturnedVerifierKnowledgeSource HiddenTape TapeIdentity
      Observation Statement Proof Payload) :
    RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement Proof
      Payload :=
  let witness := returned_source_constructs_final_table_execution source
  { source := source.sameTape
    returnedValue := source.adversaryResult
    adversaryReturned := source.adversaryReturned
    table := source.finalTable
    execution := Classical.choose witness }

theorem returned_verifier_root_has_exact_action_replies
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (source : ReturnedVerifierKnowledgeSource HiddenTape TapeIdentity
      Observation Statement Proof Payload) :
    (restrictedReplayRootOfReturnedVerifier source).execution.trace.actionReplies =
      source.result.actionReplies := by
  exact Classical.choose_spec
    (returned_source_constructs_final_table_execution source)

theorem returned_verifier_constructs_operational_restricted_root
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (source : ReturnedVerifierKnowledgeSource HiddenTape TapeIdentity
      Observation Statement Proof Payload) :
    (restrictedReplayRootOfReturnedVerifier source).IsOperational :=
  restricted_replay_root_is_operational _

theorem returned_verifier_root_every_generated_prefix_is_legal
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (source : ReturnedVerifierKnowledgeSource HiddenTape TapeIdentity
      Observation Statement Proof Payload)
    (generated : GeneratedReplayPrefix
      (restrictedReplayRootOfReturnedVerifier source).dag) :
    let root := restrictedReplayRootOfReturnedVerifier source
    let restoration := concreteRestoration root.execution generated
    IsComplete restoration.snapshot ∧
      PreviouslySeen restoration.snapshot root.execution.interactiveState ∧
      NonemptyVerifierHistory root.execution.interactiveState ∧
      restoration.snapshot.bindings =
        FixedBindings.ofContext root.dag.tape.messages.context := by
  let root := restrictedReplayRootOfReturnedVerifier source
  let restoration := concreteRestoration root.execution generated
  exact ⟨restoration_snapshot_is_complete restoration,
    restoration_snapshot_is_previously_seen restoration,
    restoration_first_run_history_is_nonempty restoration,
    restoration_preserves_fixed_bindings restoration⟩

/-! ## Normally returned actor-preserving verifier runs -/

/-- A normal return of the literal mixed prover-history verifier on one
checked returned value.  Its evidence is an actual oracle state, and its tape
is projected from that same returned value.  No acceptance bit or witness is
stored. -/
structure ReturnedValueProverHistoryVerifier
    {Statement Proof Payload : Type*}
    (returnedValue : CheckedTag73AdversaryReturnedValue Statement Proof
      Payload) where
  evidence : OracleState
  controller : AdaptiveController
  limits : OracleLimits
  fuel : Nat
  result : VerifierPlanResult
  returned :
    (runFullVerifierPlanForProverHistory controller limits fuel evidence
      evidence returnedValue.1.publicProof.proof.dag.tape).halt =
        .returned result

def ReturnedValueProverHistoryVerifier.verifierRun
    {Statement Proof Payload : Type*}
    {returnedValue : CheckedTag73AdversaryReturnedValue Statement Proof
      Payload}
    (run : ReturnedValueProverHistoryVerifier returnedValue) :
    MachineRun VerifierPlanResult :=
  runFullVerifierPlanForProverHistory run.controller run.limits run.fuel
    run.evidence run.evidence returnedValue.1.publicProof.proof.dag.tape

def ReturnedValueProverHistoryVerifier.finalTable
    {Statement Proof Payload : Type*}
    {returnedValue : CheckedTag73AdversaryReturnedValue Statement Proof
      Payload}
    (run : ReturnedValueProverHistoryVerifier returnedValue) :
    FixedOracleTable :=
  fixedTableOfOracleState run.verifierRun.oracle

/-- Inverting the actual normal return constructs, rather than assumes, the
concrete execution indexed by this returned value's own parsed DAG. -/
theorem returned_value_prover_history_constructs_reparsed_execution
    {Statement Proof Payload : Type*}
    {returnedValue : CheckedTag73AdversaryReturnedValue Statement Proof
      Payload}
    (run : ReturnedValueProverHistoryVerifier returnedValue) :
    ∃ next : ReparsedDagExecution returnedValue,
      next.table = run.finalTable ∧
      next.execution.trace.actionReplies = run.result.actionReplies := by
  obtain ⟨execution, exactReplies⟩ :=
    returned_full_prover_history_plan_gives_concrete_first_execution
      run.controller run.limits run.fuel run.evidence
        returnedValue.1.publicProof.proof.dag.tape run.result run.returned
  exact ⟨⟨run.finalTable, execution⟩, rfl, exactReplies⟩

/-- A fixed choice of the execution whose existence was established by the
operational runner inversion. -/
noncomputable def ReturnedValueProverHistoryVerifier.reparsedExecution
    {Statement Proof Payload : Type*}
    {returnedValue : CheckedTag73AdversaryReturnedValue Statement Proof
      Payload}
    (run : ReturnedValueProverHistoryVerifier returnedValue) :
    ReparsedDagExecution returnedValue :=
  Classical.choose
    (returned_value_prover_history_constructs_reparsed_execution run)

@[simp] theorem returned_value_reparsed_execution_uses_final_table
    {Statement Proof Payload : Type*}
    {returnedValue : CheckedTag73AdversaryReturnedValue Statement Proof
      Payload}
    (run : ReturnedValueProverHistoryVerifier returnedValue) :
    run.reparsedExecution.table = run.finalTable := by
  exact (Classical.choose_spec
    (returned_value_prover_history_constructs_reparsed_execution run)).1

theorem returned_value_reparsed_execution_has_exact_replies
    {Statement Proof Payload : Type*}
    {returnedValue : CheckedTag73AdversaryReturnedValue Statement Proof
      Payload}
    (run : ReturnedValueProverHistoryVerifier returnedValue) :
    run.reparsedExecution.execution.trace.actionReplies =
      run.result.actionReplies := by
  exact (Classical.choose_spec
    (returned_value_prover_history_constructs_reparsed_execution run)).2

/-- The exact child-DAG execution already carries the complete, previously
seen, nonempty restoration state for every generated child prefix.  This is a
graph-node fact only; it does not promote the child to a fresh black-box root.
-/
theorem returned_value_reparsed_execution_every_prefix_is_legal
    {Statement Proof Payload : Type*}
    {returnedValue : CheckedTag73AdversaryReturnedValue Statement Proof
      Payload}
    (run : ReturnedValueProverHistoryVerifier returnedValue)
    (generated : GeneratedReplayPrefix
      returnedValue.1.publicProof.proof.dag) :
    let restoration := concreteRestoration run.reparsedExecution.execution
      generated
    IsComplete restoration.snapshot ∧
      PreviouslySeen restoration.snapshot
        run.reparsedExecution.execution.interactiveState ∧
      NonemptyVerifierHistory
        run.reparsedExecution.execution.interactiveState ∧
      restoration.snapshot.bindings = FixedBindings.ofContext
        returnedValue.1.publicProof.proof.dag.tape.messages.context ∧
      restoration.oracleTable = run.finalTable ∧
      restoration.deployedTape =
        returnedValue.1.publicProof.proof.dag.tape := by
  let restoration := concreteRestoration run.reparsedExecution.execution
    generated
  exact ⟨restoration_snapshot_is_complete restoration,
    restoration_snapshot_is_previously_seen restoration,
    restoration_first_run_history_is_nonempty restoration,
    restoration_preserves_fixed_bindings restoration,
    by
      rw [restoration_retains_same_oracle_table restoration]
      exact returned_value_reparsed_execution_uses_final_table run,
    restoration_retains_same_deployed_tape restoration⟩

/-! ## Dispatcher-child specialization -/

/-- The actual replay-final state is frozen as mixed prover evidence and used
as the shared starting oracle for the verifier of the child's own returned
DAG. -/
def returnedChildProverHistoryVerifier
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (child : RestrictedReplayChild root)
    (controller : AdaptiveController) (limits : OracleLimits) (fuel : Nat)
    (result : VerifierPlanResult)
    (returned :
      (runFullVerifierPlanForProverHistory controller limits fuel
        child.replayRun.oracle child.replayRun.oracle
          child.returnedDag.tape).halt = .returned result) :
    ReturnedValueProverHistoryVerifier child.returnedValue where
  evidence := child.replayRun.oracle
  controller := controller
  limits := limits
  fuel := fuel
  result := result
  returned := returned

/-- A child verifier normal return is sufficient for the exact dependent
`ReparsedDagExecution`; no equality with the parent's DAG is used. -/
theorem returned_child_prover_history_constructs_reparsed_execution
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (child : RestrictedReplayChild root)
    (controller : AdaptiveController) (limits : OracleLimits) (fuel : Nat)
    (result : VerifierPlanResult)
    (returned :
      (runFullVerifierPlanForProverHistory controller limits fuel
        child.replayRun.oracle child.replayRun.oracle
          child.returnedDag.tape).halt = .returned result) :
    ∃ next : ReparsedDagExecution child.returnedValue,
      next.table = fixedTableOfOracleState
        (runFullVerifierPlanForProverHistory controller limits fuel
          child.replayRun.oracle child.replayRun.oracle
            child.returnedDag.tape).oracle ∧
      next.execution.trace.actionReplies = result.actionReplies := by
  simpa [returnedChildProverHistoryVerifier,
    ReturnedValueProverHistoryVerifier.finalTable,
    ReturnedValueProverHistoryVerifier.verifierRun,
    RestrictedReplayChild.returnedDag,
    RestrictedReplayChild.returnedPublicProof] using
      returned_value_prover_history_constructs_reparsed_execution
        (returnedChildProverHistoryVerifier child controller limits fuel result
          returned)

theorem returned_child_execution_every_generated_prefix_is_legal
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (child : RestrictedReplayChild root)
    (controller : AdaptiveController) (limits : OracleLimits) (fuel : Nat)
    (result : VerifierPlanResult)
    (returned :
      (runFullVerifierPlanForProverHistory controller limits fuel
        child.replayRun.oracle child.replayRun.oracle
          child.returnedDag.tape).halt = .returned result)
    (generated : GeneratedReplayPrefix child.returnedDag) :
    let run := returnedChildProverHistoryVerifier child controller limits fuel
      result returned
    let restoration := concreteRestoration run.reparsedExecution.execution
      generated
    IsComplete restoration.snapshot ∧
      PreviouslySeen restoration.snapshot
        run.reparsedExecution.execution.interactiveState ∧
      NonemptyVerifierHistory run.reparsedExecution.execution.interactiveState ∧
      restoration.snapshot.bindings =
        FixedBindings.ofContext child.returnedDag.tape.messages.context ∧
      restoration.oracleTable = fixedTableOfOracleState
        (runFullVerifierPlanForProverHistory controller limits fuel
          child.replayRun.oracle child.replayRun.oracle
            child.returnedDag.tape).oracle := by
  let run := returnedChildProverHistoryVerifier child controller limits fuel
    result returned
  have legal := returned_value_reparsed_execution_every_prefix_is_legal run
    generated
  exact ⟨legal.1, legal.2.1, legal.2.2.1, legal.2.2.2.1,
    legal.2.2.2.2.1⟩

#print axioms two_table_constructs_operational_restricted_root
#print axioms two_table_root_every_generated_prefix_is_complete_seen_nonempty_bound
#print axioms returned_verifier_root_has_exact_action_replies
#print axioms returned_verifier_constructs_operational_restricted_root
#print axioms returned_verifier_root_every_generated_prefix_is_legal
#print axioms returned_value_prover_history_constructs_reparsed_execution
#print axioms returned_value_reparsed_execution_has_exact_replies
#print axioms returned_value_reparsed_execution_every_prefix_is_legal
#print axioms returned_child_prover_history_constructs_reparsed_execution
#print axioms returned_child_execution_every_generated_prefix_is_legal

end


end AspisK1.V7Tag73ReplayRootFromVerifier
