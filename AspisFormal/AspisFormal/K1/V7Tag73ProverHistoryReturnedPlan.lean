import AspisFormal.K1.V7Tag73ReplayWorkEvidenceBridge
import AspisFormal.K1.V7Tag73ReturnedPlanSemantics

/-!
# Returned Tag-73 plans with mixed prover-history evidence

This module connects a normal return of the actor-preserving prover-history
runner to the existing ROM-free interactive execution.  The construction
inverts the executable oracle program, retains the literal `fullPlan`, proves
the exact work-erased action/reply execution, and builds a
`ConcreteFirstExecution` over the runner's final shared table.

Historical grinding evidence may come from either an original adversary call
or a same-tape replay call.  Records retain their actual actors.  Simulator
and verifier records are not accepted as prover history, and the three
selected work actions remain exact verifier-issued queries.

The final section specializes the construction to the parsed DAG actually
returned by an atomic replay.  It does not equate that child DAG with the
first-run DAG and does not assert acceptance or extraction.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ProverHistoryReturnedPlan

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73InteractiveExecution
open AspisK1.V7Tag73SharedOracleVerifierRunner
open AspisK1.V7Tag73ReturnedPlanSemantics
open AspisK1.V7Tag73ReplayReturnedVerifier
open AspisK1.V7Tag73ReplayWorkEvidenceBridge
open AspisK1.V7Tag73ConcreteQueryDag
open AspisK1.V7Tag73AtomicPairReplay
open AspisK1.V7Tag73OperationalKnowledgeInput
open AspisK1.V7Tag73CoupledReplayAlignment
open AspisK1.V7FsAokExperiment

/-! ## Literal returned action semantics -/

theorem prover_history_plan_path_has_literal_semantics
    (frozenEvidence : OracleState) (bindings : FixedBindings)
    (core : RuntimeCore) (actions : List VerifierAction)
    (pairs : List (ShaInput × ShaOutput)) (result : VerifierPlanResult)
    (path : MachineQueryPath
      (verifierPlanProgramForProverHistory frozenEvidence bindings core actions)
      pairs result) :
    result.actionReplies.map Prod.fst = actions ∧
      runActionRepliesWorkErased core result.actionReplies =
        some result.finalCore := by
  induction actions generalizing core pairs result with
  | nil =>
      change MachineQueryPath
        (.pure { finalCore := core, actionReplies := [] }) pairs result at path
      cases path
      exact ⟨rfl, rfl⟩
  | cons action rest ih =>
      change MachineQueryPath
        (bindOracleMachine
          (verifierActionProgramForProverHistory frozenEvidence bindings core
            action)
          fun reply =>
            match applyActionWorkErased core action reply with
            | none => .abort .controllerRefused
            | some nextCore =>
                bindOracleMachine
                  (verifierPlanProgramForProverHistory frozenEvidence bindings
                    nextCore rest)
                  fun tail => .pure
                    { finalCore := tail.finalCore
                      actionReplies :=
                        (action, reply) :: tail.actionReplies })
        pairs result at path
      obtain ⟨reply, actionPairs, restPairs, actionPath, continuationPath,
          _pairDecomposition⟩ :=
        machine_query_path_bind_split
          (verifierActionProgramForProverHistory frozenEvidence bindings core
            action) _ _ _ path
      cases applied : applyActionWorkErased core action reply with
      | none =>
          rw [applied] at continuationPath
          change MachineQueryPath (.abort .controllerRefused)
            restPairs result at continuationPath
          cases continuationPath
      | some nextCore =>
          rw [applied] at continuationPath
          change MachineQueryPath
            (bindOracleMachine
              (verifierPlanProgramForProverHistory frozenEvidence bindings
                nextCore rest)
              fun tail => .pure
                { finalCore := tail.finalCore
                  actionReplies :=
                    (action, reply) :: tail.actionReplies })
            restPairs result at continuationPath
          obtain ⟨tail, tailPairs, finishPairs, tailPath, finishPath,
              _restDecomposition⟩ :=
            machine_query_path_bind_split
              (verifierPlanProgramForProverHistory frozenEvidence bindings
                nextCore rest) _ _ _ continuationPath
          change MachineQueryPath
            (.pure
              { finalCore := tail.finalCore
                actionReplies := (action, reply) :: tail.actionReplies })
            finishPairs result at finishPath
          cases finishPath
          obtain ⟨tailActions, tailRun⟩ :=
            ih nextCore tailPairs tail tailPath
          constructor
          · simp [tailActions]
          · simp only [runActionRepliesWorkErased, applied]
            exact tailRun

theorem returned_full_prover_history_plan_has_literal_semantics
    (controller : AdaptiveController) (limits : OracleLimits)
    (fuel : Nat) (frozenEvidence shared : OracleState)
    (tape : DeployedFixedTape) (result : VerifierPlanResult)
    (returned :
      (runFullVerifierPlanForProverHistory controller limits fuel
        frozenEvidence shared tape).halt = .returned result) :
    result.actionReplies.map Prod.fst = fullPlan tape ∧
      runActionRepliesWorkErased initialCore result.actionReplies =
        some result.finalCore := by
  obtain ⟨pairs, path, _history, _actors, _tableAnswers⟩ :=
    run_machine_returned_has_exact_query_path controller limits .verifier fuel
      shared
      (verifierPlanProgramForProverHistory frozenEvidence
        (FixedBindings.ofContext tape.messages.context) initialCore
          (fullPlan tape)) result (by
            simpa [runFullVerifierPlanForProverHistory] using returned)
  exact prover_history_plan_path_has_literal_semantics frozenEvidence
    (FixedBindings.ofContext tape.messages.context) initialCore
      (fullPlan tape) pairs result path

/-! ## Final-table derivation of mixed-history replies -/

def FrozenProverEvidenceCoveredByTable (frozenEvidence : OracleState)
    (table : FixedOracleTable) : Prop :=
  ∀ input output,
    frozenProverEvidenceOutput frozenEvidence input = some output →
      tableLookup table input = some output

/-- Derivation for one actor-preserving action path.  Nonhistorical actions
are definitionally the existing verifier action.  The sole new case is an
earlier grinding probe, whose answer is justified by mixed prover history. -/
theorem prover_history_action_path_derives_reply
    (frozenEvidence : OracleState) (table : FixedOracleTable)
    (bindings : FixedBindings) (core : RuntimeCore)
    (action : VerifierAction) (pairs : List (ShaInput × ShaOutput))
    (reply : VerifierReply)
    (path : MachineQueryPath
      (verifierActionProgramForProverHistory frozenEvidence bindings core
        action) pairs reply)
    (covered : QueryPairsCoveredByTable table pairs)
    (proverCovered : FrozenProverEvidenceCoveredByTable frozenEvidence table)
    (adversaryCovered : FrozenEvidenceCoveredByTable frozenEvidence table) :
    deriveReply table bindings core action = some reply := by
  cases action with
  | absorb payload =>
      change MachineQueryPath
        (verifierActionProgram frozenEvidence bindings core (.absorb payload))
        pairs reply at path
      exact verifier_action_path_derives_reply frozenEvidence table bindings
        core (.absorb payload) pairs reply path covered adversaryCovered
  | requestRootSalt tree =>
      change MachineQueryPath
        (verifierActionProgram frozenEvidence bindings core
          (.requestRootSalt tree)) pairs reply at path
      exact verifier_action_path_derives_reply frozenEvidence table bindings
        core (.requestRootSalt tree) pairs reply path covered adversaryCovered
  | absorbC1 root =>
      change MachineQueryPath
        (verifierActionProgram frozenEvidence bindings core (.absorbC1 root))
        pairs reply at path
      exact verifier_action_path_derives_reply frozenEvidence table bindings
        core (.absorbC1 root) pairs reply path covered adversaryCovered
  | absorbC2 lambda chi commitment =>
      change MachineQueryPath
        (verifierActionProgram frozenEvidence bindings core
          (.absorbC2 lambda chi commitment)) pairs reply at path
      exact verifier_action_path_derives_reply frozenEvidence table bindings
        core (.absorbC2 lambda chi commitment) pairs reply path covered
          adversaryCovered
  | squeezePair owner block =>
      change MachineQueryPath
        (verifierActionProgram frozenEvidence bindings core
          (.squeezePair owner block)) pairs reply at path
      exact verifier_action_path_derives_reply frozenEvidence table bindings
        core (.squeezePair owner block) pairs reply path covered adversaryCovered
  | workProbe stage nonce kind =>
      cases kind with
      | verifierSelected =>
          change MachineQueryPath
            (verifierActionProgram frozenEvidence bindings core
              (.workProbe stage nonce .verifierSelected)) pairs reply at path
          exact verifier_action_path_derives_reply frozenEvidence table bindings
            core (.workProbe stage nonce .verifierSelected) pairs reply path
              covered adversaryCovered
      | adversaryHistory =>
          rw [historical_work_program_for_prover_history_is_pure_or_abort] at path
          cases found : frozenProverEvidenceOutput frozenEvidence
              (historicalWorkInput core nonce) with
          | none =>
              rw [found] at path
              change MachineQueryPath (.abort .controllerRefused)
                pairs reply at path
              cases path
          | some output =>
              rw [found] at path
              change MachineQueryPath (.pure (.single output))
                pairs reply at path
              cases path
              have lookup : tableLookup table
                  (bytes core.digest ++ [domGrind] ++ bytes nonce) =
                    some output := by
                simpa [historicalWorkInput] using
                  proverCovered (historicalWorkInput core nonce) output found
              simp only [deriveReply, actionInputs, lookupSingleInput]
              rw [lookup]
              rfl
  | checkpoint checkpoint =>
      change MachineQueryPath
        (verifierActionProgram frozenEvidence bindings core
          (.checkpoint checkpoint)) pairs reply at path
      exact verifier_action_path_derives_reply frozenEvidence table bindings
        core (.checkpoint checkpoint) pairs reply path covered adversaryCovered
  | markQ16Base =>
      change MachineQueryPath
        (verifierActionProgram frozenEvidence bindings core .markQ16Base)
        pairs reply at path
      exact verifier_action_path_derives_reply frozenEvidence table bindings
        core .markQ16Base pairs reply path covered adversaryCovered
  | q16CandidateAbsorb counter outcome selected =>
      change MachineQueryPath
        (verifierActionProgram frozenEvidence bindings core
          (.q16CandidateAbsorb counter outcome selected)) pairs reply at path
      exact verifier_action_path_derives_reply frozenEvidence table bindings
        core (.q16CandidateAbsorb counter outcome selected) pairs reply path
          covered adversaryCovered
  | q16Restore counter =>
      change MachineQueryPath
        (verifierActionProgram frozenEvidence bindings core
          (.q16Restore counter)) pairs reply at path
      exact verifier_action_path_derives_reply frozenEvidence table bindings
        core (.q16Restore counter) pairs reply path covered adversaryCovered
  | q16Selected counter =>
      change MachineQueryPath
        (verifierActionProgram frozenEvidence bindings core
          (.q16Selected counter)) pairs reply at path
      exact verifier_action_path_derives_reply frozenEvidence table bindings
        core (.q16Selected counter) pairs reply path covered adversaryCovered
  | q16SamplerAbortReject counter =>
      change MachineQueryPath
        (verifierActionProgram frozenEvidence bindings core
          (.q16SamplerAbortReject counter)) pairs reply at path
      exact verifier_action_path_derives_reply frozenEvidence table bindings
        core (.q16SamplerAbortReject counter) pairs reply path covered
          adversaryCovered
  | q16AllNoncompactReject =>
      change MachineQueryPath
        (verifierActionProgram frozenEvidence bindings core
          .q16AllNoncompactReject) pairs reply at path
      exact verifier_action_path_derives_reply frozenEvidence table bindings
        core .q16AllNoncompactReject pairs reply path covered adversaryCovered
  | terminal =>
      change MachineQueryPath
        (verifierActionProgram frozenEvidence bindings core .terminal)
        pairs reply at path
      exact verifier_action_path_derives_reply frozenEvidence table bindings
        core .terminal pairs reply path covered adversaryCovered

private theorem query_pairs_covered_append_left
    (table : FixedOracleTable)
    (first second : List (ShaInput × ShaOutput))
    (covered : QueryPairsCoveredByTable table (first ++ second)) :
    QueryPairsCoveredByTable table first := by
  intro pair member
  exact covered pair (List.mem_append_left second member)

private theorem query_pairs_covered_append_right
    (table : FixedOracleTable)
    (first second : List (ShaInput × ShaOutput))
    (covered : QueryPairsCoveredByTable table (first ++ second)) :
    QueryPairsCoveredByTable table second := by
  intro pair member
  exact covered pair (List.mem_append_right first member)

theorem prover_history_plan_path_builds_exact_table_trace
    (frozenEvidence : OracleState) (table : FixedOracleTable)
    (bindings : FixedBindings) (core : RuntimeCore)
    (actions : List VerifierAction)
    (pairs : List (ShaInput × ShaOutput)) (result : VerifierPlanResult)
    (path : MachineQueryPath
      (verifierPlanProgramForProverHistory frozenEvidence bindings core actions)
      pairs result)
    (covered : QueryPairsCoveredByTable table pairs)
    (proverCovered : FrozenProverEvidenceCoveredByTable frozenEvidence table)
    (adversaryCovered : FrozenEvidenceCoveredByTable frozenEvidence table) :
    ∃ trace : TableExecutionTrace table bindings core actions,
      trace.actionReplies = result.actionReplies := by
  induction actions generalizing core pairs result with
  | nil =>
      change MachineQueryPath
        (.pure { finalCore := core, actionReplies := [] }) pairs result at path
      cases path
      exact ⟨.done core, rfl⟩
  | cons action rest ih =>
      change MachineQueryPath
        (bindOracleMachine
          (verifierActionProgramForProverHistory frozenEvidence bindings core
            action)
          fun reply =>
            match applyActionWorkErased core action reply with
            | none => .abort .controllerRefused
            | some nextCore =>
                bindOracleMachine
                  (verifierPlanProgramForProverHistory frozenEvidence bindings
                    nextCore rest)
                  fun tail => .pure
                    { finalCore := tail.finalCore
                      actionReplies :=
                        (action, reply) :: tail.actionReplies })
        pairs result at path
      obtain ⟨reply, actionPairs, restPairs, actionPath, continuationPath,
          pairDecomposition⟩ :=
        machine_query_path_bind_split
          (verifierActionProgramForProverHistory frozenEvidence bindings core
            action) _ _ _ path
      cases applied : applyActionWorkErased core action reply with
      | none =>
          rw [applied] at continuationPath
          change MachineQueryPath (.abort .controllerRefused)
            restPairs result at continuationPath
          cases continuationPath
      | some nextCore =>
          rw [applied] at continuationPath
          change MachineQueryPath
            (bindOracleMachine
              (verifierPlanProgramForProverHistory frozenEvidence bindings
                nextCore rest)
              fun tail => .pure
                { finalCore := tail.finalCore
                  actionReplies :=
                    (action, reply) :: tail.actionReplies })
            restPairs result at continuationPath
          obtain ⟨tail, tailPairs, finishPairs, tailPath, finishPath,
              restDecomposition⟩ :=
            machine_query_path_bind_split
              (verifierPlanProgramForProverHistory frozenEvidence bindings
                nextCore rest) _ _ _ continuationPath
          change MachineQueryPath
            (.pure
              { finalCore := tail.finalCore
                actionReplies := (action, reply) :: tail.actionReplies })
            finishPairs result at finishPath
          cases finishPath
          have coveredAction :
              QueryPairsCoveredByTable table actionPairs := by
            apply query_pairs_covered_append_left table actionPairs restPairs
            simpa [pairDecomposition] using covered
          have coveredRest : QueryPairsCoveredByTable table restPairs := by
            apply query_pairs_covered_append_right table actionPairs restPairs
            simpa [pairDecomposition] using covered
          have coveredTail : QueryPairsCoveredByTable table tailPairs := by
            have restEqualsTail : restPairs = tailPairs := by
              simpa using restDecomposition
            rw [← restEqualsTail]
            exact coveredRest
          have derived := prover_history_action_path_derives_reply
            frozenEvidence table bindings core action actionPairs reply
              actionPath coveredAction proverCovered adversaryCovered
          obtain ⟨tailTrace, tailReplies⟩ :=
            ih nextCore tailPairs tail tailPath coveredTail
          refine ⟨TableExecutionTrace.step reply derived applied tailTrace, ?_⟩
          simp [TableExecutionTrace.actionReplies, tailReplies]

/-! ## Same-start final-table coverage -/

def CachedEvidenceCoveredByTable (evidence : OracleState)
    (table : FixedOracleTable) : Prop :=
  ∀ input output, cachedEvidenceOutput evidence input = some output →
    tableLookup table input = some output

theorem prover_history_same_start_final_table_covers_cached
    (controller : AdaptiveController) (limits : OracleLimits)
    (fuel : Nat) (evidence : OracleState) (tape : DeployedFixedTape) :
    CachedEvidenceCoveredByTable evidence
      (fixedTableOfOracleState
        (runFullVerifierPlanForProverHistory controller limits fuel evidence
          evidence tape).oracle) := by
  intro input output cached
  have initiallyStored :
      tableLookup (fixedTableOfOracleState evidence) input = some output := by
    rw [fixed_table_lookup_eq_lookup_entry_output]
    simpa [cachedEvidenceOutput] using cached
  simpa [runFullVerifierPlanForProverHistory] using
    run_machine_preserves_fixed_table_answer controller limits .verifier fuel
      evidence
      (verifierPlanProgramForProverHistory evidence
        (FixedBindings.ofContext tape.messages.context) initialCore
          (fullPlan tape)) input output initiallyStored

theorem prover_history_same_start_final_table_covers_prover_evidence
    (controller : AdaptiveController) (limits : OracleLimits)
    (fuel : Nat) (evidence : OracleState) (tape : DeployedFixedTape) :
    FrozenProverEvidenceCoveredByTable evidence
      (fixedTableOfOracleState
        (runFullVerifierPlanForProverHistory controller limits fuel evidence
          evidence tape).oracle) := by
  intro input output found
  obtain ⟨_record, _member, _actor, _recordInput, _recordOutput, cached⟩ :=
    frozen_prover_evidence_has_exact_record evidence input output found
  exact prover_history_same_start_final_table_covers_cached controller limits
    fuel evidence tape input output cached

theorem prover_history_same_start_final_table_covers_adversary_evidence
    (controller : AdaptiveController) (limits : OracleLimits)
    (fuel : Nat) (evidence : OracleState) (tape : DeployedFixedTape) :
    FrozenEvidenceCoveredByTable evidence
      (fixedTableOfOracleState
        (runFullVerifierPlanForProverHistory controller limits fuel evidence
          evidence tape).oracle) := by
  intro input output found
  obtain ⟨_record, _member, _actor, _recordInput, _recordOutput, cached⟩ :=
    frozen_adversary_evidence_has_q1_record evidence input output found
  exact prover_history_same_start_final_table_covers_cached controller limits
    fuel evidence tape input output cached

/-- A normal mixed-history full-plan return produces the exact existing
table- and tape-indexed interactive first execution. -/
theorem returned_full_prover_history_plan_gives_concrete_first_execution
    (controller : AdaptiveController) (limits : OracleLimits)
    (fuel : Nat) (evidence : OracleState)
    (tape : DeployedFixedTape) (result : VerifierPlanResult)
    (returned :
      (runFullVerifierPlanForProverHistory controller limits fuel evidence
        evidence tape).halt = .returned result) :
    ∃ execution : ConcreteFirstExecution
        (fixedTableOfOracleState
          (runFullVerifierPlanForProverHistory controller limits fuel evidence
            evidence tape).oracle) tape,
      execution.trace.actionReplies = result.actionReplies := by
  obtain ⟨pairs, path, _history, _actors, tableAnswers⟩ :=
    run_machine_returned_has_exact_query_path controller limits .verifier fuel
      evidence
      (verifierPlanProgramForProverHistory evidence
        (FixedBindings.ofContext tape.messages.context) initialCore
          (fullPlan tape)) result (by
            simpa [runFullVerifierPlanForProverHistory] using returned)
  have covered : QueryPairsCoveredByTable
      (fixedTableOfOracleState
        (runFullVerifierPlanForProverHistory controller limits fuel evidence
          evidence tape).oracle) pairs := by
    intro pair member
    rcases pair with ⟨input, output⟩
    simpa [runFullVerifierPlanForProverHistory] using
      tableAnswers (input, output) member
  have proverCovered :=
    prover_history_same_start_final_table_covers_prover_evidence controller
      limits fuel evidence tape
  have adversaryCovered :=
    prover_history_same_start_final_table_covers_adversary_evidence controller
      limits fuel evidence tape
  obtain ⟨trace, exactReplies⟩ :=
    prover_history_plan_path_builds_exact_table_trace evidence
      (fixedTableOfOracleState
        (runFullVerifierPlanForProverHistory controller limits fuel evidence
          evidence tape).oracle)
      (FixedBindings.ofContext tape.messages.context) initialCore
      (fullPlan tape) pairs result path covered proverCovered adversaryCovered
  exact ⟨⟨trace⟩, exactReplies⟩

/-! ## Actual atomic replay child -/

def runProverHistoryVerifierOnAtomicReplayChild
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    {source : Tag73SameTapeSource HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    {execution : ConcreteFirstExecution table dag.tape}
    {generated : GeneratedReplayPrefix dag}
    {configuration : AtomicPairReplayConfiguration}
    (controller : AdaptiveController) (limits : OracleLimits) (fuel : Nat)
    (output :
      {run : AtomicPairReplayOutput TapeIdentity Statement
          (ParsedTag73Proof Proof Payload)
          (CheckedTag73AdversaryReturnedValue Statement Proof Payload) //
        IsOperationalAtomicPairReplay source.origin execution generated
          configuration run}) : MachineRun VerifierPlanResult :=
  runFullVerifierPlanForProverHistory controller limits fuel
    output.1.replayRun.oracle output.1.replayRun.oracle
      (atomicReplayReturnedDag output).tape

@[simp] theorem atomic_replay_child_uses_actual_returned_dag
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    {source : Tag73SameTapeSource HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    {execution : ConcreteFirstExecution table dag.tape}
    {generated : GeneratedReplayPrefix dag}
    {configuration : AtomicPairReplayConfiguration}
    (controller : AdaptiveController) (limits : OracleLimits) (fuel : Nat)
    (output :
      {run : AtomicPairReplayOutput TapeIdentity Statement
          (ParsedTag73Proof Proof Payload)
          (CheckedTag73AdversaryReturnedValue Statement Proof Payload) //
        IsOperationalAtomicPairReplay source.origin execution generated
          configuration run}) :
    runProverHistoryVerifierOnAtomicReplayChild controller limits fuel output =
      runFullVerifierPlanForProverHistory controller limits fuel
        output.1.replayRun.oracle output.1.replayRun.oracle
          output.1.returned.1.publicProof.proof.dag.tape := by
  rfl

theorem returned_atomic_replay_child_gives_concrete_first_execution
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    {source : Tag73SameTapeSource HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    {execution : ConcreteFirstExecution table dag.tape}
    {generated : GeneratedReplayPrefix dag}
    {configuration : AtomicPairReplayConfiguration}
    (controller : AdaptiveController) (limits : OracleLimits) (fuel : Nat)
    (output :
      {run : AtomicPairReplayOutput TapeIdentity Statement
          (ParsedTag73Proof Proof Payload)
          (CheckedTag73AdversaryReturnedValue Statement Proof Payload) //
        IsOperationalAtomicPairReplay source.origin execution generated
          configuration run})
    (result : VerifierPlanResult)
    (returned :
      (runProverHistoryVerifierOnAtomicReplayChild controller limits fuel
        output).halt = .returned result) :
    ∃ childExecution : ConcreteFirstExecution
        (fixedTableOfOracleState
          (runProverHistoryVerifierOnAtomicReplayChild controller limits fuel
            output).oracle)
        (atomicReplayReturnedDag output).tape,
      childExecution.trace.actionReplies = result.actionReplies := by
  exact returned_full_prover_history_plan_gives_concrete_first_execution
    controller limits fuel output.1.replayRun.oracle
      (atomicReplayReturnedDag output).tape result returned

#print axioms prover_history_plan_path_has_literal_semantics
#print axioms returned_full_prover_history_plan_has_literal_semantics
#print axioms prover_history_action_path_derives_reply
#print axioms prover_history_plan_path_builds_exact_table_trace
#print axioms returned_full_prover_history_plan_gives_concrete_first_execution
#print axioms atomic_replay_child_uses_actual_returned_dag
#print axioms returned_atomic_replay_child_gives_concrete_first_execution

end AspisK1.V7Tag73ProverHistoryReturnedPlan
