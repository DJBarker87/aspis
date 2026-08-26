import AspisFormal.K1.V7Tag73SharedOracleVerifierRunner
import AspisFormal.K1.V7Tag73RefinementExecutionBridge

/-!
# Returned shared-oracle Tag-73 plans have literal operational semantics

This module removes a small but important ambiguity in the shared-oracle
runner.  A normal return from `verifierPlanProgram` is proved to contain one
reply for every literal input action, in the same order, and those replies run
the work-erased ancestor from the supplied core to the returned final core.

The statement is derived by inversion of the executable `OracleMachine`; it
does not assume acceptance, trace coverage, restoration, or extraction.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ReturnedPlanSemantics

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73InteractiveExecution
open AspisK1.V7Tag73RefinementExecutionBridge
open AspisK1.V7Tag73SharedOracleVerifierRunner
open AspisK1.V7Tag73CoupledReplayAlignment
open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling

/-! ## Literal reply replay -/

def runActionRepliesWorkErased :
    RuntimeCore → List (VerifierAction × VerifierReply) →
      Option RuntimeCore
  | core, [] => some core
  | core, (action, reply) :: rest => do
      let nextCore ← applyActionWorkErased core action reply
      runActionRepliesWorkErased nextCore rest

/-! ## Paths through free-machine sequencing -/

theorem machine_query_path_bind_split
    {First Second : Type*} (program : OracleMachine First)
    (next : First → OracleMachine Second)
    (pairs : List (ShaInput × ShaOutput)) (result : Second)
    (path : MachineQueryPath (bindOracleMachine program next) pairs result) :
    ∃ value headPairs tailPairs,
      MachineQueryPath program headPairs value ∧
      MachineQueryPath (next value) tailPairs result ∧
      pairs = headPairs ++ tailPairs := by
  induction program generalizing pairs result with
  | pure value =>
      exact ⟨value, [], pairs, .pure value, path, rfl⟩
  | abort reason => cases path
  | query input continuation ih =>
      change MachineQueryPath
        (.query input fun output =>
          bindOracleMachine (continuation output) next) pairs result at path
      cases path with
      | query _ _ output restPairs _ restPath =>
          obtain ⟨value, headPairs, tailPairs, headPath, tailPath, equal⟩ :=
            ih output restPairs result restPath
          exact ⟨value, (input, output) :: headPairs, tailPairs,
            .query input continuation output headPairs value headPath,
            tailPath, by simp [equal]⟩

/-! ## A returned plan is the literal action/reply execution -/

theorem verifier_plan_path_has_literal_semantics
    (frozenEvidence : OracleState) (bindings : FixedBindings)
    (core : RuntimeCore) (actions : List VerifierAction)
    (pairs : List (ShaInput × ShaOutput)) (result : VerifierPlanResult)
    (path : MachineQueryPath
      (verifierPlanProgram frozenEvidence bindings core actions)
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
          (verifierActionProgram frozenEvidence bindings core action)
          fun reply =>
            match applyActionWorkErased core action reply with
            | none => .abort .controllerRefused
            | some nextCore =>
                bindOracleMachine
                  (verifierPlanProgram frozenEvidence bindings nextCore rest)
                  fun tail => .pure
                    { finalCore := tail.finalCore
                      actionReplies := (action, reply) :: tail.actionReplies })
        pairs result at path
      obtain ⟨reply, actionPairs, restPairs, actionPath, continuationPath,
          pairDecomposition⟩ :=
        machine_query_path_bind_split
          (verifierActionProgram frozenEvidence bindings core action) _ _ _ path
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
              (verifierPlanProgram frozenEvidence bindings nextCore rest)
              fun tail => .pure
                { finalCore := tail.finalCore
                  actionReplies := (action, reply) :: tail.actionReplies })
            restPairs result at continuationPath
          obtain ⟨tail, tailPairs, finishPairs, tailPath, finishPath,
              restDecomposition⟩ :=
            machine_query_path_bind_split
              (verifierPlanProgram frozenEvidence bindings nextCore rest) _ _ _
                continuationPath
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

theorem returned_verifier_plan_has_literal_semantics
    (controller : AdaptiveController) (limits : OracleLimits)
    (fuel : Nat) (frozenEvidence shared : OracleState)
    (bindings : FixedBindings) (core : RuntimeCore)
    (actions : List VerifierAction) (result : VerifierPlanResult)
    (returned :
      (runVerifierPlan controller limits fuel frozenEvidence shared bindings
        core actions).halt = .returned result) :
    result.actionReplies.map Prod.fst = actions ∧
    runActionRepliesWorkErased core result.actionReplies =
      some result.finalCore := by
  obtain ⟨pairs, path, _history, _actors, _tableAnswers⟩ :=
    run_machine_returned_has_exact_query_path controller limits .verifier fuel
      shared (verifierPlanProgram frozenEvidence bindings core actions) result
        returned
  exact verifier_plan_path_has_literal_semantics frozenEvidence bindings core
    actions pairs result path

theorem returned_full_verifier_plan_has_literal_semantics
    (controller : AdaptiveController) (limits : OracleLimits)
    (fuel : Nat) (frozenEvidence shared : OracleState)
    (tape : DeployedFixedTape) (result : VerifierPlanResult)
    (returned :
      (runFullVerifierPlan controller limits fuel frozenEvidence shared tape).halt =
        .returned result) :
    result.actionReplies.map Prod.fst = fullPlan tape ∧
    runActionRepliesWorkErased initialCore result.actionReplies =
      some result.finalCore := by
  simpa [runFullVerifierPlan] using
    returned_verifier_plan_has_literal_semantics controller limits fuel
      frozenEvidence shared (FixedBindings.ofContext tape.messages.context)
        initialCore (fullPlan tape) result returned

/-! ## Final-table derivation of the returned replies -/

def FrozenEvidenceCoveredByTable (frozenEvidence : OracleState)
    (table : FixedOracleTable) : Prop :=
  ∀ input output,
    frozenAdversaryEvidenceOutput frozenEvidence input = some output →
      tableLookup table input = some output

def QueryPairsCoveredByTable (table : FixedOracleTable)
    (pairs : List (ShaInput × ShaOutput)) : Prop :=
  ∀ pair ∈ pairs, tableLookup table pair.1 = some pair.2

private theorem returned_outputs_derive_reply
    (frozenEvidence : OracleState) (table : FixedOracleTable)
    (bindings : FixedBindings) (core : RuntimeCore)
    (action : VerifierAction) (outputs : List ShaOutput)
    (reply : VerifierReply)
    (length : outputs.length =
      (verifierIssuedInputs bindings core action).length)
    (decoded : replyFromVerifierOutputs frozenEvidence bindings core action
      outputs = some reply)
    (covered : QueryPairsCoveredByTable table
      ((verifierIssuedInputs bindings core action).zip outputs))
    (frozenCovered : FrozenEvidenceCoveredByTable frozenEvidence table) :
    deriveReply table bindings core action = some reply := by
  cases action with
  | absorb payload =>
      obtain ⟨output, rfl⟩ := List.length_eq_one_iff.mp (by
        simpa [verifierIssuedInputs, actionInputs] using length)
      have replyEq : VerifierReply.single output = reply := by
        simpa [replyFromVerifierOutputs] using decoded
      have lookup : tableLookup table
          (bytes core.digest ++ [domAbsorb, payload.label] ++ payload.data) =
          some output := covered
            (bytes core.digest ++ [domAbsorb, payload.label] ++ payload.data,
              output) (by
        simp [verifierIssuedInputs, actionInputs])
      rw [← replyEq]
      simp only [deriveReply, actionInputs, lookupSingleInput]
      rw [lookup]
      rfl
  | requestRootSalt tree =>
      obtain ⟨output, rfl⟩ := List.length_eq_one_iff.mp (by
        simpa [verifierIssuedInputs, actionInputs] using length)
      have replyEq : VerifierReply.single output = reply := by
        simpa [replyFromVerifierOutputs] using decoded
      have lookup : tableLookup table (rootSaltInput bindings.context tree.tag) =
          some output := covered
            (rootSaltInput bindings.context tree.tag, output) (by
        simp [verifierIssuedInputs, actionInputs])
      rw [← replyEq]
      simp only [deriveReply, actionInputs, lookupSingleInput]
      rw [lookup]
      rfl
  | absorbC1 root =>
      cases salt : core.c1Salt with
      | none =>
          have empty : outputs = [] := List.length_eq_zero_iff.mp (by
            simpa [verifierIssuedInputs, actionInputs, salt] using length)
          subst outputs
          simp [replyFromVerifierOutputs] at decoded
      | some value =>
          obtain ⟨output, rfl⟩ := List.length_eq_one_iff.mp (by
            simpa [verifierIssuedInputs, actionInputs, salt] using length)
          have replyEq : VerifierReply.single output = reply := by
            simpa [replyFromVerifierOutputs] using decoded
          have lookup : tableLookup table
              (bytes core.digest ++ [domAbsorb, c1RootLabel] ++
                (Payload.c1Root root.value value).data) = some output :=
            covered
              (bytes core.digest ++ [domAbsorb, c1RootLabel] ++
                (Payload.c1Root root.value value).data, output) (by
              simp [verifierIssuedInputs, actionInputs, salt])
          rw [← replyEq]
          simp only [deriveReply, actionInputs, salt, lookupSingleInput]
          rw [lookup]
          rfl
  | absorbC2 lambda chi commitment =>
      cases salt : core.c2Salt with
      | none =>
          have empty : outputs = [] := List.length_eq_zero_iff.mp (by
            simpa [verifierIssuedInputs, actionInputs, salt] using length)
          subst outputs
          simp [replyFromVerifierOutputs] at decoded
      | some value =>
          obtain ⟨output, rfl⟩ := List.length_eq_one_iff.mp (by
            simpa [verifierIssuedInputs, actionInputs, salt] using length)
          have replyEq : VerifierReply.single output = reply := by
            simpa [replyFromVerifierOutputs] using decoded
          have lookup : tableLookup table
              (bytes core.digest ++ [domAbsorb, c2RootLabel] ++
                (Payload.c2Root commitment.root value).data) = some output :=
            covered
              (bytes core.digest ++ [domAbsorb, c2RootLabel] ++
                (Payload.c2Root commitment.root value).data, output) (by
              simp [verifierIssuedInputs, actionInputs, salt])
          rw [← replyEq]
          simp only [deriveReply, actionInputs, salt, lookupSingleInput]
          rw [lookup]
          rfl
  | squeezePair owner block =>
      obtain ⟨output, advance, rfl⟩ := List.length_eq_two.mp (by
        simpa [verifierIssuedInputs, actionInputs] using length)
      have replyEq : VerifierReply.squeeze output advance = reply := by
        simpa [replyFromVerifierOutputs] using decoded
      have outputLookup : tableLookup table
          (bytes core.digest ++ [domSqueeze]) = some output := covered
            (bytes core.digest ++ [domSqueeze], output) (by
        simp [verifierIssuedInputs, actionInputs])
      have advanceLookup : tableLookup table
          (bytes core.digest ++ [domAdvance]) = some advance := covered
            (bytes core.digest ++ [domAdvance], advance) (by
        simp [verifierIssuedInputs, actionInputs])
      rw [← replyEq]
      simp [deriveReply, actionInputs, outputLookup, advanceLookup]
  | workProbe stage nonce kind =>
      cases kind with
      | adversaryHistory =>
          have empty : outputs = [] := List.length_eq_zero_iff.mp (by
            simpa [verifierIssuedInputs] using length)
          subst outputs
          cases evidenceOutput : frozenAdversaryEvidenceOutput frozenEvidence
              (bytes core.digest ++ [domGrind] ++ bytes nonce) with
          | none =>
              change (frozenAdversaryEvidenceOutput frozenEvidence
                (bytes core.digest ++ [domGrind] ++ bytes nonce)).map
                  VerifierReply.single = some reply at decoded
              rw [evidenceOutput] at decoded
              cases decoded
          | some output =>
              have lookup := frozenCovered
                (bytes core.digest ++ [domGrind] ++ bytes nonce) output
                  evidenceOutput
              have replyEq : VerifierReply.single output = reply := by
                change (frozenAdversaryEvidenceOutput frozenEvidence
                  (bytes core.digest ++ [domGrind] ++ bytes nonce)).map
                    VerifierReply.single = some reply at decoded
                rw [evidenceOutput] at decoded
                exact Option.some.inj decoded
              rw [← replyEq]
              simp only [deriveReply, actionInputs, lookupSingleInput]
              rw [lookup]
              rfl
      | verifierSelected =>
          obtain ⟨output, rfl⟩ := List.length_eq_one_iff.mp (by
            simpa [verifierIssuedInputs, actionInputs] using length)
          have replyEq : VerifierReply.single output = reply := by
            simpa [replyFromVerifierOutputs] using decoded
          have lookup : tableLookup table
              (bytes core.digest ++ [domGrind] ++ bytes nonce) = some output :=
            covered (bytes core.digest ++ [domGrind] ++ bytes nonce, output)
              (by simp [verifierIssuedInputs, actionInputs])
          rw [← replyEq]
          simp only [deriveReply, actionInputs, lookupSingleInput]
          rw [lookup]
          rfl
  | checkpoint checkpoint =>
      have empty : outputs = [] := List.length_eq_zero_iff.mp (by
        simpa [verifierIssuedInputs, actionInputs] using length)
      subst outputs
      simpa [replyFromVerifierOutputs, deriveReply] using decoded
  | markQ16Base =>
      have empty : outputs = [] := List.length_eq_zero_iff.mp (by
        simpa [verifierIssuedInputs, actionInputs] using length)
      subst outputs
      simpa [replyFromVerifierOutputs, deriveReply] using decoded
  | q16CandidateAbsorb counter outcome selected =>
      obtain ⟨output, rfl⟩ := List.length_eq_one_iff.mp (by
        simpa [verifierIssuedInputs, actionInputs] using length)
      have replyEq : VerifierReply.single output = reply := by
        simpa [replyFromVerifierOutputs] using decoded
      have lookup : tableLookup table
          (bytes core.digest ++ [domAbsorb, queryCandidateLabel,
            UInt8.ofNat counter.val]) = some output := covered
              (bytes core.digest ++ [domAbsorb, queryCandidateLabel,
                UInt8.ofNat counter.val], output) (by
        simp [verifierIssuedInputs, actionInputs])
      rw [← replyEq]
      simp only [deriveReply, actionInputs, lookupSingleInput]
      rw [lookup]
      rfl
  | q16Restore counter =>
      have empty : outputs = [] := List.length_eq_zero_iff.mp (by
        simpa [verifierIssuedInputs, actionInputs] using length)
      subst outputs
      simpa [replyFromVerifierOutputs, deriveReply] using decoded
  | q16Selected counter =>
      have empty : outputs = [] := List.length_eq_zero_iff.mp (by
        simpa [verifierIssuedInputs, actionInputs] using length)
      subst outputs
      simpa [replyFromVerifierOutputs, deriveReply] using decoded
  | q16SamplerAbortReject counter =>
      have empty : outputs = [] := List.length_eq_zero_iff.mp (by
        simpa [verifierIssuedInputs, actionInputs] using length)
      subst outputs
      simpa [replyFromVerifierOutputs, deriveReply] using decoded
  | q16AllNoncompactReject =>
      have empty : outputs = [] := List.length_eq_zero_iff.mp (by
        simpa [verifierIssuedInputs, actionInputs] using length)
      subst outputs
      simpa [replyFromVerifierOutputs, deriveReply] using decoded
  | terminal =>
      have empty : outputs = [] := List.length_eq_zero_iff.mp (by
        simpa [verifierIssuedInputs, actionInputs] using length)
      subst outputs
      simpa [replyFromVerifierOutputs, deriveReply] using decoded

theorem verifier_action_path_derives_reply
    (frozenEvidence : OracleState) (table : FixedOracleTable)
    (bindings : FixedBindings) (core : RuntimeCore)
    (action : VerifierAction) (pairs : List (ShaInput × ShaOutput))
    (reply : VerifierReply)
    (path : MachineQueryPath
      (verifierActionProgram frozenEvidence bindings core action) pairs reply)
    (covered : QueryPairsCoveredByTable table pairs)
    (frozenCovered : FrozenEvidenceCoveredByTable frozenEvidence table) :
    deriveReply table bindings core action = some reply := by
  obtain ⟨outputs, length, equalPairs, decoded⟩ :=
    query_inputs_for_path (verifierIssuedInputs bindings core action)
      (replyFromVerifierOutputs frozenEvidence bindings core action)
        pairs reply path
  apply returned_outputs_derive_reply frozenEvidence table bindings core action
    outputs reply length decoded
  · simpa [QueryPairsCoveredByTable, equalPairs] using covered
  · exact frozenCovered

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

theorem verifier_plan_path_builds_exact_table_trace
    (frozenEvidence : OracleState) (table : FixedOracleTable)
    (bindings : FixedBindings) (core : RuntimeCore)
    (actions : List VerifierAction)
    (pairs : List (ShaInput × ShaOutput)) (result : VerifierPlanResult)
    (path : MachineQueryPath
      (verifierPlanProgram frozenEvidence bindings core actions) pairs result)
    (covered : QueryPairsCoveredByTable table pairs)
    (frozenCovered : FrozenEvidenceCoveredByTable frozenEvidence table) :
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
          (verifierActionProgram frozenEvidence bindings core action)
          fun reply =>
            match applyActionWorkErased core action reply with
            | none => .abort .controllerRefused
            | some nextCore =>
                bindOracleMachine
                  (verifierPlanProgram frozenEvidence bindings nextCore rest)
                  fun tail => .pure
                    { finalCore := tail.finalCore
                      actionReplies := (action, reply) :: tail.actionReplies })
        pairs result at path
      obtain ⟨reply, actionPairs, restPairs, actionPath, continuationPath,
          pairDecomposition⟩ :=
        machine_query_path_bind_split
          (verifierActionProgram frozenEvidence bindings core action) _ _ _ path
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
              (verifierPlanProgram frozenEvidence bindings nextCore rest)
              fun tail => .pure
                { finalCore := tail.finalCore
                  actionReplies := (action, reply) :: tail.actionReplies })
            restPairs result at continuationPath
          obtain ⟨tail, tailPairs, finishPairs, tailPath, finishPath,
              restDecomposition⟩ :=
            machine_query_path_bind_split
              (verifierPlanProgram frozenEvidence bindings nextCore rest) _ _ _
                continuationPath
          change MachineQueryPath
            (.pure
              { finalCore := tail.finalCore
                actionReplies := (action, reply) :: tail.actionReplies })
            finishPairs result at finishPath
          cases finishPath
          have coveredAction : QueryPairsCoveredByTable table actionPairs := by
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
          have derived := verifier_action_path_derives_reply frozenEvidence table
            bindings core action actionPairs reply actionPath coveredAction
              frozenCovered
          obtain ⟨tailTrace, tailReplies⟩ :=
            ih nextCore tailPairs tail tailPath coveredTail
          refine ⟨TableExecutionTrace.step reply derived applied tailTrace, ?_⟩
          simp [TableExecutionTrace.actionReplies, tailReplies]

theorem same_start_final_table_covers_frozen_evidence
    (controller : AdaptiveController) (limits : OracleLimits)
    (fuel : Nat) (frozenEvidence : OracleState)
    (bindings : FixedBindings) (core : RuntimeCore)
    (actions : List VerifierAction) :
    FrozenEvidenceCoveredByTable frozenEvidence
      (fixedTableOfOracleState
        (runVerifierPlan controller limits fuel frozenEvidence frozenEvidence
          bindings core actions).oracle) := by
  intro input output evidenceOutput
  obtain ⟨record, member, actor, recordInput, recordOutput, cached⟩ :=
    frozen_adversary_evidence_has_q1_record frozenEvidence input output
      evidenceOutput
  have initiallyStored :
      tableLookup (fixedTableOfOracleState frozenEvidence) input =
        some output := by
    rw [fixed_table_lookup_eq_lookup_entry_output]
    simpa [cachedEvidenceOutput] using cached
  simpa [runVerifierPlan] using
    run_machine_preserves_fixed_table_answer controller limits .verifier fuel
      frozenEvidence
      (verifierPlanProgram frozenEvidence bindings core actions)
      input output initiallyStored

/-- When the deployed verifier begins from the frozen post-adversary oracle
state itself, a normal full-plan return constructs the existing concrete first
execution over the final shared table.  Its action/reply list is exactly the
one returned by the shared-oracle runner. -/
theorem returned_full_plan_from_frozen_state_gives_concrete_first_execution
    (controller : AdaptiveController) (limits : OracleLimits)
    (fuel : Nat) (frozenEvidence : OracleState)
    (tape : DeployedFixedTape) (result : VerifierPlanResult)
    (returned :
      (runFullVerifierPlan controller limits fuel frozenEvidence frozenEvidence
        tape).halt = .returned result) :
    ∃ execution : ConcreteFirstExecution
        (fixedTableOfOracleState
          (runFullVerifierPlan controller limits fuel frozenEvidence
            frozenEvidence tape).oracle) tape,
      execution.trace.actionReplies = result.actionReplies := by
  obtain ⟨pairs, path, history, length, actors, tableAnswers⟩ :=
    returned_full_verifier_plan_has_exact_ordered_history controller limits fuel
      frozenEvidence frozenEvidence tape result returned
  have covered : QueryPairsCoveredByTable
      (fixedTableOfOracleState
        (runFullVerifierPlan controller limits fuel frozenEvidence
          frozenEvidence tape).oracle) pairs := tableAnswers
  have frozenCovered := same_start_final_table_covers_frozen_evidence
    controller limits fuel frozenEvidence
      (FixedBindings.ofContext tape.messages.context) initialCore (fullPlan tape)
  obtain ⟨trace, exactReplies⟩ :=
    verifier_plan_path_builds_exact_table_trace frozenEvidence
      (fixedTableOfOracleState
        (runFullVerifierPlan controller limits fuel frozenEvidence
          frozenEvidence tape).oracle)
      (FixedBindings.ofContext tape.messages.context) initialCore (fullPlan tape)
      pairs result path covered (by
        simpa [runFullVerifierPlan] using frozenCovered)
  exact ⟨⟨trace⟩, exactReplies⟩

#print axioms machine_query_path_bind_split
#print axioms verifier_plan_path_has_literal_semantics
#print axioms returned_verifier_plan_has_literal_semantics
#print axioms returned_full_verifier_plan_has_literal_semantics
#print axioms verifier_action_path_derives_reply
#print axioms verifier_plan_path_builds_exact_table_trace
#print axioms same_start_final_table_covers_frozen_evidence
#print axioms returned_full_plan_from_frozen_state_gives_concrete_first_execution

end AspisK1.V7Tag73ReturnedPlanSemantics
