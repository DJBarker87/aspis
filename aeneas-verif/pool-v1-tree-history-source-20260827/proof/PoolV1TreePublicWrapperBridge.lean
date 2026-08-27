import PoolV1TreeReconstructBridge
import Aeneas.Tactic.Step.Step

/-!
# Pool V1 public one-append wrapper bridge

Successful literal public-wrapper execution is factored into the exact
validated constructor and exact sealed one-append call it executed.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace PoolV1TreePublicWrapperBridge

open Aeneas Aeneas.Std Result ControlFlow Error
open PoolV1TreeAppendOneGenerated
open PoolV1TreeAppendOneSourceBridge
open PoolV1TreeAppendOneAbstractBridge

abbrev Digest := Array Std.U32 8#usize
abbrev GeneratedTree :=
  aspis_statement.pool_v1.incremental_merkle.IncrementalMerkleTreeV1
abbrev GeneratedValidatedTree :=
  aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1
abbrev GeneratedReceipt :=
  aspis_statement.pool_v1.incremental_merkle.AppendOneV1

theorem production_append_one_success_factors_exact_calls
    (source next : GeneratedTree) (leaf : Digest)
    (empty : Array Digest 21#usize) (receipt : GeneratedReceipt)
    (run : production_tree_append_one source leaf empty =
      .ok (.Ok (next, receipt))) :
    ∃ validated nextValidated : GeneratedValidatedTree,
      aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.from_parts
          source.next_leaf_index source.root source.frontier empty =
        .ok (.Ok validated) ∧
      aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.append_one
          validated leaf = .ok (.Ok (nextValidated, receipt)) ∧
      validated.inner = source ∧ validated.empty = empty ∧
      nextValidated.inner = next := by
  unfold production_tree_append_one at run
  unfold
    aspis_statement.pool_v1.incremental_merkle.IncrementalMerkleTreeV1.append_one_with_empty_roots
    at run
  cases validateResult :
      aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.from_parts
        source.next_leaf_index source.root source.frontier empty with
  | fail error => simp [validateResult] at run
  | div => simp [validateResult] at run
  | ok validateOutcome =>
      cases validateOutcome with
      | Err treeError =>
          simp [validateResult,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
            at run
      | Ok validated =>
          simp only [validateResult,
            core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at run
          cases appendResult :
              aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.append_one
                validated leaf with
          | fail error => simp [appendResult] at run
          | div => simp [appendResult] at run
          | ok appendOutcome =>
              cases appendOutcome with
              | Err treeError =>
                  simp [appendResult, core.result.Result.map] at run
              | Ok pair =>
                  rcases pair with ⟨nextValidated, innerReceipt⟩
                  simp [appendResult, core.result.Result.map,
                    aspis_statement.pool_v1.incremental_merkle.IncrementalMerkleTreeV1.append_one_with_empty_roots.closure.Insts.CoreOpsFunctionFnOnceTuplePairValidatedIncrementalMerkleTreeV1AppendOneV1PairIncrementalMerkleTreeV1AppendOneV1.call_once,
                    aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.into_inner]
                    at run
                  rcases run with ⟨nextEq, receiptEq⟩
                  subst next
                  subst receipt
                  refine ⟨validated, nextValidated, rfl,
                    appendResult, ?_, ?_, rfl⟩
                  · -- `from_parts` success constructs these fields literally.
                    unfold
                      aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.from_parts
                      at validateResult
                    cases validationRun :
                        aspis_statement.pool_v1.incremental_merkle.IncrementalMerkleTreeV1.validate_with_empty_roots
                          { next_leaf_index := source.next_leaf_index
                            root := source.root
                            frontier := source.frontier }
                          empty with
                    | fail error => simp [validationRun] at validateResult
                    | div => simp [validationRun] at validateResult
                    | ok validationOutcome =>
                        cases validationOutcome with
                        | Err treeError =>
                            simp [validationRun,
                              core.result.Result.Insts.CoreOpsTry.branch,
                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                              at validateResult
                        | Ok okUnit =>
                            simp [validationRun,
                              core.result.Result.Insts.CoreOpsTry.branch]
                              at validateResult
                            cases validateResult
                            rfl
                  · unfold
                      aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.from_parts
                      at validateResult
                    cases validationRun :
                        aspis_statement.pool_v1.incremental_merkle.IncrementalMerkleTreeV1.validate_with_empty_roots
                          { next_leaf_index := source.next_leaf_index
                            root := source.root
                            frontier := source.frontier }
                          empty with
                    | fail error => simp [validationRun] at validateResult
                    | div => simp [validationRun] at validateResult
                    | ok validationOutcome =>
                        cases validationOutcome with
                        | Err treeError =>
                            simp [validationRun,
                              core.result.Result.Insts.CoreOpsTry.branch,
                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                              at validateResult
                        | Ok okUnit =>
                            simp [validationRun,
                              core.result.Result.Insts.CoreOpsTry.branch]
                              at validateResult
                            cases validateResult
                            rfl

theorem production_append_one_success_implies_abstract_append_result
    (parent : Digest → Digest → Digest)
    (parentExact : ParentCallbackExact parent)
    (source next : GeneratedTree) (leaf : Digest)
    (empty : Array Digest 21#usize) (receipt : GeneratedReceipt)
    (run : production_tree_append_one source leaf empty =
      .ok (.Ok (next, receipt))) :
    ∃ final : CarryState,
      match finalizedTraceResult final with
      | .more _ =>
          AspisPool.IncrementalMerkleV1.appendCarry parent leaf
              (modelFrontier source.next_leaf_index.val source.frontier.val) =
            .more (modelFrontier next.next_leaf_index.val next.frontier.val)
      | .full root =>
          AspisPool.IncrementalMerkleV1.appendCarry parent leaf
              (modelFrontier source.next_leaf_index.val source.frontier.val) =
            .full root := by
  obtain ⟨validated, nextValidated, validateRun, appendRun,
      validatedInner, validatedEmpty, nextInner⟩ :=
    production_append_one_success_factors_exact_calls source next leaf empty
      receipt run
  obtain ⟨final, loopRun, abstractResult⟩ :=
    PoolV1TreeAppendOneCallerBridge.accepted_append_one_implies_abstract_append_result
      parent parentExact validated nextValidated leaf receipt appendRun
  refine ⟨final, ?_⟩
  cases result : finalizedTraceResult final with
  | more updated =>
      rw [result] at abstractResult
      change AspisPool.IncrementalMerkleV1.appendCarry parent leaf
        (modelFrontier validated.inner.next_leaf_index.val
          validated.inner.frontier.val) =
        .more (modelFrontier nextValidated.inner.next_leaf_index.val
          nextValidated.inner.frontier.val) at abstractResult
      change AspisPool.IncrementalMerkleV1.appendCarry parent leaf
        (modelFrontier source.next_leaf_index.val source.frontier.val) =
        .more (modelFrontier next.next_leaf_index.val next.frontier.val)
      simpa [validatedInner, nextInner] using abstractResult
  | full root =>
      rw [result] at abstractResult
      change AspisPool.IncrementalMerkleV1.appendCarry parent leaf
        (modelFrontier validated.inner.next_leaf_index.val
          validated.inner.frontier.val) = .full root at abstractResult
      change AspisPool.IncrementalMerkleV1.appendCarry parent leaf
        (modelFrontier source.next_leaf_index.val source.frontier.val) =
        .full root
      simpa [validatedInner] using abstractResult

#print axioms production_append_one_success_factors_exact_calls
#print axioms production_append_one_success_implies_abstract_append_result

end PoolV1TreePublicWrapperBridge
