import PoolV1TreeAppendOneAbstractBridge
import Aeneas.Tactic.Step.Step

/-!
# Pool V1 production outer one-append caller bridge

This file lifts the exact carry-loop theorem through the translated
`ValidatedIncrementalMerkleTreeV1::append_one` caller.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace PoolV1TreeAppendOneCallerBridge

open Aeneas Aeneas.Std Result ControlFlow Error
open PoolV1TreeAppendOneGenerated
open PoolV1TreeAppendOneSourceBridge
open PoolV1TreeAppendOneAbstractBridge

abbrev Digest := Array Std.U32 8#usize
abbrev GeneratedValidatedTree :=
  aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1
abbrev GeneratedReceipt :=
  aspis_statement.pool_v1.incremental_merkle.AppendOneV1
abbrev GeneratedLocation :=
  aspis_statement.pool_v1.root_history.RootHistoryLocationV1

private theorem leafCapacity_eval :
    (1#u64 <<< 20#usize) = (.ok 1048576#u64 : Result Std.U64) := by
  rfl

theorem generated_root_history_location_exact
    (sequence : Std.U64) (location : GeneratedLocation)
    (run :
      aspis_statement.pool_v1.root_history.root_history_location sequence =
        .ok location) :
    location.page_number.val = sequence.val / 256 ∧
      location.slot.val = sequence.val % 256 := by
  have specification :
      aspis_statement.pool_v1.root_history.root_history_location sequence
        ⦃ result =>
          result.page_number.val = sequence.val / 256 ∧
            result.slot.val = sequence.val % 256 ⦄ := by
    unfold aspis_statement.pool_v1.root_history.root_history_location
    unfold aspis_statement.pool_v1.root_history.POOL_V1_ROOT_HISTORY_CAPACITY
    unfold
      aspis_statement.pool_v1.root_history.POOL_V1_ROOT_HISTORY_CAPACITY_LOG2
    repeat' step
    all_goals simp_all
    all_goals cases System.Platform.numBits_eq <;>
      simp [Usize.size, Usize.numBits, UScalarTy.numBits, *]
    all_goals omega
  rw [run] at specification
  exact specification

theorem accepted_append_one_exposes_loop
    (self next : GeneratedValidatedTree)
    (leaf : Digest) (receipt : GeneratedReceipt)
    (run :
      aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.append_one
          self leaf = .ok (.Ok (next, receipt))) :
    ∃ final : CarryState,
      aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.append_one_loop
          self self.inner.next_leaf_index self.inner.frontier leaf 0#usize =
        .ok final := by
  unfold
    aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.append_one
    at run
  unfold aspis_statement.pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY at run
  unfold aspis_statement.pool_v1.format.POOL_V1_TREE_DEPTH at run
  simp only [bind_tc_ok] at run
  rw [leafCapacity_eval] at run
  simp only [bind_tc_ok] at run
  by_cases full : self.inner.next_leaf_index = 1048576#u64
  · simp [full] at run
  · simp only [full, if_false] at run
    cases loopResult :
        aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.append_one_loop
          self self.inner.next_leaf_index self.inner.frontier leaf 0#usize with
    | fail error => simp [loopResult] at run
    | div => simp [loopResult] at run
    | ok final => exact ⟨final, rfl⟩

def finalizedCallerFrontier (final : CarryState) : Array Digest 20#usize :=
  if final.2.2 = 20#usize then
    final.1
  else
    final.1.set final.2.2 final.2.1

theorem CarryTrace.final_level_le_depth
    {parent : Digest → Digest → Digest}
    {self : GeneratedValidatedTree} {leafIndex : Std.U64}
    {start final : CarryState}
    (trace : CarryTrace parent self leafIndex start final)
    (startBound : start.2.2.val ≤ 20) :
    final.2.2.val ≤ 20 := by
  induction trace with
  | terminal => exact startBound
  | @step before next final oneStep rest inductionHypothesis =>
      rcases oneStep with
        ⟨levelLt, shifted, shiftRun, bitOne, left, leftEq,
          emptyAtLevel, emptyEq, nextLevel, nextLevelVal, afterEq⟩
      subst next
      apply inductionHypothesis
      simpa [nextLevelVal] using (show before.2.2.val + 1 ≤ 20 by omega)

theorem accepted_append_one_exact_structural_afterimage
    (parent : Digest → Digest → Digest)
    (parentExact : ParentCallbackExact parent)
    (self next : GeneratedValidatedTree)
    (leaf : Digest) (receipt : GeneratedReceipt)
    (run :
      aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.append_one
          self leaf = .ok (.Ok (next, receipt))) :
    ∃ final : CarryState,
      aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.append_one_loop
          self self.inner.next_leaf_index self.inner.frontier leaf 0#usize =
        .ok final ∧
      next.empty = self.empty ∧
      next.inner.next_leaf_index.val = self.inner.next_leaf_index.val + 1 ∧
      next.inner.frontier = finalizedCallerFrontier final ∧
      receipt.leaf_index = self.inner.next_leaf_index ∧
      receipt.root_sequence = next.inner.next_leaf_index ∧
      receipt.root = next.inner.root ∧
      receipt.history.page_number.val =
        next.inner.next_leaf_index.val / 256 ∧
      receipt.history.slot.val = next.inner.next_leaf_index.val % 256 := by
  obtain ⟨final, loopRun⟩ :=
    accepted_append_one_exposes_loop self next leaf receipt run
  refine ⟨final, loopRun, ?_⟩
  unfold
    aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.append_one
    at run
  unfold aspis_statement.pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY at run
  unfold aspis_statement.pool_v1.format.POOL_V1_TREE_DEPTH at run
  simp only [bind_tc_ok] at run
  rw [leafCapacity_eval] at run
  simp only [bind_tc_ok] at run
  by_cases full : self.inner.next_leaf_index = 1048576#u64
  · simp [full] at run
  · simp only [full, if_false, loopRun, bind_tc_ok] at run
    rcases final with ⟨finalFrontier, finalRoot, finalLevel⟩
    have sourceTrace := append_loop_has_recursive_source_trace
      parent parentExact self self.inner.next_leaf_index
      (self.inner.frontier, leaf, 0#usize)
    rw [loopRun] at sourceTrace
    simp only [WP.spec_ok] at sourceTrace
    have finalLevelBound : finalLevel.val ≤ 20 :=
      PoolV1TreeAppendOneCallerBridge.CarryTrace.final_level_le_depth
        sourceTrace (by norm_num)
    cases addResult : self.inner.next_leaf_index + 1#u64 with
    | fail error => simp [addResult] at run
    | div => simp [addResult] at run
    | ok nextIndex =>
        have addSpec := UScalar.add_equiv self.inner.next_leaf_index 1#u64
        rw [addResult] at addSpec
        have nextIndexVal : nextIndex.val =
            self.inner.next_leaf_index.val + 1 := addSpec.2.1
        by_cases terminal : finalLevel = 20#usize
        · simp only [addResult, bind_tc_ok, terminal] at run
          cases historyResult :
              aspis_statement.pool_v1.root_history.root_history_location nextIndex with
          | fail error => simp [historyResult] at run
          | div => simp [historyResult] at run
          | ok history =>
              have historyExact := generated_root_history_location_exact
                nextIndex history historyResult
              simp [historyResult] at run
              rcases run with ⟨nextEq, receiptEq⟩
              subst next
              subst receipt
              simp [finalizedCallerFrontier, terminal, nextIndexVal,
                historyExact]
        · simp only [addResult, bind_tc_ok] at run
          cases updateResult : finalFrontier.update finalLevel finalRoot with
          | fail error => simp [terminal, updateResult] at run
          | div => simp [terminal, updateResult] at run
          | ok updated =>
              have terminalValNe : finalLevel.val ≠ 20 := by
                intro levelEq
                apply terminal
                apply UScalar.eq_of_val_eq
                simpa using levelEq
              have finalLevelLt : finalLevel.val < 20 := by omega
              have updateSpec := Array.update_spec finalFrontier finalLevel
                finalRoot (by simpa [finalFrontier.property] using finalLevelLt)
              rw [updateResult] at updateSpec
              simp only [WP.spec_ok] at updateSpec
              cases zeroResult : aspis_core.field.M31.ZERO with
              | fail error =>
                  simp [terminal, updateResult, zeroResult] at run
              | div =>
                  simp [terminal, updateResult, zeroResult] at run
              | ok zero =>
                  cases rootResult :
                      aspis_statement.pool_v1.incremental_merkle.IncrementalMerkleTreeV1.reconstruct_nonfull_root_from_level
                        { next_leaf_index := nextIndex
                          root := Array.repeat 8#usize zero
                          frontier := updated }
                        self.empty finalLevel with
                  | fail error =>
                      simp [terminal, updateResult, zeroResult, rootResult]
                        at run
                  | div =>
                      simp [terminal, updateResult, zeroResult, rootResult]
                        at run
                  | ok rootOutcome =>
                      cases rootOutcome with
                      | Err treeError =>
                          simp [updateResult, zeroResult, rootResult,
                            terminal,
                            core.result.Result.Insts.CoreOpsTry.branch,
                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                            at run
                      | Ok root =>
                          cases historyResult :
                              aspis_statement.pool_v1.root_history.root_history_location nextIndex with
                          | fail error =>
                              simp [updateResult, zeroResult, rootResult,
                                historyResult, terminal,
                                core.result.Result.Insts.CoreOpsTry.branch]
                                at run
                          | div =>
                              simp [updateResult, zeroResult, rootResult,
                                historyResult, terminal,
                                core.result.Result.Insts.CoreOpsTry.branch]
                                at run
                          | ok history =>
                              have historyExact :=
                                generated_root_history_location_exact
                                  nextIndex history historyResult
                              simp [updateResult, zeroResult, rootResult,
                                historyResult, terminal,
                                core.result.Result.Insts.CoreOpsTry.branch]
                                at run
                              rcases run with ⟨nextEq, receiptEq⟩
                              subst next
                              subst receipt
                              simp [finalizedCallerFrontier, terminal,
                                nextIndexVal, updateSpec, historyExact]

/-- Successful translated outer-caller execution refines the same abstract
append result as the carry loop, using the returned tree's exact cursor and
frontier in the open case. -/
theorem accepted_append_one_implies_abstract_append_result
    (parent : Digest → Digest → Digest)
    (parentExact : ParentCallbackExact parent)
    (self next : GeneratedValidatedTree)
    (leaf : Digest) (receipt : GeneratedReceipt)
    (run :
      aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.append_one
          self leaf = .ok (.Ok (next, receipt))) :
    ∃ final : CarryState,
      aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.append_one_loop
          self self.inner.next_leaf_index self.inner.frontier leaf 0#usize =
        .ok final ∧
      match finalizedTraceResult final with
      | .more _ =>
          AspisPool.IncrementalMerkleV1.appendCarry parent leaf
              (modelFrontier self.inner.next_leaf_index.val
                self.inner.frontier.val) =
            .more (modelFrontier next.inner.next_leaf_index.val
              next.inner.frontier.val)
      | .full root =>
          AspisPool.IncrementalMerkleV1.appendCarry parent leaf
              (modelFrontier self.inner.next_leaf_index.val
                self.inner.frontier.val) = .full root := by
  obtain ⟨final, loopRun, emptyEq, nextIndexVal, nextFrontierEq,
      receiptLeafEq, receiptSequenceEq, receiptRootEq,
      receiptPageEq, receiptSlotEq⟩ :=
    accepted_append_one_exact_structural_afterimage parent parentExact
      self next leaf receipt run
  refine ⟨final, loopRun, ?_⟩
  have abstractResult :=
    translated_append_loop_implies_modelFrontier_appendCarry
      parent parentExact self self.inner.next_leaf_index self.inner.frontier
      leaf final loopRun
  rcases final with ⟨finalFrontier, finalRoot, finalLevel⟩
  by_cases terminal : finalLevel = 20#usize
  · have terminalVal : finalLevel.val = 20 := congrArg UScalar.val terminal
    simp only [finalizedTraceResult, terminalVal, if_pos] at abstractResult ⊢
    exact abstractResult
  · have terminalVal : finalLevel.val ≠ 20 := by
      intro levelEq
      apply terminal
      apply UScalar.eq_of_val_eq
      simpa using levelEq
    have concreteFrontier :
        next.inner.frontier = finalFrontier.set finalLevel finalRoot := by
      simpa [finalizedCallerFrontier, terminal] using nextFrontierEq
    simp only [finalizedTraceResult, terminalVal, if_false] at abstractResult ⊢
    rw [nextIndexVal, concreteFrontier]
    simpa [Array.set_val_eq] using abstractResult

#print axioms accepted_append_one_exposes_loop
#print axioms generated_root_history_location_exact
#print axioms CarryTrace.final_level_le_depth
#print axioms accepted_append_one_exact_structural_afterimage
#print axioms accepted_append_one_implies_abstract_append_result

end PoolV1TreeAppendOneCallerBridge
