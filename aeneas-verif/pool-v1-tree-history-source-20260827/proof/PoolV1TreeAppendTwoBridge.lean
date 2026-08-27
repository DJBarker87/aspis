import PoolV1TreeAppendTwo.Funs
import Aeneas.Tactic.Step.Step

/-!
# Pool V1 ordered two-append source bridge

Literal translated two-append success is factored into the exact two
successful one-append calls, in their deployed order, and through the public
validation wrapper.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace PoolV1TreeAppendTwoBridge

open Aeneas Aeneas.Std Result ControlFlow Error
open PoolV1TreeAppendTwoGenerated

abbrev Digest := Array Std.U32 8#usize
abbrev GeneratedTree :=
  aspis_statement.pool_v1.incremental_merkle.IncrementalMerkleTreeV1
abbrev GeneratedValidatedTree :=
  aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1
abbrev GeneratedReceipt :=
  aspis_statement.pool_v1.incremental_merkle.AppendOneV1
abbrev GeneratedReceipts :=
  aspis_statement.pool_v1.incremental_merkle.AppendTwoV1

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

/-- The receipt and cursor fields of any successful translated one-append are
literal source after-images. This statement deliberately does not identify the
new root mathematically; that is the separate parent-owned tree theorem. -/
theorem append_one_success_exact_receipt_afterimage
    (self next : GeneratedValidatedTree)
    (leaf : Digest) (receipt : GeneratedReceipt)
    (run :
      aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.append_one
          self leaf = .ok (.Ok (next, receipt))) :
    next.empty = self.empty ∧
      next.inner.next_leaf_index.val = self.inner.next_leaf_index.val + 1 ∧
      receipt.leaf_index = self.inner.next_leaf_index ∧
      receipt.root_sequence = next.inner.next_leaf_index ∧
      receipt.root = next.inner.root ∧
      receipt.history.page_number.val =
        next.inner.next_leaf_index.val / 256 ∧
      receipt.history.slot.val = next.inner.next_leaf_index.val % 256 := by
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
    | ok final =>
      rcases final with ⟨finalFrontier, finalRoot, finalLevel⟩
      cases addResult : self.inner.next_leaf_index + 1#u64 with
      | fail error => simp [loopResult, addResult] at run
      | div => simp [loopResult, addResult] at run
      | ok nextIndex =>
        have addSpec := UScalar.add_equiv self.inner.next_leaf_index 1#u64
        rw [addResult] at addSpec
        have nextIndexVal : nextIndex.val =
            self.inner.next_leaf_index.val + 1 := addSpec.2.1
        by_cases terminal : finalLevel = 20#usize
        · simp only [loopResult, addResult, bind_tc_ok, terminal] at run
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
              simp [nextIndexVal, historyExact]
        · simp only [loopResult, addResult, bind_tc_ok] at run
          cases updateResult : finalFrontier.update finalLevel finalRoot with
          | fail error => simp [terminal, updateResult] at run
          | div => simp [terminal, updateResult] at run
          | ok updated =>
            cases zeroResult : aspis_core.field.M31.ZERO with
            | fail error => simp [terminal, updateResult, zeroResult] at run
            | div => simp [terminal, updateResult, zeroResult] at run
            | ok zero =>
              cases rootResult :
                  aspis_statement.pool_v1.incremental_merkle.IncrementalMerkleTreeV1.reconstruct_nonfull_root_from_level
                    { next_leaf_index := nextIndex
                      root := Array.repeat 8#usize zero
                      frontier := updated }
                    self.empty finalLevel with
              | fail error =>
                  simp [terminal, updateResult, zeroResult, rootResult] at run
              | div =>
                  simp [terminal, updateResult, zeroResult, rootResult] at run
              | ok rootOutcome =>
                  cases rootOutcome with
                  | Err treeError =>
                      simp [terminal, updateResult, zeroResult, rootResult,
                        core.result.Result.Insts.CoreOpsTry.branch,
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                        at run
                  | Ok root =>
                      cases historyResult :
                          aspis_statement.pool_v1.root_history.root_history_location nextIndex with
                      | fail error =>
                          simp [terminal, updateResult, zeroResult, rootResult,
                            historyResult,
                            core.result.Result.Insts.CoreOpsTry.branch] at run
                      | div =>
                          simp [terminal, updateResult, zeroResult, rootResult,
                            historyResult,
                            core.result.Result.Insts.CoreOpsTry.branch] at run
                      | ok history =>
                          have historyExact :=
                            generated_root_history_location_exact
                              nextIndex history historyResult
                          simp [terminal, updateResult, zeroResult, rootResult,
                            historyResult,
                            core.result.Result.Insts.CoreOpsTry.branch] at run
                          rcases run with ⟨nextEq, receiptEq⟩
                          subst next
                          subst receipt
                          simp [nextIndexVal, historyExact]

theorem validated_append_two_success_is_exact_ordered_composition
    (source next : GeneratedValidatedTree) (first second : Digest)
    (receipts : GeneratedReceipts)
    (run :
      aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.append_two
          source first second = .ok (.Ok (next, receipts))) :
    ∃ middle : GeneratedValidatedTree,
      aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.append_one
          source first = .ok (.Ok (middle, receipts.first)) ∧
      aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.append_one
          middle second = .ok (.Ok (next, receipts.second)) := by
  unfold
    aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.append_two
    at run
  cases capacityResult :
      aspis_statement.pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY with
  | fail error => simp [capacityResult] at run
  | div => simp [capacityResult] at run
  | ok capacity =>
    simp only [capacityResult, bind_tc_ok] at run
    cases remaining : U64.checked_sub capacity source.inner.next_leaf_index with
    | none =>
      simp [remaining, lift, core.option.Option.ok_or,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
        at run
    | some available =>
      simp only [remaining, lift, core.option.Option.ok_or,
        core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at run
      split at run
      · simp at run
      · cases firstRun :
          aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.append_one
            source first with
        | fail error => simp [firstRun] at run
        | div => simp [firstRun] at run
        | ok firstOutcome =>
            cases firstOutcome with
            | Err treeError =>
                simp [firstRun,
                  core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                  at run
            | Ok firstPair =>
                rcases firstPair with ⟨middle, firstReceipt⟩
                simp only [firstRun,
                  core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at run
                cases secondRun :
                    aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.append_one
                      middle second with
                | fail error => simp [secondRun] at run
                | div => simp [secondRun] at run
                | ok secondOutcome =>
                    cases secondOutcome with
                    | Err treeError =>
                        simp [secondRun,
                          core.result.Result.Insts.CoreOpsTry.branch,
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                          at run
                    | Ok secondPair =>
                        rcases secondPair with ⟨returned, secondReceipt⟩
                        simp [secondRun] at run
                        rcases run with ⟨nextEq, receiptsEq⟩
                        subst next
                        subst receipts
                        exact ⟨middle, by simpa using firstRun,
                          by simpa using secondRun⟩

theorem production_append_two_success_factors_exact_calls
    (source next : GeneratedTree) (first second : Digest)
    (empty : Array Digest 21#usize) (receipts : GeneratedReceipts)
    (run : production_tree_append_two source first second empty =
      .ok (.Ok (next, receipts))) :
    ∃ validated nextValidated : GeneratedValidatedTree,
      aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.from_parts
          source.next_leaf_index source.root source.frontier empty =
        .ok (.Ok validated) ∧
      aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.append_two
          validated first second = .ok (.Ok (nextValidated, receipts)) ∧
      validated.inner = source ∧ validated.empty = empty ∧
      nextValidated.inner = next := by
  unfold production_tree_append_two at run
  unfold
    aspis_statement.pool_v1.incremental_merkle.IncrementalMerkleTreeV1.append_two_with_empty_roots
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
              aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.append_two
                validated first second with
          | fail error => simp [appendResult] at run
          | div => simp [appendResult] at run
          | ok appendOutcome =>
              cases appendOutcome with
              | Err treeError =>
                  simp [appendResult, core.result.Result.map] at run
              | Ok pair =>
                  rcases pair with ⟨nextValidated, innerReceipts⟩
                  simp [appendResult, core.result.Result.map,
                    aspis_statement.pool_v1.incremental_merkle.IncrementalMerkleTreeV1.append_two_with_empty_roots.closure.Insts.CoreOpsFunctionFnOnceTuplePairValidatedIncrementalMerkleTreeV1AppendTwoV1PairIncrementalMerkleTreeV1AppendTwoV1.call_once,
                    aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.into_inner]
                    at run
                  rcases run with ⟨nextEq, receiptsEq⟩
                  subst next
                  subst receipts
                  refine ⟨validated, nextValidated, rfl,
                    appendResult, ?_, ?_, rfl⟩
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

theorem production_append_two_success_is_exact_ordered_composition
    (source next : GeneratedTree) (first second : Digest)
    (empty : Array Digest 21#usize) (receipts : GeneratedReceipts)
    (run : production_tree_append_two source first second empty =
      .ok (.Ok (next, receipts))) :
    ∃ validated middle nextValidated : GeneratedValidatedTree,
      aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.from_parts
          source.next_leaf_index source.root source.frontier empty =
        .ok (.Ok validated) ∧
      aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.append_one
          validated first = .ok (.Ok (middle, receipts.first)) ∧
      aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.append_one
          middle second = .ok (.Ok (nextValidated, receipts.second)) ∧
      validated.inner = source ∧ validated.empty = empty ∧
      nextValidated.inner = next := by
  obtain ⟨validated, nextValidated, validateRun, appendTwoRun,
      validatedInner, validatedEmpty, nextInner⟩ :=
    production_append_two_success_factors_exact_calls source next first second
      empty receipts run
  obtain ⟨middle, firstRun, secondRun⟩ :=
    validated_append_two_success_is_exact_ordered_composition
      validated nextValidated first second receipts appendTwoRun
  exact ⟨validated, middle, nextValidated, validateRun, firstRun, secondRun,
    validatedInner, validatedEmpty, nextInner⟩

theorem production_append_two_success_exact_receipt_afterimage
    (source next : GeneratedTree) (first second : Digest)
    (empty : Array Digest 21#usize) (receipts : GeneratedReceipts)
    (run : production_tree_append_two source first second empty =
      .ok (.Ok (next, receipts))) :
    next.next_leaf_index.val = source.next_leaf_index.val + 2 ∧
      receipts.first.leaf_index = source.next_leaf_index ∧
      receipts.first.root_sequence.val = source.next_leaf_index.val + 1 ∧
      receipts.second.leaf_index = receipts.first.root_sequence ∧
      receipts.second.root_sequence = next.next_leaf_index ∧
      receipts.second.root = next.root ∧
      receipts.first.history.page_number.val =
        receipts.first.root_sequence.val / 256 ∧
      receipts.first.history.slot.val =
        receipts.first.root_sequence.val % 256 ∧
      receipts.second.history.page_number.val =
        receipts.second.root_sequence.val / 256 ∧
      receipts.second.history.slot.val =
        receipts.second.root_sequence.val % 256 := by
  obtain ⟨validated, middle, nextValidated, validateRun, firstRun, secondRun,
      validatedInner, validatedEmpty, nextInner⟩ :=
    production_append_two_success_is_exact_ordered_composition
      source next first second empty receipts run
  have firstAfterimage := append_one_success_exact_receipt_afterimage
    validated middle first receipts.first firstRun
  have secondAfterimage := append_one_success_exact_receipt_afterimage
    middle nextValidated second receipts.second secondRun
  rcases firstAfterimage with ⟨middleEmpty, middleIndex,
    firstLeaf, firstSequence, firstRoot, firstPage, firstSlot⟩
  rcases secondAfterimage with ⟨nextEmpty, nextIndex,
    secondLeaf, secondSequence, secondRoot, secondPage, secondSlot⟩
  have finalIndex : next.next_leaf_index.val =
      source.next_leaf_index.val + 2 := by
    rw [← nextInner, nextIndex, middleIndex, validatedInner]
  refine ⟨finalIndex, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [validatedInner] using firstLeaf
  · rw [firstSequence, middleIndex, validatedInner]
  · rw [secondLeaf, ← firstSequence]
  · simpa [nextInner] using secondSequence
  · simpa [nextInner] using secondRoot
  · simpa [firstSequence] using firstPage
  · simpa [firstSequence] using firstSlot
  · simpa [secondSequence] using secondPage
  · simpa [secondSequence] using secondSlot

#print axioms generated_root_history_location_exact
#print axioms append_one_success_exact_receipt_afterimage
#print axioms validated_append_two_success_is_exact_ordered_composition
#print axioms production_append_two_success_factors_exact_calls
#print axioms production_append_two_success_is_exact_ordered_composition
#print axioms production_append_two_success_exact_receipt_afterimage

end PoolV1TreeAppendTwoBridge
