import PoolV1TreeAppendOneCallerBridge
import Aeneas.Tactic.Step.Step

/-!
# Pool V1 production non-full root reconstruction bridge

The translated range loop is proved against an exact pure fold first.  A
separate representation theorem then identifies that fold with the existing
`reconstructFrom` kernel.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace PoolV1TreeReconstructBridge

open Aeneas Aeneas.Std Result ControlFlow Error
open PoolV1TreeAppendOneGenerated
open PoolV1TreeAppendOneSourceBridge
open PoolV1TreeAppendOneAbstractBridge
open AspisPool.IncrementalMerkleV1

abbrev Digest := Array Std.U32 8#usize

private theorem leafCapacity_eval :
    (1#u64 <<< 20#usize) = (.ok 1048576#u64 : Result Std.U64) := by
  rfl

def reconstructConcrete (parent : Digest → Digest → Digest)
    (cursor : Nat) (frontier empty : List Digest)
    (level : Nat) : Nat → Digest → Digest
  | 0, node => node
  | fuel + 1, node =>
      if (cursor >>> level) % 2 = 0 then
        reconstructConcrete parent cursor frontier empty (level + 1) fuel
          (parent node empty[level]!)
      else
        reconstructConcrete parent cursor frontier empty (level + 1) fuel
          (parent frontier[level]! node)

def ReconstructInvariant (parent : Digest → Digest → Digest)
    (cursor : Std.U64) (frontier : Array Digest 20#usize)
    (empty : Array Digest 21#usize) (expected : Digest)
    (state : core.ops.range.Range Std.Usize × Digest) : Prop :=
  state.1.end.val = 20 ∧ state.1.start.val ≤ 20 ∧
    reconstructConcrete parent cursor.val frontier.val empty.val
      state.1.start.val (20 - state.1.start.val) state.2 = expected

def EmptyTableExact (parent : Digest → Digest → Digest)
    (emptyLeaf : Digest) (empty : List Digest) : Prop :=
  ∀ level, level ≤ 20 →
    empty[level]! = recursiveEmptyRoot parent emptyLeaf level

theorem reconstructConcrete_eq_reconstructFrom
    (parent : Digest → Digest → Digest)
    (emptyLeaf : Digest) (cursor : Nat)
    (frontier empty : List Digest) (level fuel : Nat) (node : Digest)
    (emptyExact : EmptyTableExact parent emptyLeaf empty)
    (depthBound : level + fuel ≤ 20) :
    reconstructConcrete parent cursor frontier empty level fuel node =
      reconstructFrom parent emptyLeaf level node
        (modelFrom (cursor >>> level) frontier level fuel) := by
  induction fuel generalizing level node with
  | zero => simp [reconstructConcrete, modelFrom, reconstructFrom]
  | succ fuel inductionHypothesis =>
      have levelBound : level ≤ 20 := by omega
      have emptyAtLevel := emptyExact level levelBound
      have shiftedSucc : cursor >>> (level + 1) =
          (cursor >>> level) / 2 := by
        simp [Nat.shiftRight_succ]
      by_cases even : (cursor >>> level) % 2 = 0
      · simp only [reconstructConcrete, modelFrom, even, if_pos]
        rw [emptyAtLevel]
        rw [← shiftedSucc]
        exact inductionHypothesis (level := level + 1)
          (node := parent node (recursiveEmptyRoot parent emptyLeaf level))
          (by omega)
      · have odd : (cursor >>> level) % 2 = 1 := by
          have modBound := Nat.mod_lt (cursor >>> level) (by omega : 0 < 2)
          omega
        simp only [reconstructConcrete, modelFrom, odd, if_pos,
          reconstructFrom]
        rw [← shiftedSucc]
        exact inductionHypothesis (level := level + 1)
          (node := parent frontier[level]! node) (by omega)

theorem shifted_low_bit_value
    (cursor shifted : Std.U64) (level : Std.Usize)
    (levelBound : level.val < 64)
    (shiftRun : cursor >>> level = .ok shifted) :
    (shifted &&& 1#u64).val = (cursor.val >>> level.val) % 2 := by
  have shiftSpec := Std.U64.ShiftRight_spec cursor level levelBound
  rw [shiftRun] at shiftSpec
  have andValue : (shifted &&& 1#u64).val = shifted.val % 2 := by
    rw [UScalar.val_and]
    norm_num [Nat.and_one_is_mod]
  rw [andValue, shiftSpec.1]

private theorem reconstruct_loop_body_spec
    (parent : Digest → Digest → Digest)
    (parentExact : ParentCallbackExact parent)
    (cursor : Std.U64) (frontier : Array Digest 20#usize)
    (empty : Array Digest 21#usize) (expected : Digest)
    (state : core.ops.range.Range Std.Usize × Digest)
    (invariant : ReconstructInvariant parent cursor frontier empty expected state) :
    aspis_statement.pool_v1.incremental_merkle.IncrementalMerkleTreeV1.reconstruct_nonfull_root_from_level_loop.body
        cursor frontier empty state.1 state.2
      ⦃ flow => match flow with
        | .done root => root = expected
        | .cont next =>
            ReconstructInvariant parent cursor frontier empty expected next ∧
              20 - next.1.start.val < 20 - state.1.start.val ⦄ := by
  rcases state with ⟨iter, node⟩
  rcases invariant with ⟨endEq, startBound, expectedEq⟩
  simp only at endEq startBound expectedEq ⊢
  by_cases active : iter.start.val < iter.end.val
  · have levelBound : iter.start.val < 20 := by omega
    unfold
      aspis_statement.pool_v1.incremental_merkle.IncrementalMerkleTreeV1.reconstruct_nonfull_root_from_level_loop.body
    apply WP.spec_bind
      (core.iter.range.IteratorRange.next_Usize_some_spec iter active)
    rintro ⟨option, nextIter⟩ ⟨optionEq, nextStart, nextEnd⟩
    simp only [optionEq]
    apply WP.spec_bind
      (Std.U64.ShiftRight_spec cursor iter.start (by omega))
    intro shifted shiftFacts
    simp only [bind_tc_ok, lift]
    have lowBitValue :
        (shifted &&& 1#u64).val =
          (cursor.val >>> iter.start.val) % 2 := by
      rw [UScalar.val_and]
      norm_num [Nat.and_one_is_mod, shiftFacts.1]
    by_cases bitZero : shifted &&& 1#u64 = 0#u64
    · have quotientEven : (cursor.val >>> iter.start.val) % 2 = 0 := by
        have valueEq := congrArg UScalar.val bitZero
        rw [lowBitValue] at valueEq
        simpa using valueEq
      rw [if_pos bitZero]
      have emptyIndex : iter.start.val < empty.length := by
        simpa [empty.property] using (show iter.start.val < 21 by omega)
      apply WP.spec_bind (Array.index_usize_spec empty iter.start emptyIndex)
      intro emptyAtLevel emptyEq
      rw [parentExact node emptyAtLevel]
      simp only [bind_tc_ok, WP.spec_ok]
      constructor
      · unfold ReconstructInvariant
        simp only
        have nextEndVal : nextIter.end.val = 20 := by
          rw [nextEnd]
          exact endEq
        refine ⟨nextEndVal, by omega, ?_⟩
        have remaining : 20 - iter.start.val =
            (19 - iter.start.val) + 1 := by omega
        have nextRemaining : 20 - (iter.start.val + 1) =
            19 - iter.start.val := by omega
        have emptyBang : empty.val[iter.start.val]! = emptyAtLevel := by
          rw [← List.Inhabited_getElem_eq_getElem! empty.val
            iter.start.val emptyIndex]
          exact emptyEq.symm
        rw [nextStart, nextRemaining]
        rw [remaining, reconstructConcrete, quotientEven] at expectedEq
        simp only [emptyBang] at expectedEq
        exact expectedEq
      · omega
    · have quotientNotEven :
          (cursor.val >>> iter.start.val) % 2 ≠ 0 := by
        intro quotientEven
        apply bitZero
        apply UScalar.eq_of_val_eq
        rw [lowBitValue, quotientEven]
        norm_num
      rw [if_neg bitZero]
      have frontierIndex : iter.start.val < frontier.length := by
        simpa [frontier.property] using levelBound
      apply WP.spec_bind
        (Array.index_usize_spec frontier iter.start frontierIndex)
      intro left leftEq
      rw [parentExact left node]
      simp only [bind_tc_ok, WP.spec_ok]
      constructor
      · unfold ReconstructInvariant
        simp only
        have nextEndVal : nextIter.end.val = 20 := by
          rw [nextEnd]
          exact endEq
        refine ⟨nextEndVal, by omega, ?_⟩
        have remaining : 20 - iter.start.val =
            (19 - iter.start.val) + 1 := by omega
        have nextRemaining : 20 - (iter.start.val + 1) =
            19 - iter.start.val := by omega
        have frontierBang : frontier.val[iter.start.val]! = left := by
          rw [← List.Inhabited_getElem_eq_getElem! frontier.val
            iter.start.val frontierIndex]
          exact leftEq.symm
        rw [nextStart, nextRemaining]
        rw [remaining, reconstructConcrete, if_neg quotientNotEven,
          frontierBang] at expectedEq
        exact expectedEq
      · omega
  · have finished : iter.start.val = 20 := by omega
    unfold
      aspis_statement.pool_v1.incremental_merkle.IncrementalMerkleTreeV1.reconstruct_nonfull_root_from_level_loop.body
    apply WP.spec_bind
      (core.iter.range.IteratorRange.next_Usize_none_spec iter (by omega))
    rintro ⟨option, nextIter⟩ ⟨optionEq, nextIterEq⟩
    simp only [optionEq]
    simpa [finished, reconstructConcrete] using expectedEq

theorem production_reconstruct_loop_source_exact
    (parent : Digest → Digest → Digest)
    (parentExact : ParentCallbackExact parent)
    (cursor : Std.U64) (frontier : Array Digest 20#usize)
    (empty : Array Digest 21#usize) (startLevel : Std.Usize)
    (node : Digest) (startBound : startLevel.val ≤ 20) :
    aspis_statement.pool_v1.incremental_merkle.IncrementalMerkleTreeV1.reconstruct_nonfull_root_from_level_loop
        { start := startLevel, «end» := 20#usize }
        cursor frontier empty node
      ⦃ root => root =
        reconstructConcrete parent cursor.val frontier.val empty.val
          startLevel.val (20 - startLevel.val) node ⦄ := by
  let expected := reconstructConcrete parent cursor.val frontier.val empty.val
    startLevel.val (20 - startLevel.val) node
  apply loop.spec_decr_nat
    (measure := fun state : core.ops.range.Range Std.Usize × Digest =>
      20 - state.1.start.val)
    (inv := ReconstructInvariant parent cursor frontier empty expected)
    (body := fun state =>
      aspis_statement.pool_v1.incremental_merkle.IncrementalMerkleTreeV1.reconstruct_nonfull_root_from_level_loop.body
        cursor frontier empty state.1 state.2)
  · rintro ⟨iter, current⟩ invariant
    apply WP.spec_mono
      (reconstruct_loop_body_spec parent parentExact cursor frontier empty
        expected (iter, current) invariant)
    intro flow result
    cases flow <;> exact result
  · exact ⟨rfl, startBound, rfl⟩

theorem production_reconstruct_from_level_source_exact
    (parent : Digest → Digest → Digest)
    (parentExact : ParentCallbackExact parent)
    (emptyLeaf : Digest)
    (tree : aspis_statement.pool_v1.incremental_merkle.IncrementalMerkleTreeV1)
    (empty : Array Digest 21#usize) (startLevel : Std.Usize)
    (root : Digest)
    (cursorBound : tree.next_leaf_index.val < 2 ^ 20)
    (startBound : startLevel.val ≤ 20)
    (emptyExact : EmptyTableExact parent emptyLeaf empty.val)
    (run :
      aspis_statement.pool_v1.incremental_merkle.IncrementalMerkleTreeV1.reconstruct_nonfull_root_from_level
          tree empty startLevel = .ok (.Ok root)) :
    root = reconstructFrom parent emptyLeaf startLevel.val
      (recursiveEmptyRoot parent emptyLeaf startLevel.val)
      (modelFrom (tree.next_leaf_index.val >>> startLevel.val)
        tree.frontier.val startLevel.val (20 - startLevel.val)) := by
  unfold
    aspis_statement.pool_v1.incremental_merkle.IncrementalMerkleTreeV1.reconstruct_nonfull_root_from_level
    at run
  unfold aspis_statement.pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY at run
  unfold aspis_statement.pool_v1.format.POOL_V1_TREE_DEPTH at run
  simp only [bind_tc_ok] at run
  rw [leafCapacity_eval] at run
  simp only [bind_tc_ok] at run
  have notFull : ¬ tree.next_leaf_index ≥ 1048576#u64 := by
    simpa [UScalar.le_equiv] using cursorBound
  have startNotPast : ¬ startLevel > 20#usize := by
    simpa [UScalar.lt_equiv] using startBound
  simp only [notFull, if_false, startNotPast] at run
  have emptyIndex : startLevel.val < empty.length := by
    simpa [empty.property] using (show startLevel.val < 21 by omega)
  have indexSpec := Array.index_usize_spec empty startLevel emptyIndex
  obtain ⟨initialNode, indexRun, initialNodeEq⟩ :=
    WP.spec_imp_exists indexSpec
  rw [indexRun] at run
  simp only [bind_tc_ok] at run
  have loopSpec := production_reconstruct_loop_source_exact parent parentExact
    tree.next_leaf_index tree.frontier empty startLevel initialNode startBound
  obtain ⟨loopRoot, loopRun, loopRootEq⟩ := WP.spec_imp_exists loopSpec
  rw [loopRun] at run
  simp only [bind_tc_ok] at run
  injection run with rootEq
  injection rootEq with rootValueEq
  subst root
  have initialNodeBang : empty.val[startLevel.val]! = initialNode := by
    rw [← List.Inhabited_getElem_eq_getElem! empty.val startLevel.val
      emptyIndex]
    exact initialNodeEq.symm
  have initialNodeModel :
      initialNode = recursiveEmptyRoot parent emptyLeaf startLevel.val := by
    rw [← initialNodeBang]
    exact emptyExact startLevel.val startBound
  rw [loopRootEq, initialNodeModel]
  exact reconstructConcrete_eq_reconstructFrom parent emptyLeaf
    tree.next_leaf_index.val tree.frontier.val empty.val startLevel.val
    (20 - startLevel.val)
    (recursiveEmptyRoot parent emptyLeaf startLevel.val) emptyExact (by omega)

theorem accepted_append_one_nonterminal_root_suffix_exact
    (parent : Digest → Digest → Digest)
    (parentExact : ParentCallbackExact parent)
    (emptyLeaf : Digest)
    (self next :
      aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1)
    (leaf : Digest)
    (receipt : aspis_statement.pool_v1.incremental_merkle.AppendOneV1)
    (final : CarryState)
    (loopRun :
      aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.append_one_loop
          self self.inner.next_leaf_index self.inner.frontier leaf 0#usize =
        .ok final)
    (nonterminal : final.2.2 ≠ 20#usize)
    (nextCursorBound : next.inner.next_leaf_index.val < 2 ^ 20)
    (emptyExact : EmptyTableExact parent emptyLeaf self.empty.val)
    (run :
      aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.append_one
          self leaf = .ok (.Ok (next, receipt))) :
    next.inner.root = reconstructFrom parent emptyLeaf final.2.2.val
      (recursiveEmptyRoot parent emptyLeaf final.2.2.val)
      (modelFrom (next.inner.next_leaf_index.val >>> final.2.2.val)
        next.inner.frontier.val final.2.2.val (20 - final.2.2.val)) := by
  rcases final with ⟨finalFrontier, finalRoot, finalLevel⟩
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
    cases addResult : self.inner.next_leaf_index + 1#u64 with
    | fail error => simp [addResult] at run
    | div => simp [addResult] at run
    | ok nextIndex =>
        simp only [addResult, bind_tc_ok] at run
        have terminalFalse : ¬ finalLevel = 20#usize := nonterminal
        change (if finalLevel = 20#usize then _ else _) = _ at run
        rw [if_neg terminalFalse] at run
        cases updateResult : finalFrontier.update finalLevel finalRoot with
        | fail error => simp [updateResult] at run
        | div => simp [updateResult] at run
        | ok updated =>
            rw [updateResult] at run
            simp only [bind_tc_ok] at run
            cases zeroResult : aspis_core.field.M31.ZERO with
            | fail error => simp [zeroResult] at run
            | div => simp [zeroResult] at run
            | ok zero =>
                rw [zeroResult] at run
                simp only [bind_tc_ok] at run
                let provisional :
                    aspis_statement.pool_v1.incremental_merkle.IncrementalMerkleTreeV1 :=
                  { next_leaf_index := nextIndex
                    root := Array.repeat 8#usize zero
                    frontier := updated }
                cases rootResult :
                    aspis_statement.pool_v1.incremental_merkle.IncrementalMerkleTreeV1.reconstruct_nonfull_root_from_level
                      provisional self.empty finalLevel with
                | fail error =>
                    simp [provisional, rootResult] at run
                | div =>
                    simp [provisional, rootResult] at run
                | ok rootOutcome =>
                    cases rootOutcome with
                    | Err treeError =>
                        simp [provisional, rootResult,
                          core.result.Result.Insts.CoreOpsTry.branch,
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                          at run
                    | Ok root =>
                        simp only [provisional, rootResult,
                          core.result.Result.Insts.CoreOpsTry.branch,
                          bind_tc_ok] at run
                        cases historyResult :
                            aspis_statement.pool_v1.root_history.root_history_location nextIndex with
                        | fail error =>
                            simp [historyResult] at run
                        | div =>
                            simp [historyResult] at run
                        | ok history =>
                            simp [historyResult] at run
                            rcases run with ⟨nextEq, receiptEq⟩
                            have nextIndexEq : nextIndex.val =
                                next.inner.next_leaf_index.val :=
                              congrArg
                                (fun tree :
                                  aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1 =>
                                    tree.inner.next_leaf_index.val)
                                nextEq
                            have nextCursorBound' : nextIndex.val < 2 ^ 20 := by
                              rw [nextIndexEq]
                              exact nextCursorBound
                            have levelBound : finalLevel.val ≤ 20 := by
                              have sourceTrace :=
                                append_loop_has_recursive_source_trace parent
                                  parentExact self self.inner.next_leaf_index
                                  (self.inner.frontier, leaf, 0#usize)
                              rw [loopRun] at sourceTrace
                              simp only [WP.spec_ok] at sourceTrace
                              exact
                                PoolV1TreeAppendOneCallerBridge.CarryTrace.final_level_le_depth
                                  sourceTrace (by norm_num)
                            have rootExact :=
                              production_reconstruct_from_level_source_exact
                                parent parentExact emptyLeaf provisional self.empty
                                finalLevel root nextCursorBound' levelBound
                                emptyExact rootResult
                            subst next
                            subst receipt
                            simpa [provisional] using rootExact

#print axioms shifted_low_bit_value
#print axioms reconstructConcrete_eq_reconstructFrom
#print axioms production_reconstruct_loop_source_exact
#print axioms production_reconstruct_from_level_source_exact
#print axioms accepted_append_one_nonterminal_root_suffix_exact

end PoolV1TreeReconstructBridge
