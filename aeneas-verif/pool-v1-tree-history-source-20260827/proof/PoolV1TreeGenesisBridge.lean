import PoolV1TreeGenesis.Funs
import AspisFormal.Pool.PoolTreeHistoryInvariantV1
import Aeneas.Tactic.Step.Step

/-!
# Pool V1 production genesis bridge

This file proves the structural part of the literal production
`IncrementalMerkleTreeV1::empty` implementation.  The only semantic premise is
the explicitly named Poseidon tree-parent callback boundary.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace PoolV1TreeGenesisSourceBridge

open Aeneas Aeneas.Std Result ControlFlow Error
open PoolV1TreeGenesisGenerated
open AspisPool.IncrementalMerkleV1

abbrev Digest := Array Std.U32 8#usize
abbrev GeneratedTree :=
  aspis_statement.pool_v1.incremental_merkle.IncrementalMerkleTreeV1

def zeroDigest : Digest := Array.repeat 8#usize 0#u32

def ParentCallbackExact (parent : Digest → Digest → Digest) : Prop :=
  ∀ left right,
    aspis_statement.pool_v1.format.pool_v1_tree_parent left right =
      .ok (parent left right)

def EmptyRootsPrefix (parent : Digest → Digest → Digest)
    (roots : Array Digest 21#usize) (count : Nat) : Prop :=
  ∀ level, level ≤ count →
    roots.val[level]! = recursiveEmptyRoot parent zeroDigest level

def EmptyRootsLoopInvariant (parent : Digest → Digest → Digest)
    (state : core.ops.range.Range Std.Usize × Array Digest 21#usize) : Prop :=
  state.1.end.val = 20 ∧ state.1.start.val ≤ 20 ∧
    EmptyRootsPrefix parent state.2 state.1.start.val

def EmptyRootsPost (parent : Digest → Digest → Digest)
    (roots : Array Digest 21#usize) : Prop :=
  EmptyRootsPrefix parent roots 20

def modelFrontier (tree : GeneratedTree) : List (Option Digest) :=
  (List.range 20).map fun level =>
    if tree.next_leaf_index.val.testBit level then
      some tree.frontier.val[level]!
    else
      none

private theorem empty_roots_loop_body_spec
    (parent : Digest → Digest → Digest)
    (parentExact : ParentCallbackExact parent)
    (state : core.ops.range.Range Std.Usize × Array Digest 21#usize)
    (invariant : EmptyRootsLoopInvariant parent state) :
    aspis_statement.pool_v1.incremental_merkle.pool_v1_empty_roots_loop.body
        state.1 state.2
      ⦃ flow => match flow with
        | .done roots => EmptyRootsPost parent roots
        | .cont next =>
            EmptyRootsLoopInvariant parent next ∧
              20 - next.1.start.val < 20 - state.1.start.val ⦄ := by
  rcases state with ⟨iter, roots⟩
  rcases invariant with ⟨hend, hstart, hprefix⟩
  simp only at hend hstart hprefix
  by_cases hactive : iter.start.val < iter.end.val
  · have hlevel : iter.start.val < 20 := by omega
    have hindex : iter.start.val < roots.length := by
      simpa [roots.property] using (show iter.start.val < 21 by omega)
    have hnextIndex : iter.start.val + 1 < roots.length := by
      simpa [roots.property] using (show iter.start.val + 1 < 21 by omega)
    have hwrap :
        (iter.start.wrapping_add 1#usize).val = iter.start.val + 1 := by
      rw [Usize.wrapping_add_val_eq]
      apply Nat.mod_eq_of_lt
      rcases System.Platform.numBits_eq with hbits | hbits <;>
        simp [UScalar.size, Usize.size, Usize.numBits, UScalarTy.numBits,
          hbits] <;> omega
    unfold aspis_statement.pool_v1.incremental_merkle.pool_v1_empty_roots_loop.body
    apply WP.spec_bind
      (core.iter.range.IteratorRange.next_Usize_some_spec iter hactive)
    rintro ⟨option, nextIter⟩ ⟨hoption, hnextStart, hnextEnd⟩
    simp only [hoption]
    apply WP.spec_bind (Array.index_usize_spec roots iter.start hindex)
    intro node hnode
    rw [parentExact node node]
    simp only [bind_tc_ok]
    repeat' step
    simp only [EmptyRootsLoopInvariant, EmptyRootsPrefix, hnextEnd, hend,
      hnextStart, roots1_post, i_post, hnode, true_and]
    refine ⟨⟨by omega, ?_⟩, by omega⟩
    intro level hle
    by_cases hnew : level = iter.start.val + 1
    · subst level
      rw [Array.set_val_eq, hwrap]
      rw [List.set_getElem!_eq _ _ _ _ ⟨hnextIndex, rfl⟩]
      have hcurrent :
          roots.val[iter.start.val]'hindex =
            recursiveEmptyRoot parent zeroDigest iter.start.val := by
        rw [List.Inhabited_getElem_eq_getElem! roots.val iter.start.val hindex]
        exact hprefix iter.start.val (by omega)
      simpa only [recursiveEmptyRoot, hcurrent]
    · have hold : level ≤ iter.start.val := by omega
      have holdValue := hprefix level hold
      rw [Array.set_val_eq, hwrap]
      rw [List.set_getElem!_ne _ _ _ _ (by omega)]
      exact holdValue
  · have hdone : iter.start.val = 20 := by omega
    unfold aspis_statement.pool_v1.incremental_merkle.pool_v1_empty_roots_loop.body
    apply WP.spec_bind
      (core.iter.range.IteratorRange.next_Usize_none_spec iter (by omega))
    rintro ⟨option, nextIter⟩ ⟨hoption, hnextIter⟩
    simp only [hoption, WP.spec_ok]
    simpa [EmptyRootsPost, hdone] using hprefix

theorem production_empty_roots_source_exact
    (parent : Digest → Digest → Digest)
    (parentExact : ParentCallbackExact parent) :
    aspis_statement.pool_v1.incremental_merkle.pool_v1_empty_roots
      ⦃ roots => EmptyRootsPost parent roots ⦄ := by
  unfold aspis_statement.pool_v1.incremental_merkle.pool_v1_empty_roots
  simp only [aspis_core.field.M31.ZERO,
    aspis_statement.pool_v1.format.POOL_V1_TREE_DEPTH, bind_tc_ok]
  apply loop.spec_decr_nat
    (measure := fun state : core.ops.range.Range Std.Usize × Array Digest 21#usize =>
      20 - state.1.start.val)
    (inv := EmptyRootsLoopInvariant parent)
    (body := fun state =>
      aspis_statement.pool_v1.incremental_merkle.pool_v1_empty_roots_loop.body
        state.1 state.2)
  · rintro ⟨iter, roots⟩ invariant
    apply WP.spec_mono
      (empty_roots_loop_body_spec parent parentExact (iter, roots) invariant)
    intro flow hflow
    cases flow <;> exact hflow
  · refine ⟨by norm_num, by norm_num, ?_⟩
    intro level hlevel
    change level ≤ 0 at hlevel
    have : level = 0 := by omega
    subst level
    simp [zeroDigest, recursiveEmptyRoot]

theorem production_tree_genesis_source_state_exact
    (parent : Digest → Digest → Digest)
    (parentExact : ParentCallbackExact parent) :
    production_tree_genesis
      ⦃ tree =>
        tree.next_leaf_index.val = 0 ∧
        tree.root = recursiveEmptyRoot parent zeroDigest 20 ∧
        modelFrontier tree =
          List.replicate 20 (Option.none : Option Digest) ⦄ := by
  unfold production_tree_genesis
  unfold aspis_statement.pool_v1.incremental_merkle.IncrementalMerkleTreeV1.empty
  apply WP.spec_bind (production_empty_roots_source_exact parent parentExact)
  intro empty hempty
  have hindex : 20 < empty.length := by
    simpa [empty.property]
  apply WP.spec_bind (Array.index_usize_spec empty 20#usize hindex)
  intro root hroot
  have hempty20 :
      empty.val[20]'hindex = recursiveEmptyRoot parent zeroDigest 20 := by
    rw [List.Inhabited_getElem_eq_getElem! empty.val 20 hindex]
    exact hempty 20 (by omega)
  unfold core.array.from_fn
  simp only [if_pos rfl, bind_tc_ok]
  unfold
    aspis_statement.pool_v1.incremental_merkle.IncrementalMerkleTreeV1.empty.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM318.call_mut
  simp [Array.index_usize, empty.property, modelFrontier, hempty20]
  exact hroot.trans hempty20

theorem production_tree_genesis_establishes_pool_tree_history
    (parent : Digest → Digest → Digest)
    (parentExact : ParentCallbackExact parent)
    (tree : GeneratedTree)
    (run : production_tree_genesis = .ok tree) :
    AspisPool.PoolTreeHistoryInvariantV1.PoolTreeHistoryInvariant
      parent zeroDigest 20 [] [tree.root] (modelFrontier tree) := by
  have hspec := production_tree_genesis_source_state_exact parent parentExact
  rw [run] at hspec
  rcases hspec with ⟨hindex, hroot, hfrontier⟩
  have hrootModel :
      tree.root = rootWithEmptySuffix parent zeroDigest 20 [] := by
    rw [hroot, emptyTreeRoot_exact]
  simpa [hrootModel, hfrontier] using
    (AspisPool.PoolTreeHistoryInvariantV1.genesis_pool_tree_history_invariant
      parent zeroDigest 20)

#print axioms production_empty_roots_source_exact
#print axioms production_tree_genesis_source_state_exact
#print axioms production_tree_genesis_establishes_pool_tree_history

end PoolV1TreeGenesisSourceBridge
