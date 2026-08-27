import AspisFormal.Pool.HistoricalAnchorV1
import AspisFormal.Pool.DepositV1
import AspisFormal.Pool.TransferOneToTwoV1

/-!
# Composed Pool V1 tree and root-history invariant

The incremental frontier proof and historical-anchor proof were previously
separate.  This module composes them into the state invariant needed by the
Pool lifecycle: the chronological commitments are exactly the authenticated
frontier leaves, root sequence zero is the empty-tree root, the current
post-append root is retained at the leaf-count sequence, and root-history
length is always leaf count plus one.

Theorems cover genesis, one append, and two sequential appends.  The only
remaining production boundary is showing that the Rust account update writes
the same frontier and root-history lists atomically under the correct owner.
-/

set_option autoImplicit false

namespace AspisPool.PoolTreeHistoryInvariantV1

open AspisPool.HistoricalAnchorV1
open AspisPool.IncrementalMerkleV1
open AspisPool.DepositV1
open AspisPool.TransferOneToTwoV1

/-- One complete mathematical Pool tree state.  Leaves and roots share the
digest type used by the deployed Poseidon commitment tree. -/
structure PoolTreeHistoryInvariant {Digest : Type}
    (parent : Digest → Digest → Digest) (emptyLeaf : Digest)
    (depth : Nat) (leaves roots : List Digest)
    (frontier : List (Option Digest)) : Prop where
  frontierInvariant :
    FrontierInvariant parent emptyLeaf depth leaves frontier
  emptyRootRetained :
    RetainedAt roots 0 (rootWithEmptySuffix parent emptyLeaf depth [])
  currentRootRetained :
    RetainedAt roots leaves.length
      (rootWithEmptySuffix parent emptyLeaf depth leaves)
  rootCount : roots.length = leaves.length + 1

theorem retainedAt_append_last {Root : Type} (history : List Root)
    (root : Root) :
    RetainedAt (history ++ [root]) history.length root := by
  exact ⟨history, [], by simp, rfl⟩

/-- Genesis has no commitments, an all-empty frontier, and one retained root
at sequence zero. -/
theorem genesis_pool_tree_history_invariant {Digest : Type}
    (parent : Digest → Digest → Digest) (emptyLeaf : Digest) (depth : Nat) :
    PoolTreeHistoryInvariant parent emptyLeaf depth []
      [rootWithEmptySuffix parent emptyLeaf depth []]
      (List.replicate depth (Option.none : Option Digest)) := by
  refine
    { frontierInvariant := genesis_invariant parent emptyLeaf depth
      emptyRootRetained := ⟨[], [], by simp, rfl⟩
      currentRootRetained := ⟨[], [], by simp, rfl⟩
      rootCount := by simp }

/-- One successful open append preserves the complete composed invariant and
adds exactly the reconstructed post-append root at the next sequence. -/
theorem append_one_preserves_pool_tree_history
    {Digest : Type}
    (parent : Digest → Digest → Digest) (emptyLeaf leaf : Digest)
    (depth : Nat) (leaves roots : List Digest)
    (frontier updated : List (Option Digest))
    (invariant : PoolTreeHistoryInvariant parent emptyLeaf depth leaves roots
      frontier)
    (result : appendCarry parent leaf frontier = .more updated) :
    let newLeaves := leaves ++ [leaf]
    let newRoot := reconstructRoot parent emptyLeaf updated
    PoolTreeHistoryInvariant parent emptyLeaf depth newLeaves
      (roots ++ [newRoot]) updated := by
  dsimp only
  have appended := append_correct parent emptyLeaf leaf depth leaves frontier
    updated invariant.frontierInvariant result
  have newRootExact : reconstructRoot parent emptyLeaf updated =
      rootWithEmptySuffix parent emptyLeaf depth (leaves ++ [leaf]) :=
    appended.2
  refine
    { frontierInvariant := appended.1
      emptyRootRetained := retainedAt_append_one roots 0
        (rootWithEmptySuffix parent emptyLeaf depth [])
        (reconstructRoot parent emptyLeaf updated)
        invariant.emptyRootRetained
      currentRootRetained := ?_
      rootCount := ?_ }
  · rw [newRootExact]
    have retained := retainedAt_append_last roots
      (rootWithEmptySuffix parent emptyLeaf depth (leaves ++ [leaf]))
    rw [invariant.rootCount] at retained
    simpa using retained
  · rw [List.length_append, invariant.rootCount]
    simp

/-- Two successful output appends preserve the invariant, retain both exact
intermediate roots in order, and advance leaf/root sequence twice. -/
theorem append_two_preserves_pool_tree_history
    {Digest : Type}
    (parent : Digest → Digest → Digest)
    (emptyLeaf first second : Digest)
    (depth : Nat) (leaves roots : List Digest)
    (frontier afterFirst afterSecond : List (Option Digest))
    (invariant : PoolTreeHistoryInvariant parent emptyLeaf depth leaves roots
      frontier)
    (firstResult : appendCarry parent first frontier = .more afterFirst)
    (secondResult : appendCarry parent second afterFirst = .more afterSecond) :
    let firstRoot := reconstructRoot parent emptyLeaf afterFirst
    let secondRoot := reconstructRoot parent emptyLeaf afterSecond
    PoolTreeHistoryInvariant parent emptyLeaf depth
      (leaves ++ [first, second]) (roots ++ [firstRoot, secondRoot])
      afterSecond := by
  dsimp only
  have afterFirstInvariant := append_one_preserves_pool_tree_history
    parent emptyLeaf first depth leaves roots frontier afterFirst invariant
    firstResult
  have afterSecondInvariant := append_one_preserves_pool_tree_history
    parent emptyLeaf second depth (leaves ++ [first])
    (roots ++ [reconstructRoot parent emptyLeaf afterFirst]) afterFirst
    afterSecond afterFirstInvariant secondResult
  simpa [List.append_assoc] using afterSecondInvariant

/-- Every previously retained anchor and every old commitment remain valid
after either one or two output appends. -/
theorem prior_anchor_and_commitment_prefix_survive_two_appends
    {Digest : Type}
    (roots : List Digest) (leaves : List Digest)
    (firstRoot secondRoot firstLeaf secondLeaf anchor : Digest)
    (sequence : Nat) (retained : RetainedAt roots sequence anchor) :
    RetainedAt (roots ++ [firstRoot, secondRoot]) sequence anchor ∧
      (leaves ++ [firstLeaf, secondLeaf]).take leaves.length = leaves := by
  exact retained_anchor_and_leaf_prefix_survive roots
    [firstRoot, secondRoot] leaves [firstLeaf, secondLeaf] sequence anchor
    retained

/-- A vault-backed deposit and its one tree append preserve custody and the
complete tree/history invariant in the same pure post-state. -/
theorem deposit_preserves_custody_tree_and_history
    {Owner Asset Salt Payload Digest : Type}
    (parent : Digest → Digest → Digest) (emptyLeaf : Digest)
    (depth : Nat)
    (commit : Owner → Nat → Asset → Salt → Digest)
    (before : Ledger Digest Digest)
    (input : DepositInput Owner Asset Salt Payload)
    (frontier updated : List (Option Digest))
    (reserve : Nat)
    (custody : VaultConserved reserve before)
    (treeHistory : PoolTreeHistoryInvariant parent emptyLeaf depth
      before.notes before.roots frontier)
    (appendResult : appendCarry parent
      (commit input.ownerKey input.amount input.asset input.salt) frontier =
        .more updated) :
    let newRoot := reconstructRoot parent emptyLeaf updated
    let after := deposit commit before input newRoot
    VaultConserved reserve after ∧
      PoolTreeHistoryInvariant parent emptyLeaf depth after.notes after.roots
        updated := by
  dsimp only
  constructor
  · exact deposit_preserves_vault_conservation commit before input
      (reconstructRoot parent emptyLeaf updated) reserve custody
  · simpa [deposit] using
      (append_one_preserves_pool_tree_history parent emptyLeaf
        (commit input.ownerKey input.amount input.asset input.salt) depth
        before.notes before.roots frontier updated treeHistory appendResult)

/-- An authorized one-input/two-output transition, the two chronological
tree appends, and the two exact retained roots preserve the same composed
custody/tree/history invariant. -/
theorem transfer_preserves_custody_tree_and_history
    {Digest : Type}
    (parent : Digest → Digest → Digest) (emptyLeaf : Digest)
    (depth : Nat)
    (before : Ledger Digest Digest)
    (relation : Relation) (outputs : OrderedOutputs Digest)
    (frontier afterFirst afterSecond : List (Option Digest))
    (reserve : Nat)
    (custody : VaultConserved reserve before)
    (inputBacked : relation.inputValue ≤ before.unspentValue)
    (treeHistory : PoolTreeHistoryInvariant parent emptyLeaf depth
      before.notes before.roots frontier)
    (firstResult : appendCarry parent outputs.first frontier =
      .more afterFirst)
    (secondResult : appendCarry parent outputs.second afterFirst =
      .more afterSecond) :
    let firstRoot := reconstructRoot parent emptyLeaf afterFirst
    let secondRoot := reconstructRoot parent emptyLeaf afterSecond
    let after := transfer before relation outputs firstRoot secondRoot
    VaultConserved reserve after ∧
      PoolTreeHistoryInvariant parent emptyLeaf depth after.notes after.roots
        afterSecond := by
  dsimp only
  constructor
  · exact (private_transfer_preserves_vault_invariant before relation outputs
      (reconstructRoot parent emptyLeaf afterFirst)
      (reconstructRoot parent emptyLeaf afterSecond) reserve custody
      inputBacked).2.2.2.2.2.2
  · simpa [transfer] using
      (append_two_preserves_pool_tree_history parent emptyLeaf outputs.first
        outputs.second depth before.notes before.roots frontier afterFirst
        afterSecond treeHistory firstResult secondResult)

#print axioms retainedAt_append_last
#print axioms genesis_pool_tree_history_invariant
#print axioms append_one_preserves_pool_tree_history
#print axioms append_two_preserves_pool_tree_history
#print axioms prior_anchor_and_commitment_prefix_survive_two_appends
#print axioms deposit_preserves_custody_tree_and_history
#print axioms transfer_preserves_custody_tree_and_history

end AspisPool.PoolTreeHistoryInvariantV1
