import Mathlib
import AspisFormal.Pool.FormatV1

/-!
# Pool V1 binary-carry frontier kernel

This is a small, hash-parametric model of the Rust incremental frontier.  The
list is least-significant level first.  `none` is the unique inactive slot;
`some node` is a live complete subtree.  Appending clears consecutive live
slots, combines each left subtree with the right-hand carry, and stops at the
first inactive slot.  Carry beyond the final slot is the terminal tree root.

The count theorem proves that an open append preserves depth and increments
the frontier's exact binary value; a terminal carry occurs exactly at the
capacity boundary.  The ordered-leaf theorem instantiates the node operation
with list concatenation and proves that neither carry direction nor leaf order
is reversed.
-/

set_option autoImplicit false

namespace AspisPool.IncrementalMerkleV1

inductive AppendResult (α : Type) where
  | more (frontier : List (Option α))
  | full (root : α)
  deriving DecidableEq, Repr

/-- Binary value of the live-slot pattern, level zero first. -/
def frontierValue {α : Type} : List (Option α) → Nat
  | [] => 0
  | none :: rest => 2 * frontierValue rest
  | some _ :: rest => 1 + 2 * frontierValue rest

/-- The exact first-zero/carry-stop append used by the Rust kernel. -/
def appendCarry {α : Type} (parent : α → α → α) (carry : α) :
    List (Option α) → AppendResult α
  | [] => .full carry
  | none :: rest => .more (some carry :: rest)
  | some left :: rest =>
      match appendCarry parent (parent left carry) rest with
      | .more updated => .more (none :: updated)
      | .full root => .full root

/-- An open append preserves depth and adds one to the exact live-slot value;
a full carry is possible exactly when the prior pattern was all live. -/
theorem appendCarry_count_spec {α : Type} (parent : α → α → α)
    (carry : α) (frontier : List (Option α)) :
    match appendCarry parent carry frontier with
    | .more updated =>
        updated.length = frontier.length ∧
          frontierValue updated = frontierValue frontier + 1
    | .full _ => frontierValue frontier + 1 = 2 ^ frontier.length := by
  induction frontier generalizing carry with
  | nil => simp [appendCarry, frontierValue]
  | cons slot rest inductionHypothesis =>
      cases slot with
      | none => simp [appendCarry, frontierValue, Nat.add_comm]
      | some left =>
          cases result : appendCarry parent (parent left carry) rest with
          | more updated =>
              have specification := inductionHypothesis (parent left carry)
              rw [result] at specification
              simp only [appendCarry, result, frontierValue, List.length_cons]
              constructor
              · exact congrArg Nat.succ specification.1
              · omega
          | full root =>
              have specification := inductionHypothesis (parent left carry)
              rw [result] at specification
              simp only [appendCarry, result, frontierValue, List.length_cons]
              rw [pow_succ]
              omega

theorem appendCarry_open_spec {α : Type} (parent : α → α → α)
    (carry : α) (frontier updated : List (Option α))
    (result : appendCarry parent carry frontier = .more updated) :
    updated.length = frontier.length ∧
      frontierValue updated = frontierValue frontier + 1 := by
  have specification := appendCarry_count_spec parent carry frontier
  rw [result] at specification
  exact specification

theorem appendCarry_full_spec {α : Type} (parent : α → α → α)
    (carry root : α) (frontier : List (Option α))
    (result : appendCarry parent carry frontier = .full root) :
    frontierValue frontier + 1 = 2 ^ frontier.length := by
  have specification := appendCarry_count_spec parent carry frontier
  rw [result] at specification
  exact specification

/-- Existing complete blocks in chronological leaf order. -/
def flattenFrontier {β : Type} : List (Option (List β)) → List β
  | [] => []
  | none :: rest => flattenFrontier rest
  | some block :: rest => flattenFrontier rest ++ block

/-- With concatenation as the abstract parent operation, carry append is
exactly chronological list append in both the open and terminal cases. -/
theorem appendCarry_preserves_leaf_order {β : Type} (carry : List β)
    (frontier : List (Option (List β))) :
    match appendCarry List.append carry frontier with
    | .more updated =>
        flattenFrontier updated = flattenFrontier frontier ++ carry
    | .full root => root = flattenFrontier frontier ++ carry := by
  induction frontier generalizing carry with
  | nil => simp [appendCarry, flattenFrontier]
  | cons slot rest inductionHypothesis =>
      cases slot with
      | none => simp [appendCarry, flattenFrontier]
      | some left =>
          cases result : appendCarry List.append (left.append carry) rest with
          | more updated =>
              have specification := inductionHypothesis (left.append carry)
              rw [result] at specification
              rw [appendCarry, result]
              simp only [flattenFrontier]
              simpa [List.append_assoc] using specification
          | full root =>
              have specification := inductionHypothesis (left.append carry)
              rw [result] at specification
              rw [appendCarry, result]
              simp only [flattenFrontier]
              simpa [List.append_assoc] using specification

/-- Recursive empty subtree roots.  The concrete Rust bridge instantiates
`parent` with `merkle_node_compress_v3` and `emptyLeaf` with the zero digest. -/
def recursiveEmptyRoot {α : Type} (parent : α → α → α)
    (emptyLeaf : α) : Nat → α
  | 0 => emptyLeaf
  | depth + 1 =>
      parent (recursiveEmptyRoot parent emptyLeaf depth)
        (recursiveEmptyRoot parent emptyLeaf depth)

/-- Root of an exact perfect tree read from an unbounded leaf accessor. -/
def perfectRootFrom {α : Type} (parent : α → α → α) :
    Nat → (Nat → α) → Nat → α
  | 0, leaves, offset => leaves offset
  | depth + 1, leaves, offset =>
      parent (perfectRootFrom parent depth leaves offset)
        (perfectRootFrom parent depth leaves (offset + 2 ^ depth))

/-- A prefix is completed to a perfect tree with an empty-leaf suffix. -/
def rootWithEmptySuffix {α : Type} (parent : α → α → α)
    (emptyLeaf : α) (depth : Nat) (leaves : List α) : α :=
  perfectRootFrom parent depth (fun index => leaves.getD index emptyLeaf) 0

theorem perfectRootFrom_constant {α : Type} (parent : α → α → α)
    (emptyLeaf : α) (depth offset : Nat) :
    perfectRootFrom parent depth (fun _ => emptyLeaf) offset =
      recursiveEmptyRoot parent emptyLeaf depth := by
  induction depth generalizing offset with
  | zero => rfl
  | succ depth inductionHypothesis =>
      simp only [perfectRootFrom, recursiveEmptyRoot]
      rw [inductionHypothesis, inductionHypothesis]

/-- The empty Pool tree is exactly the recursively derived empty root. -/
theorem emptyTreeRoot_exact {α : Type} (parent : α → α → α)
    (emptyLeaf : α) (depth : Nat) :
    rootWithEmptySuffix parent emptyLeaf depth [] =
      recursiveEmptyRoot parent emptyLeaf depth := by
  simpa [rootWithEmptySuffix] using
    perfectRootFrom_constant parent emptyLeaf depth 0

/-- Reconstruct the complete root above a low-to-high frontier.  `carry` is
the already-completed rightmost subtree at `level`.  An inactive slot pads it
on the right with the recursive empty root; a live slot is the completed left
subtree.  This is the root-reconstruction loop used by the Rust state image. -/
def reconstructFrom {α : Type} (parent : α → α → α) (emptyLeaf : α) :
    Nat → α → List (Option α) → α
  | _, carry, [] => carry
  | level, carry, none :: rest =>
      reconstructFrom parent emptyLeaf (level + 1)
        (parent carry (recursiveEmptyRoot parent emptyLeaf level)) rest
  | level, carry, some left :: rest =>
      reconstructFrom parent emptyLeaf (level + 1) (parent left carry) rest

def reconstructRoot {α : Type} (parent : α → α → α) (emptyLeaf : α)
    (frontier : List (Option α)) : α :=
  reconstructFrom parent emptyLeaf 0 emptyLeaf frontier

/-- The first-zero carry update and root reconstruction commute.  Unlike the
older leaf-order transport lemma, this theorem reasons about the actual hash
nodes in the frontier and the recursive empty roots. -/
theorem appendCarry_reconstruct_more {α : Type}
    (parent : α → α → α) (emptyLeaf carry : α) (level : Nat)
    (frontier updated : List (Option α))
    (result : appendCarry parent carry frontier = .more updated) :
    reconstructFrom parent emptyLeaf level
        (recursiveEmptyRoot parent emptyLeaf level) updated =
      reconstructFrom parent emptyLeaf level carry frontier := by
  induction frontier generalizing carry updated level with
  | nil => simp [appendCarry] at result
  | cons slot rest inductionHypothesis =>
      cases slot with
      | none =>
          simp only [appendCarry] at result
          cases result
          rfl
      | some left =>
          simp only [appendCarry] at result
          cases recursiveResult : appendCarry parent (parent left carry) rest with
          | more recursiveFrontier =>
              simp only [recursiveResult] at result
              cases result
              simp only [reconstructFrom]
              exact inductionHypothesis
                (carry := parent left carry)
                (updated := recursiveFrontier)
                (level := level + 1) recursiveResult
          | full root => simp [recursiveResult] at result

/-- A terminal carry is exactly the reconstructed root with the incoming
subtree in the low carry position. -/
theorem appendCarry_reconstruct_full {α : Type}
    (parent : α → α → α) (emptyLeaf carry root : α) (level : Nat)
    (frontier : List (Option α))
    (result : appendCarry parent carry frontier = .full root) :
    root = reconstructFrom parent emptyLeaf level carry frontier := by
  induction frontier generalizing carry root level with
  | nil =>
      simp only [appendCarry] at result
      cases result
      rfl
  | cons slot rest inductionHypothesis =>
      cases slot with
      | none => simp [appendCarry] at result
      | some left =>
          simp only [appendCarry] at result
          cases recursiveResult : appendCarry parent (parent left carry) rest with
          | more recursiveFrontier => simp [recursiveResult] at result
          | full recursiveRoot =>
              simp only [recursiveResult] at result
              cases result
              simp only [reconstructFrom]
              exact inductionHypothesis
                (carry := parent left carry)
                (root := root)
                (level := level + 1) recursiveResult

/-- Perfect root of one exact chronological leaf block at a named level. -/
def blockRoot {α : Type} (parent : α → α → α) (emptyLeaf : α)
    (level : Nat) (block : List α) : α :=
  perfectRootFrom parent level (fun index => block.getD index emptyLeaf) 0

theorem perfectRootFrom_congr_between {α : Type} (parent : α → α → α)
    (left right : Nat → α) (depth leftOffset rightOffset : Nat)
    (equal : ∀ index, index < 2 ^ depth →
      left (leftOffset + index) = right (rightOffset + index)) :
    perfectRootFrom parent depth left leftOffset =
      perfectRootFrom parent depth right rightOffset := by
  induction depth generalizing leftOffset rightOffset with
  | zero => simpa [perfectRootFrom] using equal 0 (by norm_num)
  | succ depth inductionHypothesis =>
      simp only [perfectRootFrom]
      apply congrArg₂ parent
      · exact inductionHypothesis leftOffset rightOffset fun index bound =>
          equal index (by rw [pow_succ]; omega)
      · exact inductionHypothesis (leftOffset + 2 ^ depth)
          (rightOffset + 2 ^ depth) fun index bound => by
            simpa [Nat.add_assoc] using
              equal (2 ^ depth + index) (by rw [pow_succ]; omega)

theorem blockRoot_append_equal {α : Type} (parent : α → α → α)
    (emptyLeaf : α) (level : Nat) (left right : List α)
    (leftLength : left.length = 2 ^ level)
    (rightLength : right.length = 2 ^ level) :
    blockRoot parent emptyLeaf (level + 1) (left ++ right) =
      parent (blockRoot parent emptyLeaf level left)
        (blockRoot parent emptyLeaf level right) := by
  simp only [blockRoot, perfectRootFrom]
  apply congrArg₂ parent
  · apply perfectRootFrom_congr_between parent
    intro index bound
    simpa only [Nat.zero_add] using
      List.getD_append left right emptyLeaf index (by omega)
  · apply perfectRootFrom_congr_between parent
    intro index bound
    rw [Nat.zero_add]
    rw [List.getD_append_right left right emptyLeaf (2 ^ level + index) (by omega)]
    congr 1
    omega

theorem blockRoot_replicate_empty {α : Type} (parent : α → α → α)
    (emptyLeaf : α) (level : Nat) :
    blockRoot parent emptyLeaf level (List.replicate (2 ^ level) emptyLeaf) =
      recursiveEmptyRoot parent emptyLeaf level := by
  unfold blockRoot
  calc
    perfectRootFrom parent level
        (fun index => (List.replicate (2 ^ level) emptyLeaf).getD index emptyLeaf) 0 =
      perfectRootFrom parent level (fun _ => emptyLeaf) 0 := by
        apply perfectRootFrom_congr_between parent
        intro index bound
        simp only [Nat.zero_add]
        exact List.getD_replicate (x := emptyLeaf) (y := emptyLeaf) bound
    _ = recursiveEmptyRoot parent emptyLeaf level :=
      perfectRootFrom_constant parent emptyLeaf level 0

theorem blockRoot_padded_eq_rootWithEmptySuffix {α : Type}
    (parent : α → α → α) (emptyLeaf : α) (depth : Nat)
    (leaves : List α) (withinCapacity : leaves.length ≤ 2 ^ depth) :
    blockRoot parent emptyLeaf depth
        (leaves ++ List.replicate (2 ^ depth - leaves.length) emptyLeaf) =
      rootWithEmptySuffix parent emptyLeaf depth leaves := by
  unfold blockRoot rootWithEmptySuffix
  apply perfectRootFrom_congr_between parent
  intro index bound
  simp only [Nat.zero_add]
  by_cases inLeaves : index < leaves.length
  · exact List.getD_append leaves
      (List.replicate (2 ^ depth - leaves.length) emptyLeaf)
      emptyLeaf index inLeaves
  · have afterLeaves : leaves.length ≤ index := Nat.le_of_not_gt inLeaves
    rw [List.getD_append_right leaves
      (List.replicate (2 ^ depth - leaves.length) emptyLeaf)
      emptyLeaf index afterLeaves]
    rw [List.getD_eq_default leaves emptyLeaf afterLeaves]
    exact List.getD_replicate (x := emptyLeaf) (y := emptyLeaf) (by omega)

/-- Ghost blocks used only for proof: a live level-h frontier node is tied to
the exact chronological block of 2^h leaves that it authenticates. -/
inductive BlocksMatch {α : Type} (parent : α → α → α) (emptyLeaf : α) :
    Nat → List (Option α) → List (Option (List α)) → Prop where
  | nil (level : Nat) : BlocksMatch parent emptyLeaf level [] []
  | none {level frontier blocks} :
      BlocksMatch parent emptyLeaf (level + 1) frontier blocks →
      BlocksMatch parent emptyLeaf level (none :: frontier) (none :: blocks)
  | some {level node block frontier blocks} :
      block.length = 2 ^ level →
      node = blockRoot parent emptyLeaf level block →
      BlocksMatch parent emptyLeaf (level + 1) frontier blocks →
      BlocksMatch parent emptyLeaf level
        (some node :: frontier) (some block :: blocks)

/-- Leaf-level mirror of `reconstructFrom`, used to prove that reconstruction
pads only on the right and never reorders an authenticated block. -/
def reconstructBlocksFrom {α : Type} (emptyLeaf : α) :
    Nat → List α → List (Option (List α)) → List α
  | _, carry, [] => carry
  | level, carry, none :: rest =>
      reconstructBlocksFrom emptyLeaf (level + 1)
        (carry ++ List.replicate (2 ^ level) emptyLeaf) rest
  | level, carry, some left :: rest =>
      reconstructBlocksFrom emptyLeaf (level + 1) (left ++ carry) rest

theorem frontierValue_lt_capacity {α : Type} (frontier : List (Option α)) :
    frontierValue frontier < 2 ^ frontier.length := by
  induction frontier with
  | nil => norm_num [frontierValue]
  | cons slot rest inductionHypothesis =>
      cases slot <;> simp only [frontierValue, List.length_cons, pow_succ] <;> omega

theorem BlocksMatch.reconstruct {α : Type} (parent : α → α → α)
    (emptyLeaf : α) (level : Nat) (frontier : List (Option α))
    (blocks : List (Option (List α)))
    (matching : BlocksMatch parent emptyLeaf level frontier blocks)
    (carryNode : α) (carryBlock : List α)
    (carryLength : carryBlock.length = 2 ^ level)
    (carryRoot : carryNode = blockRoot parent emptyLeaf level carryBlock) :
    reconstructFrom parent emptyLeaf level carryNode frontier =
      blockRoot parent emptyLeaf (level + frontier.length)
        (reconstructBlocksFrom emptyLeaf level carryBlock blocks) := by
  induction matching generalizing carryNode carryBlock with
  | nil level =>
      simpa [reconstructFrom, reconstructBlocksFrom] using carryRoot
  | @none currentLevel currentFrontier currentBlocks matching inductionHypothesis =>
      let emptyBlock := List.replicate (2 ^ currentLevel) emptyLeaf
      have emptyLength : emptyBlock.length = 2 ^ currentLevel := by
        simp [emptyBlock]
      have combinedLength :
          (carryBlock ++ emptyBlock).length = 2 ^ (currentLevel + 1) := by
        simp only [List.length_append, carryLength, emptyLength, pow_succ]
        omega
      have combinedRoot :
          parent carryNode (recursiveEmptyRoot parent emptyLeaf currentLevel) =
            blockRoot parent emptyLeaf (currentLevel + 1)
              (carryBlock ++ emptyBlock) := by
        rw [carryRoot,
          ← blockRoot_replicate_empty parent emptyLeaf currentLevel]
        exact (blockRoot_append_equal parent emptyLeaf currentLevel carryBlock emptyBlock
          carryLength emptyLength).symm
      have recurse := inductionHypothesis
        (carryNode :=
          parent carryNode (recursiveEmptyRoot parent emptyLeaf currentLevel))
        (carryBlock := carryBlock ++ emptyBlock) combinedLength combinedRoot
      have exponentEq :
          currentLevel + 1 + currentFrontier.length =
            currentLevel + (currentFrontier.length + 1) := by omega
      rw [exponentEq] at recurse
      simpa [reconstructFrom, reconstructBlocksFrom, emptyBlock] using recurse
  | @some currentLevel node block currentFrontier currentBlocks blockLength nodeRoot
      matching inductionHypothesis =>
      have combinedLength :
          (block ++ carryBlock).length = 2 ^ (currentLevel + 1) := by
        simp only [List.length_append, blockLength, carryLength, pow_succ]
        omega
      have combinedRoot :
          parent node carryNode =
            blockRoot parent emptyLeaf (currentLevel + 1) (block ++ carryBlock) := by
        rw [nodeRoot, carryRoot]
        exact (blockRoot_append_equal parent emptyLeaf currentLevel block carryBlock
          blockLength carryLength).symm
      have recurse := inductionHypothesis
        (carryNode := parent node carryNode)
        (carryBlock := block ++ carryBlock) combinedLength combinedRoot
      have exponentEq :
          currentLevel + 1 + currentFrontier.length =
            currentLevel + (currentFrontier.length + 1) := by omega
      rw [exponentEq] at recurse
      simpa [reconstructFrom, reconstructBlocksFrom] using recurse

/-- The ghost blocks occupy exactly the live binary-frontier weight at the
current level.  This is the non-circular size fact used by the completion and
append proofs below. -/
theorem BlocksMatch.flatten_length {α : Type} (parent : α → α → α)
    (emptyLeaf : α) (level : Nat) (frontier : List (Option α))
    (blocks : List (Option (List α)))
    (matching : BlocksMatch parent emptyLeaf level frontier blocks) :
    (flattenFrontier blocks).length = 2 ^ level * frontierValue frontier := by
  induction matching with
  | nil => simp [flattenFrontier, frontierValue]
  | @none currentLevel currentFrontier currentBlocks matching inductionHypothesis =>
      simp only [flattenFrontier, frontierValue]
      rw [inductionHypothesis, pow_succ]
      ring
  | @some currentLevel node block currentFrontier currentBlocks blockLength nodeRoot
      matching inductionHypothesis =>
      simp only [flattenFrontier, List.length_append, frontierValue]
      rw [inductionHypothesis, blockLength, pow_succ]
      ring

/-- A full level-sized carry plus all authenticated blocks fits in the
remaining perfect subtree. -/
theorem BlocksMatch.used_with_carry_le {α : Type}
    (parent : α → α → α) (emptyLeaf : α) (level : Nat)
    (frontier : List (Option α)) (blocks : List (Option (List α)))
    (matching : BlocksMatch parent emptyLeaf level frontier blocks)
    (carry : List α) (carryLength : carry.length = 2 ^ level) :
    (flattenFrontier blocks).length + carry.length ≤
      2 ^ (level + frontier.length) := by
  rw [matching.flatten_length, carryLength, pow_add]
  have bound : frontierValue frontier + 1 ≤ 2 ^ frontier.length :=
    Nat.succ_le_iff.mpr (frontierValue_lt_capacity frontier)
  nlinarith

/-- Leaf-level reconstruction is the authenticated chronological prefix,
then the incoming level-sized carry, then only empty leaves up to the exact
perfect-subtree capacity. -/
theorem BlocksMatch.reconstructBlocks_completion {α : Type}
    (parent : α → α → α) (emptyLeaf : α) (level : Nat)
    (frontier : List (Option α)) (blocks : List (Option (List α)))
    (matching : BlocksMatch parent emptyLeaf level frontier blocks)
    (carry : List α) (carryLength : carry.length = 2 ^ level) :
    reconstructBlocksFrom emptyLeaf level carry blocks =
      flattenFrontier blocks ++ carry ++
        List.replicate
          (2 ^ (level + frontier.length) -
            ((flattenFrontier blocks).length + carry.length)) emptyLeaf := by
  induction matching generalizing carry with
  | nil currentLevel =>
      simp [reconstructBlocksFrom, flattenFrontier, carryLength]
  | @none currentLevel currentFrontier currentBlocks matching inductionHypothesis =>
      let emptyBlock := List.replicate (2 ^ currentLevel) emptyLeaf
      have emptyLength : emptyBlock.length = 2 ^ currentLevel := by
        simp [emptyBlock]
      have combinedLength : (carry ++ emptyBlock).length = 2 ^ (currentLevel + 1) := by
        simp only [List.length_append, carryLength, emptyLength, pow_succ]
        omega
      have recurse := inductionHypothesis (carry := carry ++ emptyBlock) combinedLength
      have recursiveBound := BlocksMatch.used_with_carry_le
        parent emptyLeaf (currentLevel + 1) currentFrontier currentBlocks matching
        (carry ++ emptyBlock) combinedLength
      have capacityEq :
          2 ^ (currentLevel + (currentFrontier.length + 1)) =
            2 ^ (currentLevel + 1 + currentFrontier.length) := by
        congr 1
        omega
      have remainingEq :
          2 ^ (currentLevel + (currentFrontier.length + 1)) -
              ((flattenFrontier currentBlocks).length + carry.length) =
            emptyBlock.length +
              (2 ^ (currentLevel + 1 + currentFrontier.length) -
                ((flattenFrontier currentBlocks).length +
                  (carry ++ emptyBlock).length)) := by
        rw [capacityEq]
        simp only [List.length_append]
        omega
      rw [reconstructBlocksFrom, recurse]
      simp only [flattenFrontier, List.length_cons]
      rw [remainingEq, List.replicate_add]
      simp [List.append_assoc, emptyBlock]
  | @some currentLevel node block currentFrontier currentBlocks blockLength nodeRoot
      matching inductionHypothesis =>
      have combinedLength : (block ++ carry).length = 2 ^ (currentLevel + 1) := by
        simp only [List.length_append, blockLength, carryLength, pow_succ]
        omega
      have recurse := inductionHypothesis (carry := block ++ carry) combinedLength
      rw [reconstructBlocksFrom, recurse]
      simp only [flattenFrontier, List.length_append, List.length_cons]
      have exponentEq :
          currentLevel + 1 + currentFrontier.length =
            currentLevel + (currentFrontier.length + 1) := by omega
      rw [exponentEq]
      simp [List.append_assoc, Nat.add_assoc]

/-- Hash carry and chronological-block carry have the same shape.  In the
open case the new frontier again has exact block witnesses; in the terminal
case the returned node is the perfect root of the complete chronological
block. -/
theorem BlocksMatch.append_related {α : Type}
    (parent : α → α → α) (emptyLeaf : α) (level : Nat)
    (frontier : List (Option α)) (blocks : List (Option (List α)))
    (matching : BlocksMatch parent emptyLeaf level frontier blocks)
    (carryNode : α) (carryBlock : List α)
    (carryLength : carryBlock.length = 2 ^ level)
    (carryRoot : carryNode = blockRoot parent emptyLeaf level carryBlock) :
    match appendCarry parent carryNode frontier with
    | .more updated =>
        ∃ updatedBlocks,
          appendCarry List.append carryBlock blocks = .more updatedBlocks ∧
            BlocksMatch parent emptyLeaf level updated updatedBlocks
    | .full root =>
        ∃ fullBlock,
          appendCarry List.append carryBlock blocks = .full fullBlock ∧
            fullBlock.length = 2 ^ (level + frontier.length) ∧
              root = blockRoot parent emptyLeaf
                (level + frontier.length) fullBlock := by
  induction matching generalizing carryNode carryBlock with
  | nil currentLevel =>
      simp [appendCarry, carryLength, carryRoot]
  | @none currentLevel currentFrontier currentBlocks matching inductionHypothesis =>
      simp only [appendCarry]
      refine ⟨Option.some carryBlock :: currentBlocks, rfl, ?_⟩
      exact BlocksMatch.some carryLength carryRoot matching
  | @some currentLevel node block currentFrontier currentBlocks blockLength nodeRoot
      matching inductionHypothesis =>
      have combinedLength : (block ++ carryBlock).length = 2 ^ (currentLevel + 1) := by
        simp only [List.length_append, blockLength, carryLength, pow_succ]
        omega
      have combinedRoot :
          parent node carryNode =
            blockRoot parent emptyLeaf (currentLevel + 1) (block ++ carryBlock) := by
        rw [nodeRoot, carryRoot]
        exact (blockRoot_append_equal parent emptyLeaf currentLevel block carryBlock
          blockLength carryLength).symm
      have recurse := inductionHypothesis
        (carryNode := parent node carryNode)
        (carryBlock := block ++ carryBlock) combinedLength combinedRoot
      cases recursiveResult : appendCarry parent (parent node carryNode) currentFrontier with
      | more recursiveUpdated =>
          rw [recursiveResult] at recurse
          rcases recurse with ⟨updatedBlocks, blockResult, updatedMatching⟩
          rw [appendCarry, recursiveResult]
          refine ⟨Option.none :: updatedBlocks, ?_, BlocksMatch.none updatedMatching⟩
          simp [appendCarry, blockResult]
      | full root =>
          rw [recursiveResult] at recurse
          rcases recurse with ⟨fullBlock, blockResult, fullLength, rootCorrect⟩
          rw [appendCarry, recursiveResult]
          refine ⟨fullBlock, ?_, ?_, ?_⟩
          · simp [appendCarry, blockResult]
          · simp only [List.length_cons]
            have exponentEq :
                currentLevel + 1 + currentFrontier.length =
                  currentLevel + (currentFrontier.length + 1) := by omega
            rw [← exponentEq]
            exact fullLength
          · simp only [List.length_cons]
            have exponentEq :
                currentLevel + 1 + currentFrontier.length =
                  currentLevel + (currentFrontier.length + 1) := by omega
            rw [← exponentEq]
            exact rootCorrect

theorem BlocksMatch.append_more {α : Type}
    (parent : α → α → α) (emptyLeaf : α) (level : Nat)
    (frontier updated : List (Option α))
    (blocks : List (Option (List α)))
    (matching : BlocksMatch parent emptyLeaf level frontier blocks)
    (carryNode : α) (carryBlock : List α)
    (carryLength : carryBlock.length = 2 ^ level)
    (carryRoot : carryNode = blockRoot parent emptyLeaf level carryBlock)
    (result : appendCarry parent carryNode frontier = .more updated) :
    ∃ updatedBlocks,
      appendCarry List.append carryBlock blocks = .more updatedBlocks ∧
        BlocksMatch parent emptyLeaf level updated updatedBlocks := by
  have related := BlocksMatch.append_related parent emptyLeaf level frontier blocks
    matching carryNode carryBlock carryLength carryRoot
  rw [result] at related
  exact related

theorem BlocksMatch.append_full {α : Type}
    (parent : α → α → α) (emptyLeaf : α) (level : Nat)
    (frontier : List (Option α)) (blocks : List (Option (List α)))
    (matching : BlocksMatch parent emptyLeaf level frontier blocks)
    (carryNode root : α) (carryBlock : List α)
    (carryLength : carryBlock.length = 2 ^ level)
    (carryRoot : carryNode = blockRoot parent emptyLeaf level carryBlock)
    (result : appendCarry parent carryNode frontier = .full root) :
    ∃ fullBlock,
      appendCarry List.append carryBlock blocks = .full fullBlock ∧
        fullBlock.length = 2 ^ (level + frontier.length) ∧
          root = blockRoot parent emptyLeaf
            (level + frontier.length) fullBlock := by
  have related := BlocksMatch.append_related parent emptyLeaf level frontier blocks
    matching carryNode carryBlock carryLength carryRoot
  rw [result] at related
  exact related

/-- The representation invariant contains only concrete authenticated block
witnesses and elementary shape/count facts.  It does not assume any future
append or root equality. -/
structure FrontierInvariant {α : Type} (parent : α → α → α) (emptyLeaf : α)
    (depth : Nat) (leaves : List α) (frontier : List (Option α)) : Prop where
  authenticated_blocks : ∃ blocks : List (Option (List α)),
    BlocksMatch parent emptyLeaf 0 frontier blocks ∧
      flattenFrontier blocks = leaves
  depth_eq : frontier.length = depth
  count_eq : frontierValue frontier = leaves.length
  open_capacity : leaves.length < 2 ^ depth

theorem blocksMatch_replicate_none {α : Type}
    (parent : α → α → α) (emptyLeaf : α) (level depth : Nat) :
    BlocksMatch parent emptyLeaf level
      (List.replicate depth (Option.none : Option α))
      (List.replicate depth (Option.none : Option (List α))) := by
  induction depth generalizing level with
  | zero => exact BlocksMatch.nil level
  | succ depth inductionHypothesis =>
      simpa [List.replicate_succ] using
        BlocksMatch.none (inductionHypothesis (level + 1))

theorem frontierValue_replicate_none {α : Type} (depth : Nat) :
    frontierValue (List.replicate depth (Option.none : Option α)) = 0 := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      simp [List.replicate_succ, frontierValue, inductionHypothesis]

theorem flattenFrontier_replicate_none {α : Type} (depth : Nat) :
    flattenFrontier
      (List.replicate depth (Option.none : Option (List α))) = [] := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      simp [List.replicate_succ, flattenFrontier, inductionHypothesis]

/-- Genesis satisfies the non-circular block-witness invariant. -/
theorem genesis_invariant {α : Type} (parent : α → α → α)
    (emptyLeaf : α) (depth : Nat) :
    FrontierInvariant parent emptyLeaf depth []
      (List.replicate depth (Option.none : Option α)) := by
  refine
    { authenticated_blocks := ⟨
        List.replicate depth (Option.none : Option (List α)),
        blocksMatch_replicate_none parent emptyLeaf 0 depth,
        flattenFrontier_replicate_none depth⟩
      depth_eq := by simp
      count_eq := by simpa using frontierValue_replicate_none (α := α) depth
      open_capacity := by positivity }

/-- A block-witness frontier reconstructs to exactly its chronological leaf
prefix followed by recursive empty padding. -/
theorem FrontierInvariant.root_correct {α : Type}
    (parent : α → α → α) (emptyLeaf : α) (depth : Nat)
    (leaves : List α) (frontier : List (Option α))
    (invariant : FrontierInvariant parent emptyLeaf depth leaves frontier) :
    reconstructRoot parent emptyLeaf frontier =
      rootWithEmptySuffix parent emptyLeaf depth leaves := by
  rcases invariant.authenticated_blocks with ⟨blocks, blocksMatch, flattenEq⟩
  have hashReconstruction := BlocksMatch.reconstruct parent emptyLeaf 0 frontier
    blocks blocksMatch emptyLeaf [emptyLeaf] (by norm_num) (by rfl)
  have leafReconstruction := BlocksMatch.reconstructBlocks_completion parent
    emptyLeaf 0 frontier blocks blocksMatch [emptyLeaf] (by norm_num)
  have withinCapacity : leaves.length ≤ 2 ^ depth :=
    Nat.le_of_lt invariant.open_capacity
  have openCapacity := invariant.open_capacity
  have suffixCount :
      1 + (2 ^ depth - (leaves.length + 1)) =
        2 ^ depth - leaves.length := by omega
  have reconstructedLeaves :
      reconstructBlocksFrom emptyLeaf 0 [emptyLeaf] blocks =
        leaves ++ List.replicate (2 ^ depth - leaves.length) emptyLeaf := by
    rw [leafReconstruction, flattenEq, invariant.depth_eq]
    simp only [Nat.zero_add, List.length_singleton]
    rw [show [emptyLeaf] = List.replicate 1 emptyLeaf by rfl,
      List.append_assoc, ← List.replicate_add, suffixCount]
  calc
    reconstructRoot parent emptyLeaf frontier =
        blockRoot parent emptyLeaf depth
          (reconstructBlocksFrom emptyLeaf 0 [emptyLeaf] blocks) := by
            unfold reconstructRoot
            rw [hashReconstruction, invariant.depth_eq]
            simp only [Nat.zero_add]
    _ = blockRoot parent emptyLeaf depth
          (leaves ++ List.replicate (2 ^ depth - leaves.length) emptyLeaf) := by
            rw [reconstructedLeaves]
    _ = rootWithEmptySuffix parent emptyLeaf depth leaves :=
      blockRoot_padded_eq_rootWithEmptySuffix parent emptyLeaf depth leaves
        withinCapacity

/-- One open carry preserves the exact authenticated-block invariant and
extends the chronological leaf list by exactly one element. -/
theorem FrontierInvariant.append_preserves {α : Type}
    (parent : α → α → α) (emptyLeaf leaf : α) (depth : Nat)
    (leaves : List α) (frontier updated : List (Option α))
    (invariant : FrontierInvariant parent emptyLeaf depth leaves frontier)
    (result : appendCarry parent leaf frontier = .more updated) :
    FrontierInvariant parent emptyLeaf depth (leaves ++ [leaf]) updated := by
  rcases invariant.authenticated_blocks with ⟨blocks, blocksMatch, flattenEq⟩
  rcases BlocksMatch.append_more parent emptyLeaf 0 frontier updated blocks
      blocksMatch leaf [leaf] (by norm_num) (by rfl) result with
    ⟨updatedBlocks, blockResult, updatedMatching⟩
  have order := appendCarry_preserves_leaf_order [leaf] blocks
  rw [blockResult] at order
  rcases appendCarry_open_spec parent leaf frontier updated result with
    ⟨updatedLength, updatedCount⟩
  have updatedCapacity := frontierValue_lt_capacity updated
  refine
    { authenticated_blocks := ⟨updatedBlocks, updatedMatching, by
          rw [order, flattenEq]⟩
      depth_eq := by rw [updatedLength, invariant.depth_eq]
      count_eq := by
        rw [updatedCount, invariant.count_eq]
        simp
      open_capacity := ?_ }
  rw [updatedCount, invariant.count_eq, updatedLength, invariant.depth_eq] at updatedCapacity
  simpa using updatedCapacity

/-- The roadmap's central theorem: the concrete carry update preserves the
non-circular block invariant and reconstructs the exact perfect-tree root of
the old leaves followed by the new leaf and empty suffix. -/
theorem append_correct {α : Type} (parent : α → α → α) (emptyLeaf leaf : α)
    (depth : Nat) (leaves : List α) (frontier updated : List (Option α))
    (invariant : FrontierInvariant parent emptyLeaf depth leaves frontier)
    (result : appendCarry parent leaf frontier = .more updated) :
    FrontierInvariant parent emptyLeaf depth (leaves ++ [leaf]) updated ∧
      reconstructRoot parent emptyLeaf updated =
        rootWithEmptySuffix parent emptyLeaf depth (leaves ++ [leaf]) := by
  let post := FrontierInvariant.append_preserves parent emptyLeaf leaf depth leaves
    frontier updated invariant result
  exact ⟨post, post.root_correct⟩

theorem append_terminal_correct {α : Type}
    (parent : α → α → α) (emptyLeaf leaf root : α) (depth : Nat)
    (leaves : List α) (frontier : List (Option α))
    (invariant : FrontierInvariant parent emptyLeaf depth leaves frontier)
    (result : appendCarry parent leaf frontier = .full root) :
    (leaves ++ [leaf]).length = 2 ^ depth ∧
      root = rootWithEmptySuffix parent emptyLeaf depth (leaves ++ [leaf]) := by
  rcases invariant.authenticated_blocks with ⟨blocks, blocksMatch, flattenEq⟩
  rcases BlocksMatch.append_full parent emptyLeaf 0 frontier blocks blocksMatch
      leaf root [leaf] (by norm_num) (by rfl) result with
    ⟨fullBlock, blockResult, fullLength, rootCorrect⟩
  have order := appendCarry_preserves_leaf_order [leaf] blocks
  rw [blockResult] at order
  have capacityEq : (leaves ++ [leaf]).length = 2 ^ depth := by
    calc
      (leaves ++ [leaf]).length = fullBlock.length := by
        rw [order, flattenEq]
      _ = 2 ^ (0 + frontier.length) := fullLength
      _ = 2 ^ depth := by rw [Nat.zero_add, invariant.depth_eq]
  constructor
  · exact capacityEq
  · have rootAsBlock :
        root = blockRoot parent emptyLeaf depth (leaves ++ [leaf]) := by
          rw [rootCorrect, Nat.zero_add, invariant.depth_eq, order,
            flattenEq]
    have padded := blockRoot_padded_eq_rootWithEmptySuffix parent emptyLeaf depth
      (leaves ++ [leaf]) (Nat.le_of_eq capacityEq)
    rw [rootAsBlock]
    simpa [capacityEq] using padded

/-- Append-only storage preserves every old leaf as an exact prefix. -/
theorem old_leaf_membership_preserved {α : Type} (leaves outputs : List α) :
    (leaves ++ outputs).take leaves.length = leaves := by
  simp

/-- Two open appends sequentially preserve the block invariant, leaf order,
count, depth and exact recursively padded root. -/
theorem append_two_sequential_correct {α : Type}
    (parent : α → α → α) (emptyLeaf first second : α) (depth : Nat)
    (leaves : List α) (frontier afterFirst afterSecond : List (Option α))
    (invariant : FrontierInvariant parent emptyLeaf depth leaves frontier)
    (firstResult : appendCarry parent first frontier = .more afterFirst)
    (secondResult : appendCarry parent second afterFirst = .more afterSecond) :
    FrontierInvariant parent emptyLeaf depth
        (leaves ++ [first, second]) afterSecond ∧
      afterSecond.length = depth ∧
      frontierValue afterSecond = leaves.length + 2 ∧
      reconstructRoot parent emptyLeaf afterSecond =
        rootWithEmptySuffix parent emptyLeaf depth
          (leaves ++ [first, second]) := by
  have afterFirstInvariant := FrontierInvariant.append_preserves parent emptyLeaf first
    depth leaves frontier afterFirst invariant firstResult
  have afterSecondInvariant :=
    FrontierInvariant.append_preserves parent emptyLeaf second depth
      (leaves ++ [first]) afterFirst afterSecond afterFirstInvariant secondResult
  have normalizedInvariant : FrontierInvariant parent emptyLeaf depth
      (leaves ++ [first, second]) afterSecond := by
    simpa [List.append_assoc] using afterSecondInvariant
  refine ⟨normalizedInvariant, normalizedInvariant.depth_eq,
    normalizedInvariant.count_eq.trans ?_, normalizedInvariant.root_correct⟩
  simp

/-- The second append may be the terminal carry at exact capacity; the first
append's proved invariant is the sole premise for the second step. -/
theorem append_two_terminal_correct {α : Type}
    (parent : α → α → α) (emptyLeaf first second root : α) (depth : Nat)
    (leaves : List α) (frontier afterFirst : List (Option α))
    (invariant : FrontierInvariant parent emptyLeaf depth leaves frontier)
    (firstResult : appendCarry parent first frontier = .more afterFirst)
    (secondResult : appendCarry parent second afterFirst = .full root) :
    (leaves ++ [first, second]).length = 2 ^ depth ∧
      root = rootWithEmptySuffix parent emptyLeaf depth
        (leaves ++ [first, second]) := by
  have afterFirstInvariant := FrontierInvariant.append_preserves parent emptyLeaf first
    depth leaves frontier afterFirst invariant firstResult
  have terminal := append_terminal_correct parent emptyLeaf second root depth
    (leaves ++ [first]) afterFirst afterFirstInvariant secondResult
  simpa [List.append_assoc] using terminal

/-- Named source boundary for the abstract parent/empty-leaf model.  The Rust
and Aeneas bridge must instantiate these equalities with production
`merkle_node_compress_v3` and the all-zero M31 digest; no concrete Poseidon
claim is hidden in the hash-parametric theorems above. -/
structure PoseidonV3SourceRefinement {α : Type}
    (modelParent productionParent : α → α → α)
    (modelEmptyLeaf productionEmptyLeaf : α) : Prop where
  parent_eq : productionParent = modelParent
  empty_leaf_eq : productionEmptyLeaf = modelEmptyLeaf

/-- The carry proof transports directly to the recursively padded Merkle
root.  This theorem is hash-parametric: the source bridge must establish that
production `merkle_node_compress_v3` is the same `parent` operation. -/
theorem appendCarry_root_with_empty_suffix {α : Type}
    (parent : α → α → α) (emptyLeaf leaf : α) (depth : Nat)
    (frontier updated : List (Option (List α)))
    (result : appendCarry List.append [leaf] frontier = .more updated) :
    rootWithEmptySuffix parent emptyLeaf depth (flattenFrontier updated) =
      rootWithEmptySuffix parent emptyLeaf depth
        (flattenFrontier frontier ++ [leaf]) := by
  have order := appendCarry_preserves_leaf_order [leaf] frontier
  rw [result] at order
  rw [order]

/-- Pool V1's concrete depth and capacity are the exact Rust constants. -/
theorem poolV1_depth_capacity :
    AspisPool.FormatV1.binding.treeDepth = 20 ∧
      2 ^ AspisPool.FormatV1.binding.treeDepth = 1_048_576 := by
  norm_num [AspisPool.FormatV1.binding]

#print axioms appendCarry_count_spec
#print axioms appendCarry_open_spec
#print axioms appendCarry_full_spec
#print axioms appendCarry_preserves_leaf_order
#print axioms perfectRootFrom_constant
#print axioms emptyTreeRoot_exact
#print axioms appendCarry_root_with_empty_suffix
#print axioms appendCarry_reconstruct_more
#print axioms appendCarry_reconstruct_full
#print axioms BlocksMatch.flatten_length
#print axioms BlocksMatch.reconstructBlocks_completion
#print axioms BlocksMatch.append_related
#print axioms genesis_invariant
#print axioms FrontierInvariant.root_correct
#print axioms FrontierInvariant.append_preserves
#print axioms append_correct
#print axioms append_terminal_correct
#print axioms old_leaf_membership_preserved
#print axioms append_two_sequential_correct
#print axioms append_two_terminal_correct
#print axioms poolV1_depth_capacity

end AspisPool.IncrementalMerkleV1
