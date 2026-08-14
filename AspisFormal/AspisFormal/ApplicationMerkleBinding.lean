import AspisFormal.HashMerkleModel

/-!
# Binding for the private-note Merkle tree

The private-note tree and the SHA-256 trees inside the proof system are
different objects.  This file concerns only the private-note tree whose node
function is `merkle_node_compress_v3` in Rust and `nodeHash` in the Lean model.

A different leaf with a different direction path can be a normal opening of a
different tree position.  It is therefore false to treat every alternative
leaf or path under one root as a hash collision.  The theorem below states the
property needed for theft of one fixed note position: if two different leaves
open at the same position to the same root, the two paths expose a level where
different ordered child pairs have the same node hash.

This is a deterministic reduction.  It does not assign a probability to
finding such a collision; collision resistance of the deployed Poseidon2-M31
node function remains a cryptographic assumption.
-/

namespace AspisApplicationMerkleBinding

open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel

/-- The ordered node input selected by one direction bit. -/
def orderedChildren (direction : Bool) (current sibling : Digest) : Digest × Digest :=
  if direction then (sibling, current) else (current, sibling)

theorem parent_eq_hash_ordered_children
    (nodeHash : Digest → Digest → Digest)
    (direction : Bool) (current sibling : Digest) :
    Parent nodeHash direction current sibling =
      nodeHash (orderedChildren direction current sibling).1
        (orderedChildren direction current sibling).2 := by
  cases direction <;> rfl

/-- Running digest after `steps` levels of one depth-20 authentication path. -/
def pathCurrent
    (nodeHash : Digest → Digest → Digest)
    (leaf : Digest) (bits : Fin 20 → Bool) (siblings : Fin 20 → Digest) :
    Nat → Digest
  | 0 => leaf
  | steps + 1 =>
      if h : steps < 20 then
        Parent nodeHash (bits ⟨steps, h⟩)
          (pathCurrent nodeHash leaf bits siblings steps) (siblings ⟨steps, h⟩)
      else
        pathCurrent nodeHash leaf bits siblings steps

theorem pathCurrent_zero
    (nodeHash : Digest → Digest → Digest)
    (leaf : Digest) (bits : Fin 20 → Bool) (siblings : Fin 20 → Digest) :
    pathCurrent nodeHash leaf bits siblings 0 = leaf := by
  rfl

theorem pathCurrent_succ
    (nodeHash : Digest → Digest → Digest)
    (leaf : Digest) (bits : Fin 20 → Bool) (siblings : Fin 20 → Digest)
    (level : Nat) (hlevel : level < 20) :
    pathCurrent nodeHash leaf bits siblings (level + 1) =
      Parent nodeHash (bits ⟨level, hlevel⟩)
        (pathCurrent nodeHash leaf bits siblings level)
        (siblings ⟨level, hlevel⟩) := by
  simp [pathCurrent, hlevel]

theorem pathCurrent_twenty_eq_root
    (nodeHash : Digest → Digest → Digest)
    (leaf : Digest) (bits : Fin 20 → Bool) (siblings : Fin 20 → Digest) :
    pathCurrent nodeHash leaf bits siblings 20 =
      Root nodeHash leaf bits siblings := by
  exact root_of_chain nodeHash leaf bits siblings
    (pathCurrent nodeHash leaf bits siblings)
    (pathCurrent_zero nodeHash leaf bits siblings)
    (fun level => pathCurrent_succ nodeHash leaf bits siblings level level.isLt)

theorem ordered_children_ne_of_current_ne
    (direction : Bool) {currentOne currentTwo : Digest}
    (differentCurrent : currentOne ≠ currentTwo)
    (siblingOne siblingTwo : Digest) :
    orderedChildren direction currentOne siblingOne ≠
      orderedChildren direction currentTwo siblingTwo := by
  cases direction with
  | false =>
      intro equalPairs
      exact differentCurrent (congrArg Prod.fst equalPairs)
  | true =>
      intro equalPairs
      exact differentCurrent (congrArg Prod.snd equalPairs)

/-- Two concrete paths expose a node collision when, at some level, their
ordered child pairs differ but the node function gives the same parent. -/
def PathsExposeNodeCollision
    (nodeHash : Digest → Digest → Digest)
    (leafOne leafTwo : Digest) (bits : Fin 20 → Bool)
    (siblingsOne siblingsTwo : Fin 20 → Digest) : Prop :=
  ∃ level : Fin 20,
    orderedChildren (bits level)
        (pathCurrent nodeHash leafOne bits siblingsOne level) (siblingsOne level) ≠
      orderedChildren (bits level)
        (pathCurrent nodeHash leafTwo bits siblingsTwo level) (siblingsTwo level) ∧
    nodeHash
        (orderedChildren (bits level)
          (pathCurrent nodeHash leafOne bits siblingsOne level) (siblingsOne level)).1
        (orderedChildren (bits level)
          (pathCurrent nodeHash leafOne bits siblingsOne level) (siblingsOne level)).2 =
      nodeHash
        (orderedChildren (bits level)
          (pathCurrent nodeHash leafTwo bits siblingsTwo level) (siblingsTwo level)).1
        (orderedChildren (bits level)
          (pathCurrent nodeHash leafTwo bits siblingsTwo level) (siblingsTwo level)).2

/-- A different leaf at the same depth-20 position cannot reach the same root
without the two authentication paths producing a concrete node-hash
collision.  The sibling lists may differ. -/
theorem same_position_different_leaf_same_root_exposes_node_collision
    (nodeHash : Digest → Digest → Digest)
    {leafOne leafTwo : Digest} {bits : Fin 20 → Bool}
    {siblingsOne siblingsTwo : Fin 20 → Digest}
    (differentLeaf : leafOne ≠ leafTwo)
    (sameRoot : Root nodeHash leafOne bits siblingsOne =
      Root nodeHash leafTwo bits siblingsTwo) :
    PathsExposeNodeCollision nodeHash leafOne leafTwo bits siblingsOne siblingsTwo := by
  by_contra noCollision
  have differentAtEveryLevel : ∀ steps, steps ≤ 20 →
      pathCurrent nodeHash leafOne bits siblingsOne steps ≠
        pathCurrent nodeHash leafTwo bits siblingsTwo steps := by
    intro steps hsteps
    induction steps with
    | zero =>
        simpa [pathCurrent] using differentLeaf
    | succ previous inductionHypothesis =>
        have previousLt : previous < 20 := by omega
        have previousDifferent := inductionHypothesis (by omega)
        have orderedDifferent := ordered_children_ne_of_current_ne
          (bits ⟨previous, previousLt⟩) previousDifferent
          (siblingsOne ⟨previous, previousLt⟩)
          (siblingsTwo ⟨previous, previousLt⟩)
        intro nextEqual
        rw [pathCurrent_succ nodeHash leafOne bits siblingsOne previous previousLt,
          pathCurrent_succ nodeHash leafTwo bits siblingsTwo previous previousLt,
          parent_eq_hash_ordered_children,
          parent_eq_hash_ordered_children] at nextEqual
        exact noCollision ⟨⟨previous, previousLt⟩, orderedDifferent, nextEqual⟩
  have finalDifferent := differentAtEveryLevel 20 (by omega)
  apply finalDifferent
  rw [pathCurrent_twenty_eq_root, pathCurrent_twenty_eq_root, sameRoot]

/-- Regression against an invalid security argument: opposite directions from
the two children of one node are two ordinary openings of the same parent.
Different path bits alone therefore do not imply a collision. -/
theorem opposite_children_are_valid_openings_of_one_parent
    (nodeHash : Digest → Digest → Digest) (left right : Digest) :
    Parent nodeHash false left right = Parent nodeHash true right left := by
  rfl

end AspisApplicationMerkleBinding

#print axioms AspisApplicationMerkleBinding.pathCurrent_twenty_eq_root
#print axioms
  AspisApplicationMerkleBinding.same_position_different_leaf_same_root_exposes_node_collision
#print axioms AspisApplicationMerkleBinding.opposite_children_are_valid_openings_of_one_parent
