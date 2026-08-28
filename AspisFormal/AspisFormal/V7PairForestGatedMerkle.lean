import AspisFormal.HashMerkleModel

/-!
# V7 pair-forest gated Merkle selection

The eight-lane V7 layout does not serialize a redundant sibling copy in an
auxiliary row.  Instead, the two children entering the Poseidon node block are
the witnesses themselves and the relation gates only the selected child:

* `(1 - b) * (left - current) = 0`;
* `b * (right - current) = 0`;
* `b * (b - 1) = 0`.

This file proves in-kernel that those equations are exactly enough.  The
unselected child is the sibling witness, so the node block still computes one
ordinary paper `Parent` step.  No collision, one-wayness, or hash assumption is
used in this structural theorem.
-/

namespace AspisFormal.V7PairForestGatedMerkle

open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel

/-- Boolean gated selection forces one child to equal the running digest; the
other child is therefore a canonical existential sibling for this level. -/
theorem gated_selected_child_forces_ordered_children
    (b : F) (hb : b * (b - 1) = 0) (current left right : Digest)
    (hleft : ∀ i, (1 - b) * (left i - current i) = 0)
    (hright : ∀ i, b * (right i - current i) = 0) :
    ∃ sibling : Digest,
      (b = 0 ∧ left = current ∧ right = sibling) ∨
      (b = 1 ∧ left = sibling ∧ right = current) := by
  rcases field_bool hb with hb0 | hb1
  · refine ⟨right, Or.inl ⟨hb0, ?_, rfl⟩⟩
    funext i
    have h := hleft i
    rw [hb0] at h
    have h' : left i - current i = 0 := by simpa using h
    exact sub_eq_zero.mp h'
  · refine ⟨left, Or.inr ⟨hb1, rfl, ?_⟩⟩
    funext i
    have h := hright i
    rw [hb1] at h
    have h' : right i - current i = 0 := by simpa using h
    exact sub_eq_zero.mp h'

/-- Literal gate data for one V7 pair-forest membership level.  The sibling is
not a separate trace cell: it is whichever node child is not selected by `b`. -/
structure GatedMerkleLevelData
    (rc : RoundConstants) (β : Bool) (current next : Digest) where
  b : F
  hbit : b = if β then 1 else 0
  left : Digest
  right : Digest
  hleft : ∀ i, (1 - b) * (left i - current i) = 0
  hright : ∀ i, b * (right i - current i) = 0
  parentState : State
  hnode : RoundChain rc (nodeState NODE_TWEAK left right) parentState
  hnext : next = truncate8 parentState

/-- A V7 gated membership level is an ordinary Merkle `Parent` step for the
existential sibling carried by the unselected node child. -/
theorem GatedMerkleLevelData.forces
    {rc : RoundConstants} {β : Bool} {current next : Digest}
    (d : GatedMerkleLevelData rc β current next) :
    ∃ sibling : Digest, next = Parent (nodeHash rc) β current sibling := by
  have hb : d.b * (d.b - 1) = 0 := by
    rw [d.hbit]
    cases β <;> norm_num
  obtain ⟨sibling, hselected⟩ :=
    gated_selected_child_forces_ordered_children
      d.b hb current d.left d.right d.hleft d.hright
  have hcomp : truncate8 d.parentState = nodeHash rc d.left d.right :=
    node_gate_forces_compression rc d.left d.right d.parentState d.hnode
  refine ⟨sibling, ?_⟩
  rw [d.hnext, hcomp]
  cases β with
  | false =>
      have hb0 : d.b = 0 := by simp [d.hbit]
      rcases hselected with ⟨_, hl, hr⟩ | ⟨hbne, _, _⟩
      · rw [hl, hr]
        simp [Parent]
      · exact absurd hbne (by rw [hb0]; norm_num)
  | true =>
      have hb1 : d.b = 1 := by simp [d.hbit]
      rcases hselected with ⟨hbne, _, _⟩ | ⟨_, hl, hr⟩
      · exact absurd hbne (by rw [hb1]; norm_num)
      · rw [hl, hr]
        simp [Parent]

end AspisFormal.V7PairForestGatedMerkle

#print axioms AspisFormal.V7PairForestGatedMerkle.gated_selected_child_forces_ordered_children
#print axioms AspisFormal.V7PairForestGatedMerkle.GatedMerkleLevelData.forces
