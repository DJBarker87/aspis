import Mathlib.Data.Fintype.Perm
import AspisFormal.V6CompactFrontierSemantics

/-!
# Semantic count of cap-203 q16 schedules

The generated V7 frontier certificate counts unordered sixteen-leaf subsets.
This file connects that recurrence to ordered q16 schedules.  It first proves
that the semantic cap-203 shape type has exactly `compactFavourable` members;
the remaining order factor is represented explicitly rather than hidden in a
decimal count.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace AspisK1.V7Tag73Q16CompactScheduleCount

open AspisV6CompactFrontierRecurrence
open AspisV6CompactFrontierSemantics

noncomputable section

/-- One exact nonempty depth-18 shape with sixteen selected leaves and a
frontier in `0..203`. -/
abbrev Cap203Shape :=
  Σ frontierCount : Fin 204, Fibre 18 16 frontierCount.val

/-- The favourable count stated directly as the semantic recurrence.  The
separate generated certificate proves this integer equals the frozen decimal
used by the V7 security ledger. -/
noncomputable def semanticCompactFavourable : Nat :=
  ∑ frontierCount ∈ Finset.range 204,
    semanticCount 18 16 frontierCount

theorem cap203_shape_card_eq_semanticCompactFavourable :
    Fintype.card Cap203Shape = semanticCompactFavourable := by
  rw [Fintype.card_sigma]
  change (∑ frontierCount : Fin 204,
    semanticCount 18 16 frontierCount.val) = semanticCompactFavourable
  rw [Fin.sum_univ_eq_sum_range]
  rfl

/-- Every cap-203 shape contains exactly the sixteen selected leaves expected
by the deployed q16 schedule. -/
theorem cap203_shape_leaves_card (capShape : Cap203Shape) :
    (shapeLeaves capShape.2.1).card = 16 := by
  rw [shapeLeaves_card]
  exact capShape.2.2.1

/-- The orderings of a shape are bijections from a canonical slot type to
the exact selected-leaf subtype.  Keeping `depth` abstract prevents the
kernel from expanding the depth-18 binary sum merely to find the standard
finite instances. -/
abbrev ShapeOrdering {depth : Nat} (shape : Shape depth) :=
  Fin (selected shape) ≃ (shapeLeaves shape : Type)

/-- A fixed reference ordering for a shape.  Security arguments use only its
bijection laws; deployed position compatibility is supplied separately by
`leafPositionEquiv`. -/
def canonicalShapeOrdering {depth : Nat} (shape : Shape depth) :
    ShapeOrdering shape :=
  Fintype.equivOfCardEq (by
    simpa [shapeLeaves_card])

theorem shape_ordering_card {depth : Nat} (shape : Shape depth) :
    Fintype.card (ShapeOrdering shape) =
      Nat.factorial (selected shape) := by
  simpa using Fintype.card_equiv (canonicalShapeOrdering shape)

/-! ## Bit-compatible leaf positions -/

/-- The canonical full-binary-tree identification.  At each recursive level
the left subtree occupies the lower half and the right subtree the upper
half.  This is the integer layout used by the deployed sorted-XOR frontier
routine, rather than an arbitrary cardinality-only equivalence. -/
def leafPositionEquiv : (depth : Nat) → Leaf depth ≃ Fin (2 ^ depth)
  | 0 =>
      { toFun := fun _leaf => ⟨0, by norm_num⟩
        invFun := fun _position => PUnit.unit
        left_inv := by
          intro leaf
          cases leaf
          rfl
        right_inv := by
          intro position
          apply Fin.ext
          omega }
  | depth + 1 =>
      ((leafPositionEquiv depth).sumCongr (leafPositionEquiv depth)).trans
        (finSumFinEquiv.trans (finCongr (by
          rw [pow_succ]
          omega)))

@[simp] theorem leafPositionEquiv_zero_apply (leaf : Leaf 0) :
    (leafPositionEquiv 0 leaf).val = 0 := by
  rfl

theorem leafPositionEquiv_succ_left_val
    (depth : Nat) (leaf : Leaf depth) :
    (leafPositionEquiv (depth + 1) (Sum.inl leaf)).val =
      (leafPositionEquiv depth leaf).val := by
  simp [leafPositionEquiv, finSumFinEquiv]

theorem leafPositionEquiv_succ_right_val
    (depth : Nat) (leaf : Leaf depth) :
    (leafPositionEquiv (depth + 1) (Sum.inr leaf)).val =
      2 ^ depth + (leafPositionEquiv depth leaf).val := by
  simp [leafPositionEquiv, finSumFinEquiv, Nat.add_comm]

/-- An exact ordered compact schedule: a cap-203 semantic shape plus a
permutation of its canonical sixteen-element ordering.  `shape_ordering_card`
proves that this representation has exactly the same fibre cardinality as
the explicit selected-leaf bijections, without forcing the kernel to unfold
the depth-18 leaf type during instance search. -/
abbrev OrderedCap203Schedule :=
  Cap203Shape × Equiv.Perm (Fin 16)

theorem ordered_cap203_schedule_card :
    Fintype.card OrderedCap203Schedule =
      semanticCompactFavourable * Nat.factorial 16 := by
  rw [Fintype.card_prod,
    cap203_shape_card_eq_semanticCompactFavourable,
    Fintype.card_perm, Fintype.card_fin]

/-! ## Audit -/

#print axioms cap203_shape_card_eq_semanticCompactFavourable
#print axioms cap203_shape_leaves_card
#print axioms shape_ordering_card
#print axioms ordered_cap203_schedule_card

end

end AspisK1.V7Tag73Q16CompactScheduleCount
