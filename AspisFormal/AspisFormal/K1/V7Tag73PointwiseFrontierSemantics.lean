import AspisFormal.V6CompactFrontierSemantics

/-!
# Pointwise binary-frontier semantics

The generated compact-frontier certificate counts recursive binary-tree
shapes, while production evaluates the sorted adjacent-boundary formula.  This
module proves their pointwise equality before any representation-specific
`u32`/XOR bridge.

For a nonempty ordered leaf set, each adjacent pair contributes the height of
its highest separating binary node.  The exact identity is

`frontier + selected = depth + 1 + sum adjacent heights`.

It is proved structurally on the same `Shape` used by the semantic counting
certificate.  The remaining source leaf only has to identify the recursive
leaf order and separation height with sorted `u32` positions and Rust's
`31 - leading_zeros(xor)` expression.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73PointwiseFrontierSemantics

open AspisV6CompactFrontierSemantics

/-- Height of the highest binary node separating two leaves.  Equal leaves
are assigned zero; only distinct adjacent leaves are used in the frontier
identity. -/
def leafSeparationHeight : {depth : Nat} → Leaf depth → Leaf depth → Nat
  | 0, _, _ => 0
  | depth + 1, Sum.inl left, Sum.inl right =>
      leafSeparationHeight left right
  | depth + 1, Sum.inr left, Sum.inr right =>
      leafSeparationHeight left right
  | depth + 1, Sum.inl _, Sum.inr _ => depth
  | depth + 1, Sum.inr _, Sum.inl _ => depth

/-- Canonical left-to-right leaf list of one recursive semantic shape. -/
def orderedShapeLeaves : {depth : Nat} → Shape depth → List (Leaf depth)
  | 0, _ => [PUnit.unit]
  | _ + 1, Sum.inl (false, child) =>
      (orderedShapeLeaves child).map Sum.inl
  | _ + 1, Sum.inl (true, child) =>
      (orderedShapeLeaves child).map Sum.inr
  | _ + 1, Sum.inr (left, right) =>
      (orderedShapeLeaves left).map Sum.inl ++
        (orderedShapeLeaves right).map Sum.inr

def adjacentHeightSumFrom {depth : Nat} (previous : Leaf depth) :
    List (Leaf depth) → Nat
  | [] => 0
  | next :: rest =>
      leafSeparationHeight previous next + adjacentHeightSumFrom next rest

def adjacentHeightSum {depth : Nat} : List (Leaf depth) → Nat
  | [] => 0
  | first :: rest => adjacentHeightSumFrom first rest

def leftLeaf {depth : Nat} (leaf : Leaf depth) : Leaf (depth + 1) :=
  Sum.inl leaf

def rightLeaf {depth : Nat} (leaf : Leaf depth) : Leaf (depth + 1) :=
  Sum.inr leaf

@[simp] theorem leaf_separation_height_left
    {depth : Nat} (left right : Leaf depth) :
    leafSeparationHeight (leftLeaf left) (leftLeaf right) =
      leafSeparationHeight left right := by
  rfl

@[simp] theorem leaf_separation_height_right
    {depth : Nat} (left right : Leaf depth) :
    leafSeparationHeight (rightLeaf left) (rightLeaf right) =
      leafSeparationHeight left right := by
  rfl

@[simp] theorem leaf_separation_height_left_right
    {depth : Nat} (left right : Leaf depth) :
    leafSeparationHeight (leftLeaf left) (rightLeaf right) = depth := by
  rfl

theorem ordered_shape_leaves_nonempty
    {depth : Nat} (shape : Shape depth) :
    orderedShapeLeaves shape ≠ [] := by
  induction depth with
  | zero =>
      cases shape
      simp [orderedShapeLeaves]
  | succ depth ih =>
      cases shape with
      | inl one =>
          rcases one with ⟨orientation, child⟩
          cases orientation <;>
            simp [orderedShapeLeaves, ih child]
      | inr both =>
          rcases both with ⟨left, right⟩
          simp [orderedShapeLeaves, ih left]

theorem ordered_shape_leaves_length
    {depth : Nat} (shape : Shape depth) :
    (orderedShapeLeaves shape).length = selected shape := by
  induction depth with
  | zero =>
      cases shape
      simp [orderedShapeLeaves, selected]
  | succ depth ih =>
      cases shape with
      | inl one =>
          rcases one with ⟨orientation, child⟩
          cases orientation <;>
            simp [orderedShapeLeaves, selected, ih child]
      | inr both =>
          rcases both with ⟨left, right⟩
          simp [orderedShapeLeaves, selected, ih left, ih right]

private theorem adjacent_height_sum_from_map_inl
    {depth : Nat} (previous : Leaf depth) (rest : List (Leaf depth)) :
    adjacentHeightSumFrom (leftLeaf previous) (rest.map leftLeaf) =
      adjacentHeightSumFrom previous rest := by
  induction rest generalizing previous with
  | nil => rfl
  | cons next tail ih =>
      simp [adjacentHeightSumFrom, ih]

private theorem adjacent_height_sum_from_map_inr
    {depth : Nat} (previous : Leaf depth) (rest : List (Leaf depth)) :
    adjacentHeightSumFrom (rightLeaf previous) (rest.map rightLeaf) =
      adjacentHeightSumFrom previous rest := by
  induction rest generalizing previous with
  | nil => rfl
  | cons next tail ih =>
      simp [adjacentHeightSumFrom, ih]

@[simp] theorem adjacent_height_sum_map_inl
    {depth : Nat} (leaves : List (Leaf depth)) :
    adjacentHeightSum (leaves.map leftLeaf) =
      adjacentHeightSum leaves := by
  cases leaves with
  | nil => rfl
  | cons first rest =>
      exact adjacent_height_sum_from_map_inl first rest

@[simp] theorem adjacent_height_sum_map_inr
    {depth : Nat} (leaves : List (Leaf depth)) :
    adjacentHeightSum (leaves.map rightLeaf) =
      adjacentHeightSum leaves := by
  cases leaves with
  | nil => rfl
  | cons first rest =>
      exact adjacent_height_sum_from_map_inr first rest

/-- Concatenating a nonempty left subtree and nonempty right subtree adds
exactly the current child depth as the one cross-subtree boundary. -/
theorem adjacent_height_sum_inl_append_inr
    {depth : Nat} (left right : List (Leaf depth))
    (leftNonempty : left ≠ []) (rightNonempty : right ≠ []) :
    adjacentHeightSum (left.map leftLeaf ++ right.map rightLeaf) =
      adjacentHeightSum left + depth + adjacentHeightSum right := by
  induction left with
  | nil => exact False.elim (leftNonempty rfl)
  | cons first rest ih =>
      cases rest with
      | nil =>
          cases right with
          | nil => exact False.elim (rightNonempty rfl)
          | cons rightFirst rightRest =>
              simp only [List.map_cons, List.map_nil, List.nil_append,
                List.cons_append, adjacentHeightSum, adjacentHeightSumFrom,
                leaf_separation_height_left_right, Nat.zero_add]
              rw [adjacent_height_sum_from_map_inr]
      | cons second tail =>
          have tailNonempty : second :: tail ≠ [] := by simp
          have tailExact := ih tailNonempty
          have tailExact' :
              adjacentHeightSumFrom
                  (leftLeaf second)
                  (tail.map leftLeaf ++ right.map rightLeaf) =
                adjacentHeightSumFrom second tail + depth +
                  adjacentHeightSum right := by
            simpa [adjacentHeightSum] using tailExact
          change
            leafSeparationHeight (leftLeaf first) (leftLeaf second) +
                adjacentHeightSumFrom (leftLeaf second)
                  (tail.map leftLeaf ++ right.map rightLeaf) =
              leafSeparationHeight first second +
                adjacentHeightSumFrom second tail + depth +
                  adjacentHeightSum right
          rw [leaf_separation_height_left]
          rw [tailExact']
          omega

/-- Pointwise semantic frontier identity for every recursive nonempty binary
shape. -/
theorem frontier_add_selected_eq_adjacent_heights
    {depth : Nat} (shape : Shape depth) :
    AspisV6CompactFrontierSemantics.frontier shape + selected shape =
      depth + 1 + adjacentHeightSum (orderedShapeLeaves shape) := by
  induction depth with
  | zero =>
      cases shape
      rfl
  | succ depth ih =>
      cases shape with
      | inl one =>
          rcases one with ⟨orientation, child⟩
          have childExact := ih child
          cases orientation with
          | false =>
              change
                (AspisV6CompactFrontierSemantics.frontier child + 1) +
                    selected child =
                  (depth + 1) + 1 +
                    adjacentHeightSum
                      ((orderedShapeLeaves child).map leftLeaf)
              rw [adjacent_height_sum_map_inl]
              omega
          | true =>
              change
                (AspisV6CompactFrontierSemantics.frontier child + 1) +
                    selected child =
                  (depth + 1) + 1 +
                    adjacentHeightSum
                      ((orderedShapeLeaves child).map rightLeaf)
              rw [adjacent_height_sum_map_inr]
              omega
      | inr both =>
          rcases both with ⟨left, right⟩
          have leftExact := ih left
          have rightExact := ih right
          have joined := adjacent_height_sum_inl_append_inr
            (orderedShapeLeaves left) (orderedShapeLeaves right)
            (ordered_shape_leaves_nonempty left)
            (ordered_shape_leaves_nonempty right)
          change
            (AspisV6CompactFrontierSemantics.frontier left +
                AspisV6CompactFrontierSemantics.frontier right) +
                (selected left + selected right) =
              (depth + 1) + 1 +
                adjacentHeightSum
                  ((orderedShapeLeaves left).map leftLeaf ++
                    (orderedShapeLeaves right).map rightLeaf)
          rw [joined]
          omega

/-- Natural checked-sub spelling used by the production adjacent-boundary
implementation. -/
theorem frontier_eq_adjacent_heights_checked_sub
    {depth : Nat} (shape : Shape depth) :
    AspisV6CompactFrontierSemantics.frontier shape =
      depth + 1 + adjacentHeightSum (orderedShapeLeaves shape) -
        selected shape := by
  have exact := frontier_add_selected_eq_adjacent_heights shape
  omega

#print axioms ordered_shape_leaves_nonempty
#print axioms ordered_shape_leaves_length
#print axioms adjacent_height_sum_map_inl
#print axioms adjacent_height_sum_map_inr
#print axioms adjacent_height_sum_inl_append_inr
#print axioms frontier_add_selected_eq_adjacent_heights
#print axioms frontier_eq_adjacent_heights_checked_sub

end AspisK1.V7Tag73PointwiseFrontierSemantics
