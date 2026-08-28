import AspisFormal.K1.V7Tag73PointwiseFrontierXor
import AspisFormal.K1.V7Tag73Q16SemanticFrontierBridge

/-!
# Exact q16 semantic frontier as a sorted adjacent-XOR expression

The semantic query shape is reconstructed from the deployed schedule range.
This file proves that its canonical recursive leaf order is exactly the
strictly sorted integer schedule range.  Combined with the pointwise XOR
theorem, this removes the last set-vs-array ambiguity from the frontier
bridge.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73Q16PointwiseFrontierBridge

open AspisV6CompactFrontierSemantics
open AspisK1.V7Tag73PointwiseFrontierSemantics
open AspisK1.V7Tag73PointwiseFrontierXor
open AspisK1.V7Tag73Q16CompactScheduleCount
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73Q16FirstCompactUniformity

def orderedShapePositionValues {depth : Nat} (shape : Shape depth) :
    List Nat :=
  (orderedShapeLeaves shape).map leafPositionValue

theorem ordered_shape_leaf_mem_iff_shapeLeaves :
    ∀ {depth : Nat} (shape : Shape depth) (leaf : Leaf depth),
      leaf ∈ orderedShapeLeaves shape ↔ leaf ∈ shapeLeaves shape := by
  intro depth
  induction depth with
  | zero =>
      intro shape leaf
      cases shape
      cases leaf
      simp [orderedShapeLeaves, shapeLeaves]
  | succ depth inductionHypothesis =>
      intro shape leaf
      cases shape with
      | inl one =>
          rcases one with ⟨orientation, child⟩
          cases orientation with
          | false =>
              cases leaf with
              | inl leaf =>
                  simpa [orderedShapeLeaves, shapeLeaves] using
                    inductionHypothesis child leaf
              | inr leaf =>
                  simp [orderedShapeLeaves, shapeLeaves]
          | true =>
              cases leaf with
              | inl leaf =>
                  simp [orderedShapeLeaves, shapeLeaves]
              | inr leaf =>
                  simpa [orderedShapeLeaves, shapeLeaves] using
                    inductionHypothesis child leaf
      | inr both =>
          rcases both with ⟨left, right⟩
          cases leaf with
          | inl leaf =>
              simpa [orderedShapeLeaves, shapeLeaves] using
                inductionHypothesis left leaf
          | inr leaf =>
              simpa [orderedShapeLeaves, shapeLeaves] using
                inductionHypothesis right leaf

/-- Canonical recursive positions are strictly increasing. -/
theorem ordered_shape_position_values_pairwise :
    ∀ {depth : Nat} (shape : Shape depth),
      (orderedShapePositionValues shape).Pairwise (· < ·) := by
  intro depth
  induction depth with
  | zero =>
      intro shape
      cases shape
      simp [orderedShapePositionValues, orderedShapeLeaves,
        leafPositionValue]
  | succ depth inductionHypothesis =>
      intro shape
      cases shape with
      | inl one =>
          rcases one with ⟨orientation, child⟩
          cases orientation with
          | false =>
              simpa [orderedShapePositionValues, orderedShapeLeaves,
                List.map_map, Function.comp_def,
                leaf_position_value_succ_left] using
                  inductionHypothesis child
          | true =>
              rw [orderedShapePositionValues, orderedShapeLeaves, List.map_map,
                List.pairwise_map]
              have childSorted := inductionHypothesis child
              have childLeafSorted :=
                (List.pairwise_map.mp childSorted)
              exact childLeafSorted.imp (fun relation => by
                simp only [Function.comp_apply,
                  leaf_position_value_succ_right]
                omega)
      | inr both =>
          rcases both with ⟨left, right⟩
          rw [orderedShapePositionValues, orderedShapeLeaves, List.map_append,
            List.map_map, List.map_map, List.pairwise_append]
          constructor
          · simpa [orderedShapePositionValues, Function.comp_def,
              leaf_position_value_succ_left] using
                inductionHypothesis left
          constructor
          · rw [List.pairwise_map]
            have rightLeafSorted :=
              List.pairwise_map.mp (inductionHypothesis right)
            exact rightLeafSorted.imp (fun relation => by
              simp only [Function.comp_apply,
                leaf_position_value_succ_right]
              omega)
          · intro leftPosition leftMembership rightPosition rightMembership
            rcases List.mem_map.mp leftMembership with
              ⟨leftLeaf, _leftLeafMem, leftEquality⟩
            rcases List.mem_map.mp rightMembership with
              ⟨rightLeaf, _rightLeafMem, rightEquality⟩
            simp only [Function.comp_apply, leaf_position_value_succ_left]
              at leftEquality
            simp only [Function.comp_apply, leaf_position_value_succ_right]
              at rightEquality
            have leftBound := leaf_position_value_lt leftLeaf
            omega

/-- The canonical recursive position list has exactly the shape's selected
leaf set. -/
theorem ordered_shape_position_values_toFinset
    {depth : Nat} (shape : Shape depth) :
    (orderedShapePositionValues shape).toFinset =
      (shapeLeaves shape).map
        ((leafPositionEquiv depth).toEmbedding.trans Fin.valEmbedding) := by
  ext position
  simp only [List.mem_toFinset, orderedShapePositionValues, List.mem_map,
    Finset.mem_map]
  constructor
  · rintro ⟨leaf, leafMembership, positionEquality⟩
    exact ⟨leaf,
      (ordered_shape_leaf_mem_iff_shapeLeaves shape leaf).mp leafMembership,
      positionEquality⟩
  · rintro ⟨leaf, leafMembership, positionEquality⟩
    exact ⟨leaf,
      (ordered_shape_leaf_mem_iff_shapeLeaves shape leaf).mpr leafMembership,
      positionEquality⟩

/-- For the reconstructed q16 shape, the canonical position set is exactly
the deployed schedule range. -/
def queryPositionNatFinset (schedule : Q16Schedule) : Finset Nat :=
  (queryPositionFinset schedule).map Fin.valEmbedding

theorem query_shape_position_values_toFinset (schedule : Q16Schedule) :
    (orderedShapePositionValues (queryShape schedule)).toFinset =
      queryPositionNatFinset schedule := by
  rw [ordered_shape_position_values_toFinset, queryShape_leaves]
  ext position
  change position ∈
      (queryLeafFinset schedule).map
        ((leafPositionEquiv 18).toEmbedding.trans Fin.valEmbedding) ↔
    position ∈ (queryPositionFinset schedule).map Fin.valEmbedding
  rw [Finset.mem_map, Finset.mem_map]
  constructor
  · rintro ⟨leaf, leafMembership, leafValueEquality⟩
    rw [queryLeafFinset, Finset.mem_map] at leafMembership
    rcases leafMembership with
      ⟨queryPosition, queryMembership, leafEquality⟩
    refine ⟨queryPosition, ?_, ?_⟩
    · exact queryMembership
    · change queryPosition.val = position
      have leafExact :
          leafPositionEquiv 18 leaf = queryPosition := by
        have exact := congrArg (leafPositionEquiv 18) leafEquality.symm
        simpa using exact
      rw [← leafExact]
      exact leafValueEquality
  · rintro ⟨queryPosition, queryMembership, queryValueEquality⟩
    let leaf := (leafPositionEquiv 18).symm queryPosition
    refine ⟨leaf, ?_, ?_⟩
    · rw [queryLeafFinset, Finset.mem_map]
      exact ⟨queryPosition, queryMembership, rfl⟩
    · change (leafPositionEquiv 18 leaf).val = position
      rw [Equiv.apply_symm_apply]
      exact queryValueEquality

/-- Sorting the deployed q16 range returns precisely the recursive canonical
leaf order. -/
theorem query_position_sort_eq_ordered_shape (schedule : Q16Schedule) :
    (queryPositionNatFinset schedule).sort (· ≤ ·) =
      orderedShapePositionValues (queryShape schedule) := by
  let positions := orderedShapePositionValues (queryShape schedule)
  have strictlySorted : positions.Pairwise (· < ·) :=
    ordered_shape_position_values_pairwise (queryShape schedule)
  have sorted : positions.Pairwise (· ≤ ·) :=
    strictlySorted.imp Nat.le_of_lt
  have nodup : positions.Nodup := strictlySorted.nodup
  have canonical := (List.toFinset_sort (· ≤ ·) nodup).2 sorted
  rw [query_shape_position_values_toFinset schedule] at canonical
  exact canonical

def sortedQueryPositions (schedule : Q16Schedule) : List Nat :=
  (queryPositionNatFinset schedule).sort (· ≤ ·)

theorem ordered_shape_position_values_eq_sorted_query
    (schedule : Q16Schedule) :
    (orderedShapeLeaves (queryShape schedule)).map leafPositionValue =
      sortedQueryPositions schedule := by
  change orderedShapePositionValues (queryShape schedule) =
    sortedQueryPositions schedule
  exact (query_position_sort_eq_ordered_shape schedule).symm

/-- Exact q16 semantic frontier expressed solely through the sorted deployed
positions and adjacent XORs. -/
theorem semantic_frontier_eq_sorted_adjacent_xor
    (schedule : Q16Schedule) :
    semanticFrontierNodes schedule =
      18 + 1 + adjacentXorSum (sortedQueryPositions schedule) - 16 := by
  unfold semanticFrontierNodes
  rw [frontier_eq_canonical_adjacent_xor]
  rw [queryShape_selected]
  rw [ordered_shape_position_values_eq_sorted_query]

#print axioms ordered_shape_leaf_mem_iff_shapeLeaves
#print axioms ordered_shape_position_values_pairwise
#print axioms ordered_shape_position_values_toFinset
#print axioms query_position_sort_eq_ordered_shape
#print axioms semantic_frontier_eq_sorted_adjacent_xor

end AspisK1.V7Tag73Q16PointwiseFrontierBridge
