import Mathlib

/-!
# Exact lowering of the deployed nested decoder loop

The archived V5 source decodes four points with nineteen columns per point.
Its `?` return is inside both loops.  The extended pinned Aeneas pre-pass now
lowers that return, but translation then stops at the nested mutable-iterator
borrow carried by the same two loops.

For extraction only, the checked source transformation moves the same decode
operation into one 76-entry loop and reconstructs row `point` from entries
`19 * point + column`.  This file proves the semantic part of that lowering:
the original nested loop and the extraction loop visit exactly the same
indices in exactly the same order.  Consequently they return the same first
decode error, including its index, or the same ordered list of 76 values.

This theorem is deliberately about the one released loop shape.  It is not a
general extension of Aeneas and it does not claim that Aeneas translated the
unmodified nested loop.
-/

namespace AspisV5DeployedNestedLoopLowering

/-- Observable result of the decode part of `prepare_v5_pcs_claims`.
`failure i` records the exact index carried by
`NonCanonicalEvaluation { index: i }`. -/
inductive DecodeOutcome (α : Type) where
  | success (values : List α)
  | failure (index : Nat)
deriving Repr, DecidableEq

/-- Execute decode operations from left to right, stopping at the first
non-canonical field exactly as Rust's `?` does. -/
def runDecodeOrder {α : Type} (decode : Nat → Option α) :
    List Nat → DecodeOutcome α
  | [] => .success []
  | index :: rest =>
      match decode index with
      | none => .failure index
      | some value =>
          match runDecodeOrder decode rest with
          | .failure failed => .failure failed
          | .success values => .success (value :: values)

/-- Point-major index order of the exact archived nested loops:
`point = 0..3`, then `column = 0..18`. -/
def deployedNestedVisitOrder : List Nat :=
  (List.range 4).flatMap fun point =>
    (List.range 19).map fun column => point * 19 + column

/-- Index order of the single extraction-only decoder loop. -/
def loweredFlatVisitOrder : List Nat := List.range 76

/-- Source-shaped semantics of the archived nested decoder. -/
def deployedNestedDecode {α : Type} (decode : Nat → Option α) :
    DecodeOutcome α :=
  runDecodeOrder decode deployedNestedVisitOrder

/-- Source-shaped semantics of the extraction-only flat decoder. -/
def loweredFlatDecode {α : Type} (decode : Nat → Option α) :
    DecodeOutcome α :=
  runDecodeOrder decode loweredFlatVisitOrder

/-- The two concrete loop nests enumerate the identical sequence `0..75`.
This is the entire control-flow fact needed to lower the unsupported nested
early return without changing which operation runs next. -/
theorem deployed_nested_visit_order_eq_lowered_flat :
    deployedNestedVisitOrder = loweredFlatVisitOrder := by
  norm_num [deployedNestedVisitOrder, loweredFlatVisitOrder,
    List.range_succ]

/-- Universal semantics-preservation theorem for the checked lowering.
The decoder is arbitrary, so the equality covers all byte strings and all
possible decoder behaviours, not only the released proof. -/
theorem deployed_nested_decode_eq_lowered_flat_decode {α : Type}
    (decode : Nat → Option α) :
    deployedNestedDecode decode = loweredFlatDecode decode := by
  simp only [deployedNestedDecode, loweredFlatDecode,
    deployed_nested_visit_order_eq_lowered_flat]

/-- In particular, both versions report exactly the same first failing field
and therefore the same `NonCanonicalEvaluation` index. -/
theorem deployed_nested_failure_iff_lowered_flat_failure {α : Type}
    (decode : Nat → Option α) (failed : Nat) :
    deployedNestedDecode decode = .failure failed ↔
      loweredFlatDecode decode = .failure failed := by
  rw [deployed_nested_decode_eq_lowered_flat_decode]

/-- On success, both versions return exactly the same ordered 76 values. -/
theorem deployed_nested_success_iff_lowered_flat_success {α : Type}
    (decode : Nat → Option α) (values : List α) :
    deployedNestedDecode decode = .success values ↔
      loweredFlatDecode decode = .success values := by
  rw [deployed_nested_decode_eq_lowered_flat_decode]

/-- Every index in the transformed successful table has the same released
point-major address used by the proved row helper. -/
theorem lowered_row_index_eq_deployed_index (point : Fin 4)
    (column : Fin 19) :
    point.val * 19 + column.val = 19 * point.val + column.val := by
  omega

#print axioms deployed_nested_visit_order_eq_lowered_flat
#print axioms deployed_nested_decode_eq_lowered_flat_decode
#print axioms deployed_nested_failure_iff_lowered_flat_failure
#print axioms deployed_nested_success_iff_lowered_flat_success
#print axioms lowered_row_index_eq_deployed_index

end AspisV5DeployedNestedLoopLowering
