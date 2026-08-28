import AspisFormal.K1.V7Tag73PointwiseFrontierSemantics
import AspisFormal.K1.V7Tag73Q16CompactScheduleCount

/-!
# Pointwise binary-frontier XOR bridge

The recursive semantic frontier theorem uses the height of the highest node
separating two canonical leaves.  Production uses `floor(log2(left XOR
right))` on the corresponding integer positions.  This file proves those
quantities equal for every pair of leaves, and consequently rewrites the
semantic adjacent-height sum as the exact adjacent-XOR sum.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73PointwiseFrontierXor

open AspisV6CompactFrontierSemantics
open AspisK1.V7Tag73PointwiseFrontierSemantics
open AspisK1.V7Tag73Q16CompactScheduleCount

def leafPositionValue {depth : Nat} (leaf : Leaf depth) : Nat :=
  (leafPositionEquiv depth leaf).val

theorem leaf_position_value_lt {depth : Nat} (leaf : Leaf depth) :
    leafPositionValue leaf < 2 ^ depth :=
  (leafPositionEquiv depth leaf).isLt

@[simp] theorem leaf_position_value_succ_left
    {depth : Nat} (leaf : Leaf depth) :
    @leafPositionValue (depth + 1) (Sum.inl leaf) =
      leafPositionValue leaf := by
  exact leafPositionEquiv_succ_left_val depth leaf

@[simp] theorem leaf_position_value_succ_right
    {depth : Nat} (leaf : Leaf depth) :
    @leafPositionValue (depth + 1) (Sum.inr leaf) =
      2 ^ depth + leafPositionValue leaf := by
  exact leafPositionEquiv_succ_right_val depth leaf

private theorem xor_high_high
    {depth left right : Nat}
    (leftBound : left < 2 ^ depth)
    (rightBound : right < 2 ^ depth) :
    Nat.xor (2 ^ depth + left) (2 ^ depth + right) =
      Nat.xor left right := by
  apply Nat.eq_of_testBit_eq
  intro bit
  have xorBound : Nat.xor left right < 2 ^ depth :=
    Nat.xor_lt_two_pow leftBound rightBound
  simp only [Nat.xor_eq]
  rw [Nat.testBit_xor, Nat.testBit_xor]
  rw [show 2 ^ depth + left = 2 ^ depth * 1 + left by omega]
  rw [show 2 ^ depth + right = 2 ^ depth * 1 + right by omega]
  rw [Nat.testBit_two_pow_mul_add 1 leftBound bit]
  rw [Nat.testBit_two_pow_mul_add 1 rightBound bit]
  have lowDecomposition :=
    Nat.testBit_two_pow_mul_add 0 xorBound bit
  simp only [Nat.mul_zero, Nat.zero_add] at lowDecomposition
  by_cases below : bit < depth
  · simpa [below] using lowDecomposition.symm
  · simpa [below] using lowDecomposition.symm

private theorem xor_low_high
    {depth left right : Nat}
    (leftBound : left < 2 ^ depth)
    (rightBound : right < 2 ^ depth) :
    Nat.xor left (2 ^ depth + right) =
      2 ^ depth + Nat.xor left right := by
  apply Nat.eq_of_testBit_eq
  intro bit
  have xorBound : Nat.xor left right < 2 ^ depth :=
    Nat.xor_lt_two_pow leftBound rightBound
  simp only [Nat.xor_eq]
  rw [Nat.testBit_xor]
  have leftBits : left.testBit bit =
      if bit < depth then left.testBit bit else (0 : Nat).testBit (bit - depth) := by
    simpa using Nat.testBit_two_pow_mul_add 0 leftBound bit
  have rightBits : (2 ^ depth + right).testBit bit =
      if bit < depth then right.testBit bit else (1 : Nat).testBit (bit - depth) := by
    simpa using Nat.testBit_two_pow_mul_add 1 rightBound bit
  have outputBits : (2 ^ depth + (left ^^^ right)).testBit bit =
      if bit < depth then (left ^^^ right).testBit bit
      else (1 : Nat).testBit (bit - depth) := by
    simpa using Nat.testBit_two_pow_mul_add 1 xorBound bit
  rw [leftBits, rightBits, outputBits]
  by_cases below : bit < depth <;> simp [below]

private theorem log2_xor_low_high
    {depth left right : Nat}
    (leftBound : left < 2 ^ depth)
    (rightBound : right < 2 ^ depth) :
    Nat.log2 (Nat.xor left (2 ^ depth + right)) = depth := by
  rw [xor_low_high leftBound rightBound]
  have xorBound : Nat.xor left right < 2 ^ depth :=
    Nat.xor_lt_two_pow leftBound rightBound
  apply (Nat.log2_eq_iff (by omega)).2
  constructor
  · omega
  · rw [pow_succ]
    omega

private theorem log2_xor_high_low
    {depth left right : Nat}
    (leftBound : left < 2 ^ depth)
    (rightBound : right < 2 ^ depth) :
    Nat.log2 (Nat.xor (2 ^ depth + left) right) = depth := by
  rw [Nat.xor_eq, Nat.xor_comm]
  exact log2_xor_low_high rightBound leftBound

/-- The recursive separation height is exactly the highest differing bit of
the canonical integer positions. -/
theorem leaf_separation_height_eq_log2_xor_position :
    ∀ {depth : Nat} (left right : Leaf depth),
      leafSeparationHeight left right =
        Nat.log2 (Nat.xor (leafPositionValue left)
          (leafPositionValue right)) := by
  intro depth
  induction depth with
  | zero =>
      intro left right
      cases left
      cases right
      rfl
  | succ depth inductionHypothesis =>
      intro left right
      cases left with
      | inl leftLeaf =>
          cases right with
          | inl rightLeaf =>
              change leafSeparationHeight leftLeaf rightLeaf = Nat.log2
                (Nat.xor (leafPositionValue leftLeaf)
                  (leafPositionValue rightLeaf))
              exact inductionHypothesis leftLeaf rightLeaf
          | inr rightLeaf =>
              change depth = Nat.log2
                (Nat.xor (leafPositionValue leftLeaf)
                  (2 ^ depth + leafPositionValue rightLeaf))
              exact (log2_xor_low_high
                (leaf_position_value_lt leftLeaf)
                (leaf_position_value_lt rightLeaf)).symm
      | inr leftLeaf =>
          cases right with
          | inl rightLeaf =>
              change depth = Nat.log2
                (Nat.xor (2 ^ depth + leafPositionValue leftLeaf)
                  (leafPositionValue rightLeaf))
              exact (log2_xor_high_low
                (leaf_position_value_lt leftLeaf)
                (leaf_position_value_lt rightLeaf)).symm
          | inr rightLeaf =>
              change leafSeparationHeight leftLeaf rightLeaf = Nat.log2
                (Nat.xor (2 ^ depth + leafPositionValue leftLeaf)
                  (2 ^ depth + leafPositionValue rightLeaf))
              rw [xor_high_high
                (leaf_position_value_lt leftLeaf)
                (leaf_position_value_lt rightLeaf)]
              exact inductionHypothesis leftLeaf rightLeaf

def adjacentXorSumFrom (previous : Nat) : List Nat → Nat
  | [] => 0
  | next :: rest =>
      Nat.log2 (Nat.xor previous next) + adjacentXorSumFrom next rest

def adjacentXorSum : List Nat → Nat
  | [] => 0
  | first :: rest => adjacentXorSumFrom first rest

private theorem adjacent_height_sum_from_eq_xor
    {depth : Nat} (previous : Leaf depth) (rest : List (Leaf depth)) :
    adjacentHeightSumFrom previous rest =
      adjacentXorSumFrom (leafPositionValue previous)
        (rest.map leafPositionValue) := by
  induction rest generalizing previous with
  | nil => rfl
  | cons next tail inductionHypothesis =>
      simp only [adjacentHeightSumFrom, List.map_cons, adjacentXorSumFrom]
      rw [leaf_separation_height_eq_log2_xor_position]
      rw [inductionHypothesis]

/-- The full semantic adjacent-height sum is the exact adjacent-XOR sum on
canonical integer positions. -/
theorem adjacent_height_sum_eq_xor
    {depth : Nat} (leaves : List (Leaf depth)) :
    adjacentHeightSum leaves =
      adjacentXorSum (leaves.map leafPositionValue) := by
  cases leaves with
  | nil => rfl
  | cons first rest =>
      exact adjacent_height_sum_from_eq_xor first rest

/-- Pointwise frontier identity in the same adjacent-XOR arithmetic used by
production, before specializing the canonical leaf list to a q16 schedule. -/
theorem frontier_eq_canonical_adjacent_xor
    {depth : Nat} (shape : Shape depth) :
    frontier shape =
      depth + 1 +
          adjacentXorSum
            ((orderedShapeLeaves shape).map leafPositionValue) -
        selected shape := by
  rw [frontier_eq_adjacent_heights_checked_sub]
  rw [adjacent_height_sum_eq_xor]

#print axioms leaf_separation_height_eq_log2_xor_position
#print axioms adjacent_height_sum_eq_xor
#print axioms frontier_eq_canonical_adjacent_xor

end AspisK1.V7Tag73PointwiseFrontierXor
