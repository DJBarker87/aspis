import Mathlib

/-!
# Exact adjacent-prefix factorisation of a binary Merkle frontier

The production V6 verifier no longer walks all eighteen tree levels once for
every rejected compact-query candidate.  For sorted, distinct leaves, let
`height i` be the index of the highest differing bit of adjacent leaves
`i` and `i+1`.  At level `l`, the occupied-node count is one plus the number
of adjacent boundaries whose height is at least `l`.

This file proves that summing the ordinary per-level frontier balance

`2 * occupied (l + 1) - occupied l`

is exactly

`depth + 1 - queryCount + sum height`.

The theorem is pure integer algebra.  Its hypotheses expose the two source
obligations instead of hiding them: every adjacent height is below the tree
depth, and the optimized natural-number subtraction is nonnegative.  The
Rust-to-model bridge must additionally establish that `floor(log2(a XOR b))`
is the adjacent height for the sorted `u32` leaves.
-/

set_option autoImplicit false

namespace AspisV6BinaryFrontier

/-- Occupied nodes at one level, expressed by the adjacent-prefix boundary
law for a sorted nonempty leaf sequence.  `gaps + 1` is the query count. -/
def occupiedFromAdjacent {gaps : Nat} (height : Fin gaps → Nat)
    (level : Nat) : Nat :=
  1 + ∑ gap : Fin gaps, if level ≤ height gap then 1 else 0

/-- Signed form of the ordinary level-walk frontier count.  For an actual
binary tree every summand is nonnegative and is the number of parents with
exactly one occupied child. -/
def levelWalkSigned {gaps : Nat} (depth : Nat)
    (height : Fin gaps → Nat) : Int :=
  ∑ level ∈ Finset.range depth,
    ((2 * occupiedFromAdjacent height (level + 1) : Int) -
      occupiedFromAdjacent height level)

/-- The exact expression evaluated by `binary_frontier_nodes` after sorting
and validating the query array. -/
def adjacentPrefixExpanded {gaps : Nat} (depth : Nat)
    (height : Fin gaps → Nat) : Nat :=
  depth + 1 + ∑ gap : Fin gaps, height gap

/-- A finite indicator sum counts exactly `height` levels when the height is
within the depth bound. -/
private theorem sum_level_indicator
    (depth height : Nat) (heightBound : height ≤ depth) :
    (∑ level ∈ Finset.range depth,
      if level < height then (1 : Int) else 0) = height := by
  induction depth generalizing height with
  | zero =>
      have : height = 0 := by omega
      simp [this]
  | succ depth inductionHypothesis =>
      by_cases withinPrevious : height ≤ depth
      · rw [Finset.sum_range_succ]
        have notAtLast : ¬ depth < height := Nat.not_lt.mpr withinPrevious
        rw [if_neg notAtLast, add_zero,
          inductionHypothesis height withinPrevious]
      · have exactHeight : height = depth + 1 := by omega
        subst exactHeight
        calc
          (∑ level ∈ Finset.range (depth + 1),
              if level < depth + 1 then (1 : Int) else 0) =
              ∑ _level ∈ Finset.range (depth + 1), (1 : Int) := by
                apply Finset.sum_congr rfl
                intro level membership
                simp [Finset.mem_range.mp membership]
          _ = depth + 1 := by simp

/-- Telescoping identity behind the level walk, stated for an arbitrary
natural occupied-node sequence. -/
private theorem level_balance_telescopes (depth : Nat)
    (occupied : Nat → Nat) :
    (∑ level ∈ Finset.range depth,
      ((2 * occupied (level + 1) : Int) - occupied level)) =
      (occupied depth : Int) - occupied 0 +
        ∑ level ∈ Finset.range depth, (occupied (level + 1) : Int) := by
  induction depth with
  | zero => simp
  | succ depth inductionHypothesis =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ,
        inductionHypothesis]
      ring

/-- Summing the occupied-node law over levels turns each adjacent boundary
of height `h` into exactly `h` contributions. -/
private theorem occupied_tail_sum
    {gaps depth : Nat} (height : Fin gaps → Nat)
    (heightBound : ∀ gap, height gap < depth) :
    (∑ level ∈ Finset.range depth,
      (occupiedFromAdjacent height (level + 1) : Int)) =
      depth + ∑ gap : Fin gaps, height gap := by
  simp only [occupiedFromAdjacent, Nat.cast_add, Nat.cast_one,
    Nat.cast_sum, Nat.cast_ite]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [Finset.sum_comm]
  apply congrArg (fun value : Int => (depth : Int) + value)
  apply Finset.sum_congr rfl
  intro gap _
  have bound : height gap ≤ depth := Nat.le_of_lt (heightBound gap)
  simpa [Nat.add_one_le_iff] using
    sum_level_indicator depth (height gap) bound

/-- The ordinary eighteen-level walk and the adjacent-XOR expression are
exactly equal.  This is the mathematical justification for replacing the
level loop; it changes no Merkle topology or acceptance predicate. -/
theorem levelWalkSigned_eq_adjacentPrefix
    {gaps depth : Nat} (height : Fin gaps → Nat)
    (heightBound : ∀ gap, height gap < depth) :
    levelWalkSigned depth height =
      (adjacentPrefixExpanded depth height : Int) - (gaps + 1) := by
  rw [levelWalkSigned, level_balance_telescopes]
  have occupiedTop : occupiedFromAdjacent height depth = 1 := by
    simp [occupiedFromAdjacent, Nat.not_le.mpr (heightBound _)]
  have occupiedBottom : occupiedFromAdjacent height 0 = gaps + 1 := by
    simp [occupiedFromAdjacent, Nat.add_comm]
  rw [occupiedTop, occupiedBottom, occupied_tail_sum height heightBound]
  simp [adjacentPrefixExpanded]
  ring

/-- Natural-number spelling used by Rust's final `checked_sub`. -/
theorem levelWalkSigned_eq_checkedSub
    {gaps depth : Nat} (height : Fin gaps → Nat)
    (heightBound : ∀ gap, height gap < depth)
    (subtractionSafe : gaps + 1 ≤ adjacentPrefixExpanded depth height) :
    levelWalkSigned depth height =
      (adjacentPrefixExpanded depth height - (gaps + 1) : Nat) := by
  rw [levelWalkSigned_eq_adjacentPrefix height heightBound]
  exact (Int.ofNat_sub subtractionSafe).symm

/-- The final `checked_sub` cannot fail whenever the number of adjacent gaps
fits within the tree depth.  V6 instantiates this with fifteen gaps and depth
eighteen. -/
theorem levelWalkSigned_eq_checkedSub_of_gapBound
    {gaps depth : Nat} (height : Fin gaps → Nat)
    (heightBound : ∀ gap, height gap < depth)
    (gapBound : gaps ≤ depth) :
    levelWalkSigned depth height =
      (adjacentPrefixExpanded depth height - (gaps + 1) : Nat) := by
  apply levelWalkSigned_eq_checkedSub height heightBound
  calc
    gaps + 1 ≤ depth + 1 := Nat.add_le_add_right gapBound 1
    _ ≤ adjacentPrefixExpanded depth height := by
      simp [adjacentPrefixExpanded]

/-- Exact mathematical spelling of the optimized Rust adjacent-XOR loop.
The remaining source bridge identifies `31 - xor.leading_zeros()` with
`Nat.log2 xor` for each nonzero 32-bit XOR. -/
def adjacentXorHeight {gaps : Nat} (queries : Fin (gaps + 1) → Nat)
    (gap : Fin gaps) : Nat :=
  Nat.log2 (Nat.xor (queries gap.castSucc) (queries gap.succ))

theorem levelWalkSigned_eq_adjacentXor_checkedSub
    {gaps depth : Nat} (queries : Fin (gaps + 1) → Nat)
    (heightBound : ∀ gap, adjacentXorHeight queries gap < depth)
    (gapBound : gaps ≤ depth) :
    levelWalkSigned depth (adjacentXorHeight queries) =
      (adjacentPrefixExpanded depth (adjacentXorHeight queries) -
        (gaps + 1) : Nat) :=
  levelWalkSigned_eq_checkedSub_of_gapBound
    (adjacentXorHeight queries) heightBound gapBound

#print axioms levelWalkSigned_eq_adjacentPrefix
#print axioms levelWalkSigned_eq_checkedSub
#print axioms levelWalkSigned_eq_checkedSub_of_gapBound
#print axioms levelWalkSigned_eq_adjacentXor_checkedSub

end AspisV6BinaryFrontier
