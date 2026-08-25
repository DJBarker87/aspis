import AspisFormal.V6CompactFrontierRecurrence

/-!
# Verified `2^frontier` prefactorization

`rawFrontierCount` is the ordinary oriented binary-subtree recurrence. Its
one-child branch has two placements (left or right), while the both-child
branch is the ordered convolution. The theorem below proves that factoring
out `2^frontier` yields exactly the normalized recurrence used by the sparse
release certificate. The generator therefore contributes certificate text,
not an unchecked algebraic assumption.
-/

set_option autoImplicit false

namespace AspisV6CompactFrontierPrefactorization

open AspisV6CompactFrontierRecurrence

def rawFrontierCount : Nat → Nat → Nat → Nat
  | 0, selected, frontier =>
      if selected = 1 ∧ frontier = 0 then 1 else 0
  | depth + 1, selected, frontier =>
      (if frontier = 0 then 0
       else 2 * rawFrontierCount depth selected (frontier - 1)) +
      ∑ offset ∈ Finset.range (selected - 1),
        ∑ leftFrontier ∈ Finset.range (frontier + 1),
          rawFrontierCount depth (offset + 1) leftFrontier *
            rawFrontierCount depth (selected - (offset + 1))
              (frontier - leftFrontier)

theorem rawFrontierCount_eq_concreteFrontierCount
    (depth selected frontier : Nat) :
    rawFrontierCount depth selected frontier =
      concreteFrontierCount depth selected frontier := by
  induction depth generalizing selected frontier with
  | zero =>
      by_cases base : selected = 1 ∧ frontier = 0
      · rcases base with ⟨rfl, rfl⟩
        simp [rawFrontierCount, concreteFrontierCount, frontierCoeff]
      · simp [rawFrontierCount, concreteFrontierCount, frontierCoeff, base]
  | succ depth inductionHypothesis =>
      rw [rawFrontierCount, concreteFrontierCount, frontierCoeff]
      by_cases frontierZero : frontier = 0
      · subst frontier
        simp [inductionHypothesis, concreteFrontierCount]
      · have powerSuccessor :
            2 ^ frontier = 2 * 2 ^ (frontier - 1) := by
          obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero frontierZero
          simp [pow_succ, Nat.mul_comm]
        have convolution :
            (∑ offset ∈ Finset.range (selected - 1),
              ∑ leftFrontier ∈ Finset.range (frontier + 1),
                rawFrontierCount depth (offset + 1) leftFrontier *
                  rawFrontierCount depth (selected - (offset + 1))
                    (frontier - leftFrontier)) =
              (∑ offset ∈ Finset.range (selected - 1),
                ∑ leftFrontier ∈ Finset.range (frontier + 1),
                  frontierCoeff depth (offset + 1) leftFrontier *
                    frontierCoeff depth (selected - (offset + 1))
                      (frontier - leftFrontier)) * 2 ^ frontier := by
          calc
            _ = ∑ offset ∈ Finset.range (selected - 1),
                ∑ leftFrontier ∈ Finset.range (frontier + 1),
                  (frontierCoeff depth (offset + 1) leftFrontier *
                    frontierCoeff depth (selected - (offset + 1))
                      (frontier - leftFrontier)) * 2 ^ frontier := by
                apply Finset.sum_congr rfl
                intro offset offsetMembership
                apply Finset.sum_congr rfl
                intro leftFrontier leftMembership
                rw [inductionHypothesis, inductionHypothesis]
                unfold concreteFrontierCount
                have leftBound : leftFrontier ≤ frontier := by
                  have := Finset.mem_range.mp leftMembership
                  omega
                have addSub : leftFrontier + (frontier - leftFrontier) =
                    frontier := Nat.add_sub_of_le leftBound
                calc
                  frontierCoeff depth (offset + 1) leftFrontier *
                        2 ^ leftFrontier *
                      (frontierCoeff depth (selected - (offset + 1))
                          (frontier - leftFrontier) *
                        2 ^ (frontier - leftFrontier)) =
                      (frontierCoeff depth (offset + 1) leftFrontier *
                        frontierCoeff depth (selected - (offset + 1))
                          (frontier - leftFrontier)) *
                        (2 ^ leftFrontier *
                          2 ^ (frontier - leftFrontier)) := by ring
                  _ = (frontierCoeff depth (offset + 1) leftFrontier *
                        frontierCoeff depth (selected - (offset + 1))
                          (frontier - leftFrontier)) * 2 ^ frontier := by
                        rw [← pow_add, addSub]
            _ = _ := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro offset offsetMembership
              rw [Finset.sum_mul]
        rw [if_neg frontierZero, if_neg frontierZero,
          inductionHypothesis, convolution]
        unfold concreteFrontierCount
        rw [powerSuccessor]
        ring

#print axioms rawFrontierCount_eq_concreteFrontierCount

end AspisV6CompactFrontierPrefactorization
