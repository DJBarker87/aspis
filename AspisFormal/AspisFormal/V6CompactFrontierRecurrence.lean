import Mathlib

/-!
# Exact normalized binary-frontier recurrence for V6

For a nonempty selected subset, `frontierCoeff d k f` is the coefficient of
the normalized frontier polynomial: the concrete number of `k`-leaf subsets
with `f` frontier siblings is `frontierCoeff d k f * 2^f`.

At the next binary-tree level there are two cases.  If exactly one child is
nonempty, the two child placements cancel the factor two contributed by the
new frontier node, giving the shifted coefficient.  If both children are
nonempty, their ordered selected-leaf and frontier counts convolve.  This is
the exact subtree factorization used by the generated release certificate.
-/

set_option autoImplicit false

namespace AspisV6CompactFrontierRecurrence

/-- Coefficients of the normalized nonempty-subset frontier polynomial. -/
def frontierCoeff : Nat → Nat → Nat → Nat
  | 0, selected, frontier =>
      if selected = 1 ∧ frontier = 0 then 1 else 0
  | depth + 1, selected, frontier =>
      (if frontier = 0 then 0
       else frontierCoeff depth selected (frontier - 1)) +
      ∑ offset ∈ Finset.range (selected - 1),
        ∑ leftFrontier ∈ Finset.range (frontier + 1),
          frontierCoeff depth (offset + 1) leftFrontier *
            frontierCoeff depth (selected - (offset + 1))
              (frontier - leftFrontier)

/-- A `k`-leaf shape at depth `d` has at most `k*d` frontier nodes.  The
release certificate uses this proved bound to omit only provably zero terms. -/
theorem frontierCoeff_eq_zero_of_frontier_gt_mul
    (depth selected frontier : Nat) (selectedPositive : 0 < selected)
    (above : selected * depth < frontier) :
    frontierCoeff depth selected frontier = 0 := by
  induction depth generalizing selected frontier with
  | zero =>
      have frontierPositive : 0 < frontier := by
        simpa using above
      simp [frontierCoeff, Nat.ne_of_gt frontierPositive]
  | succ depth inductionHypothesis =>
      rw [frontierCoeff]
      have frontierPositive : 0 < frontier := by
        have : selected * (depth + 1) < frontier := above
        omega
      have previousBound : selected * depth < frontier - 1 := by
        rw [Nat.mul_succ] at above
        omega
      rw [if_neg (Nat.ne_of_gt frontierPositive)]
      rw [inductionHypothesis selected (frontier - 1)
        selectedPositive previousBound]
      simp only [zero_add]
      apply Finset.sum_eq_zero
      intro offset offsetMembership
      apply Finset.sum_eq_zero
      intro leftFrontier leftMembership
      have offsetBound : offset < selected - 1 :=
        Finset.mem_range.mp offsetMembership
      let leftSelected := offset + 1
      let rightSelected := selected - leftSelected
      have leftPositive : 0 < leftSelected := by
        simp [leftSelected]
      have leftBelow : leftSelected < selected := by
        dsimp [leftSelected]
        omega
      have rightPositive : 0 < rightSelected := by
        dsimp [rightSelected]
        omega
      have split : leftSelected + rightSelected = selected := by
        dsimp [rightSelected]
        omega
      have leftFrontierBound : leftFrontier ≤ frontier := by
        have := Finset.mem_range.mp leftMembership
        omega
      by_cases leftAbove : leftSelected * depth < leftFrontier
      · rw [inductionHypothesis leftSelected leftFrontier
          leftPositive leftAbove]
        simp
      · have rightAbove :
            rightSelected * depth < frontier - leftFrontier := by
          have depthSplit :
              selected * depth =
                leftSelected * depth + rightSelected * depth := by
            rw [← Nat.add_mul, split]
          have frontierAbovePrevious : selected * depth < frontier := by
            rw [Nat.mul_succ] at above
            omega
          omega
        rw [inductionHypothesis rightSelected
          (frontier - leftFrontier) rightPositive rightAbove]
        simp

/-- Concrete subset count represented by a normalized coefficient. -/
def concreteFrontierCount (depth selected frontier : Nat) : Nat :=
  frontierCoeff depth selected frontier * 2 ^ frontier

#print axioms frontierCoeff_eq_zero_of_frontier_gt_mul

end AspisV6CompactFrontierRecurrence
