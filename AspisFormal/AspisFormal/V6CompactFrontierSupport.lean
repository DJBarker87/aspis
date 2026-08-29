import AspisFormal.V6CompactFrontierRecurrence

/-!
# Tight support bounds for the compact-frontier recurrence

The release certificate used to discharge every omitted recurrence cell with
the loose `selected * depth` bound.  That is mathematically correct but causes
the simplifier to expand large forests of impossible convolution terms.  This
module proves the exact recursive support envelope once, generically.  A
generated numeric certificate can then discard an impossible cell with one
small theorem application instead of replaying its complete zero recurrence.
-/

set_option autoImplicit false

namespace AspisV6CompactFrontierSupport

open AspisV6CompactFrontierRecurrence

/-- Recursive upper envelope of every nonzero frontier coefficient. -/
def frontierSupportMax : Nat → Nat → Nat
  | 0, _selected => 0
  | depth + 1, selected =>
      max (frontierSupportMax depth selected + 1)
        ((Finset.range (selected - 1)).sup fun offset =>
          frontierSupportMax depth (offset + 1) +
            frontierSupportMax depth (selected - (offset + 1)))

/-- Largest support contributed by a two-nonempty-child split. -/
def splitSupportMax (depth selected : Nat) : Nat :=
  (Finset.range (selected - 1)).sup fun offset =>
    frontierSupportMax depth (offset + 1) +
      frontierSupportMax depth (selected - (offset + 1))

theorem frontierSupportMax_succ (depth selected : Nat) :
    frontierSupportMax (depth + 1) selected =
      max (frontierSupportMax depth selected + 1)
        (splitSupportMax depth selected) := by
  rfl

/-- A selected set cannot contain more leaves than the full depth-`d` tree. -/
theorem frontierCoeff_eq_zero_of_selected_gt_pow
    (depth selected frontier : Nat)
    (above : 2 ^ depth < selected) :
    frontierCoeff depth selected frontier = 0 := by
  induction depth generalizing selected frontier with
  | zero =>
      by_cases base : selected = 1 ∧ frontier = 0
      · rcases base with ⟨rfl, _⟩
        norm_num at above
      · simp [frontierCoeff, base]
  | succ depth inductionHypothesis =>
      rw [frontierCoeff]
      have previousAbove : 2 ^ depth < selected := by
        rw [pow_succ] at above
        omega
      rw [inductionHypothesis selected (frontier - 1) previousAbove]
      simp only [ite_self, zero_add]
      apply Finset.sum_eq_zero
      intro offset offsetMembership
      apply Finset.sum_eq_zero
      intro leftFrontier _leftMembership
      have offsetBound : offset < selected - 1 :=
        Finset.mem_range.mp offsetMembership
      let leftSelected := offset + 1
      let rightSelected := selected - leftSelected
      have split : leftSelected + rightSelected = selected := by
        dsimp [leftSelected, rightSelected]
        omega
      by_cases leftAbove : 2 ^ depth < leftSelected
      · rw [inductionHypothesis leftSelected leftFrontier leftAbove]
        simp
      · have rightAbove : 2 ^ depth < rightSelected := by
          rw [pow_succ] at above
          omega
        rw [inductionHypothesis rightSelected
          (frontier - leftFrontier) rightAbove]
        simp

/-- Every coefficient above the exact recursive support envelope is zero. -/
theorem frontierCoeff_eq_zero_of_frontier_gt_support
    (depth selected frontier : Nat)
    (above : frontierSupportMax depth selected < frontier) :
    frontierCoeff depth selected frontier = 0 := by
  induction depth generalizing selected frontier with
  | zero =>
      have frontierPositive : 0 < frontier := by
        simpa [frontierSupportMax] using above
      simp [frontierCoeff, Nat.ne_of_gt frontierPositive]
  | succ depth inductionHypothesis =>
      rw [frontierSupportMax_succ] at above
      rw [frontierCoeff]
      have frontierPositive : 0 < frontier := by omega
      rw [if_neg (Nat.ne_of_gt frontierPositive)]
      have previousAbove :
          frontierSupportMax depth selected < frontier - 1 := by
        have oneBound :
            frontierSupportMax depth selected + 1 ≤
              max (frontierSupportMax depth selected + 1)
                (splitSupportMax depth selected) :=
          le_max_left _ _
        omega
      rw [inductionHypothesis selected (frontier - 1) previousAbove]
      simp only [zero_add]
      apply Finset.sum_eq_zero
      intro offset offsetMembership
      apply Finset.sum_eq_zero
      intro leftFrontier leftMembership
      let leftSelected := offset + 1
      let rightSelected := selected - leftSelected
      have splitMember :
          frontierSupportMax depth leftSelected +
              frontierSupportMax depth rightSelected ≤
            splitSupportMax depth selected := by
        simpa [leftSelected, rightSelected, splitSupportMax] using
          (Finset.le_sup (f := fun candidate =>
            frontierSupportMax depth (candidate + 1) +
              frontierSupportMax depth (selected - (candidate + 1)))
            offsetMembership)
      have splitBelow :
          frontierSupportMax depth leftSelected +
              frontierSupportMax depth rightSelected < frontier := by
        have splitBound :
            splitSupportMax depth selected ≤
              max (frontierSupportMax depth selected + 1)
                (splitSupportMax depth selected) :=
          le_max_right _ _
        exact lt_of_le_of_lt (splitMember.trans splitBound) above
      have leftFrontierBound : leftFrontier ≤ frontier := by
        have := Finset.mem_range.mp leftMembership
        omega
      by_cases leftWithin :
          leftFrontier ≤ frontierSupportMax depth leftSelected
      · have rightAbove :
            frontierSupportMax depth rightSelected <
              frontier - leftFrontier := by
          omega
        rw [inductionHypothesis rightSelected
          (frontier - leftFrontier) rightAbove]
        simp
      · have leftAbove :
            frontierSupportMax depth leftSelected < leftFrontier := by
          omega
        rw [inductionHypothesis leftSelected leftFrontier leftAbove]
        simp

#print axioms frontierCoeff_eq_zero_of_selected_gt_pow
#print axioms frontierCoeff_eq_zero_of_frontier_gt_support

end AspisV6CompactFrontierSupport
