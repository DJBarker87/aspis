import Mathlib.Combinatorics.Pigeonhole

/-!
# Weighted fixed-branch pigeonhole for correlated agreement

The improved BCH+25 count cannot use a uniform worst-case branch budget.
Different irreducible pairs `(R,H)` carry different degree products.  This
module proves the exact weighted finite combinatorial step: after deleting an
explicit exceptional set, if the remaining challenge count exceeds the sum
of the branch budgets, one *fixed* branch exceeds its own budget.
-/

set_option autoImplicit false

namespace AspisK1.V7ExactCorrelatedAgreementWeightedPigeonhole

open scoped BigOperators

/-- Weighted pigeonhole with an independently chosen branch for every
challenge.  The conclusion concerns one fixed element of `branches`; it does
not merely choose a fresh witness inside each fiber. -/
theorem exists_fixed_branch_exceeding_budget
    {Challenge Branch : Type*} [DecidableEq Challenge] [DecidableEq Branch]
    (challenges exceptions : Finset Challenge) (branches : Finset Branch)
    (selectedBranch : Challenge → Branch) (budget : Branch → Nat)
    (selectedMaps : ∀ challenge ∈ challenges \ exceptions,
      selectedBranch challenge ∈ branches)
    (many : ∑ branch ∈ branches, budget branch <
      (challenges \ exceptions).card) :
    ∃ branch ∈ branches,
      budget branch <
        ((challenges \ exceptions).filter fun challenge =>
          selectedBranch challenge = branch).card := by
  classical
  by_contra noBranch
  push Not at noBranch
  have fiberBounds : ∀ branch ∈ branches,
      ((challenges \ exceptions).filter fun challenge =>
        selectedBranch challenge = branch).card ≤ budget branch := by
    intro branch branchMem
    exact noBranch branch branchMem
  have fiberSumBound :
      ∑ branch ∈ branches,
          ((challenges \ exceptions).filter fun challenge =>
            selectedBranch challenge = branch).card ≤
        ∑ branch ∈ branches, budget branch := by
    exact Finset.sum_le_sum fun branch branchMem => fiberBounds branch branchMem
  have partitionEquality : (challenges \ exceptions).card =
      ∑ branch ∈ branches,
        ((challenges \ exceptions).filter fun challenge =>
          selectedBranch challenge = branch).card :=
    Finset.card_eq_sum_card_fiberwise selectedMaps
  rw [partitionEquality] at many
  exact (Nat.not_lt_of_ge fiberSumBound) many

/-- A convenient form in which the published bound includes the size of the
deleted exceptional set. -/
theorem exists_fixed_branch_exceeding_budget_of_exception_add_sum_lt
    {Challenge Branch : Type*} [DecidableEq Challenge] [DecidableEq Branch]
    (challenges exceptions : Finset Challenge) (branches : Finset Branch)
    (selectedBranch : Challenge → Branch) (budget : Branch → Nat)
    (selectedMaps : ∀ challenge ∈ challenges \ exceptions,
      selectedBranch challenge ∈ branches)
    (many : exceptions.card + ∑ branch ∈ branches, budget branch <
      challenges.card) :
    ∃ branch ∈ branches,
      budget branch <
        ((challenges \ exceptions).filter fun challenge =>
          selectedBranch challenge = branch).card := by
  apply exists_fixed_branch_exceeding_budget challenges exceptions branches
    selectedBranch budget selectedMaps
  have remainingCard : challenges.card ≤
      exceptions.card + (challenges \ exceptions).card := by
    calc
      challenges.card = (challenges \ exceptions).card +
          (challenges ∩ exceptions).card := by
        rw [Finset.card_sdiff_add_card_inter]
      _ ≤ (challenges \ exceptions).card + exceptions.card := by
        gcongr
        exact Finset.inter_subset_right
      _ = exceptions.card + (challenges \ exceptions).card := Nat.add_comm _ _
  omega

#print axioms exists_fixed_branch_exceeding_budget
#print axioms exists_fixed_branch_exceeding_budget_of_exception_add_sum_lt

end AspisK1.V7ExactCorrelatedAgreementWeightedPigeonhole
