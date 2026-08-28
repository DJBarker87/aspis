import Mathlib

/-!
# Incidence counting for exact correlated agreement

This is the quantifier-sensitive double count used after one irreducible
branch has been fixed.  The support may still be chosen independently at
every challenge.  A large total incidence count forces more than the message
degree many domain coordinates to occur in more than the branch's algebraic
zero budget supports.
-/

set_option autoImplicit false

namespace AspisK1.V7ExactCorrelatedAgreementIncidence

open scoped BigOperators

variable {Challenge Domain : Type*}
  [DecidableEq Challenge] [DecidableEq Domain] [Fintype Domain]

/-- Challenges whose independently selected support contains one fixed
domain coordinate. -/
def supportFiber (challenges : Finset Challenge)
    (support : Challenge → Finset Domain) (coordinate : Domain) :
    Finset Challenge :=
  challenges.filter fun challenge => coordinate ∈ support challenge

/-- Exact support-pair double count.  No independence or common-support
hypothesis is used. -/
theorem sum_support_card_eq_sum_supportFiber_card
    (challenges : Finset Challenge)
    (support : Challenge → Finset Domain) :
    ∑ challenge ∈ challenges, (support challenge).card =
      ∑ coordinate : Domain,
        (supportFiber challenges support coordinate).card := by
  classical
  simp only [Finset.card_eq_sum_ones, supportFiber, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro challenge challengeMem
  simpa only [Finset.card_eq_sum_ones] using
    (Finset.card_eq_sum_ite
      (s := support challenge) (t := Finset.univ)
      (Finset.subset_univ _))

/-- Coordinates whose support frequency strictly exceeds the one fixed
branch's regular-function zero budget. -/
def heavyCoordinates (challenges : Finset Challenge)
    (support : Challenge → Finset Domain) (branchBudget : Nat) :
    Finset Domain :=
  Finset.univ.filter fun coordinate =>
    branchBudget < (supportFiber challenges support coordinate).card

/-- If every challenge support has more than `agreementThreshold` points and
the literal incidence lower bound exceeds the largest possible contribution
of only `maximumDegree` heavy coordinates, then there are more than
`maximumDegree` heavy coordinates. -/
theorem maximumDegree_lt_card_heavyCoordinates
    (challenges : Finset Challenge)
    (support : Challenge → Finset Domain)
    (agreementThreshold maximumDegree branchBudget : Nat)
    (supportLarge : ∀ challenge ∈ challenges,
      agreementThreshold < (support challenge).card)
    (incidenceLarge :
      maximumDegree * challenges.card +
          Fintype.card Domain * branchBudget <
        challenges.card * (agreementThreshold + 1)) :
    maximumDegree <
      (heavyCoordinates challenges support branchBudget).card := by
  classical
  by_contra notLarge
  have heavyCardLe :
      (heavyCoordinates challenges support branchBudget).card ≤
        maximumDegree := Nat.le_of_not_gt notLarge
  have supportLower : challenges.card * (agreementThreshold + 1) ≤
      ∑ challenge ∈ challenges, (support challenge).card := by
    calc
      challenges.card * (agreementThreshold + 1) =
          ∑ challenge ∈ challenges, (agreementThreshold + 1) := by
            simp [Nat.mul_comm]
      _ ≤ ∑ challenge ∈ challenges, (support challenge).card := by
        apply Finset.sum_le_sum
        intro challenge challengeMem
        exact supportLarge challenge challengeMem
  have fiberBound : ∀ coordinate : Domain,
      (supportFiber challenges support coordinate).card ≤
        branchBudget +
          if coordinate ∈ heavyCoordinates challenges support branchBudget then
            challenges.card
          else 0 := by
    intro coordinate
    by_cases heavy : coordinate ∈
        heavyCoordinates challenges support branchBudget
    · rw [if_pos heavy]
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans
        (Nat.le_add_left _ _)
    · rw [if_neg heavy]
      have notTooLarge : ¬ branchBudget <
          (supportFiber challenges support coordinate).card := by
        simpa [heavyCoordinates] using heavy
      simpa using Nat.le_of_not_gt notTooLarge
  have fiberUpper :
      ∑ coordinate : Domain,
          (supportFiber challenges support coordinate).card ≤
        Fintype.card Domain * branchBudget +
          (heavyCoordinates challenges support branchBudget).card *
            challenges.card := by
    calc
      ∑ coordinate : Domain,
          (supportFiber challenges support coordinate).card ≤
          ∑ coordinate : Domain,
            (branchBudget +
              if coordinate ∈
                  heavyCoordinates challenges support branchBudget then
                challenges.card
              else 0) := by
              apply Finset.sum_le_sum
              intro coordinate _
              exact fiberBound coordinate
      _ = Fintype.card Domain * branchBudget +
            (heavyCoordinates challenges support branchBudget).card *
              challenges.card := by
          simp [Finset.sum_add_distrib, Finset.sum_ite,
            Nat.mul_comm]
  have fiberUpper' :
      ∑ coordinate : Domain,
          (supportFiber challenges support coordinate).card ≤
        maximumDegree * challenges.card +
          Fintype.card Domain * branchBudget := by
    calc
      ∑ coordinate : Domain,
          (supportFiber challenges support coordinate).card ≤
          Fintype.card Domain * branchBudget +
            (heavyCoordinates challenges support branchBudget).card *
              challenges.card := fiberUpper
      _ ≤ Fintype.card Domain * branchBudget +
            maximumDegree * challenges.card := by
          exact Nat.add_le_add_left
            (Nat.mul_le_mul_right challenges.card heavyCardLe) _
      _ = maximumDegree * challenges.card +
            Fintype.card Domain * branchBudget := Nat.add_comm _ _
  rw [sum_support_card_eq_sum_supportFiber_card] at supportLower
  exact (Nat.not_lt_of_ge (supportLower.trans fiberUpper')) incidenceLarge

#print axioms sum_support_card_eq_sum_supportFiber_card
#print axioms maximumDegree_lt_card_heavyCoordinates

end AspisK1.V7ExactCorrelatedAgreementIncidence
