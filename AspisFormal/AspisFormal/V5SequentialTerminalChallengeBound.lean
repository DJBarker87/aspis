import AspisFormal.V5AcceptedTerminalResidualExtraction

/-!
# Sequential bound for theta, the equality point, and mu

The terminal constraint argument uses three differently shaped random
challenges in order:

1. one field element `theta` batches the 25 constraint lanes;
2. ten field elements select the Boolean-table equality point; and
3. one field element `mu` batches the helper table.

The bad set at the second stage may depend on `theta`, and the bad set at the
third stage may depend on both earlier answers. This file first proves a
generic three-stage fresh-answer bound and then applies the existing exact
root counts `24`, `10`, and `1`. For one trace fixed before `theta`, the full
sequential failure probability is at most `35 / |K|`.

This is an ideal finite-field theorem. A deployed Fiat--Shamir claim still has
to show that the trace and helper table are fixed before `theta` and that the
three source samplers have the required fresh conditional laws.
-/

namespace AspisV5SequentialTerminalChallengeBound

open AspisFormal.ArithmetizationCore
open AspisSumcheckMasking
open AspisV5AcceptedTerminalResidualExtraction
open AspisV5ConstraintLaneBatching
open AspisV5ProductionPublicResidualBinding
open AspisV5TowerPackedResidualExtraction
open Module

/-! ## A heterogeneous three-stage fresh-answer experiment -/

structure ThreeStageFreshPlan (First Second Third : Type*) where
  badFirst : Finset First
  badSecond : First → Finset Second
  badThird : First → Second → Finset Third

noncomputable def ThreeStageFreshPlan.failureProbability
    {First Second Third : Type*}
    [Fintype First] [DecidableEq First]
    [Fintype Second] [DecidableEq Second]
    [Fintype Third] [DecidableEq Third]
    (plan : ThreeStageFreshPlan First Second Third) : Rat :=
  (plan.badFirst.card : Rat) / Fintype.card First +
    ((Finset.univ.filter fun first ↦ first ∉ plan.badFirst).sum
      (fun first ↦
        ((plan.badSecond first).card : Rat) / Fintype.card Second +
          ((Finset.univ.filter fun second ↦
              second ∉ plan.badSecond first).sum
            (fun second ↦
              ((plan.badThird first second).card : Rat) /
                Fintype.card Third)) /
            Fintype.card Second)) /
      Fintype.card First

structure ThreeStageFreshBounds
    {First Second Third : Type*}
    [Fintype First] [Fintype Second] [Fintype Third]
    (plan : ThreeStageFreshPlan First Second Third)
    (firstBound secondBound thirdBound : Rat) : Prop where
  first : (plan.badFirst.card : Rat) / Fintype.card First ≤ firstBound
  second : ∀ first,
    ((plan.badSecond first).card : Rat) / Fintype.card Second ≤ secondBound
  third : ∀ first second,
    ((plan.badThird first second).card : Rat) / Fintype.card Third ≤ thirdBound

theorem finiteSubsetAverage_le
    {Answer : Type*} [Fintype Answer] [Nonempty Answer]
    (subset : Finset Answer) (value : Answer → Rat) (bound : Rat)
    (boundNonnegative : 0 ≤ bound)
    (each : ∀ answer ∈ subset, value answer ≤ bound) :
    subset.sum value / Fintype.card Answer ≤ bound := by
  have cardPositive : (0 : Rat) < Fintype.card Answer := by
    exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ cardPositive]
  calc
    subset.sum value ≤ subset.sum (fun _ ↦ bound) :=
      Finset.sum_le_sum each
    _ = (subset.card : Rat) * bound := by simp
    _ ≤ (Fintype.card Answer : Rat) * bound := by
      apply mul_le_mul_of_nonneg_right _ boundNonnegative
      exact_mod_cast Finset.card_le_univ subset
    _ = bound * Fintype.card Answer := by ring

/-- A sequential union bound for three answer types. The second bad set may
depend on the first answer and the third on both earlier answers. -/
theorem ThreeStageFreshPlan.failureProbability_le
    {First Second Third : Type*}
    [Fintype First] [DecidableEq First] [Nonempty First]
    [Fintype Second] [DecidableEq Second] [Nonempty Second]
    [Fintype Third] [DecidableEq Third] [Nonempty Third]
    (plan : ThreeStageFreshPlan First Second Third)
    (firstBound secondBound thirdBound : Rat)
    (secondNonnegative : 0 ≤ secondBound)
    (thirdNonnegative : 0 ≤ thirdBound)
    (bounds : ThreeStageFreshBounds plan firstBound secondBound thirdBound) :
    plan.failureProbability ≤ firstBound + secondBound + thirdBound := by
  let goodSecond := fun first ↦
    Finset.univ.filter fun second ↦ second ∉ plan.badSecond first
  have thirdAverage : ∀ first,
      (goodSecond first).sum
          (fun second ↦
            ((plan.badThird first second).card : Rat) /
              Fintype.card Third) /
          Fintype.card Second ≤ thirdBound := by
    intro first
    exact finiteSubsetAverage_le (goodSecond first)
      (fun second ↦
        ((plan.badThird first second).card : Rat) / Fintype.card Third)
      thirdBound thirdNonnegative (fun second _ ↦ bounds.third first second)
  have secondAndThird : ∀ first,
      ((plan.badSecond first).card : Rat) / Fintype.card Second +
          (goodSecond first).sum
            (fun second ↦
              ((plan.badThird first second).card : Rat) /
                Fintype.card Third) /
            Fintype.card Second ≤
        secondBound + thirdBound := by
    intro first
    exact add_le_add (bounds.second first) (thirdAverage first)
  have laterAverage :
      ((Finset.univ.filter fun first ↦ first ∉ plan.badFirst).sum
        (fun first ↦
          ((plan.badSecond first).card : Rat) / Fintype.card Second +
            ((Finset.univ.filter fun second ↦
                second ∉ plan.badSecond first).sum
              (fun second ↦
                ((plan.badThird first second).card : Rat) /
                  Fintype.card Third)) /
              Fintype.card Second)) /
        Fintype.card First ≤ secondBound + thirdBound := by
    exact finiteSubsetAverage_le
      (Finset.univ.filter fun first ↦ first ∉ plan.badFirst)
      (fun first ↦
        ((plan.badSecond first).card : Rat) / Fintype.card Second +
          ((Finset.univ.filter fun second ↦
              second ∉ plan.badSecond first).sum
            (fun second ↦
              ((plan.badThird first second).card : Rat) /
                Fintype.card Third)) /
            Fintype.card Second)
      (secondBound + thirdBound)
      (add_nonneg secondNonnegative thirdNonnegative)
      (fun first _ ↦ secondAndThird first)
  unfold ThreeStageFreshPlan.failureProbability
  exact (add_le_add bounds.first laterAverage).trans_eq (by ring)

/-! ## The exact terminal bad sets -/

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Algebra F K]

-- The remaining definitions carry the full 1,024-row, 25-lane residual family.
set_option maxRecDepth 100000

structure FixedTerminalAlgebraPlan (K : Type*) [Field K] [Algebra F K] where
  basis : Basis (Fin 4) F K
  constraintRows : Fin 1024 → ConstraintRowResiduals (F := F) (K := K)
  helper : Fin 1024 → K

noncomputable def FixedTerminalAlgebraPlan.thetaBad
    (plan : FixedTerminalAlgebraPlan K) : Finset K := by
  classical
  exact if existsNonzero : ∃ row,
      rowConstraintPolynomial plan.basis plan.constraintRows row ≠ 0 then
    width25CollisionSet
      ((plan.constraintRows
        (selectedNonzeroPolynomialRow plan.basis plan.constraintRows)).laneVector
          plan.basis)
  else ∅

noncomputable def FixedTerminalAlgebraPlan.pointBad
    (plan : FixedTerminalAlgebraPlan K) (theta : K) :
    Finset (Fin 10 → K) := by
  classical
  let table := thetaConstraintTable plan.basis plan.constraintRows theta
  exact if table ≠ 0 then zerocheckCollisionSet table else ∅

noncomputable def FixedTerminalAlgebraPlan.muBad
    (plan : FixedTerminalAlgebraPlan K) (theta : K)
    (point : Fin 10 → K) : Finset K := by
  classical
  let value := constraintMLE plan.basis plan.constraintRows theta point
  exact if value ≠ 0 then helperCancellationSet value (tableSum plan.helper)
    else ∅

noncomputable def FixedTerminalAlgebraPlan.toThreeStageFreshPlan
    (plan : FixedTerminalAlgebraPlan K) :
    ThreeStageFreshPlan K (Fin 10 → K) K where
  badFirst := plan.thetaBad
  badSecond := plan.pointBad
  badThird := plan.muBad

theorem FixedTerminalAlgebraPlan.thetaCollision_iff
    (plan : FixedTerminalAlgebraPlan K) (theta : K) :
    ThetaLaneCollision plan.basis plan.constraintRows theta ↔
      theta ∈ plan.thetaBad := by
  classical
  by_cases existsNonzero : ∃ row,
      rowConstraintPolynomial plan.basis plan.constraintRows row ≠ 0
  · simpa [FixedTerminalAlgebraPlan.thetaBad, existsNonzero] using
      thetaLaneCollision_iff_mem_width25CollisionSet plan.basis
        plan.constraintRows existsNonzero theta
  · constructor
    · intro collision
      exact (existsNonzero ⟨selectedNonzeroPolynomialRow plan.basis
        plan.constraintRows, collision.1⟩).elim
    · simp [FixedTerminalAlgebraPlan.thetaBad, existsNonzero]

theorem FixedTerminalAlgebraPlan.zerocheckCollision_iff
    (plan : FixedTerminalAlgebraPlan K) (theta : K)
    (point : Fin 10 → K) :
    ZerocheckEvaluationCollision plan.basis plan.constraintRows theta point ↔
      point ∈ plan.pointBad theta := by
  classical
  by_cases tableNonzero :
      thetaConstraintTable plan.basis plan.constraintRows theta ≠ 0
  · simp [FixedTerminalAlgebraPlan.pointBad, tableNonzero,
      ZerocheckEvaluationCollision, zerocheckCollisionSet, constraintMLE]
  · simp [FixedTerminalAlgebraPlan.pointBad, tableNonzero,
      ZerocheckEvaluationCollision]

theorem FixedTerminalAlgebraPlan.helperCancellation_iff
    (plan : FixedTerminalAlgebraPlan K) (theta : K)
    (point : Fin 10 → K) (mu : K) :
    HelperCancellation plan.basis plan.constraintRows theta point mu
        plan.helper ↔
      mu ∈ plan.muBad theta point := by
  classical
  by_cases valueNonzero :
      constraintMLE plan.basis plan.constraintRows theta point ≠ 0
  · simp [FixedTerminalAlgebraPlan.muBad, valueNonzero,
      HelperCancellation, helperCancellationSet]
  · simp [FixedTerminalAlgebraPlan.muBad, valueNonzero,
      HelperCancellation]

theorem FixedTerminalAlgebraPlan.thetaBad_fraction_le
    (plan : FixedTerminalAlgebraPlan K) :
    (plan.thetaBad.card : Rat) / Fintype.card K ≤
      (24 : Rat) / Fintype.card K := by
  classical
  have fieldCardPositive : (0 : Rat) < Fintype.card K := by
    exact_mod_cast Fintype.card_pos
  by_cases existsNonzero : ∃ row,
      rowConstraintPolynomial plan.basis plan.constraintRows row ≠ 0
  · rw [div_le_div_iff_of_pos_right fieldCardPositive]
    rw [FixedTerminalAlgebraPlan.thetaBad, dif_pos existsNonzero]
    exact_mod_cast thetaLaneCollision_card_le_twenty_four plan.basis
      plan.constraintRows existsNonzero
  · rw [FixedTerminalAlgebraPlan.thetaBad, dif_neg existsNonzero]
    simp only [Finset.card_empty, Nat.cast_zero, zero_div]
    positivity

theorem FixedTerminalAlgebraPlan.pointBad_fraction_le
    (plan : FixedTerminalAlgebraPlan K) (theta : K) :
    (plan.pointBad theta).card / Fintype.card (Fin 10 → K) ≤
      (10 : Rat) / Fintype.card K := by
  classical
  rw [show Fintype.card (Fin 10 → K) = Fintype.card K ^ 10 by simp]
  by_cases tableNonzero :
      thetaConstraintTable plan.basis plan.constraintRows theta ≠ 0
  · rw [FixedTerminalAlgebraPlan.pointBad, if_pos tableNonzero]
    exact_mod_cast uniform_zerocheck_collision_fraction_le_ten
      (thetaConstraintTable plan.basis plan.constraintRows theta) tableNonzero
  · rw [FixedTerminalAlgebraPlan.pointBad, if_neg tableNonzero]
    simp only [Finset.card_empty, Nat.cast_zero, zero_div]
    positivity

theorem FixedTerminalAlgebraPlan.muBad_fraction_le
    (plan : FixedTerminalAlgebraPlan K) (theta : K)
    (point : Fin 10 → K) :
    (plan.muBad theta point).card / Fintype.card K ≤
      (1 : Rat) / Fintype.card K := by
  classical
  have fieldCardPositive : (0 : Rat) < Fintype.card K := by
    exact_mod_cast Fintype.card_pos
  by_cases valueNonzero :
      constraintMLE plan.basis plan.constraintRows theta point ≠ 0
  · rw [div_le_div_iff_of_pos_right fieldCardPositive]
    rw [FixedTerminalAlgebraPlan.muBad, if_pos valueNonzero]
    exact_mod_cast helperCancellationSet_card_le_one
      (constraintMLE plan.basis plan.constraintRows theta point)
      (tableSum plan.helper) valueNonzero
  · rw [FixedTerminalAlgebraPlan.muBad, if_neg valueNonzero]
    simp only [Finset.card_empty, Nat.cast_zero, zero_div]
    positivity

/-- Exact recursive probability for the three terminal challenge stages. -/
noncomputable def terminalAlgebraFailureProbability
    (plan : FixedTerminalAlgebraPlan K) : Rat :=
  plan.toThreeStageFreshPlan.failureProbability

/-- For one trace and helper table fixed before `theta`, all three terminal
algebraic events together have ideal probability at most `35 / |K|`. -/
theorem terminalAlgebraFailureProbability_le
    (plan : FixedTerminalAlgebraPlan K) :
    terminalAlgebraFailureProbability plan ≤
      (35 : Rat) / Fintype.card K := by
  have secondNonnegative : (0 : Rat) ≤
      (10 : Rat) / Fintype.card K := by positivity
  have thirdNonnegative : (0 : Rat) ≤
      (1 : Rat) / Fintype.card K := by positivity
  have bounds : ThreeStageFreshBounds plan.toThreeStageFreshPlan
      ((24 : Rat) / Fintype.card K)
      ((10 : Rat) / Fintype.card K)
      ((1 : Rat) / Fintype.card K) := {
    first := plan.thetaBad_fraction_le
    second := plan.pointBad_fraction_le
    third := plan.muBad_fraction_le
  }
  calc
    terminalAlgebraFailureProbability plan ≤
        (24 : Rat) / Fintype.card K +
          (10 : Rat) / Fintype.card K +
          (1 : Rat) / Fintype.card K :=
      ThreeStageFreshPlan.failureProbability_le
        plan.toThreeStageFreshPlan _ _ _ secondNonnegative
          thirdNonnegative bounds
    _ = (35 : Rat) / Fintype.card K := by ring

#print axioms finiteSubsetAverage_le
#print axioms ThreeStageFreshPlan.failureProbability_le
#print axioms FixedTerminalAlgebraPlan.thetaCollision_iff
#print axioms FixedTerminalAlgebraPlan.zerocheckCollision_iff
#print axioms FixedTerminalAlgebraPlan.helperCancellation_iff
#print axioms FixedTerminalAlgebraPlan.thetaBad_fraction_le
#print axioms FixedTerminalAlgebraPlan.pointBad_fraction_le
#print axioms FixedTerminalAlgebraPlan.muBad_fraction_le
#print axioms terminalAlgebraFailureProbability_le

end AspisV5SequentialTerminalChallengeBound
