import AspisFormal.K1.V7Tag73ExactOneFoldEncoderBinding
import AspisFormal.CircleDiscreteAvailability

/-!
# Canonical total one-fold schedule

The production verifier computes inverse circle coordinates only at the
sixteen selected queries.  The algebraic one-fold argument uses a total
schedule on the whole log-18 domain.  This file constructs that total object
from the already-fixed stored circle domain; no parser or source premise is
needed.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73CanonicalOneFoldSchedule

open AspisCircleDiscreteAvailability
open AspisCircleGroupOrder
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisPool.V7CoherentTraceExtraction
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5ComponentCQM31TowerExact
open AspisV5FriBitReverse
open AspisV5FriExactLineDomains
open AspisV7ExactOneFoldDomains

noncomputable section

-- The exponent-coordinate contradiction requires normalization of the
-- 29-bit circle-order congruence.
set_option maxHeartbeats 5000000 in
theorem stored_initial_fibre_x_ne_zero (index : Fin 262144) :
    X (storedInitialFibrePoint20 index) ≠ 0 := by
  intro zero
  have zeroExp :
      X (g ^ AspisV6EncoderDistance.initialCircleExponent
        (storedInitialNaturalIndex20 (childIndex index 0))) = 0 := by
    simpa only [storedInitialFibrePoint20_eq_zpow] using zero
  have sameQuarter :
      X (g ^ AspisV6EncoderDistance.initialCircleExponent
          (storedInitialNaturalIndex20 (childIndex index 0))) =
        X (g ^ (2 ^ 29 : Int)) := by
    rw [zeroExp, quarterTurn_x_zero]
  have modular := (sameXCoord_exp
    (AspisV6EncoderDistance.initialCircleExponent
      (storedInitialNaturalIndex20 (childIndex index 0)))
    (2 ^ 29 : Int)).mp sameQuarter
  simp only [storedInitialNaturalIndex20_child_zero] at modular
  unfold AspisV6EncoderDistance.initialCircleExponent Int.ModEq at modular
  have bound := (reverseFin 18 index).isLt
  norm_num at bound modular
  rcases modular with modular | modular <;> omega

-- The exponent-coordinate contradiction requires normalization of the
-- 29-bit circle-order congruence.
set_option maxHeartbeats 5000000 in
theorem stored_initial_fibre_y_ne_zero (index : Fin 262144) :
    (storedInitialFibrePoint20 index).1.2 ≠ 0 := by
  intro zero
  have onCircle := (storedInitialFibrePoint20 index).2
  simp only [OnCircle] at onCircle
  have xSquare : X (storedInitialFibrePoint20 index) ^ 2 = 1 := by
    unfold X
    rw [zero] at onCircle
    simpa using onCircle
  have sameIdentity :
      X (line18Point (reverseFin 18 index)) = X (g ^ (0 : Int)) := by
    rw [← storedInitialFibrePoint20_sq, AspisV5FriExactLineDomains.X_sq,
      xSquare]
    norm_num [X]
  have modular := (sameXCoord_exp
    (2048 + 8192 * ((reverseFin 18 index : Fin 262144) : Int))
    (0 : Int)).mp sameIdentity
  unfold Int.ModEq at modular
  have bound := (reverseFin 18 index).isLt
  norm_num at bound modular
  rcases modular with modular | modular <;> omega

/-- The total M31 inverse tables attached to the fixed stored circle domain. -/
def canonicalOneFoldSchedule (alpha : QM31Exact) : ExactSchedule :=
  { alpha := alpha
    circleInv2x := fun index =>
      (2 * X (storedInitialFibrePoint20 index))⁻¹
    circleInv2y := fun index =>
      (2 * (storedInitialFibrePoint20 index).1.2)⁻¹ }

-- Elaborating both full-domain inverse identities expands the concrete
-- circle-coordinate definitions.
set_option maxHeartbeats 5000000 in
theorem canonical_one_fold_schedule_exact (alpha : QM31Exact) :
    ExactOneFoldInverseTables (canonicalOneFoldSchedule alpha) := by
  simp only [ExactOneFoldInverseTables, canonicalOneFoldSchedule,
    exactCircleX, exactCircleY]
  constructor
  · intro index
    have denominatorNe :
        (2 : M31Exact) * X (storedInitialFibrePoint20 index) ≠ 0 :=
      mul_ne_zero two_ne_zero_ZModP (stored_initial_fibre_x_ne_zero index)
    calc
      2 * algebraMap M31Exact QM31Exact
            (X (storedInitialFibrePoint20 index)) *
          algebraMap M31Exact QM31Exact
            (((2 : M31Exact) * X (storedInitialFibrePoint20 index))⁻¹) =
          algebraMap M31Exact QM31Exact
            ((2 : M31Exact) * X (storedInitialFibrePoint20 index)) *
          algebraMap M31Exact QM31Exact
            (((2 : M31Exact) * X (storedInitialFibrePoint20 index))⁻¹) := by
              rw [map_mul, map_ofNat]
      _ = algebraMap M31Exact QM31Exact
          (((2 : M31Exact) * X (storedInitialFibrePoint20 index)) *
            ((2 : M31Exact) * X (storedInitialFibrePoint20 index))⁻¹) := by
              simp only [map_mul]
      _ = 1 := by rw [mul_inv_cancel₀ denominatorNe, map_one]
  · intro index
    have denominatorNe :
        (2 : M31Exact) * (storedInitialFibrePoint20 index).1.2 ≠ 0 :=
      mul_ne_zero two_ne_zero_ZModP (stored_initial_fibre_y_ne_zero index)
    calc
      2 * algebraMap M31Exact QM31Exact
            (storedInitialFibrePoint20 index).1.2 *
          algebraMap M31Exact QM31Exact
            (((2 : M31Exact) * (storedInitialFibrePoint20 index).1.2)⁻¹) =
          algebraMap M31Exact QM31Exact
            ((2 : M31Exact) * (storedInitialFibrePoint20 index).1.2) *
          algebraMap M31Exact QM31Exact
            (((2 : M31Exact) * (storedInitialFibrePoint20 index).1.2)⁻¹) := by
              rw [map_mul, map_ofNat]
      _ = algebraMap M31Exact QM31Exact
          (((2 : M31Exact) * (storedInitialFibrePoint20 index).1.2) *
            ((2 : M31Exact) * (storedInitialFibrePoint20 index).1.2)⁻¹) := by
              simp only [map_mul]
      _ = 1 := by rw [mul_inv_cancel₀ denominatorNe, map_one]

/-- Canonical schedule together with the exact interface required by the
one-fold algebra. -/
def canonicalOneFoldScheduleExact (alpha : QM31Exact) :
    {schedule : ExactSchedule //
      schedule.alpha = alpha ∧ ExactOneFoldInverseTables schedule} :=
  ⟨canonicalOneFoldSchedule alpha, rfl, canonical_one_fold_schedule_exact alpha⟩

#print axioms stored_initial_fibre_x_ne_zero
#print axioms stored_initial_fibre_y_ne_zero
#print axioms canonical_one_fold_schedule_exact
#print axioms canonicalOneFoldScheduleExact

end

end AspisK1.V7Tag73CanonicalOneFoldSchedule
