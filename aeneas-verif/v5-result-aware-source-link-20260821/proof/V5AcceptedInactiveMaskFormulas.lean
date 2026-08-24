import V5AcceptedInactiveFoldDenominator

/-!
# Exact released inactive-mask formulas

The released compact inactive table contains seven fixed 16-bit masks.  This
file proves that the Rust low-mask numerators are exactly the maintained
two-fold values of those masks after cancelling the fixed denominator 16.
-/

namespace AspisV5AcceptedInactiveMaskFormulas

open AspisV5RelationLinkedGroupedFold
open AspisV5RelationLinkedGroupedLowSemantics
open AspisV5AcceptedInactiveFoldDenominator

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

abbrev ExactQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

def maskBitWeight (mask : Nat) (low : Fin 16) : ExactQM31 :=
  if Nat.testBit mask low.val then 1 else 0

def foldMaskTwice (alpha0 alpha1 : ExactQM31) (mask : Nat) : ExactQM31 :=
  AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 1 alpha1
    (AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 4 alpha0
      (maskBitWeight mask)) 0

theorem four_ne_zero : (4 : ExactQM31) ≠ 0 := by
  intro h
  have h' := congrArg (fun x : ExactQM31 => x.re.re) h
  simp [QuadraticAlgebra.re_ofNat] at h'
  change ((4 : Nat) : ZMod AspisV5ComponentCQM31TowerExact.P) = 0 at h'
  rw [ZMod.natCast_eq_zero_iff] at h'
  norm_num [AspisV5ComponentCQM31TowerExact.P] at h'

theorem sixteen_ne_zero : (16 : ExactQM31) ≠ 0 := by
  intro h
  have h' := congrArg (fun x : ExactQM31 => x.re.re) h
  simp [QuadraticAlgebra.re_ofNat] at h'
  change ((16 : Nat) : ZMod AspisV5ComponentCQM31TowerExact.P) = 0 at h'
  rw [ZMod.natCast_eq_zero_iff] at h'
  norm_num [AspisV5ComponentCQM31TowerExact.P] at h'

theorem sixteen_foldMaskTwice_eq_releasedLowNumerator
    (alpha0 alpha1 : ExactQM31) (group : Fin 7) :
    (16 : ExactQM31) * foldMaskTwice alpha0 alpha1
        (releasedMasks.val[group.val]!).val =
      releasedLowNumerator alpha0 alpha1 group := by
  unfold foldMaskTwice
  rw [sixteen_mul_two_dualWeightFoldLayers four_ne_zero]
  fin_cases group <;>
    simp (config := { decide := true }) [nestedUnscaledDualWeightFoldValue,
      unscaledDualWeightFoldValue, maskBitWeight, releasedMasks,
      AspisV5ComponentCConcreteFoldLinearity.childIndex,
      releasedLowNumerator, releasedLowTotal] <;>
    ring

#print axioms sixteen_foldMaskTwice_eq_releasedLowNumerator

end AspisV5AcceptedInactiveMaskFormulas
