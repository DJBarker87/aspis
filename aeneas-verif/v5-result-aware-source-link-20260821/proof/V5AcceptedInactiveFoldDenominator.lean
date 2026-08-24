import V5RelationLinkedGroupedLowSemantics

/-!
# Denominator cancellation for two inactive-table folds

The maintained dual fold divides each arity-four fibre by four.  These
generic field lemmas cancel the two fixed denominators before the seven
released mask identities are reduced.  Keeping this algebra generic avoids
normalising the concrete quadratic field tower merely to move scalar fours.
-/

namespace AspisV5AcceptedInactiveFoldDenominator

variable {K : Type*} [Field K]

def unscaledDualWeightFoldValue
    (alpha : K) (weights : Fin 4 → K) : K :=
  weights 0 + alpha ^ 3 * weights 1 + alpha ^ 2 * weights 2 +
    alpha * weights 3

theorem four_mul_dualWeightFoldValue
    (hfour : (4 : K) ≠ 0) (alpha : K) (weights : Fin 4 → K) :
    4 * AspisV5FriRelationCandidateBridge.dualWeightFoldValue alpha weights =
      unscaledDualWeightFoldValue alpha weights := by
  unfold AspisV5FriRelationCandidateBridge.dualWeightFoldValue
    unscaledDualWeightFoldValue
  rw [mul_comm]
  exact div_mul_cancel₀ _ hfour

theorem dualWeightFoldValue_mul_four
    (hfour : (4 : K) ≠ 0) (alpha : K) (weights : Fin 4 → K) :
    AspisV5FriRelationCandidateBridge.dualWeightFoldValue alpha weights * 4 =
      unscaledDualWeightFoldValue alpha weights := by
  rw [mul_comm]
  exact four_mul_dualWeightFoldValue hfour alpha weights

theorem mul_dualWeightFoldValue_mul_four
    (hfour : (4 : K) ≠ 0) (coefficient alpha : K)
    (weights : Fin 4 → K) :
    coefficient *
          AspisV5FriRelationCandidateBridge.dualWeightFoldValue alpha weights *
        4 =
      coefficient * unscaledDualWeightFoldValue alpha weights := by
  rw [mul_assoc, dualWeightFoldValue_mul_four hfour]

def nestedUnscaledDualWeightFoldValue
    (alpha0 alpha1 : K) (weights : Fin 16 → K) : K :=
  unscaledDualWeightFoldValue alpha1 fun outer =>
    unscaledDualWeightFoldValue alpha0 fun inner =>
      weights (AspisV5ComponentCConcreteFoldLinearity.childIndex outer inner)

theorem sixteen_mul_two_dualWeightFoldLayers
    (hfour : (4 : K) ≠ 0)
    (alpha0 alpha1 : K) (weights : Fin 16 → K) :
    16 *
        AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 1 alpha1
          (AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 4 alpha0
            weights) 0 =
      nestedUnscaledDualWeightFoldValue alpha0 alpha1 weights := by
  change 16 * AspisV5FriRelationCandidateBridge.dualWeightFoldValue alpha1
      (fun outer =>
        AspisV5FriRelationCandidateBridge.dualWeightFoldValue alpha0
          (fun inner => weights
            (AspisV5ComponentCConcreteFoldLinearity.childIndex outer inner))) =
    nestedUnscaledDualWeightFoldValue alpha0 alpha1 weights
  calc
    16 * AspisV5FriRelationCandidateBridge.dualWeightFoldValue alpha1
        (fun outer =>
          AspisV5FriRelationCandidateBridge.dualWeightFoldValue alpha0
            (fun inner => weights
              (AspisV5ComponentCConcreteFoldLinearity.childIndex outer inner))) =
      4 * (4 * AspisV5FriRelationCandidateBridge.dualWeightFoldValue alpha1
        (fun outer =>
          AspisV5FriRelationCandidateBridge.dualWeightFoldValue alpha0
            (fun inner => weights
              (AspisV5ComponentCConcreteFoldLinearity.childIndex outer inner)))) := by
        ring
    _ = 4 * unscaledDualWeightFoldValue alpha1
        (fun outer =>
          AspisV5FriRelationCandidateBridge.dualWeightFoldValue alpha0
            (fun inner => weights
              (AspisV5ComponentCConcreteFoldLinearity.childIndex outer inner))) := by
      rw [four_mul_dualWeightFoldValue hfour]
    _ = nestedUnscaledDualWeightFoldValue alpha0 alpha1 weights := by
      unfold nestedUnscaledDualWeightFoldValue unscaledDualWeightFoldValue
      ring_nf
      simp only [dualWeightFoldValue_mul_four hfour,
        mul_dualWeightFoldValue_mul_four hfour]
      unfold unscaledDualWeightFoldValue
      ring

#print axioms sixteen_mul_two_dualWeightFoldLayers

end AspisV5AcceptedInactiveFoldDenominator
