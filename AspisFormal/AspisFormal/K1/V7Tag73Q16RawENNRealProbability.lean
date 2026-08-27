import AspisFormal.K1.V7Tag73Q16SemanticProbability
import AspisFormal.K1.V7Tag73SuccessfulSamplerConditioningBridge

/-!
# Raw ENNReal probability of the Tag-73 first-cap-203 q16 scan

The final K1.3 ledger is an `ENNReal` measure statement, whereas the original
finite q16 report used a `Real` ratio.  This file identifies the literal bad
subset of the successful first-admitted sample space and transports the exact
semantic bound into the measure type consumed by K1.6.  No proof-of-work
normalization occurs.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73Q16RawENNRealProbability

open MeasureTheory
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisK1.V7Tag73Q16CompactScheduleCount
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73Q16SemanticProbability

noncomputable section

def q16FirstAdmittedBadEvent
    (bad : Finset (Fin 262144)) :
    Set (FirstAdmittedSample q16CandidateOutput SemanticCap203Admitted 64) :=
  {sample | AllInBad bad sample.1.1}

def q16FirstAdmittedBadEventSubtypeEquiv
    (bad : Finset (Fin 262144)) :
    {sample : FirstAdmittedSample q16CandidateOutput SemanticCap203Admitted 64 //
      sample ∈ q16FirstAdmittedBadEvent bad} ≃
      FirstAdmittedBadSample q16CandidateOutput SemanticCap203Admitted
        (AllInBad bad) 64 :=
  Equiv.refl _

theorem q16_first_admitted_bad_measure_eq_card_ratio
    [Nonempty
      (FirstAdmittedSample q16CandidateOutput SemanticCap203Admitted 64)]
    (bad : Finset (Fin 262144)) :
    (PMF.uniformOfFintype
      (FirstAdmittedSample q16CandidateOutput SemanticCap203Admitted 64)
      ).toOuterMeasure (q16FirstAdmittedBadEvent bad) =
      (Fintype.card
        (FirstAdmittedBadSample q16CandidateOutput SemanticCap203Admitted
          (AllInBad bad) 64) : ENNReal) /
        (Fintype.card
          (FirstAdmittedSample q16CandidateOutput SemanticCap203Admitted 64) :
            ENNReal) := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  rw [Fintype.card_congr (q16FirstAdmittedBadEventSubtypeEquiv bad)]

theorem ennreal_nat_ratio_le_of_real_ratio_le
    (a b c d : Nat) (bPos : 0 < b) (dPos : 0 < d)
    (bound : (a : Real) / b ≤ (c : Real) / d) :
    (a : ENNReal) / b ≤ (c : ENNReal) / d := by
  have bNe : (b : ENNReal) ≠ 0 := by exact_mod_cast bPos.ne'
  have dNe : (d : ENNReal) ≠ 0 := by exact_mod_cast dPos.ne'
  apply (ENNReal.toReal_le_toReal
    (ENNReal.div_ne_top (by simp) bNe)
    (ENNReal.div_ne_top (by simp) dNe)).mp
  simpa [ENNReal.toReal_div, ENNReal.toReal_natCast] using bound

/-- Exact successful-scan raw probability in the same `ENNReal` ledger used
by the end-to-end theorem. -/
theorem q16_first_cap203_bad_measure_le_semantic_choose
    [Nonempty
      (FirstAdmittedSample q16CandidateOutput SemanticCap203Admitted 64)]
    (bad : Finset (Fin 262144))
    (badCard : bad.card ≤ 9557)
    (reference : AdmittedResult SemanticCap203Admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        reference.1)) :
    (PMF.uniformOfFintype
      (FirstAdmittedSample q16CandidateOutput SemanticCap203Admitted 64)
      ).toOuterMeasure (q16FirstAdmittedBadEvent bad) ≤
      (Nat.choose 9557 16 : ENNReal) /
        (semanticCompactFavourable : ENNReal) := by
  rw [q16_first_admitted_bad_measure_eq_card_ratio]
  apply ennreal_nat_ratio_le_of_real_ratio_le _ _ _ _
    Fintype.card_pos
    (semanticCompactFavourable_pos reference)
  exact q16_first_cap203_bad_probability_le_semantic_choose bad badCard
    reference traceExists

end

#print axioms q16_first_admitted_bad_measure_eq_card_ratio
#print axioms ennreal_nat_ratio_le_of_real_ratio_le
#print axioms q16_first_cap203_bad_measure_le_semantic_choose

end AspisK1.V7Tag73Q16RawENNRealProbability
