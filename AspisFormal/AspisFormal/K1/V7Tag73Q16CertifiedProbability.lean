import AspisFormal.K1.V7Tag73Q16SemanticProbability
import AspisFormal.V7CompactFrontierCertificate

/-!
# Generated-certificate closure of the q16 probability bound

The semantic bridge proves the first-cap-203 sampler bound against the exact
shape recurrence.  This final small layer identifies that recurrence with the
already generated V7 cap-203 certificate and applies its frozen numeric
`2^-107` check after the separate 34-bit work division.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73Q16CertifiedProbability

open AspisV6CompactFrontierPrefactorization
open AspisV6CompactFrontierSemantics
open AspisV7CompactFrontierCertificate
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisK1.V7Tag73Q16CompactScheduleCount
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73Q16SemanticProbability

noncomputable section

theorem semanticCompactFavourable_eq_compactFavourable :
    semanticCompactFavourable = compactFavourable := by
  rw [compactFavourable_eq_recurrence]
  unfold semanticCompactFavourable
  apply Finset.sum_congr rfl
  intro frontierCount _membership
  change semanticCount 18 16 frontierCount =
    concreteFrontierCount 18 16 frontierCount
  rw [← rawFrontierCount_eq_semanticCount,
    rawFrontierCount_eq_concreteFrontierCount]

/-- Fully numeric q16 query-plus-final-work theorem for the exact first-cap
sampler and a bad consistency set of size at most 9557. -/
theorem q16_first_cap203_bad_probability_div_work_le_two_pow_neg_107
    (bad : Finset (Fin 262144))
    (badCard : bad.card ≤ 9557)
    (reference :
      AdmittedResult (Cap203Admitted semanticFrontierNodes))
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput
        (Cap203Admitted semanticFrontierNodes) 64 reference.1)) :
    firstAdmittedBadProbability q16CandidateOutput
          (Cap203Admitted semanticFrontierNodes) (AllInBad bad) 64 /
        2 ^ 34 ≤
      (1 : Real) / 2 ^ 107 := by
  calc
    firstAdmittedBadProbability q16CandidateOutput
          (Cap203Admitted semanticFrontierNodes) (AllInBad bad) 64 /
        2 ^ 34 ≤
        ((Nat.choose 9557 16 : Real) /
          semanticCompactFavourable) / 2 ^ 34 :=
      q16_first_cap203_bad_probability_div_work_le_semantic_choose
        bad badCard reference traceExists
    _ = ((Nat.choose 9557 16 : Real) / compactFavourable) /
        2 ^ 34 := by
      rw [semanticCompactFavourable_eq_compactFavourable]
    _ ≤ (1 : Real) / 2 ^ 107 :=
      conditioned_q16_div_work_le_two_pow_neg_107

/-! ## Audit -/

#print axioms semanticCompactFavourable_eq_compactFavourable
#print axioms q16_first_cap203_bad_probability_div_work_le_two_pow_neg_107

end

end AspisK1.V7Tag73Q16CertifiedProbability
