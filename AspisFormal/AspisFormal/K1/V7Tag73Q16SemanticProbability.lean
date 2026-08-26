import AspisFormal.K1.V7Tag73Q16SemanticFrontierBridge

/-!
# Exact q16 compact-query probability bound

This module cancels the ordering factor from the exact admitted-schedule
count and the without-replacement bad-schedule bound.  It remains at the
semantic frontier count; the generated V7 certificate supplies the separate
equality with the frozen cap-203 decimal.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace AspisK1.V7Tag73Q16SemanticProbability

open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisK1.V7Tag73Q16CompactScheduleCount
open AspisK1.V7Tag73Q16SemanticFrontierBridge

noncomputable section

private theorem common_order_factor_cancels
    (semantic ordering numerator : Real)
    (semanticNonzero : semantic ≠ 0)
    (orderingNonzero : ordering ≠ 0) :
    (ordering * numerator) / (semantic * ordering) =
      numerator / semantic := by
  field_simp [semanticNonzero, orderingNonzero]

theorem semanticCompactFavourable_pos
    (reference : AdmittedResult SemanticCap203Admitted) :
    0 < semanticCompactFavourable := by
  have admittedPositive :
      0 < Fintype.card (AdmittedResult SemanticCap203Admitted) := by
    rw [Fintype.card_pos_iff]
    exact ⟨reference⟩
  rw [semantic_cap203_admitted_card] at admittedPositive
  exact pos_of_mul_pos_left admittedPositive (Nat.zero_le _)

/-- The exact uniform-over-compact bad ratio is bounded by the q16
hypergeometric numerator.  The `16!` ordering factor cancels algebraically;
it is not charged as a union bound. -/
theorem semantic_compact_bad_ratio_le_choose_9557
    (bad : Finset (Fin 262144))
    (badCard : bad.card ≤ 9557)
    (reference : AdmittedResult SemanticCap203Admitted) :
    (Fintype.card
          (BadAdmittedResult SemanticCap203Admitted (AllInBad bad)) : Real) /
        Fintype.card (AdmittedResult SemanticCap203Admitted) ≤
      (Nat.choose 9557 16 : Real) /
        semanticCompactFavourable := by
  have numeratorNat :
      Fintype.card
          (BadAdmittedResult SemanticCap203Admitted (AllInBad bad)) ≤
        (9557 : Nat).descFactorial 16 :=
    (compact_bad_admitted_card_le_descFactorial bad).trans
      (Nat.descFactorial_le 16 badCard)
  have numeratorReal :
      (Fintype.card
          (BadAdmittedResult SemanticCap203Admitted (AllInBad bad)) : Real) ≤
        ((9557 : Nat).descFactorial 16 : Real) := by
    exact_mod_cast numeratorNat
  have semanticPositive : 0 < semanticCompactFavourable :=
    semanticCompactFavourable_pos reference
  have semanticCastPositive : (0 : Real) < semanticCompactFavourable := by
    exact_mod_cast semanticPositive
  have factorialCastPositive :
      (0 : Real) < Nat.factorial 16 := by positivity
  rw [semantic_cap203_admitted_card, Nat.cast_mul]
  calc
    (Fintype.card
          (BadAdmittedResult SemanticCap203Admitted (AllInBad bad)) : Real) /
        ((semanticCompactFavourable : Real) * Nat.factorial 16) ≤
        ((9557 : Nat).descFactorial 16 : Real) /
          ((semanticCompactFavourable : Real) * Nat.factorial 16) :=
      div_le_div_of_nonneg_right numeratorReal
        (mul_pos semanticCastPositive factorialCastPositive).le
    _ = (Nat.choose 9557 16 : Real) /
        semanticCompactFavourable := by
      rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
      exact common_order_factor_cancels
        semanticCompactFavourable (Nat.factorial 16) (Nat.choose 9557 16)
        semanticCastPositive.ne' factorialCastPositive.ne'

/-- End-to-end finite-sampler statement: the literal first-cap-203 scan has
the semantic hypergeometric bound. -/
theorem q16_first_cap203_bad_probability_le_semantic_choose
    (bad : Finset (Fin 262144))
    (badCard : bad.card ≤ 9557)
    (reference :
      AdmittedResult (Cap203Admitted semanticFrontierNodes))
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput
        (Cap203Admitted semanticFrontierNodes) 64 reference.1)) :
    firstAdmittedBadProbability q16CandidateOutput
        (Cap203Admitted semanticFrontierNodes) (AllInBad bad) 64 ≤
      (Nat.choose 9557 16 : Real) /
        semanticCompactFavourable := by
  rw [q16_first_cap203_bad_probability_eq_uniform_compact
    semanticFrontierNodes bad reference traceExists]
  exact semantic_compact_bad_ratio_le_choose_9557 bad badCard reference

/-- The final 34-bit work normalization remains a separate division after
the exact first-success sampler bound. -/
theorem q16_first_cap203_bad_probability_div_work_le_semantic_choose
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
      ((Nat.choose 9557 16 : Real) /
          semanticCompactFavourable) / 2 ^ 34 := by
  exact div_le_div_of_nonneg_right
    (q16_first_cap203_bad_probability_le_semantic_choose
      bad badCard reference traceExists) (by positivity)

/-! ## Audit -/

#print axioms semanticCompactFavourable_pos
#print axioms semantic_compact_bad_ratio_le_choose_9557
#print axioms q16_first_cap203_bad_probability_le_semantic_choose
#print axioms q16_first_cap203_bad_probability_div_work_le_semantic_choose

end

end AspisK1.V7Tag73Q16SemanticProbability
