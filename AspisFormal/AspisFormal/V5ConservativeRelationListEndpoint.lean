import AspisFormal.SoundnessWorkNormalizedEndpoint

/-!
# Arithmetic check for a conservative relation-list cost

This file checks one hypothetical update to the V5 soundness ledger.  Suppose
the missing FRI-list-to-relation proof pays the full list cap `240` for all
four relation rounds, with `6 / |K|` for the degree-six alpha check and
`2 / |K|` for the two sequential OOD mixes in each round.  The replacement
term is then

`4 * (6 + 2) * 240 / |K| = 32 * 240 / |K|`.

Lean proves that this term is at most `2^-111`.  Replacing the old
`24 / |K|` arithmetic term by that dyadic upper bound still leaves the complete
maintained conservative BCS calculation, including the width-29 batch term,
`R ≤ 32`, selector factor three, and the existing `2^-256` additive term, at
most `2^-100`.  These inputs are conservative relative to the corrected V5
width-19 batch and `R = 30`; this file does not claim to be the exact deployed
V5 ledger.

This is only an arithmetic contingency check.  It does not prove that
`32 * 240 / |K|` is the correct cost, that the missing reduction exists, or
that Tag-67 has deployed 100-bit soundness.  Any additional event or union
factor requires a fresh calculation.
-/

namespace AspisV5ConservativeRelationListEndpoint

open AspisSoundnessLedger
open AspisWorkNormalizedEndpoint

/-- Hypothetical four-round list-cost term:
`4 rounds * (6 alpha roots + 2 sequential-mix roots) * list cap 240`. -/
noncomputable def conservativeRelationListTerm : ℝ :=
  (32 * 240) / FIELD

/-- The hypothetical `32 * 240 / |K|` term fits below `2^-111`. -/
theorem conservative_relation_list_term_le :
    conservativeRelationListTerm ≤ (1 : ℝ) / 2 ^ 111 := by
  unfold conservativeRelationListTerm FIELD
  norm_num

/-- The maintained tight dyadic union with only the relation term changed:
the former `2^-119` slot is replaced by `2^-111`.

The three remaining `2^-119` terms are the theta, gamma, and inactive-copy
entries. -/
noncomputable def conservativeListUnionBound : ℝ :=
  3291 / 2 ^ 119 + 2837 / 2 ^ 121 + 3502 / 2 ^ 123 +
    2260 / 2 ^ 124 + 2288 / 2 ^ 125 +
    1 / 2 ^ 111 + 1 / 2 ^ 213 +
    1 / 2 ^ 111 +
    1 / 2 ^ 119 + 1 / 2 ^ 119 + 1 / 2 ^ 119 +
    1 / 2 ^ 112 + 1 / 2 ^ 111 + 1 / 2 ^ 120 +
    1 / 2 ^ 123 + 1 / 2 ^ 123 + 1 / 2 ^ 115 +
    1 / 2 ^ 124 + 1 / 2 ^ 128

/-- Exact round-error expression with the old relation term replaced by the
hypothetical full-list term.  No other event is changed or omitted. -/
noncomputable def conservativeListRoundError : ℝ :=
  batchTerm + fold0Term + fold1Term + fold2Term + fold3Term +
    rawTerm + oodTerm +
    conservativeRelationListTerm +
    24 / FIELD + 30 / (FIELD - 1) + 28 / (FIELD - 1) +
    3111 / FIELD + 4828 / FIELD + 10 / FIELD + 1 / FIELD +
    1 / (FIELD - 1) + 270 / FIELD +
    1 / 2 ^ 124 + 1 / 2 ^ 128

/-- The hypothetical exact round-error expression is bounded by the adjusted
dyadic union. -/
theorem conservative_list_round_error_le_union_bound :
    conservativeListRoundError ≤ conservativeListUnionBound := by
  unfold conservativeListRoundError conservativeListUnionBound
  linarith [batchTerm_le, fold0Term_le, fold1Term_le, fold2Term_le,
    fold3Term_le,
    (show rawTerm ≤ 1 / 2 ^ 111 by
      unfold rawTerm
      exact raw_query_miss),
    (show oodTerm ≤ 1 / 2 ^ 213 by
      unfold oodTerm
      exact ood_list_union),
    conservative_relation_list_term_le, sz_theta, sz_three_point,
    sz_inactive, sz_tuple, sz_poles, sz_zerocheck_eq, sz_zero_sum,
    sz_nonzero_eta, sz_ten_rounds]

theorem conservative_list_round_error_nonnegative :
    0 ≤ conservativeListRoundError := by
  unfold conservativeListRoundError conservativeRelationListTerm
  unfold batchTerm fold0Term fold1Term fold2Term fold3Term rawTerm oodTerm FIELD
  positivity

/-- Maintained conservative BCS arithmetic under the adjusted union.  This
carries the width-29 batch bound, `R ≤ 32`, the existing capacity term, and the
worst `T = 1` multiplier; it is not merely the shortcut
`99 * conservativeListUnionBound` and is not the exact corrected V5 ledger. -/
theorem conservative_work_normalized_endpoint
    (epsRound R capErr T : ℝ)
    (hround0 : 0 ≤ epsRound)
    (hround : epsRound ≤ conservativeListUnionBound)
    (_hRnn : 0 ≤ R) (hR : R ≤ R_BCS)
    (hcapnn : 0 ≤ capErr) (hcap : capErr ≤ roCapErr)
    (hT1 : 1 ≤ T) (hTmax : T ≤ 2 ^ 128) :
    selectorInflation * bcsError epsRound T R capErr ≤ 1 / 2 ^ 100 := by
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le one_pos hT1
  have hRT : R / T ≤ 32 := by
    rw [div_le_iff₀ hTpos]
    unfold R_BCS at hR
    nlinarith [hR, hT1]
  have h1T : 1 / T ≤ 1 := by
    rw [div_le_one hTpos]
    exact hT1
  have hcap' : capErr ≤ 1 / 2 ^ 256 := by
    unfold roCapErr at hcap
    exact hcap
  have hA : (1 + R / T) * epsRound ≤
      33 * conservativeListUnionBound := by
    have h1 : (1 + R / T) * epsRound ≤ 33 * epsRound :=
      mul_le_mul_of_nonneg_right (by linarith [hRT]) hround0
    have h2 : 33 * epsRound ≤ 33 * conservativeListUnionBound := by
      linarith [hround]
    linarith [h1, h2]
  have hB : 3 * (T + 1 / T) * capErr ≤
      3 * (2 ^ 128 + 1) * (1 / 2 ^ 256) := by
    have hTsum : T + 1 / T ≤ 2 ^ 128 + 1 := by
      linarith [hTmax, h1T]
    have h1 : 3 * (T + 1 / T) * capErr ≤
        3 * (2 ^ 128 + 1) * capErr :=
      mul_le_mul_of_nonneg_right (by linarith [hTsum]) hcapnn
    have h2 : 3 * (2 ^ 128 + 1) * capErr ≤
        3 * (2 ^ 128 + 1) * (1 / 2 ^ 256) :=
      mul_le_mul_of_nonneg_left hcap' (by positivity)
    linarith [h1, h2]
  have hbcs : bcsError epsRound T R capErr ≤
      33 * conservativeListUnionBound +
        3 * (2 ^ 128 + 1) * (1 / 2 ^ 256) := by
    unfold bcsError
    linarith [hA, hB]
  have hfinal : selectorInflation * bcsError epsRound T R capErr ≤
      selectorInflation *
        (33 * conservativeListUnionBound +
          3 * (2 ^ 128 + 1) * (1 / 2 ^ 256)) :=
    mul_le_mul_of_nonneg_left hbcs (by
      unfold selectorInflation
      norm_num)
  refine hfinal.trans ?_
  unfold selectorInflation conservativeListUnionBound
  norm_num

/-- Applying the adjusted arithmetic endpoint to the hypothetical exact
round-error expression.  The cryptographic reduction establishing that this
is the right expression remains outside this file. -/
theorem conservative_list_cost_endpoint_if_complete
    (R capErr T : ℝ)
    (hRnn : 0 ≤ R) (hR : R ≤ R_BCS)
    (hcapnn : 0 ≤ capErr) (hcap : capErr ≤ roCapErr)
    (hT1 : 1 ≤ T) (hTmax : T ≤ 2 ^ 128) :
    selectorInflation *
        bcsError conservativeListRoundError T R capErr ≤
      1 / 2 ^ 100 :=
  conservative_work_normalized_endpoint conservativeListRoundError R capErr T
    conservative_list_round_error_nonnegative
    conservative_list_round_error_le_union_bound
    hRnn hR hcapnn hcap hT1 hTmax

#print axioms conservative_relation_list_term_le
#print axioms conservative_list_round_error_le_union_bound
#print axioms conservative_work_normalized_endpoint
#print axioms conservative_list_cost_endpoint_if_complete

end AspisV5ConservativeRelationListEndpoint
