import AspisFormal.SoundnessWorkNormalizedEndpoint
import AspisFormal.V6PublishedTheoremInterfaces
import AspisFormal.V7CompactOneFold

/-!
# V7 compact-profile security arithmetic

This module checks the exact arithmetic for the cap-203, one-stream profile.
The favourable frontier numerator is deliberately named `frontierFavourableCandidate`
until the generated recurrence replay certifies its provenance.  No theorem in
this file claims that provenance; the final release ledger must replace that
candidate boundary with the generated certificate.

Relative to V6, batch work rises from 34 to 35 bits, the fold and final work
remain 31 and 34 bits, and the proof cannot choose among public selector
domains: the verifier enforces the first cap-203 schedule in one 64-counter
stream.  The exact conditional query term, rather than a rounded power of two,
is retained so the core stays well inside one half of the 100-bit budget.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisV7CompactSecurityLedger

open AspisSoundnessLedger
open AspisWorkNormalizedEndpoint
open AspisV6PublishedTheoremInterfaces

def frontierTotal : Nat :=
  23758572837246225120935263320500846372979925468707821836403823401582444544

/-- Generator output for `depth=18`, `q=16`, `frontier <= 203`.  This is an
arithmetic input here, not yet a recurrence theorem. -/
def frontierFavourableCandidate : Nat :=
  2168847668270364480248463894820533103335517458992692508721007794996625408

def candidateCount : Nat := 64

theorem frontier_total_eq_choose : frontierTotal = Nat.choose (2 ^ 18) 16 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  norm_num [frontierTotal, Nat.descFactorial, Nat.factorial]

/-- One candidate is favourable with probability strictly above nine percent. -/
theorem one_candidate_probability_gt_nine_percent :
    9 * frontierTotal < 100 * frontierFavourableCandidate := by
  norm_num [frontierTotal, frontierFavourableCandidate]

/-- Under the release's independent-candidate random-oracle interface, the
64-candidate exhaustion probability is below `1/400`. -/
theorem sixty_four_candidate_failure_bound_arithmetic :
    ((91 : Real) / 100) ^ candidateCount < (1 : Real) / 400 := by
  norm_num [candidateCount]

/-- Charging a conservative `400/399` retry multiplier still leaves expected
honest work below 1.5 times V6. -/
theorem retry_adjusted_honest_work_below_three_halves :
    2 * AspisV7CompactOneFold.v7HonestWork * 400 ≤
      3 * AspisV7CompactOneFold.v6HonestWork * 399 := by
  norm_num [AspisV7CompactOneFold.v7HonestWork,
    AspisV7CompactOneFold.v6HonestWork]

noncomputable def exactInitialBatchUpper : Real :=
  (initialBatchChallengeCap : Real) / (FIELD - 1) / 2 ^ 35

noncomputable def exactOneFoldUpper : Real :=
  (foldChallengeCap : Real) / FIELD / 2 ^ 31

noncomputable def exactCompactQueryUpper : Real :=
  ((Nat.choose 9557 16 : Nat) : Real) /
    (frontierFavourableCandidate : Real) / 2 ^ 34

theorem exact_initial_batch_upper_le_two_pow_neg_110 :
    exactInitialBatchUpper ≤ (1 : Real) / 2 ^ 110 := by
  norm_num [exactInitialBatchUpper, initialBatchChallengeCap, FIELD]

theorem exact_one_fold_upper_le_two_pow_neg_111 :
    exactOneFoldUpper ≤ (1 : Real) / 2 ^ 111 := by
  norm_num [exactOneFoldUpper, foldChallengeCap, FIELD]

/-- The cap-203 conditional q16 term is approximately `2^-107.0065`. -/
theorem exact_compact_query_upper_le_two_pow_neg_107 :
    exactCompactQueryUpper ≤ (1 : Real) / 2 ^ 107 := by
  unfold exactCompactQueryUpper
  rw [Nat.choose_eq_descFactorial_div_factorial]
  norm_num [frontierFavourableCandidate,
    Nat.descFactorial, Nat.factorial]

noncomputable def conditionalRoundUpperExact : Real :=
  exactInitialBatchUpper + exactOneFoldUpper + exactCompactQueryUpper
    + 1 / 2 ^ 120 + 1 / 2 ^ 213
    + 1 / 2 ^ 119 + 1 / 2 ^ 119 + 1 / 2 ^ 119 + 1 / 2 ^ 119
    + 1 / 2 ^ 112 + 1 / 2 ^ 111 + 1 / 2 ^ 120
    + 1 / 2 ^ 123 + 1 / 2 ^ 123 + 1 / 2 ^ 115
    + 1 / 2 ^ 124 + 1 / 2 ^ 128

/-- One enforced counter stream means there is no outer selector union factor.
The exact V7 round terms plus the BCS overhead use less than half of the
100-bit work-normalized budget. -/
theorem conditional_work_normalized_core_le_one_half
    (epsRound R capErr T : Real)
    (hepsNonnegative : 0 ≤ epsRound)
    (heps : epsRound ≤ conditionalRoundUpperExact)
    (hRNonnegative : 0 ≤ R) (hR : R ≤ 30)
    (hcapNonnegative : 0 ≤ capErr) (hcap : capErr ≤ 1 / 2 ^ 256)
    (hT1 : 1 ≤ T) (hTmax : T ≤ 2 ^ 128) :
    bcsError epsRound T R capErr ≤
      (1 : Real) / (2 * 2 ^ 100) := by
  have hTpos : 0 < T := lt_of_lt_of_le one_pos hT1
  have hRT : R / T ≤ 30 := by
    rw [div_le_iff₀ hTpos]
    nlinarith [hR, hRNonnegative, hT1]
  have hInvT : 1 / T ≤ 1 := by
    rw [div_le_one hTpos]
    exact hT1
  have hA : (1 + R / T) * epsRound ≤
      31 * conditionalRoundUpperExact := by
    have hfirst : (1 + R / T) * epsRound ≤ 31 * epsRound :=
      mul_le_mul_of_nonneg_right (by linarith [hRT]) hepsNonnegative
    have hsecond : 31 * epsRound ≤ 31 * conditionalRoundUpperExact := by
      linarith [heps]
    linarith
  have hB : 3 * (T + 1 / T) * capErr ≤
      3 * (2 ^ 128 + 1) * (1 / 2 ^ 256) := by
    have hsum : T + 1 / T ≤ 2 ^ 128 + 1 := by
      linarith [hTmax, hInvT]
    have hfirst : 3 * (T + 1 / T) * capErr ≤
        3 * (2 ^ 128 + 1) * capErr :=
      mul_le_mul_of_nonneg_right (by linarith [hsum]) hcapNonnegative
    have hsecond : 3 * (2 ^ 128 + 1) * capErr ≤
        3 * (2 ^ 128 + 1) * (1 / 2 ^ 256) :=
      mul_le_mul_of_nonneg_left hcap (by positivity)
    linarith
  have hbcs : bcsError epsRound T R capErr ≤
      31 * conditionalRoundUpperExact +
        3 * (2 ^ 128 + 1) * (1 / 2 ^ 256) := by
    unfold bcsError
    linarith
  calc
    bcsError epsRound T R capErr ≤
        31 * conditionalRoundUpperExact +
          3 * (2 ^ 128 + 1) * (1 / 2 ^ 256) := hbcs
    _ ≤ (1 : Real) / (2 * 2 ^ 100) := by
      unfold conditionalRoundUpperExact exactInitialBatchUpper
        exactOneFoldUpper exactCompactQueryUpper
      rw [Nat.choose_eq_descFactorial_div_factorial]
      norm_num [initialBatchChallengeCap, foldChallengeCap, FIELD,
        frontierFavourableCandidate, Nat.descFactorial, Nat.factorial]

#print axioms frontier_total_eq_choose
#print axioms one_candidate_probability_gt_nine_percent
#print axioms sixty_four_candidate_failure_bound_arithmetic
#print axioms retry_adjusted_honest_work_below_three_halves
#print axioms exact_initial_batch_upper_le_two_pow_neg_110
#print axioms exact_one_fold_upper_le_two_pow_neg_111
#print axioms exact_compact_query_upper_le_two_pow_neg_107
#print axioms conditional_work_normalized_core_le_one_half

end AspisV7CompactSecurityLedger
