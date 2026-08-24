import AspisFormal.SoundnessWorkNormalizedEndpoint
import AspisFormal.V6PublishedTheoremInterfaces

/-!
# Conditional V6 security-ledger arithmetic

This file gives the proposed one-fold profile a conservative, kernel-checked
numerical budget. It is not an end-to-end security theorem: every probability
must still be connected to the exact V6 event and transcript.

The changed dominant terms are bounded by:

* initial 19-column batch plus work: `2^-110`;
* sole arity-four fold plus work: `2^-111`;
* compact-conditioned q16 query miss plus work: `2^-109`.

The file provisionally retains the V5 upper bounds for the relation and
semantic checks. Their arithmetic is unchanged, but their event inclusion
must be re-established for the new four-reduction transcript. Three removed
FRI fold terms do not appear.

With three selectable streams, at most thirty BCS rounds, capacity error
`2^-256`, and adversary parameter `1 <= T <= 2^128`, the conditional core is
at most `0.4 * 2^-100`. The remaining `0.6 * 2^-100` is explicitly reserved
for implementation, primitive, hiding, and any corrected event terms.
-/

namespace AspisV6SecurityLedger

open AspisSoundnessLedger
open AspisWorkNormalizedEndpoint

/-- Rounded upper bounds for the three changed events and the retained local
arithmetic. The one-OOD `2^-213` entry is conservative because V5's bound
covered four layers. -/
noncomputable def conditionalRoundUpper : Real :=
  1 / 2 ^ 110 + 1 / 2 ^ 111 + 1 / 2 ^ 109 + 1 / 2 ^ 213
    + 1 / 2 ^ 119 + 1 / 2 ^ 119 + 1 / 2 ^ 119 + 1 / 2 ^ 119
    + 1 / 2 ^ 112 + 1 / 2 ^ 111 + 1 / 2 ^ 120
    + 1 / 2 ^ 123 + 1 / 2 ^ 123 + 1 / 2 ^ 115
    + 1 / 2 ^ 124 + 1 / 2 ^ 128

theorem conditional_round_upper_le_two_pow_neg_107 :
    conditionalRoundUpper ≤ (1 : Real) / 2 ^ 107 := by
  norm_num [conditionalRoundUpper]

theorem conditional_round_upper_nonnegative :
    0 ≤ conditionalRoundUpper := by
  unfold conditionalRoundUpper
  positivity

/-- Conditional work-normalized core with the three-stream union factor
applied exactly once. -/
theorem conditional_work_normalized_core_le_two_fifths
    (epsRound R capErr T : Real)
    (hepsNonnegative : 0 ≤ epsRound)
    (heps : epsRound ≤ conditionalRoundUpper)
    (hRNonnegative : 0 ≤ R) (hR : R ≤ 30)
    (hcapNonnegative : 0 ≤ capErr) (hcap : capErr ≤ 1 / 2 ^ 256)
    (hT1 : 1 ≤ T) (hTmax : T ≤ 2 ^ 128) :
    3 * bcsError epsRound T R capErr ≤
      (2 : Real) / (5 * 2 ^ 100) := by
  have hTpos : 0 < T := lt_of_lt_of_le one_pos hT1
  have hRT : R / T ≤ 30 := by
    rw [div_le_iff₀ hTpos]
    nlinarith [hR, hRNonnegative, hT1]
  have hInvT : 1 / T ≤ 1 := by
    rw [div_le_one hTpos]
    exact hT1
  have hA : (1 + R / T) * epsRound ≤
      31 * conditionalRoundUpper := by
    have hfirst : (1 + R / T) * epsRound ≤ 31 * epsRound :=
      mul_le_mul_of_nonneg_right (by linarith [hRT]) hepsNonnegative
    have hsecond : 31 * epsRound ≤ 31 * conditionalRoundUpper := by
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
      31 * conditionalRoundUpper +
        3 * (2 ^ 128 + 1) * (1 / 2 ^ 256) := by
    unfold bcsError
    linarith
  calc
    3 * bcsError epsRound T R capErr ≤
        3 * (31 * conditionalRoundUpper +
          3 * (2 ^ 128 + 1) * (1 / 2 ^ 256)) :=
      mul_le_mul_of_nonneg_left hbcs (by norm_num)
    _ ≤ (2 : Real) / (5 * 2 ^ 100) := by
      norm_num [conditionalRoundUpper]

/-- The core plus a separately justified external-event budget still meets
the 100-bit target. Nothing in this theorem manufactures that external bound. -/
theorem conditional_core_plus_external_meets_100_bits
    (core external : Real)
    (hcore : core ≤ (2 : Real) / (5 * 2 ^ 100))
    (hexternal : external ≤ (3 : Real) / (5 * 2 ^ 100)) :
    core + external ≤ (1 : Real) / 2 ^ 100 := by
  linarith

/-! ## Audit -/

#print axioms conditional_round_upper_le_two_pow_neg_107
#print axioms conditional_work_normalized_core_le_two_fifths
#print axioms conditional_core_plus_external_meets_100_bits

end AspisV6SecurityLedger
