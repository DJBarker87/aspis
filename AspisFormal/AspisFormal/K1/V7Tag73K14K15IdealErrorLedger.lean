import AspisFormal.K1.V7Tag73RestoredGammaProbability
import AspisFormal.Pool.V7K15FailureRootInventory

/-!
# Combined ideal K1.4--K1.5 error ledger for Tag-73

This leaf records the honest numerical consequence of the two completed
algebraic probability arguments:

* the restoration-wide point-compatible K1.4 complement costs at most the
  published width-29 cap `336869026605739 / (P^4 - 1)`; and
* all remaining fixed-family K1.5 branches cost at most
  `396430 / (P^4 - 1)`.

The raw sum is below `2^-74`, not `2^-100`.  Dividing by the public 35-bit
batch-work budget gives a work-normalized reporting figure below `2^-109`;
that second theorem is deliberately named as work-normalized and is not used
as a raw false-acceptance probability.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73K14K15IdealErrorLedger

open scoped ENNReal
open AspisK1.V7Tag73RestoredGammaProbability
open AspisPool.V7K15FailureRootInventory
open AspisV5ComponentCQM31TowerExact
open AspisV6PublishedTheoremInterfaces

noncomputable section

def exactK14K15IdealRootNumerator : Nat :=
  initialBatchChallengeCap + 396430

def exactK14K15IdealRawError : ENNReal :=
  (exactK14K15IdealRootNumerator : ENNReal) /
    ((P ^ 4 - 1 : Nat) : ENNReal)

theorem exact_k14_k15_ideal_root_numerator_eq :
    exactK14K15IdealRootNumerator = 336869027002169 := by
  norm_num [exactK14K15IdealRootNumerator, initialBatchChallengeCap]

/-- The exact raw algebraic total.  This is the number that must enter the
un-normalized end-to-end security theorem. -/
theorem exact_k14_k15_ideal_raw_error_le_two_pow_neg74 :
    exactK14K15IdealRawError ≤
      (1 : ENNReal) / ((2 : ENNReal) ^ 74) := by
  unfold exactK14K15IdealRawError exactK14K15IdealRootNumerator
  rw [ENNReal.div_le_iff (by norm_num [P]) (by norm_num)]
  rw [mul_comm, one_div, ← div_eq_mul_inv,
    ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]
  norm_num [initialBatchChallengeCap, P]

def exactK14K15WorkNormalizedError : ENNReal :=
  exactK14K15IdealRawError / ((2 : ENNReal) ^ 35)

/-- Reporting-only work-normalized magnitude.  This theorem does not replace
the raw bound above and is not consumed by the classical-ROM AoK closure. -/
theorem exact_k14_k15_work_normalized_error_le_two_pow_neg109 :
    exactK14K15WorkNormalizedError ≤
      (1 : ENNReal) / ((2 : ENNReal) ^ 109) := by
  unfold exactK14K15WorkNormalizedError exactK14K15IdealRawError
    exactK14K15IdealRootNumerator
  rw [ENNReal.div_le_iff (by norm_num) (by norm_num)]
  rw [ENNReal.div_le_iff (by norm_num [P]) (by norm_num)]
  rw [one_div, mul_assoc,
    mul_comm (((2 : ENNReal) ^ 109)⁻¹), ← div_eq_mul_inv,
    ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]
  norm_num [initialBatchChallengeCap, P]

end


#print axioms exact_k14_k15_ideal_root_numerator_eq
#print axioms exact_k14_k15_ideal_raw_error_le_two_pow_neg74
#print axioms exact_k14_k15_work_normalized_error_le_two_pow_neg109

end AspisK1.V7Tag73K14K15IdealErrorLedger
