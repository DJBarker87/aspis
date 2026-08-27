import AspisFormal.K1.V7Tag73K14K15IdealErrorLedger

/-!
# Exact operational K1.4--K1.5 ledger after restoration-aware classification

The ordinary K1.4 correlated-decoding event and the residual point-compatible
K1.5 event are distinct finite events.  Each carries the published width-29
numerator.  The fixed-family K1.5 events add the exact `396430` numerator.

The earlier ideal ledger remains useful for its component terms; this module
records the honest operational total:

`2 * initialBatchChallengeCap + 396430` over the nonzero QM31 field.

No grinding-work division is used in the raw theorem.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73RestoredCausalErrorLedger

open scoped ENNReal
open AspisK1.V7Tag73K14K15IdealErrorLedger
open AspisV5ComponentCQM31TowerExact
open AspisV6PublishedTheoremInterfaces

noncomputable section

/-- K1.5 after successful restored branches have been routed to extraction:
one constrained-restoration term plus the fixed-family term. -/
def exactK15RestoredCausalRawError : ENNReal :=
  exactK14IdealRawError + exactK15IdealRawError

/-- Full operational K1.4--K1.5 numerator. -/
def exactK14K15OperationalRootNumerator : Nat :=
  2 * initialBatchChallengeCap + 396430

/-- Full operational K1.4--K1.5 raw error. -/
def exactK14K15OperationalRawError : ENNReal :=
  (exactK14K15OperationalRootNumerator : ENNReal) /
    ((P ^ 4 - 1 : Nat) : ENNReal)

theorem exact_k15_restored_causal_raw_error_eq_ratio :
    exactK15RestoredCausalRawError =
      ((initialBatchChallengeCap + 396430 : Nat) : ENNReal) /
        ((P ^ 4 - 1 : Nat) : ENNReal) := by
  unfold exactK15RestoredCausalRawError exactK14IdealRawError
    exactK15IdealRawError
  rw [Nat.cast_add, ENNReal.add_div]
  rfl

theorem exact_k14_k15_operational_root_numerator_eq :
    exactK14K15OperationalRootNumerator = 673738053607908 := by
  norm_num [exactK14K15OperationalRootNumerator, initialBatchChallengeCap]

theorem exact_k14_k15_operational_raw_error_eq_stage_sum :
    exactK14K15OperationalRawError =
      exactK14IdealRawError + exactK15RestoredCausalRawError := by
  unfold exactK14K15OperationalRawError exactK14K15OperationalRootNumerator
    exactK15RestoredCausalRawError exactK14IdealRawError exactK15IdealRawError
  push_cast
  have twoDiv : (2 : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal) =
      1 / ((P ^ 4 - 1 : Nat) : ENNReal) +
        1 / ((P ^ 4 - 1 : Nat) : ENNReal) := by
    rw [show (2 : ENNReal) = 1 + 1 by norm_num, ENNReal.add_div]
  have twoDivExact : (2 : ENNReal) /
      ((2147483647 : ENNReal) ^ 4 - 1) =
      1 / ((2147483647 : ENNReal) ^ 4 - 1) +
        1 / ((2147483647 : ENNReal) ^ 4 - 1) := by
    rw [show (2 : ENNReal) = 1 + 1 by norm_num, ENNReal.add_div]
  rw [ENNReal.add_div, ENNReal.mul_div_right_comm]
  rw [twoDivExact, add_mul]
  simp only [div_eq_mul_inv, one_mul]
  ac_rfl

/-- Even after charging both distinct width-29 events, the exact raw total
remains below `2^-74`. -/
theorem exact_k14_k15_operational_raw_error_le_two_pow_neg74 :
    exactK14K15OperationalRawError ≤
      (1 : ENNReal) / ((2 : ENNReal) ^ 74) := by
  unfold exactK14K15OperationalRawError exactK14K15OperationalRootNumerator
  rw [ENNReal.div_le_iff (by norm_num [P]) (by norm_num)]
  rw [one_div, mul_comm (((2 : ENNReal) ^ 74)⁻¹), ← div_eq_mul_inv,
    ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]
  norm_num [initialBatchChallengeCap, P]

def exactK14K15OperationalWorkNormalizedError : ENNReal :=
  exactK14K15OperationalRawError / ((2 : ENNReal) ^ 35)

/-- Reporting-only work-normalized consequence.  The raw end-to-end theorem
continues to consume `exactK14K15OperationalRawError`. -/
theorem exact_k14_k15_operational_work_normalized_error_le_two_pow_neg109 :
    exactK14K15OperationalWorkNormalizedError ≤
      (1 : ENNReal) / ((2 : ENNReal) ^ 109) := by
  unfold exactK14K15OperationalWorkNormalizedError
    exactK14K15OperationalRawError exactK14K15OperationalRootNumerator
  rw [ENNReal.div_le_iff (by norm_num) (by norm_num)]
  rw [ENNReal.div_le_iff (by norm_num [P]) (by norm_num)]
  rw [one_div, mul_assoc,
    mul_comm (((2 : ENNReal) ^ 109)⁻¹), ← div_eq_mul_inv,
    ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]
  norm_num [initialBatchChallengeCap, P]

end

#print axioms exact_k15_restored_causal_raw_error_eq_ratio
#print axioms exact_k14_k15_operational_root_numerator_eq
#print axioms exact_k14_k15_operational_raw_error_eq_stage_sum
#print axioms exact_k14_k15_operational_raw_error_le_two_pow_neg74
#print axioms
  exact_k14_k15_operational_work_normalized_error_le_two_pow_neg109

end AspisK1.V7Tag73RestoredCausalErrorLedger
