import AspisFormal.V6CompactFrontierCertificate
import AspisFormal.V7CompactFrontierDeltaCertificate

/-!
# Exact cap-203 frontier certificate for V7

V7 uses the same depth-18, sixteen-query binary frontier distribution as V6,
but lowers the admitted cap from 209 to 203.  The V6 certificate proves the
complete cap-209 prefix and rejected tail.  The generated V7 delta certificate
kernel-checks exactly the six additional rejected coefficients 204 through
209 and their missing dependency cone.  This module composes those two proved
pieces; no favourable-count decimal is trusted independently.
-/

set_option autoImplicit false

namespace AspisV7CompactFrontierCertificate

open AspisV6CompactFrontierRecurrence
open AspisV6CompactFrontierCertificate
open AspisV7CompactFrontierDeltaCertificate

def compactTotal : Nat := AspisV6CompactFrontierCertificate.compactTotal

/-- Schedules admitted at cap 209 but rejected at cap 203. -/
def compactDelta : Nat :=
  AspisV7CompactFrontierDeltaCertificate.compactDelta

/-- Exact schedules admitted by the V7 cap. -/
def compactFavourable : Nat :=
  AspisV6CompactFrontierCertificate.compactFavourable - compactDelta

theorem compactTotal_eq_choose :
    compactTotal = Nat.choose (2 ^ 18) 16 := by
  exact AspisV6CompactFrontierCertificate.compactTotal_eq_choose

theorem compactDelta_eq_exact :
    compactDelta =
      6915291501979218758486550434503151696943423928716542558271246420848672768 := by
  simpa [compactDelta, expectedCompactDelta] using compactDelta_eq_expected

theorem compactFavourable_eq_exact :
    compactFavourable =
      2168847668270364480248463894820533103335517458992692508721007794996625408 := by
  norm_num [compactFavourable, compactDelta,
    AspisV6CompactFrontierCertificate.compactFavourable,
    AspisV6CompactFrontierCertificate.compactTotal,
    AspisV6CompactFrontierCertificate.compactTail,
    AspisV6CompactFrontierTailCertificate.expectedCompactTail,
    AspisV7CompactFrontierDeltaCertificate.expectedCompactDelta]

theorem compactFavourable_add_delta_eq_v6 :
    compactFavourable + compactDelta =
      AspisV6CompactFrontierCertificate.compactFavourable := by
  norm_num [compactFavourable, compactDelta,
    AspisV6CompactFrontierCertificate.compactFavourable,
    AspisV6CompactFrontierCertificate.compactTotal,
    AspisV6CompactFrontierCertificate.compactTail,
    AspisV6CompactFrontierTailCertificate.expectedCompactTail,
    AspisV7CompactFrontierDeltaCertificate.expectedCompactDelta]

/-- The favourable integer is the exact recurrence prefix `frontier ≤ 203`. -/
theorem compactFavourable_eq_recurrence :
    compactFavourable =
      ∑ frontier ∈ Finset.range 204,
        concreteFrontierCount 18 16 frontier := by
  let frontierCount := fun frontier =>
    concreteFrontierCount 18 16 frontier
  have intervals : Finset.Ico 204 210 = Finset.Icc 204 209 := by
    ext frontier
    simp
    omega
  have recurrencePartition :
      (∑ frontier ∈ Finset.range 204, frontierCount frontier) +
        (∑ frontier ∈ Finset.Icc 204 209, frontierCount frontier) =
      ∑ frontier ∈ Finset.range 210, frontierCount frontier := by
    rw [← intervals]
    exact Finset.sum_range_add_sum_Ico frontierCount (by norm_num)
  apply Nat.add_right_cancel (n := compactDelta)
  calc
    compactFavourable + compactDelta =
        AspisV6CompactFrontierCertificate.compactFavourable :=
      compactFavourable_add_delta_eq_v6
    _ = ∑ frontier ∈ Finset.range 210,
          concreteFrontierCount 18 16 frontier :=
      AspisV6CompactFrontierCertificate.compactFavourable_eq_recurrence
    _ = (∑ frontier ∈ Finset.range 204, frontierCount frontier) +
          (∑ frontier ∈ Finset.Icc 204 209, frontierCount frontier) :=
      recurrencePartition.symm
    _ = (∑ frontier ∈ Finset.range 204,
          concreteFrontierCount 18 16 frontier) + compactDelta := by
      rw [AspisV7CompactFrontierDeltaCertificate.compactDelta_eq_expected]
      norm_num [compactDelta,
        AspisV7CompactFrontierDeltaCertificate.compactDelta,
        AspisV7CompactFrontierDeltaCertificate.expectedCompactDelta,
        concreteFrontierCount, Finset.sum_Icc_succ_top]

theorem one_candidate_probability_gt_nine_percent :
    9 * compactTotal < 100 * compactFavourable := by
  norm_num [compactTotal, compactFavourable, compactDelta,
    AspisV6CompactFrontierCertificate.compactFavourable,
    AspisV6CompactFrontierCertificate.compactTotal,
    AspisV6CompactFrontierCertificate.compactTail,
    AspisV6CompactFrontierTailCertificate.expectedCompactTail,
    AspisV7CompactFrontierDeltaCertificate.expectedCompactDelta]

/-- Exact conditioned q16 term after final work, without a rounded proxy. -/
theorem conditioned_q16_div_work_le_two_pow_neg_107 :
    (((Nat.choose 9557 16 : Nat) : Real) /
          (compactFavourable : Real)) / 2 ^ 34 ≤
      (1 : Real) / 2 ^ 107 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  norm_num [compactFavourable, compactDelta,
    AspisV6CompactFrontierCertificate.compactFavourable,
    AspisV6CompactFrontierCertificate.compactTotal,
    AspisV6CompactFrontierCertificate.compactTail,
    AspisV6CompactFrontierTailCertificate.expectedCompactTail,
    AspisV7CompactFrontierDeltaCertificate.expectedCompactDelta,
    Nat.descFactorial, Nat.factorial]

#print axioms compactTotal_eq_choose
#print axioms compactDelta_eq_exact
#print axioms compactFavourable_eq_exact
#print axioms compactFavourable_eq_recurrence
#print axioms one_candidate_probability_gt_nine_percent
#print axioms conditioned_q16_div_work_le_two_pow_neg_107

end AspisV7CompactFrontierCertificate
