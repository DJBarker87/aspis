import AspisFormal.V6CompactFrontierTailCertificate
import AspisFormal.V6CompactFrontierPrefactorization
import AspisFormal.V6CompactFrontierSemantics

/-!
# Exact finite certificate arithmetic for the V6 compact frontier

The generated certificate imported above replays the normalized binary-tree
recurrence only on the dependency cone needed for frontier values above the
release cap. This is the prefactorized form of the original subset dynamic
programme: a normalized shape coefficient at frontier `f` represents
`coefficient * 2^f` concrete leaf subsets.

This module connects that kernel-checked recurrence tail to the exact
sixteen-subset denominator. The favourable count is defined as total minus
the certified rejected tail; no untrusted decimal or pinned favourable
numerator enters the security inequality.
-/

set_option autoImplicit false

namespace AspisV6CompactFrontierCertificate

open AspisV6CompactFrontierRecurrence
open AspisV6CompactFrontierTailCertificate
open AspisV6CompactFrontierSemantics

/-- Exact number of sixteen-element subsets of a `2^18`-element domain. -/
def compactTotal : Nat :=
  23758572837246225120935263320500846372979925468707821836403823401582444544

theorem compactTotal_eq_choose :
    compactTotal = Nat.choose (2 ^ 18) 16 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  norm_num [compactTotal, Nat.descFactorial, Nat.factorial]

/-- The complete recurrence distribution is exactly the set of all
sixteen-leaf subsets. This is the semantic bridge that prevents the pinned
binomial denominator from being unrelated to the certified frontier tail. -/
theorem compactTotal_eq_recurrence :
    compactTotal =
      ∑ frontier ∈ Finset.range (16 * 18 + 1),
        concreteFrontierCount 18 16 frontier := by
  calc
    compactTotal = Nat.choose (2 ^ 18) 16 := compactTotal_eq_choose
    _ = ∑ frontier ∈ Finset.range (16 * 18 + 1),
          concreteFrontierCount 18 16 frontier :=
      (concreteFrontierCount_sum_eq_choose 18 16 (by norm_num)).symm

/-- Exact count rejected because its binary Merkle frontier exceeds 209. -/
def compactTail : Nat := expectedCompactTail

/-- The rejected count is the concrete normalized-recurrence sum for all
frontier sizes 210 through the proved loose maximum 288. -/
theorem compactTail_eq_recurrence :
    compactTail =
      ∑ frontier ∈ Finset.Icc 210 288,
        concreteFrontierCount 18 16 frontier := by
  simpa [compactTail, AspisV6CompactFrontierTailCertificate.compactTail] using
    compactTail_eq_expected.symm

/-- Schedules admitted by the release cap. Defining this by subtraction
makes the recurrence tail, rather than a separately trusted integer, its
provenance. -/
def compactFavourable : Nat := compactTotal - compactTail

theorem compactFavourable_eq_exact :
    compactFavourable =
      9084139170249583238735014329323684800278941387709235066992254215845298176 := by
  norm_num [compactFavourable, compactTotal, compactTail,
    expectedCompactTail]

theorem compact_partition_exact :
    compactFavourable + compactTail = compactTotal := by
  norm_num [compactFavourable, compactTotal, compactTail,
    expectedCompactTail]

/-- Exact accepted count as the concrete recurrence prefix `frontier ≤ 209`.
Together with `compactTail_eq_recurrence`, this proves that accepted and
rejected schedules partition the same finite binary-subset space. -/
theorem compactFavourable_eq_recurrence :
    compactFavourable =
      ∑ frontier ∈ Finset.range 210,
        concreteFrontierCount 18 16 frontier := by
  let frontierCount := fun frontier =>
    concreteFrontierCount 18 16 frontier
  have intervals : Finset.Ico 210 289 = Finset.Icc 210 288 := by
    ext frontier
    simp
    omega
  have recurrencePartition :
      (∑ frontier ∈ Finset.range 210, frontierCount frontier) +
        (∑ frontier ∈ Finset.Icc 210 288, frontierCount frontier) =
      ∑ frontier ∈ Finset.range 289, frontierCount frontier := by
    rw [← intervals]
    exact Finset.sum_range_add_sum_Ico frontierCount (by norm_num)
  apply Nat.add_right_cancel (n := compactTail)
  calc
    compactFavourable + compactTail = compactTotal :=
      compact_partition_exact
    _ = ∑ frontier ∈ Finset.range 289,
          concreteFrontierCount 18 16 frontier := by
      simpa using compactTotal_eq_recurrence
    _ = (∑ frontier ∈ Finset.range 210, frontierCount frontier) +
          (∑ frontier ∈ Finset.Icc 210 288,
            frontierCount frontier) := recurrencePartition.symm
    _ = (∑ frontier ∈ Finset.range 210,
            concreteFrontierCount 18 16 frontier) + compactTail := by
      rw [compactTail_eq_recurrence]

/-- Integer-only spelling of `Pr[frontier <= 209] >= 3/8`. -/
theorem compact_probability_at_least_three_eighths :
    3 * compactTotal <= 8 * compactFavourable := by
  norm_num [compactTotal, compactFavourable, compactTail,
    expectedCompactTail]

/-- Exact conditioned-query certificate requested by the V6 blueprint. It
avoids any independence assumption between the compact event and the bad
query set. -/
theorem conditioned_q16_integer_certificate :
    Nat.choose 9557 16 * 2 ^ 75 <= compactFavourable := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  norm_num [compactFavourable, compactTotal, compactTail,
    expectedCompactTail, Nat.descFactorial, Nat.factorial]

/-- Real-probability spelling of the same exact integer certificate. The
numerator upper-bounds compact schedules wholly contained in any fixed bad
set of at most 9557 leaves; division by `2^34` charges final work. -/
theorem conditioned_q16_div_work_le_two_pow_neg_109 :
    (((Nat.choose 9557 16 : Nat) : Real) /
          (compactFavourable : Real)) / 2 ^ 34 <=
      (1 : Real) / 2 ^ 109 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  norm_num [compactFavourable, compactTotal, compactTail,
    expectedCompactTail, Nat.descFactorial, Nat.factorial]

/-- The favourable count is a genuine nonempty proper subset count. -/
theorem compact_count_nontrivial :
    0 < compactFavourable ∧ compactFavourable < compactTotal := by
  norm_num [compactFavourable, compactTotal, compactTail,
    expectedCompactTail]

#print axioms compactTotal_eq_choose
#print axioms compactTotal_eq_recurrence
#print axioms compactTail_eq_recurrence
#print axioms compactFavourable_eq_exact
#print axioms compact_partition_exact
#print axioms compactFavourable_eq_recurrence
#print axioms compact_probability_at_least_three_eighths
#print axioms conditioned_q16_integer_certificate
#print axioms conditioned_q16_div_work_le_two_pow_neg_109
#print axioms compact_count_nontrivial

end AspisV6CompactFrontierCertificate
