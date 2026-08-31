import AspisFormal.K1.V7Tag73CanonicalOneFoldSchedule

/-!
# Uniqueness of the exact Tag-73 one-fold schedule

The source boundary supplies the two inverse-table equations, whereas the
canonical verifier-derived K1.3 view constructs their entries directly.  This
module proves the equations determine the complete total schedule uniquely.
It removes an otherwise redundant schedule-equality obligation from a source
bridge without treating a table supplied by a prover as trusted.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73CanonicalOneFoldScheduleUniqueness

open AspisCircleGroupOrder
open AspisK1.V7Tag73CanonicalOneFoldSchedule
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisPool.V7CoherentTraceExtraction
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Two base-field entries with the same nonzero extension-field multiplier
and inverse equation are equal. -/
private theorem inverse_entry_unique
    (multiplier : QM31Exact) (left right : M31Exact)
    (leftExact : multiplier * algebraMap M31Exact QM31Exact left = 1)
    (rightExact : multiplier * algebraMap M31Exact QM31Exact right = 1) :
    left = right := by
  apply FaithfulSMul.algebraMap_injective M31Exact QM31Exact
  have multiplierNonzero : multiplier ≠ 0 := by
    intro zero
    rw [zero] at leftExact
    norm_num at leftExact
  apply (mul_left_cancel₀ multiplierNonzero)
  calc
    multiplier * algebraMap M31Exact QM31Exact left = 1 := leftExact
    _ = multiplier * algebraMap M31Exact QM31Exact right := rightExact.symm

/-- The two exact inverse-table equations and alpha determine every field of
the total schedule. -/
theorem exact_one_fold_schedule_unique
    (left right : ExactSchedule)
    (alphaExact : left.alpha = right.alpha)
    (leftTables : ExactOneFoldInverseTables left)
    (rightTables : ExactOneFoldInverseTables right) :
    left = right := by
  cases left with
  | mk leftAlpha leftX leftY =>
      cases right with
      | mk rightAlpha rightX rightY =>
          dsimp only at alphaExact leftTables rightTables ⊢
          have xExact : leftX = rightX := by
            funext index
            exact inverse_entry_unique (2 * exactCircleX index)
              (leftX index) (rightX index) (leftTables.1 index)
              (rightTables.1 index)
          have yExact : leftY = rightY := by
            funext index
            exact inverse_entry_unique (2 * exactCircleY index)
              (leftY index) (rightY index) (leftTables.2 index)
              (rightTables.2 index)
          cases alphaExact
          cases xExact
          cases yExact
          rfl

/-- In particular, any source schedule satisfying the release equations is
the canonical schedule at its recorded alpha. -/
theorem exact_one_fold_schedule_eq_canonical
    (schedule : ExactSchedule)
    (tables : ExactOneFoldInverseTables schedule) :
    schedule = canonicalOneFoldSchedule schedule.alpha := by
  apply exact_one_fold_schedule_unique schedule
    (canonicalOneFoldSchedule schedule.alpha)
  · rfl
  · exact tables
  · exact canonical_one_fold_schedule_exact schedule.alpha

#print axioms exact_one_fold_schedule_unique
#print axioms exact_one_fold_schedule_eq_canonical

end

end AspisK1.V7Tag73CanonicalOneFoldScheduleUniqueness
