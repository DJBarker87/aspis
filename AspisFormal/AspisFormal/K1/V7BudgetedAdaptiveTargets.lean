import AspisFormal.K1.V7Tag73AdaptiveLazyOracle

/-!
# Causal target trees with an adaptive charged-step budget

A fixed cap at every tape coordinate is wasteful when the phase carrying a
target set begins at an answer-dependent coordinate. This module records the
stronger invariant needed by Tag-73 K1.2: at most `budget` coordinates on any
execution path are charged, although their locations may depend on all
earlier answers.

A free node retains the budget; a charged node consumes one unit before
revealing its current answer. Erasure produces the ordinary causal tree used
by the finite-tape library. The kernel proves the exact
`budget * targetCap` coefficient, independent of the padded tape length.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7BudgetedAdaptiveTargets

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AdaptiveLazyOracle

noncomputable section

/-- The list index records the remaining tape shape without coercion casts in
the erased ordinary causal tree. Every coordinate has the same local cap. -/
inductive BudgetedCausalTargetTree (Output : Type) (targetCap : Nat) :
    (caps : List Nat) → (budget : Nat) → Type
  | done (budget : Nat) : BudgetedCausalTargetTree Output targetCap [] budget
  | free {caps : List Nat} {budget : Nat}
      (next : Output → BudgetedCausalTargetTree Output targetCap caps budget) :
      BudgetedCausalTargetTree Output targetCap (targetCap :: caps) budget
  | charged {caps : List Nat} {budget : Nat}
      (targets : Finset Output) (targetCardLe : targets.card ≤ targetCap)
      (next : Output → BudgetedCausalTargetTree Output targetCap caps budget) :
      BudgetedCausalTargetTree Output targetCap (targetCap :: caps) (budget + 1)

def BudgetedCausalTargetTree.toCausal
    {Output : Type} {targetCap : Nat} :
    {caps : List Nat} → {budget : Nat} →
      BudgetedCausalTargetTree Output targetCap caps budget →
        CausalTargetTree Output caps
  | [], _, .done _ => .done
  | _ :: _, _, .free next =>
      .step ∅ (by simp) fun output => (next output).toCausal
  | _ :: _, _, .charged targets targetCardLe next =>
      .step targets targetCardLe fun output => (next output).toCausal

def budgetedCausalHitEvent
    {Output : Type} [DecidableEq Output] {targetCap budget : Nat}
    {caps : List Nat}
    (tree : BudgetedCausalTargetTree Output targetCap caps budget) :
    Set (FreshAnswerTape Output caps.length) :=
  causalHitEvent tree.toCausal

theorem budgeted_causal_hit_count_empty
    {Output : Type} [Fintype Output] [DecidableEq Output]
    {targetCap budget : Nat}
    (tree : BudgetedCausalTargetTree Output targetCap [] budget) :
    causalHitCount tree.toCausal = 0 := by
  cases tree
  simp [BudgetedCausalTargetTree.toCausal, causalHitCount,
    CausalTargetTree.everHits]

/-- Exact adaptive charged-budget count. Charged coordinates may occur at
different depths on different answer branches. -/
theorem budgeted_causal_hit_count_le
    {Output : Type} [Fintype Output] [DecidableEq Output]
    {targetCap budget : Nat} {caps : List Nat}
    (tree : BudgetedCausalTargetTree Output targetCap caps budget) :
    causalHitCount tree.toCausal ≤
      budget * targetCap * Fintype.card Output ^ (caps.length - 1) := by
  induction tree with
  | done budget =>
      simp [BudgetedCausalTargetTree.toCausal, causalHitCount,
        CausalTargetTree.everHits]
  | @free caps budget next inductionHypothesis =>
      have stepBound := causal_hit_count_step_le
        (cap := targetCap) (∅ : Finset Output) (by simp)
        (fun output => (next output).toCausal)
      simp only [Finset.card_empty, zero_mul, zero_add] at stepBound
      cases caps with
      | nil =>
          calc
            causalHitCount
                (BudgetedCausalTargetTree.free next).toCausal ≤
              ∑ output : Output, causalHitCount (next output).toCausal :=
                stepBound
            _ = 0 := by
              apply Finset.sum_eq_zero
              intro output _member
              exact budgeted_causal_hit_count_empty (next output)
            _ ≤ budget * targetCap * Fintype.card Output ^
                ((targetCap :: []).length - 1) := Nat.zero_le _
      | cons _cap tailCaps =>
          let tailBound := budget * targetCap * Fintype.card Output ^
            ((targetCap :: tailCaps).length - 1)
          have eachTail (output : Output) :
              causalHitCount (next output).toCausal ≤ tailBound := by
            simpa [tailBound] using inductionHypothesis output
          have tailSum :
              (∑ output : Output, causalHitCount (next output).toCausal) ≤
                Fintype.card Output * tailBound := by
            calc
              (∑ output : Output,
                  causalHitCount (next output).toCausal) ≤
                  ∑ _output : Output, tailBound := by
                    exact Finset.sum_le_sum fun output _ => eachTail output
              _ = Fintype.card Output * tailBound := by simp
          calc
            causalHitCount
                (BudgetedCausalTargetTree.free next).toCausal ≤
              ∑ output : Output, causalHitCount (next output).toCausal :=
                stepBound
            _ ≤ Fintype.card Output * tailBound := tailSum
            _ = budget * targetCap * Fintype.card Output ^
                ((targetCap :: _cap :: tailCaps).length - 1) := by
              simp only [tailBound, List.length_cons, Nat.add_sub_cancel]
              rw [pow_succ]
              ring
  | @charged caps budget targets targetCardLe next inductionHypothesis =>
      have stepBound := causal_hit_count_step_le targets targetCardLe
        (fun output => (next output).toCausal)
      cases caps with
      | nil =>
          have tailsZero :
              (∑ output : Output, causalHitCount (next output).toCausal) = 0 := by
            apply Finset.sum_eq_zero
            intro output _member
            exact budgeted_causal_hit_count_empty (next output)
          calc
            causalHitCount
                (BudgetedCausalTargetTree.charged targets targetCardLe
                  next).toCausal ≤
              targets.card *
                  Fintype.card (FreshAnswerTape Output [].length) +
                ∑ output : Output,
                  causalHitCount (next output).toCausal := stepBound
            _ = targets.card := by
              rw [tailsZero, add_zero, fresh_answer_tape_card]
              simp
            _ ≤ targetCap := targetCardLe
            _ ≤ (budget + 1) * targetCap * Fintype.card Output ^
                ((targetCap :: []).length - 1) := by
              simpa [Nat.succ_eq_add_one] using
                (Nat.le_mul_of_pos_left targetCap (Nat.succ_pos budget))
      | cons _cap tailCaps =>
          let tailBound := budget * targetCap * Fintype.card Output ^
            ((targetCap :: tailCaps).length - 1)
          have eachTail (output : Output) :
              causalHitCount (next output).toCausal ≤ tailBound := by
            simpa [tailBound] using inductionHypothesis output
          have tailSum :
              (∑ output : Output, causalHitCount (next output).toCausal) ≤
                Fintype.card Output * tailBound := by
            calc
              (∑ output : Output,
                  causalHitCount (next output).toCausal) ≤
                  ∑ _output : Output, tailBound := by
                    exact Finset.sum_le_sum fun output _ => eachTail output
              _ = Fintype.card Output * tailBound := by simp
          calc
            causalHitCount
                (BudgetedCausalTargetTree.charged targets targetCardLe
                  next).toCausal ≤
              targets.card *
                  Fintype.card
                    (FreshAnswerTape Output (_cap :: tailCaps).length) +
                ∑ output : Output,
                  causalHitCount (next output).toCausal := stepBound
            _ ≤ targetCap * Fintype.card Output ^ (_cap :: tailCaps).length +
                Fintype.card Output * tailBound := by
              rw [fresh_answer_tape_card]
              exact Nat.add_le_add
                (Nat.mul_le_mul_right _ targetCardLe) tailSum
            _ = (budget + 1) * targetCap * Fintype.card Output ^
                ((targetCap :: _cap :: tailCaps).length - 1) := by
              simp only [tailBound, List.length_cons, Nat.add_sub_cancel]
              rw [pow_succ]
              ring

#print axioms budgeted_causal_hit_count_empty
#print axioms budgeted_causal_hit_count_le

end

end AspisK1.V7BudgetedAdaptiveTargets
