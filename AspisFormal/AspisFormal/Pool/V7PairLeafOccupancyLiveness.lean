import AspisFormal.Pool.V7PairLeafOccupancy

/-!
# Honest-prover liveness for the occupied-slot sentinel

The one-permutation pair encoding reserves the all-zero second commitment for
an empty slot.  An occupied second commitment must therefore have a nonzero
sentinel limb.  This file records the exact ideal combinatorics for a client
which tries four fresh note salts and accepts the first nonzero sentinel.

Nothing here asserts that a concrete Poseidon output limb is information-
theoretically uniform.  Applying the ideal count to production requires the
explicitly allowed Poseidon pseudorandomness boundary, plus a source proof that
the wallet uses four independent fresh salts and never reuses a rejected one.
The algebraic spend-soundness theorems in `V7PairLeafOccupancy` do not depend
on that liveness boundary.
-/

set_option autoImplicit false

namespace AspisPool.V7PairLeafOccupancyLiveness

abbrev m31Order : Nat := 2147483647
abbrev occupiedSaltAttempts : Nat := 4

/-- Idealized sentinel values for four independent fresh-salt attempts. -/
abbrev IdealSentinel := Fin m31Order
abbrev IdealAttempt := Fin occupiedSaltAttempts
abbrev IdealAttemptTape := IdealAttempt → IdealSentinel

abbrev Exhausted (tape : IdealAttemptTape) : Prop :=
  ∀ attempt, tape attempt = 0

def zeroTape : IdealAttemptTape :=
  fun _ => 0

theorem exhausted_iff_zero_tape (tape : IdealAttemptTape) :
    Exhausted tape ↔ tape = zeroTape := by
  constructor
  · intro exhausted
    funext attempt
    exact exhausted attempt
  · intro exactZero attempt
    rw [exactZero]
    rfl

/-- There is exactly one all-zero tape among all four-attempt tapes. -/
noncomputable def exhaustedTapeEquivUnit :
    {tape : IdealAttemptTape // Exhausted tape} ≃ Unit where
  toFun := fun _ => ()
  invFun := fun _ => ⟨zeroTape, fun _ => rfl⟩
  left_inv := by
    intro tape
    apply Subtype.ext
    exact ((exhausted_iff_zero_tape tape.1).mp tape.2).symm
  right_inv := by
    intro singleton
    cases singleton
    rfl

theorem exact_exhausted_tape_count :
    Fintype.card {tape : IdealAttemptTape // Exhausted tape} = 1 := by
  classical
  exact Fintype.card_congr exhaustedTapeEquivUnit

theorem exact_total_tape_count :
    Fintype.card IdealAttemptTape = m31Order ^ occupiedSaltAttempts := by
  simp [m31Order, occupiedSaltAttempts]

/-- Exact failure probability in the ideal independent-uniform experiment. -/
def idealExhaustionProbability : Rat :=
  (1 : Rat) / m31Order ^ occupiedSaltAttempts

theorem ideal_exhaustion_probability_exact :
    idealExhaustionProbability =
      (1 : Rat) / 2147483647 ^ 4 := by
  rfl

/-- Four attempts leave more than 120 bits of ideal liveness headroom. -/
theorem ideal_exhaustion_probability_lt_two_neg_120 :
    idealExhaustionProbability < (1 : Rat) / 2 ^ 120 := by
  norm_num [idealExhaustionProbability, m31Order, occupiedSaltAttempts]

/-- A non-exhausted tape contains an attempt accepted by the nonzero-sentinel
gate. -/
theorem not_exhausted_has_nonzero_attempt (tape : IdealAttemptTape)
    (available : ¬ Exhausted tape) :
    ∃ attempt, tape attempt ≠ 0 := by
  by_contra none
  push Not at none
  exact available none

#print axioms exhausted_iff_zero_tape
#print axioms exact_exhausted_tape_count
#print axioms exact_total_tape_count
#print axioms ideal_exhaustion_probability_lt_two_neg_120
#print axioms not_exhausted_has_nonzero_attempt

end AspisPool.V7PairLeafOccupancyLiveness
