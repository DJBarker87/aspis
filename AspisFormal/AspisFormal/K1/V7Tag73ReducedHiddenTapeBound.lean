import AspisFormal.K1.V7Tag73HiddenTapeAveraging
import AspisFormal.K1.V7Tag73Q16TargetAudit

/-!
# Hidden-tape averaging for the q16-reduced target coefficient

This module combines two already proved facts:

* averaging a causal uniform-fresh-tape bound over an arbitrary finite hidden
  adversary-tape PMF adds no loss; and
* after deterministic q16 forest construction, the full-256 target coefficient
  is `Q + choose(Q,2) + P*Q`.

The exact-count form is valid for all `Q`.  For positive `Q`, its finite-tape
ratio is proved equal to the simpler coefficient divided by `2^256`.  The
zero-exposure case is stated separately and has probability exactly zero.

There is no protocol failure event, slice-inclusion hypothesis, compiler
premise, BCS term, acceptance predicate, or extraction conclusion here.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ReducedHiddenTapeBound

open MeasureTheory
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73Q16TargetAudit

noncomputable section

/-! ## Exact-count form for arbitrary hidden-tape law -/

theorem reduced_tag73_hidden_tree_probability_le_exact_count
    {HiddenTape : Type} [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape) (freshExposures programmedPoints : Nat)
    (tree : HiddenTape → CausalTargetTree Digest256
      (tag73ReducedPerExposureTargetCaps freshExposures programmedPoints)) :
    (hiddenTapeUniformFreshJointLaw hiddenLaw
        (tag73ReducedPerExposureTargetCaps freshExposures
          programmedPoints).length).toOuterMeasure
        (hiddenDependentCausalHitEvent tree) ≤
      ((tag73ReducedTargetCoefficient freshExposures programmedPoints *
          (2 ^ 256) ^ (freshExposures - 1) : Nat) : ENNReal) /
        (((2 : ENNReal) ^ 256) ^ freshExposures) := by
  have bound := hidden_dependent_causal_tree_probability_le_exact_count
    hiddenLaw tree
  calc
    (hiddenTapeUniformFreshJointLaw hiddenLaw
        (tag73ReducedPerExposureTargetCaps freshExposures
          programmedPoints).length).toOuterMeasure
          (hiddenDependentCausalHitEvent tree) ≤
        ((((tag73ReducedPerExposureTargetCaps freshExposures
              programmedPoints).sum *
            (2 ^ 256) ^
              ((tag73ReducedPerExposureTargetCaps freshExposures
                programmedPoints).length - 1) : Nat) : ENNReal) /
          (((2 : ENNReal) ^ 256) ^
            (tag73ReducedPerExposureTargetCaps freshExposures
              programmedPoints).length)) := bound
    _ = ((tag73ReducedTargetCoefficient freshExposures programmedPoints *
            (2 ^ 256) ^ (freshExposures - 1) : Nat) : ENNReal) /
          (((2 : ENNReal) ^ 256) ^ freshExposures) := by
      rw [tag73_reduced_per_exposure_target_caps_sum_exact,
        tag73_reduced_per_exposure_target_caps_length]

/-! ## Exact simplification at positive Q -/

private theorem finite_exact_count_ratio_succ
    (coefficient exponent : Nat) :
    (((coefficient * (2 ^ 256) ^ exponent : Nat) : ENNReal) /
        (((2 : ENNReal) ^ 256) ^ (exponent + 1))) =
      (coefficient : ENNReal) / ((2 : ENNReal) ^ 256) := by
  push_cast
  apply (ENNReal.div_eq_div_iff
    (a := (2 : ENNReal) ^ 256)
    (b := ((2 : ENNReal) ^ 256) ^ (exponent + 1))
    (by norm_num) (by simp) (by positivity) (by simp)).2
  rw [pow_succ]
  ring

/-- For at least one fresh exposure, the exact finite-count ratio cancels to
the familiar single-output denominator.  This is algebraic cancellation, not
an imported birthday slogan. -/
theorem reduced_tag73_hidden_tree_probability_le_div_two_pow_256
    {HiddenTape : Type} [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape) (freshExposures programmedPoints : Nat)
    (positive : 0 < freshExposures)
    (tree : HiddenTape → CausalTargetTree Digest256
      (tag73ReducedPerExposureTargetCaps freshExposures programmedPoints)) :
    (hiddenTapeUniformFreshJointLaw hiddenLaw
        (tag73ReducedPerExposureTargetCaps freshExposures
          programmedPoints).length).toOuterMeasure
        (hiddenDependentCausalHitEvent tree) ≤
      (tag73ReducedTargetCoefficient freshExposures programmedPoints : ENNReal) /
        ((2 : ENNReal) ^ 256) := by
  obtain ⟨exponent, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt positive)
  calc
    (hiddenTapeUniformFreshJointLaw hiddenLaw
        (tag73ReducedPerExposureTargetCaps (exponent + 1)
          programmedPoints).length).toOuterMeasure
          (hiddenDependentCausalHitEvent tree) ≤
        ((tag73ReducedTargetCoefficient (exponent + 1) programmedPoints *
            (2 ^ 256) ^ ((exponent + 1) - 1) : Nat) : ENNReal) /
          (((2 : ENNReal) ^ 256) ^ (exponent + 1)) :=
      reduced_tag73_hidden_tree_probability_le_exact_count hiddenLaw
        (exponent + 1) programmedPoints tree
    _ = (tag73ReducedTargetCoefficient (exponent + 1)
            programmedPoints : ENNReal) /
          ((2 : ENNReal) ^ 256) := by
      simp only [Nat.add_sub_cancel]
      exact finite_exact_count_ratio_succ
        (tag73ReducedTargetCoefficient (exponent + 1) programmedPoints)
          exponent

/-! ## Zero exposures -/

/-- With no fresh answer there is no causal step and the joint causal-hit
event has probability exactly zero, independently of the hidden-tape law and
`P`. -/
theorem reduced_tag73_hidden_tree_zero_exposures_probability
    {HiddenTape : Type} [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape) (programmedPoints : Nat)
    (tree : HiddenTape → CausalTargetTree Digest256
      (tag73ReducedPerExposureTargetCaps 0 programmedPoints)) :
    (hiddenTapeUniformFreshJointLaw hiddenLaw
        (tag73ReducedPerExposureTargetCaps 0 programmedPoints).length).toOuterMeasure
        (hiddenDependentCausalHitEvent tree) = 0 := by
  apply le_antisymm
  · have bound := reduced_tag73_hidden_tree_probability_le_exact_count
      hiddenLaw 0 programmedPoints tree
    simpa [tag73ReducedTargetCoefficient] using bound
  · exact bot_le

/-- The exact-count right side itself is zero at `Q = 0`; no cancellation by
a nonexistent fresh output is performed. -/
theorem reduced_tag73_zero_exposure_exact_count_rhs
    (programmedPoints : Nat) :
    ((tag73ReducedTargetCoefficient 0 programmedPoints *
        (2 ^ 256) ^ (0 - 1) : Nat) : ENNReal) /
      (((2 : ENNReal) ^ 256) ^ 0) = 0 := by
  simp [tag73ReducedTargetCoefficient]

#print axioms reduced_tag73_hidden_tree_probability_le_exact_count
#print axioms reduced_tag73_hidden_tree_probability_le_div_two_pow_256
#print axioms reduced_tag73_hidden_tree_zero_exposures_probability
#print axioms reduced_tag73_zero_exposure_exact_count_rhs

end

end AspisK1.V7Tag73ReducedHiddenTapeBound
