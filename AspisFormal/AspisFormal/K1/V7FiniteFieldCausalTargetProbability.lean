import AspisFormal.K1.V7Tag73HiddenTapeAveraging

/-!
# Uniform finite-output causal target probability

The adaptive target-tree counting theorem is generic in its finite output
type, but the original probability corollary was specialized to 256-bit
digests.  Tag-73's K1.5 ledger needs the same theorem for exact QM31 challenge
values.  This file supplies that missing measure bridge without adding an
independence premise: each target set may depend on all preceding answers.
-/

set_option autoImplicit false

namespace AspisK1.V7FiniteFieldCausalTargetProbability

open scoped ENNReal
open MeasureTheory
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73HiddenTapeAveraging

noncomputable section

def uniformFiniteFreshTape
    (Output : Type) [Fintype Output] [Nonempty Output] (steps : Nat) :
    PMF (FreshAnswerTape Output steps) :=
  PMF.uniformOfFintype (FreshAnswerTape Output steps)

/-- Exact event/count identity for a uniform tape over any nonempty finite
output type. -/
theorem uniform_finite_causal_hit_probability_eq
    {Output : Type} [Fintype Output] [DecidableEq Output] [Nonempty Output]
    {caps : List Nat} (tree : CausalTargetTree Output caps) :
    (uniformFiniteFreshTape Output caps.length).toOuterMeasure
        (causalHitEvent tree) =
      (causalHitCount tree : ENNReal) /
        (Fintype.card (FreshAnswerTape Output caps.length) : ENNReal) := by
  classical
  unfold uniformFiniteFreshTape
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  change (causalHitCount tree : ENNReal) /
      (Fintype.card (FreshAnswerTape Output caps.length) : ENNReal) = _
  rfl

/-- Direct probability form of the generic adaptive counting theorem. -/
theorem uniform_finite_causal_hit_probability_le_exact_count
    {Output : Type} [Fintype Output] [DecidableEq Output] [Nonempty Output]
    {caps : List Nat} (tree : CausalTargetTree Output caps) :
    (uniformFiniteFreshTape Output caps.length).toOuterMeasure
        (causalHitEvent tree) ≤
      ((caps.sum * Fintype.card Output ^ (caps.length - 1) : Nat) : ENNReal) /
        ((Fintype.card Output ^ caps.length : Nat) : ENNReal) := by
  rw [uniform_finite_causal_hit_probability_eq]
  rw [fresh_answer_tape_card]
  apply ENNReal.div_le_div_right
  exact_mod_cast causal_hit_count_le_target_caps tree

/-- For a nonempty causal schedule, the exact count ratio simplifies to the
familiar sum-of-root-caps divided by the field cardinality. -/
theorem uniform_finite_causal_hit_probability_le_sum_div_card
    {Output : Type} [Fintype Output] [DecidableEq Output] [Nonempty Output]
    {caps : List Nat} (nonempty : caps ≠ [])
    (tree : CausalTargetTree Output caps) :
    (uniformFiniteFreshTape Output caps.length).toOuterMeasure
        (causalHitEvent tree) ≤
      (caps.sum : ENNReal) / (Fintype.card Output : ENNReal) := by
  have counted := uniform_finite_causal_hit_probability_le_exact_count tree
  rcases caps with _ | ⟨cap, caps⟩
  · exact False.elim (nonempty rfl)
  · simp only [List.length_cons, Nat.succ_sub_one] at counted ⊢
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow] at counted
    have cardNe : (Fintype.card Output : ENNReal) ≠ 0 := by
      exact_mod_cast Fintype.card_pos.ne'
    calc
      (uniformFiniteFreshTape Output (cap :: caps).length).toOuterMeasure
          (causalHitEvent tree) ≤
        (((cap :: caps).sum : ENNReal) *
            (Fintype.card Output : ENNReal) ^ caps.length) /
          ((Fintype.card Output : ENNReal) ^ (caps.length + 1)) := counted
      _ = ((cap :: caps).sum : ENNReal) /
          (Fintype.card Output : ENNReal) := by
        rw [pow_succ]
        have powerNe :
            (Fintype.card Output : ENNReal) ^ caps.length ≠ 0 :=
          pow_ne_zero _ cardNe
        have powerFinite :
            (Fintype.card Output : ENNReal) ^ caps.length ≠ ∞ := by simp
        rw [mul_comm ((cap :: caps).sum : ENNReal)]
        exact ENNReal.mul_div_mul_left
          ((cap :: caps).sum : ENNReal)
          (Fintype.card Output : ENNReal) powerNe powerFinite

def fixedHiddenUniformFiniteLaw
    {HiddenTape Output : Type} [Fintype Output] [Nonempty Output]
    (hidden : HiddenTape) (steps : Nat) :
    PMF (HiddenTape × FreshAnswerTape Output steps) :=
  (uniformFiniteFreshTape Output steps).map fun answers => (hidden, answers)

def hiddenUniformFiniteJointLaw
    {HiddenTape Output : Type} [Fintype HiddenTape]
    [Fintype Output] [Nonempty Output]
    (hiddenLaw : PMF HiddenTape) (steps : Nat) :
    PMF (HiddenTape × FreshAnswerTape Output steps) :=
  hiddenLaw.bind fun hidden => fixedHiddenUniformFiniteLaw hidden steps

def finiteJointEventSlice
    {HiddenTape Output : Type} {steps : Nat}
    (event : Set (HiddenTape × FreshAnswerTape Output steps))
    (hidden : HiddenTape) : Set (FreshAnswerTape Output steps) :=
  {answers | (hidden, answers) ∈ event}

def hiddenDependentFiniteCausalHitEvent
    {HiddenTape Output : Type} [DecidableEq Output] {caps : List Nat}
    (tree : HiddenTape → CausalTargetTree Output caps) :
    Set (HiddenTape × FreshAnswerTape Output caps.length) :=
  {pair | (tree pair.1).everHits pair.2}

theorem finite_joint_event_probability_eq_weighted_slices
    {HiddenTape Output : Type} [Fintype HiddenTape]
    [Fintype Output] [Nonempty Output]
    (hiddenLaw : PMF HiddenTape) (steps : Nat)
    (event : Set (HiddenTape × FreshAnswerTape Output steps)) :
    (hiddenUniformFiniteJointLaw hiddenLaw steps).toOuterMeasure event =
      ∑' hidden : HiddenTape,
        hiddenLaw hidden *
          (uniformFiniteFreshTape Output steps).toOuterMeasure
            (finiteJointEventSlice event hidden) := by
  unfold hiddenUniformFiniteJointLaw fixedHiddenUniformFiniteLaw
  rw [PMF.toOuterMeasure_bind_apply]
  apply tsum_congr
  intro hidden
  rw [PMF.toOuterMeasure_map_apply]
  rfl

theorem finite_joint_event_probability_le_of_every_slice_le
    {HiddenTape Output : Type} [Fintype HiddenTape]
    [Fintype Output] [Nonempty Output]
    (hiddenLaw : PMF HiddenTape) (steps : Nat)
    (event : Set (HiddenTape × FreshAnswerTape Output steps))
    (bound : ENNReal)
    (sliceBound : ∀ hidden : HiddenTape,
      (uniformFiniteFreshTape Output steps).toOuterMeasure
        (finiteJointEventSlice event hidden) ≤ bound) :
    (hiddenUniformFiniteJointLaw hiddenLaw steps).toOuterMeasure event ≤
      bound := by
  rw [finite_joint_event_probability_eq_weighted_slices]
  calc
    (∑' hidden : HiddenTape,
        hiddenLaw hidden *
          (uniformFiniteFreshTape Output steps).toOuterMeasure
            (finiteJointEventSlice event hidden)) ≤
        ∑' hidden : HiddenTape, hiddenLaw hidden * bound := by
      exact ENNReal.tsum_le_tsum fun hidden =>
        mul_le_mul_left' (sliceBound hidden) (hiddenLaw hidden)
    _ = (∑' hidden : HiddenTape, hiddenLaw hidden) * bound := by
      exact ENNReal.tsum_mul_right
    _ = bound := by rw [PMF.tsum_coe, one_mul]

/-- Hidden-tape averaging for a context-dependent finite-field causal tree. -/
theorem hidden_dependent_finite_causal_probability_le_sum_div_card
    {HiddenTape Output : Type} [Fintype HiddenTape]
    [Fintype Output] [DecidableEq Output] [Nonempty Output]
    (hiddenLaw : PMF HiddenTape)
    {caps : List Nat} (nonempty : caps ≠ [])
    (tree : HiddenTape → CausalTargetTree Output caps) :
    (hiddenUniformFiniteJointLaw hiddenLaw caps.length).toOuterMeasure
        (hiddenDependentFiniteCausalHitEvent tree) ≤
      (caps.sum : ENNReal) / (Fintype.card Output : ENNReal) := by
  apply finite_joint_event_probability_le_of_every_slice_le
  intro hidden
  change (uniformFiniteFreshTape Output caps.length).toOuterMeasure
      (causalHitEvent (tree hidden)) ≤ _
  exact uniform_finite_causal_hit_probability_le_sum_div_card nonempty
    (tree hidden)

end

#print axioms uniform_finite_causal_hit_probability_eq
#print axioms uniform_finite_causal_hit_probability_le_exact_count
#print axioms uniform_finite_causal_hit_probability_le_sum_div_card
#print axioms finite_joint_event_probability_eq_weighted_slices
#print axioms finite_joint_event_probability_le_of_every_slice_le
#print axioms hidden_dependent_finite_causal_probability_le_sum_div_card

end AspisK1.V7FiniteFieldCausalTargetProbability
