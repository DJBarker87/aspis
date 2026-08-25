import AspisFormal.K1.V7Tag73UniformOracleBoundary

/-!
# Averaging causal fresh-oracle bounds over a hidden adversary tape

The hidden adversary tape need not be uniform.  This module takes an arbitrary
PMF on a finite hidden-tape type, then samples an independent uniform finite
tape of fresh 256-bit oracle answers.  The joint law is an explicit PMF bind;
it is not an `ObservedProofExperiment.law` field.

For a causal target tree selected by the hidden tape, the existing pointwise
fresh-answer bound is averaged without changing its coefficient.  A generic
joint event can also be bounded when every one of its hidden-tape slices is a
subset of the corresponding causal hit event.  This is only measure/counting
glue: no Tag-73 failure is asserted to satisfy that inclusion, and there is no
compiler, trace-cover, BCS, acceptance, or extraction conclusion here.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73HiddenTapeAveraging

open MeasureTheory
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73UniformOracleBoundary

noncomputable section

/-! ## Explicit joint law and slice identity -/

/-- Conditional law at one fixed hidden tape: sample a uniform fresh-answer
tape and pair it with that fixed hidden value. -/
def fixedHiddenUniformFreshLaw
    {HiddenTape : Type} (hidden : HiddenTape) (freshExposures : Nat) :
    PMF (HiddenTape × FreshAnswerTape Digest256 freshExposures) :=
  (uniformDigestFreshTape freshExposures).map fun answers => (hidden, answers)

/-- First sample the arbitrary hidden adversary tape, then an independent
uniform tape of fresh oracle answers. -/
def hiddenTapeUniformFreshJointLaw
    {HiddenTape : Type} [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape) (freshExposures : Nat) :
    PMF (HiddenTape × FreshAnswerTape Digest256 freshExposures) :=
  hiddenLaw.bind fun hidden =>
    fixedHiddenUniformFreshLaw hidden freshExposures

/-- The fresh-answer slice of a joint event at one fixed hidden tape. -/
def jointEventSlice
    {HiddenTape : Type} {freshExposures : Nat}
    (event : Set (HiddenTape × FreshAnswerTape Digest256 freshExposures))
    (hidden : HiddenTape) : Set (FreshAnswerTape Digest256 freshExposures) :=
  {answers | (hidden, answers) ∈ event}

/-- Exact disintegration identity for the explicit finite joint PMF. -/
theorem joint_event_probability_eq_weighted_slice_probabilities
    {HiddenTape : Type} [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape) (freshExposures : Nat)
    (event : Set (HiddenTape × FreshAnswerTape Digest256 freshExposures)) :
    (hiddenTapeUniformFreshJointLaw hiddenLaw freshExposures).toOuterMeasure
        event =
      ∑' hidden : HiddenTape,
        hiddenLaw hidden *
          (uniformDigestFreshTape freshExposures).toOuterMeasure
            (jointEventSlice event hidden) := by
  unfold hiddenTapeUniformFreshJointLaw fixedHiddenUniformFreshLaw
  rw [PMF.toOuterMeasure_bind_apply]
  apply tsum_congr
  intro hidden
  rw [PMF.toOuterMeasure_map_apply]
  rfl

/-- If all conditional slices have the same bound, averaging over an
arbitrary hidden-tape PMF preserves that bound exactly. -/
theorem joint_event_probability_le_of_every_slice_le
    {HiddenTape : Type} [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape) (freshExposures : Nat)
    (event : Set (HiddenTape × FreshAnswerTape Digest256 freshExposures))
    (bound : ENNReal)
    (sliceBound : ∀ hidden : HiddenTape,
      (uniformDigestFreshTape freshExposures).toOuterMeasure
          (jointEventSlice event hidden) ≤ bound) :
    (hiddenTapeUniformFreshJointLaw hiddenLaw freshExposures).toOuterMeasure
        event ≤ bound := by
  rw [joint_event_probability_eq_weighted_slice_probabilities]
  calc
    (∑' hidden : HiddenTape,
        hiddenLaw hidden *
          (uniformDigestFreshTape freshExposures).toOuterMeasure
            (jointEventSlice event hidden)) ≤
        ∑' hidden : HiddenTape, hiddenLaw hidden * bound := by
      exact ENNReal.tsum_le_tsum fun hidden =>
        mul_le_mul_left' (sliceBound hidden) (hiddenLaw hidden)
    _ = (∑' hidden : HiddenTape, hiddenLaw hidden) * bound := by
      exact ENNReal.tsum_mul_right
    _ = bound := by rw [PMF.tsum_coe, one_mul]

/-! ## Hidden-tape-dependent causal trees -/

def hiddenDependentCausalHitEvent
    {HiddenTape : Type} {caps : List Nat}
    (tree : HiddenTape → CausalTargetTree Digest256 caps) :
    Set (HiddenTape × FreshAnswerTape Digest256 caps.length) :=
  {pair | (tree pair.1).everHits pair.2}

theorem causal_joint_event_slice
    {HiddenTape : Type} {caps : List Nat}
    (tree : HiddenTape → CausalTargetTree Digest256 caps)
    (hidden : HiddenTape) :
    jointEventSlice (hiddenDependentCausalHitEvent tree) hidden =
      causalHitEvent (tree hidden) := by
  rfl

/-- Averaging the first-principles causal tree theorem over any finite hidden
tape law introduces no extra loss. -/
theorem hidden_dependent_causal_tree_probability_le_exact_count
    {HiddenTape : Type} [Fintype HiddenTape] {caps : List Nat}
    (hiddenLaw : PMF HiddenTape)
    (tree : HiddenTape → CausalTargetTree Digest256 caps) :
    (hiddenTapeUniformFreshJointLaw hiddenLaw caps.length).toOuterMeasure
        (hiddenDependentCausalHitEvent tree) ≤
      ((caps.sum * (2 ^ 256) ^ (caps.length - 1) : Nat) : ENNReal) /
        (((2 : ENNReal) ^ 256) ^ caps.length) := by
  apply joint_event_probability_le_of_every_slice_le
  intro hidden
  rw [causal_joint_event_slice]
  exact uniform_digest_causal_hit_probability_le_exact_count (tree hidden)

/-- Generic pointwise slice inclusion lifts to the same joint exact-count
bound.  This theorem does not assert that any deployed failure event supplies
`sliceCovered`; that is the remaining operational classification proof. -/
theorem joint_event_probability_le_causal_exact_count_of_slice_inclusion
    {HiddenTape : Type} [Fintype HiddenTape] {caps : List Nat}
    (hiddenLaw : PMF HiddenTape)
    (tree : HiddenTape → CausalTargetTree Digest256 caps)
    (event : Set (HiddenTape × FreshAnswerTape Digest256 caps.length))
    (sliceCovered : ∀ hidden : HiddenTape,
      jointEventSlice event hidden ⊆ causalHitEvent (tree hidden)) :
    (hiddenTapeUniformFreshJointLaw hiddenLaw caps.length).toOuterMeasure
        event ≤
      ((caps.sum * (2 ^ 256) ^ (caps.length - 1) : Nat) : ENNReal) /
        (((2 : ENNReal) ^ 256) ^ caps.length) := by
  apply joint_event_probability_le_of_every_slice_le
  intro hidden
  exact ((uniformDigestFreshTape caps.length).toOuterMeasure.mono
    (sliceCovered hidden)).trans
      (uniform_digest_causal_hit_probability_le_exact_count (tree hidden))

/-! ## Exact Tag-73 cap-list specialization -/

/-- The hidden-tape average retains the literal Tag-73 target coefficient
`Q + choose(Q,2) + P*Q + 1088*Q`; it does not create a BCS coefficient. -/
theorem tag73_hidden_dependent_tree_probability_le_exact_count
    {HiddenTape : Type} [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape) (freshExposures programmedPoints : Nat)
    (tree : HiddenTape → CausalTargetTree Digest256
      (tag73PerExposureTargetCaps freshExposures programmedPoints)) :
    (hiddenTapeUniformFreshJointLaw hiddenLaw
        (tag73PerExposureTargetCaps freshExposures programmedPoints).length).toOuterMeasure
        (hiddenDependentCausalHitEvent tree) ≤
      ((tag73UniformTargetCoefficient freshExposures programmedPoints *
          (2 ^ 256) ^ (freshExposures - 1) : Nat) : ENNReal) /
        (((2 : ENNReal) ^ 256) ^ freshExposures) := by
  have bound := hidden_dependent_causal_tree_probability_le_exact_count
    hiddenLaw tree
  calc
    (hiddenTapeUniformFreshJointLaw hiddenLaw
        (tag73PerExposureTargetCaps freshExposures programmedPoints).length).toOuterMeasure
          (hiddenDependentCausalHitEvent tree) ≤
        ((((tag73PerExposureTargetCaps freshExposures programmedPoints).sum *
            (2 ^ 256) ^
              ((tag73PerExposureTargetCaps freshExposures programmedPoints).length - 1) :
              Nat) : ENNReal) /
          (((2 : ENNReal) ^ 256) ^
            (tag73PerExposureTargetCaps freshExposures programmedPoints).length)) := bound
    _ = ((tag73UniformTargetCoefficient freshExposures programmedPoints *
            (2 ^ 256) ^ (freshExposures - 1) : Nat) : ENNReal) /
          (((2 : ENNReal) ^ 256) ^ freshExposures) := by
      rw [tag73_per_exposure_target_caps_sum_exact,
        tag73_per_exposure_target_caps_length]

#print axioms joint_event_probability_eq_weighted_slice_probabilities
#print axioms joint_event_probability_le_of_every_slice_le
#print axioms causal_joint_event_slice
#print axioms hidden_dependent_causal_tree_probability_le_exact_count
#print axioms joint_event_probability_le_causal_exact_count_of_slice_inclusion
#print axioms tag73_hidden_dependent_tree_probability_le_exact_count

end

end AspisK1.V7Tag73HiddenTapeAveraging
