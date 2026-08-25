import AspisFormal.K1.V7Tag73HiddenTapeAveraging
import AspisFormal.K1.V7Tag73ResourceLazyOracle

/-!
# Global-call-cap bound for Tag-73 forward references

A forward reference can be encoded by any later full SHA input, not merely by
an extractor-programming point.  Therefore its conservative per-exposure
capacity is the strict global oracle-call cap `G`.  At fresh full-output
exposure `i`, collision targets contribute the `i` prior full outputs and
forward/programming targets contribute at most `G`, giving the literal cap
list

`[0 + G, 1 + G, ..., (F - 1) + G]`

and exact coefficient

`choose(F, 2) + F * G`.

Here `F` counts only full-256 fresh answers.  `G` counts all initial,
verifier, and restoration SHA calls, including calls whose outputs belong to
the separately typed 208-bit Merkle grammar: such calls can conservatively
name later inputs, but they are not added to the full-output collision count.

This module proves causal finite-tape counting and arbitrary-hidden-tape
averaging only.  It does not claim that any Tag-73 compiler failure injects
into the tree, and it imports no BCS coefficient.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73GlobalForwardReferenceBound

open MeasureTheory
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73ResourceLazyOracle

noncomputable section

/-! ## Exact cap-list arithmetic -/

def tag73GlobalForwardReferenceCaps
    (full256FreshExposures globalOracleCalls : Nat) : List Nat :=
  (List.range' 0 full256FreshExposures).map fun prior =>
    prior + globalOracleCalls

def tag73GlobalForwardReferenceCoefficient
    (full256FreshExposures globalOracleCalls : Nat) : Nat :=
  full256FreshExposures.choose 2 +
    full256FreshExposures * globalOracleCalls

theorem tag73_global_forward_reference_caps_length
    (full256FreshExposures globalOracleCalls : Nat) :
    (tag73GlobalForwardReferenceCaps full256FreshExposures
      globalOracleCalls).length = full256FreshExposures := by
  simp [tag73GlobalForwardReferenceCaps]

private theorem sum_map_add_constant
    (indices : List Nat) (constant : Nat) :
    (indices.map fun index => index + constant).sum =
      indices.sum + indices.length * constant := by
  induction indices with
  | nil => simp
  | cons index indices ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [ih]
      ring

theorem tag73_global_forward_reference_caps_sum_exact
    (full256FreshExposures globalOracleCalls : Nat) :
    (tag73GlobalForwardReferenceCaps full256FreshExposures
      globalOracleCalls).sum =
        tag73GlobalForwardReferenceCoefficient full256FreshExposures
          globalOracleCalls := by
  unfold tag73GlobalForwardReferenceCaps
  rw [sum_map_add_constant, collision_caps_sum_exact]
  simp only [List.length_range']
  unfold tag73GlobalForwardReferenceCoefficient
  rfl

theorem tag73_global_forward_reference_coefficient_exact
    (full256FreshExposures globalOracleCalls : Nat) :
    tag73GlobalForwardReferenceCoefficient full256FreshExposures
        globalOracleCalls =
      full256FreshExposures.choose 2 +
        full256FreshExposures * globalOracleCalls := by
  rfl

/-! ## Uniform finite-tape forms -/

theorem global_forward_reference_tree_hit_count_le
    (full256FreshExposures globalOracleCalls : Nat)
    (tree : CausalTargetTree Digest256
      (tag73GlobalForwardReferenceCaps full256FreshExposures
        globalOracleCalls)) :
    causalHitCount tree ≤
      tag73GlobalForwardReferenceCoefficient full256FreshExposures
          globalOracleCalls *
        (2 ^ 256) ^ (full256FreshExposures - 1) := by
  have bound := causal_hit_count_le_target_caps tree
  rw [AspisK1.V7FsStateRestorationCoupling.deployed_digest_256_cardinality,
    tag73_global_forward_reference_caps_sum_exact,
    tag73_global_forward_reference_caps_length] at bound
  exact bound

theorem global_forward_reference_tree_probability_le_exact_count
    (full256FreshExposures globalOracleCalls : Nat)
    (tree : CausalTargetTree Digest256
      (tag73GlobalForwardReferenceCaps full256FreshExposures
        globalOracleCalls)) :
    (uniformDigestFreshTape
        (tag73GlobalForwardReferenceCaps full256FreshExposures
          globalOracleCalls).length).toOuterMeasure
        (causalHitEvent tree) ≤
      ((tag73GlobalForwardReferenceCoefficient full256FreshExposures
            globalOracleCalls *
          (2 ^ 256) ^ (full256FreshExposures - 1) : Nat) : ENNReal) /
        (((2 : ENNReal) ^ 256) ^ full256FreshExposures) := by
  have bound := uniform_digest_causal_hit_probability_le_exact_count tree
  calc
    (uniformDigestFreshTape
        (tag73GlobalForwardReferenceCaps full256FreshExposures
          globalOracleCalls).length).toOuterMeasure
        (causalHitEvent tree) ≤
      ((((tag73GlobalForwardReferenceCaps full256FreshExposures
              globalOracleCalls).sum *
          (2 ^ 256) ^
            ((tag73GlobalForwardReferenceCaps full256FreshExposures
              globalOracleCalls).length - 1) : Nat) : ENNReal) /
        (((2 : ENNReal) ^ 256) ^
          (tag73GlobalForwardReferenceCaps full256FreshExposures
            globalOracleCalls).length)) := bound
    _ = ((tag73GlobalForwardReferenceCoefficient full256FreshExposures
            globalOracleCalls *
          (2 ^ 256) ^ (full256FreshExposures - 1) : Nat) : ENNReal) /
        (((2 : ENNReal) ^ 256) ^ full256FreshExposures) := by
      rw [tag73_global_forward_reference_caps_sum_exact,
        tag73_global_forward_reference_caps_length]

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

theorem global_forward_reference_tree_probability_le_div_two_pow_256
    (full256FreshExposures globalOracleCalls : Nat)
    (positive : 0 < full256FreshExposures)
    (tree : CausalTargetTree Digest256
      (tag73GlobalForwardReferenceCaps full256FreshExposures
        globalOracleCalls)) :
    (uniformDigestFreshTape
        (tag73GlobalForwardReferenceCaps full256FreshExposures
          globalOracleCalls).length).toOuterMeasure
        (causalHitEvent tree) ≤
      (tag73GlobalForwardReferenceCoefficient full256FreshExposures
        globalOracleCalls : ENNReal) / ((2 : ENNReal) ^ 256) := by
  obtain ⟨exponent, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt positive)
  calc
    (uniformDigestFreshTape
        (tag73GlobalForwardReferenceCaps (exponent + 1)
          globalOracleCalls).length).toOuterMeasure
        (causalHitEvent tree) ≤
      ((tag73GlobalForwardReferenceCoefficient (exponent + 1)
            globalOracleCalls *
          (2 ^ 256) ^ ((exponent + 1) - 1) : Nat) : ENNReal) /
        (((2 : ENNReal) ^ 256) ^ (exponent + 1)) :=
      global_forward_reference_tree_probability_le_exact_count
        (exponent + 1) globalOracleCalls tree
    _ = (tag73GlobalForwardReferenceCoefficient (exponent + 1)
          globalOracleCalls : ENNReal) / ((2 : ENNReal) ^ 256) := by
      simp only [Nat.add_sub_cancel]
      exact finite_exact_count_ratio_succ
        (tag73GlobalForwardReferenceCoefficient (exponent + 1)
          globalOracleCalls) exponent

theorem global_forward_reference_tree_zero_exposures_probability
    (globalOracleCalls : Nat)
    (tree : CausalTargetTree Digest256
      (tag73GlobalForwardReferenceCaps 0 globalOracleCalls)) :
    (uniformDigestFreshTape
        (tag73GlobalForwardReferenceCaps 0 globalOracleCalls).length).toOuterMeasure
        (causalHitEvent tree) = 0 := by
  apply le_antisymm
  · have bound := global_forward_reference_tree_probability_le_exact_count
      0 globalOracleCalls tree
    simpa [tag73GlobalForwardReferenceCoefficient] using bound
  · exact bot_le

/-! ## Arbitrary hidden-tape forms -/

theorem global_forward_reference_hidden_tree_probability_le_exact_count
    {HiddenTape : Type} [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    (full256FreshExposures globalOracleCalls : Nat)
    (tree : HiddenTape → CausalTargetTree Digest256
      (tag73GlobalForwardReferenceCaps full256FreshExposures
        globalOracleCalls)) :
    (hiddenTapeUniformFreshJointLaw hiddenLaw
        (tag73GlobalForwardReferenceCaps full256FreshExposures
          globalOracleCalls).length).toOuterMeasure
        (hiddenDependentCausalHitEvent tree) ≤
      ((tag73GlobalForwardReferenceCoefficient full256FreshExposures
            globalOracleCalls *
          (2 ^ 256) ^ (full256FreshExposures - 1) : Nat) : ENNReal) /
        (((2 : ENNReal) ^ 256) ^ full256FreshExposures) := by
  have bound := hidden_dependent_causal_tree_probability_le_exact_count
    hiddenLaw tree
  calc
    (hiddenTapeUniformFreshJointLaw hiddenLaw
        (tag73GlobalForwardReferenceCaps full256FreshExposures
          globalOracleCalls).length).toOuterMeasure
        (hiddenDependentCausalHitEvent tree) ≤
      ((((tag73GlobalForwardReferenceCaps full256FreshExposures
              globalOracleCalls).sum *
          (2 ^ 256) ^
            ((tag73GlobalForwardReferenceCaps full256FreshExposures
              globalOracleCalls).length - 1) : Nat) : ENNReal) /
        (((2 : ENNReal) ^ 256) ^
          (tag73GlobalForwardReferenceCaps full256FreshExposures
            globalOracleCalls).length)) := bound
    _ = ((tag73GlobalForwardReferenceCoefficient full256FreshExposures
            globalOracleCalls *
          (2 ^ 256) ^ (full256FreshExposures - 1) : Nat) : ENNReal) /
        (((2 : ENNReal) ^ 256) ^ full256FreshExposures) := by
      rw [tag73_global_forward_reference_caps_sum_exact,
        tag73_global_forward_reference_caps_length]

theorem global_forward_reference_hidden_tree_probability_le_div_two_pow_256
    {HiddenTape : Type} [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    (full256FreshExposures globalOracleCalls : Nat)
    (positive : 0 < full256FreshExposures)
    (tree : HiddenTape → CausalTargetTree Digest256
      (tag73GlobalForwardReferenceCaps full256FreshExposures
        globalOracleCalls)) :
    (hiddenTapeUniformFreshJointLaw hiddenLaw
        (tag73GlobalForwardReferenceCaps full256FreshExposures
          globalOracleCalls).length).toOuterMeasure
        (hiddenDependentCausalHitEvent tree) ≤
      (tag73GlobalForwardReferenceCoefficient full256FreshExposures
        globalOracleCalls : ENNReal) / ((2 : ENNReal) ^ 256) := by
  obtain ⟨exponent, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt positive)
  calc
    (hiddenTapeUniformFreshJointLaw hiddenLaw
        (tag73GlobalForwardReferenceCaps (exponent + 1)
          globalOracleCalls).length).toOuterMeasure
        (hiddenDependentCausalHitEvent tree) ≤
      ((tag73GlobalForwardReferenceCoefficient (exponent + 1)
            globalOracleCalls *
          (2 ^ 256) ^ ((exponent + 1) - 1) : Nat) : ENNReal) /
        (((2 : ENNReal) ^ 256) ^ (exponent + 1)) :=
      global_forward_reference_hidden_tree_probability_le_exact_count
        hiddenLaw (exponent + 1) globalOracleCalls tree
    _ = (tag73GlobalForwardReferenceCoefficient (exponent + 1)
          globalOracleCalls : ENNReal) / ((2 : ENNReal) ^ 256) := by
      simp only [Nat.add_sub_cancel]
      exact finite_exact_count_ratio_succ
        (tag73GlobalForwardReferenceCoefficient (exponent + 1)
          globalOracleCalls) exponent

theorem global_forward_reference_hidden_tree_zero_exposures_probability
    {HiddenTape : Type} [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape) (globalOracleCalls : Nat)
    (tree : HiddenTape → CausalTargetTree Digest256
      (tag73GlobalForwardReferenceCaps 0 globalOracleCalls)) :
    (hiddenTapeUniformFreshJointLaw hiddenLaw
        (tag73GlobalForwardReferenceCaps 0 globalOracleCalls).length).toOuterMeasure
        (hiddenDependentCausalHitEvent tree) = 0 := by
  apply le_antisymm
  · have bound :=
      global_forward_reference_hidden_tree_probability_le_exact_count
        hiddenLaw 0 globalOracleCalls tree
    simpa [tag73GlobalForwardReferenceCoefficient] using bound
  · exact bot_le

/-! ## Strict-envelope specialization -/

def strictEnvelopeGlobalForwardReferenceCaps
    (envelope : StrictTag73ResourceEnvelope) : List Nat :=
  tag73GlobalForwardReferenceCaps envelope.full256FreshExposures
    (strictGlobalOracleCallCap envelope)

def strictEnvelopeGlobalForwardReferenceCoefficient
    (envelope : StrictTag73ResourceEnvelope) : Nat :=
  envelope.full256FreshExposures.choose 2 +
    envelope.full256FreshExposures * strictGlobalOracleCallCap envelope

theorem strict_envelope_global_forward_reference_caps_length
    (envelope : StrictTag73ResourceEnvelope) :
    (strictEnvelopeGlobalForwardReferenceCaps envelope).length =
      envelope.full256FreshExposures := by
  exact tag73_global_forward_reference_caps_length _ _

theorem strict_envelope_global_forward_reference_caps_sum_exact
    (envelope : StrictTag73ResourceEnvelope) :
    (strictEnvelopeGlobalForwardReferenceCaps envelope).sum =
      strictEnvelopeGlobalForwardReferenceCoefficient envelope := by
  exact tag73_global_forward_reference_caps_sum_exact _ _

theorem strict_envelope_global_forward_reference_coefficient_expansion
    (envelope : StrictTag73ResourceEnvelope) :
    strictEnvelopeGlobalForwardReferenceCoefficient envelope =
      envelope.full256FreshExposures.choose 2 +
      envelope.full256FreshExposures *
        (envelope.q1Calls + envelope.verifierOracleCalls +
          envelope.restorationCount * envelope.oracleCallsPerRestoration) := by
  rfl

theorem strict_envelope_global_forward_reference_probability_le_exact_count
    (envelope : StrictTag73ResourceEnvelope)
    (tree : CausalTargetTree Digest256
      (strictEnvelopeGlobalForwardReferenceCaps envelope)) :
    (uniformDigestFreshTape
        (strictEnvelopeGlobalForwardReferenceCaps envelope).length).toOuterMeasure
        (causalHitEvent tree) ≤
      ((strictEnvelopeGlobalForwardReferenceCoefficient envelope *
          (2 ^ 256) ^ (envelope.full256FreshExposures - 1) : Nat) : ENNReal) /
        (((2 : ENNReal) ^ 256) ^ envelope.full256FreshExposures) := by
  exact global_forward_reference_tree_probability_le_exact_count
    envelope.full256FreshExposures (strictGlobalOracleCallCap envelope) tree

theorem strict_envelope_global_forward_reference_hidden_probability_le_exact_count
    {HiddenTape : Type} [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape) (envelope : StrictTag73ResourceEnvelope)
    (tree : HiddenTape → CausalTargetTree Digest256
      (strictEnvelopeGlobalForwardReferenceCaps envelope)) :
    (hiddenTapeUniformFreshJointLaw hiddenLaw
        (strictEnvelopeGlobalForwardReferenceCaps envelope).length).toOuterMeasure
        (hiddenDependentCausalHitEvent tree) ≤
      ((strictEnvelopeGlobalForwardReferenceCoefficient envelope *
          (2 ^ 256) ^ (envelope.full256FreshExposures - 1) : Nat) : ENNReal) /
        (((2 : ENNReal) ^ 256) ^ envelope.full256FreshExposures) := by
  exact global_forward_reference_hidden_tree_probability_le_exact_count
    hiddenLaw envelope.full256FreshExposures
      (strictGlobalOracleCallCap envelope) tree

#print axioms tag73_global_forward_reference_caps_length
#print axioms tag73_global_forward_reference_caps_sum_exact
#print axioms global_forward_reference_tree_hit_count_le
#print axioms global_forward_reference_tree_probability_le_exact_count
#print axioms global_forward_reference_tree_probability_le_div_two_pow_256
#print axioms global_forward_reference_tree_zero_exposures_probability
#print axioms global_forward_reference_hidden_tree_probability_le_exact_count
#print axioms global_forward_reference_hidden_tree_probability_le_div_two_pow_256
#print axioms global_forward_reference_hidden_tree_zero_exposures_probability
#print axioms strict_envelope_global_forward_reference_caps_sum_exact
#print axioms strict_envelope_global_forward_reference_coefficient_expansion
#print axioms strict_envelope_global_forward_reference_probability_le_exact_count
#print axioms strict_envelope_global_forward_reference_hidden_probability_le_exact_count

end

end AspisK1.V7Tag73GlobalForwardReferenceBound
