import AspisFormal.K1.V7Tag73DeployedDecoderFiberCap
import AspisFormal.K1.V7Tag73HiddenTapeAveraging

/-!
# Adaptive probability bound for unqueried Tag-73 challenge completions

A missing `H(S || 0x01)` answer is not a singleton prediction when only its
decoded challenge is proof-visible.  This leaf turns the exact deployed
decoder fibers into a structurally causal target tree.  At each deployed
challenge occurrence the target is chosen before the current raw digest is
read; only the continuation may depend on that digest.

An occurrence may be inactive.  Inactive occurrences use the empty target
set and still consume one padded coordinate, so the probability space always
has the literal 36 deployed occurrence slots.  The exact coefficient is the
sum of the 36 per-identifier decoder caps, with the proved fallback
`36 * 2^228`.

This is not an acceptance/failure inclusion theorem.  The remaining compiler
bridge must identify, in chronological scheduler history, the raw output
coordinate that completes each live bounded sampler and prove that every
unqueried decoded-challenge prediction lands in the corresponding fiber.
It must separately prove that an unqueried rejected intermediate output is
output-oblivious (the independent advance half alone moves the duplex state),
so that only the semantically decisive completion output is selected.  q16 is
not silently charged here.
-/

set_option autoImplicit false
set_option maxRecDepth 16384

namespace AspisK1.V7Tag73UnqueriedChallengeFiberProbability

open MeasureTheory
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73ResourceLazyOracle
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73AtomicPairProbabilityAudit
open AspisK1.V7Tag73DeployedDecoderFiberCap

noncomputable section

/-! ## Exact finite targets -/

/-- The information fixed before one raw completion output is exposed. -/
structure ChallengeCompletionSpec (id : ChallengeId) where
  blockPrefix : BoundedBlockPrefix (samplerBlockCap (samplerMode id))
  value : Qm31Bytes

/-- Literal finite fiber of raw digests completing the fixed prefix with the
fixed deployed decoded value. -/
def challengeCompletionTargetFinset (id : ChallengeId)
    (spec : ChallengeCompletionSpec id) : Finset Digest256 :=
  Finset.univ.filter fun output =>
    challengeCompletionDecode id spec.blockPrefix output = some spec.value

theorem mem_challenge_completion_target_finset_iff (id : ChallengeId)
    (spec : ChallengeCompletionSpec id) (output : Digest256) :
    output ∈ challengeCompletionTargetFinset id spec ↔
      challengeCompletionDecode id spec.blockPrefix output =
        some spec.value := by
  simp [challengeCompletionTargetFinset]

theorem challenge_completion_target_finset_card_exact (id : ChallengeId)
    (spec : ChallengeCompletionSpec id) :
    (challengeCompletionTargetFinset id spec).card =
      challengeCompletionFiberCard id spec.blockPrefix spec.value := by
  classical
  unfold challengeCompletionTargetFinset challengeCompletionFiberCard
  rw [Fintype.card_subtype]

theorem challenge_completion_target_finset_card_le_cap (id : ChallengeId)
    (spec : ChallengeCompletionSpec id) :
    (challengeCompletionTargetFinset id spec).card ≤
      challengeCompletionFiberCap id := by
  rw [challenge_completion_target_finset_card_exact]
  exact challenge_completion_fiber_card_le_cap id spec.blockPrefix spec.value

/-- Empty when this deployed occurrence does not need an unqueried-output
charge; otherwise the exact deployed completion fiber. -/
def optionalChallengeCompletionTargets (id : ChallengeId) :
    Option (ChallengeCompletionSpec id) → Finset Digest256
  | none => ∅
  | some spec => challengeCompletionTargetFinset id spec

theorem optional_challenge_completion_targets_card_le_cap (id : ChallengeId)
    (spec : Option (ChallengeCompletionSpec id)) :
    (optionalChallengeCompletionTargets id spec).card ≤
      challengeCompletionFiberCap id := by
  cases spec with
  | none => simp [optionalChallengeCompletionTargets]
  | some spec =>
      exact challenge_completion_target_finset_card_le_cap id spec

/-! ## Structurally adaptive deployed plan -/

/-- At occurrence `id`, the current target is fixed before the current digest
is supplied.  Only `next` may inspect that digest. -/
inductive AdaptiveChallengeCompletionPlan : List ChallengeId → Type
  | done : AdaptiveChallengeCompletionPlan []
  | step {id : ChallengeId} {ids : List ChallengeId}
      (spec : Option (ChallengeCompletionSpec id))
      (next : Digest256 → AdaptiveChallengeCompletionPlan ids) :
      AdaptiveChallengeCompletionPlan (id :: ids)

/-- Translate the deployed plan into the generic causal finite-target tree.
The cap list retains each identifier's exact maximum fiber size. -/
def AdaptiveChallengeCompletionPlan.toCausalTree :
    {ids : List ChallengeId} → AdaptiveChallengeCompletionPlan ids →
      CausalTargetTree Digest256
        (ids.map challengeCompletionFiberCap)
  | [], .done => .done
  | _id :: _ids, .step spec next =>
      .step (optionalChallengeCompletionTargets _id spec)
        (optional_challenge_completion_targets_card_le_cap _id spec)
        fun output => (next output).toCausalTree

def deployedChallengeCompletionTargetTree
    (plan : AdaptiveChallengeCompletionPlan deployedChallengeIds) :
    CausalTargetTree Digest256
      (deployedChallengeIds.map challengeCompletionFiberCap) :=
  plan.toCausalTree

theorem deployed_challenge_completion_caps_length :
    (deployedChallengeIds.map challengeCompletionFiberCap).length = 36 :=
  deployed_challenge_prediction_coefficient_has_36_terms

theorem deployed_challenge_completion_caps_sum :
    (deployedChallengeIds.map challengeCompletionFiberCap).sum =
      deployedChallengePredictionFiberCoefficient := by
  rfl

/-! ## Exact finite-tape probability -/

theorem deployed_challenge_completion_probability_le_exact_count
    (plan : AdaptiveChallengeCompletionPlan deployedChallengeIds) :
    (uniformDigestFreshTape
        (deployedChallengeIds.map challengeCompletionFiberCap).length).toOuterMeasure
        (causalHitEvent (deployedChallengeCompletionTargetTree plan)) ≤
      ((deployedChallengePredictionFiberCoefficient *
          (2 ^ 256) ^ 35 : Nat) : ENNReal) /
        (((2 : ENNReal) ^ 256) ^ (35 + 1)) := by
  have bound := uniform_digest_causal_hit_probability_le_exact_count
    (deployedChallengeCompletionTargetTree plan)
  simpa only [deployed_challenge_completion_caps_sum,
    deployed_challenge_completion_caps_length, Nat.reduceSubDiff,
    Nat.reduceAdd] using bound

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

theorem deployed_challenge_completion_probability_le_exact_coefficient
    (plan : AdaptiveChallengeCompletionPlan deployedChallengeIds) :
    (uniformDigestFreshTape
        (deployedChallengeIds.map challengeCompletionFiberCap).length).toOuterMeasure
        (causalHitEvent (deployedChallengeCompletionTargetTree plan)) ≤
      (deployedChallengePredictionFiberCoefficient : ENNReal) /
        ((2 : ENNReal) ^ 256) := by
  calc
    (uniformDigestFreshTape
        (deployedChallengeIds.map challengeCompletionFiberCap).length).toOuterMeasure
        (causalHitEvent (deployedChallengeCompletionTargetTree plan)) ≤
      ((deployedChallengePredictionFiberCoefficient *
          (2 ^ 256) ^ 35 : Nat) : ENNReal) /
        (((2 : ENNReal) ^ 256) ^ (35 + 1)) :=
      deployed_challenge_completion_probability_le_exact_count plan
    _ = (deployedChallengePredictionFiberCoefficient : ENNReal) /
        ((2 : ENNReal) ^ 256) := by
      exact finite_exact_count_ratio_succ
        deployedChallengePredictionFiberCoefficient 35

theorem deployed_challenge_completion_probability_le_two_pow_228_fallback
    (plan : AdaptiveChallengeCompletionPlan deployedChallengeIds) :
    (uniformDigestFreshTape
        (deployedChallengeIds.map challengeCompletionFiberCap).length).toOuterMeasure
        (causalHitEvent (deployedChallengeCompletionTargetTree plan)) ≤
      ((36 * (2 ^ 228) : Nat) : ENNReal) / ((2 : ENNReal) ^ 256) := by
  have numerator :
      (deployedChallengePredictionFiberCoefficient : ENNReal) ≤
        ((36 * (2 ^ 228) : Nat) : ENNReal) := by
    exact_mod_cast
      deployed_challenge_prediction_coefficient_le_36_mul_two_pow_228
  exact
    (deployed_challenge_completion_probability_le_exact_coefficient plan).trans
      (ENNReal.div_le_div_right numerator ((2 : ENNReal) ^ 256))

/-! ## Arbitrary finite hidden adversary tape -/

def hiddenDeployedChallengeCompletionTree
    {HiddenTape : Type}
    (plan : HiddenTape → AdaptiveChallengeCompletionPlan deployedChallengeIds) :
    HiddenTape → CausalTargetTree Digest256
      (deployedChallengeIds.map challengeCompletionFiberCap) :=
  fun hidden => deployedChallengeCompletionTargetTree (plan hidden)

theorem hidden_deployed_challenge_completion_probability_le_exact_count
    {HiddenTape : Type} [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    (plan : HiddenTape → AdaptiveChallengeCompletionPlan deployedChallengeIds) :
    (hiddenTapeUniformFreshJointLaw hiddenLaw
        (deployedChallengeIds.map challengeCompletionFiberCap).length).toOuterMeasure
        (hiddenDependentCausalHitEvent
          (hiddenDeployedChallengeCompletionTree plan)) ≤
      ((deployedChallengePredictionFiberCoefficient *
          (2 ^ 256) ^ 35 : Nat) : ENNReal) /
        (((2 : ENNReal) ^ 256) ^ (35 + 1)) := by
  have bound := hidden_dependent_causal_tree_probability_le_exact_count
    hiddenLaw (hiddenDeployedChallengeCompletionTree plan)
  simpa only [deployed_challenge_completion_caps_sum,
    deployed_challenge_completion_caps_length, Nat.reduceSubDiff,
    Nat.reduceAdd] using bound

theorem hidden_deployed_challenge_completion_probability_le_exact_coefficient
    {HiddenTape : Type} [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    (plan : HiddenTape → AdaptiveChallengeCompletionPlan deployedChallengeIds) :
    (hiddenTapeUniformFreshJointLaw hiddenLaw
        (deployedChallengeIds.map challengeCompletionFiberCap).length).toOuterMeasure
        (hiddenDependentCausalHitEvent
          (hiddenDeployedChallengeCompletionTree plan)) ≤
      (deployedChallengePredictionFiberCoefficient : ENNReal) /
        ((2 : ENNReal) ^ 256) := by
  calc
    (hiddenTapeUniformFreshJointLaw hiddenLaw
        (deployedChallengeIds.map challengeCompletionFiberCap).length).toOuterMeasure
        (hiddenDependentCausalHitEvent
          (hiddenDeployedChallengeCompletionTree plan)) ≤
      ((deployedChallengePredictionFiberCoefficient *
          (2 ^ 256) ^ 35 : Nat) : ENNReal) /
        (((2 : ENNReal) ^ 256) ^ (35 + 1)) :=
      hidden_deployed_challenge_completion_probability_le_exact_count
        hiddenLaw plan
    _ = (deployedChallengePredictionFiberCoefficient : ENNReal) /
        ((2 : ENNReal) ^ 256) := by
      exact finite_exact_count_ratio_succ
        deployedChallengePredictionFiberCoefficient 35

theorem hidden_deployed_challenge_completion_probability_le_two_pow_228_fallback
    {HiddenTape : Type} [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    (plan : HiddenTape → AdaptiveChallengeCompletionPlan deployedChallengeIds) :
    (hiddenTapeUniformFreshJointLaw hiddenLaw
        (deployedChallengeIds.map challengeCompletionFiberCap).length).toOuterMeasure
        (hiddenDependentCausalHitEvent
          (hiddenDeployedChallengeCompletionTree plan)) ≤
      ((36 * (2 ^ 228) : Nat) : ENNReal) / ((2 : ENNReal) ^ 256) := by
  have numerator :
      (deployedChallengePredictionFiberCoefficient : ENNReal) ≤
        ((36 * (2 ^ 228) : Nat) : ENNReal) := by
    exact_mod_cast
      deployed_challenge_prediction_coefficient_le_36_mul_two_pow_228
  exact
    (hidden_deployed_challenge_completion_probability_le_exact_coefficient
      hiddenLaw plan).trans
      (ENNReal.div_le_div_right numerator ((2 : ENNReal) ^ 256))

#print axioms challenge_completion_target_finset_card_exact
#print axioms mem_challenge_completion_target_finset_iff
#print axioms optional_challenge_completion_targets_card_le_cap
#print axioms deployed_challenge_completion_probability_le_exact_count
#print axioms deployed_challenge_completion_probability_le_exact_coefficient
#print axioms deployed_challenge_completion_probability_le_two_pow_228_fallback
#print axioms hidden_deployed_challenge_completion_probability_le_exact_count
#print axioms hidden_deployed_challenge_completion_probability_le_exact_coefficient
#print axioms hidden_deployed_challenge_completion_probability_le_two_pow_228_fallback

end

end AspisK1.V7Tag73UnqueriedChallengeFiberProbability
