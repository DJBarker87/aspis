import AspisFormal.K1.V7Tag73AdaptiveLazyOracle
import AspisFormal.K1.V7Tag73ExactCompilerResources
import AspisFormal.Pool.V7MerkleQueryExtractor

/-!
# Exact shared-208-bit collision accounting for Tag-73 K1.2

This module proves the collision part of the K1.2 random-oracle ledger from
finite counting.  It deliberately does not claim that every K1.2 extraction
failure is a collision: the missing-query, forward-reference and guessed-root
subclasses still need their causal injection into a target tree.

The accounting is shared across both typed Merkle trees and every other call
to the same SHA-256 oracle.  In particular, the verifier's 468 typed-tree
calls are added to the exact K1.6 full-output call cap, rather than being
treated as an independent oracle.  The extractor also evaluates nineteen
canonical-default inputs per tree, so its collision universe has exactly 38
additional input slots before deduplication.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73K12Merkle208CollisionProbability

open MeasureTheory
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73ExactCompilerResources
open AspisPool.V7MerkleQueryGrammar
open AspisPool.V7MerkleQueryExtractor

noncomputable section

/-! ## Exact 208-bit output cardinality -/

theorem merkle_byte_cardinality :
    Fintype.card Byte = 2 ^ 8 := by
  norm_num [Byte]

theorem merkle_digest208_cardinality :
    Fintype.card Digest208 = 2 ^ 208 := by
  norm_num [Digest208, Byte]

/-! ## Exact canonical-default inventory -/

theorem default_c1_subtree_inputs_length
    (truncateSha256 : RawHashInput → Digest208) :
    ∀ height : Nat,
      (defaultC1SubtreeInputs truncateSha256 height).length = height + 1 := by
  intro height
  induction height with
  | zero => simp [defaultC1SubtreeInputs]
  | succ height inductionHypothesis =>
      simp [defaultC1SubtreeInputs, inductionHypothesis]

theorem default_c2_subtree_inputs_length
    (truncateSha256 : RawHashInput → Digest208) :
    ∀ height : Nat,
      (defaultC2SubtreeInputs truncateSha256 height).length = height + 1 := by
  intro height
  induction height with
  | zero => simp [defaultC2SubtreeInputs]
  | succ height inductionHypothesis =>
      simp [defaultC2SubtreeInputs, inductionHypothesis]

theorem two_tree_default_input_slots_exact
    (truncateSha256 : RawHashInput → Digest208) :
    (defaultC1SubtreeInputs truncateSha256 treeDepth).length +
        (defaultC2SubtreeInputs truncateSha256 treeDepth).length = 38 := by
  rw [default_c1_subtree_inputs_length,
    default_c2_subtree_inputs_length]
  norm_num [treeDepth]

theorem deduplicateFirstAux_length_le
    (seen : List RawHashInput) : ∀ log : OrderedRawQueryLog,
    (deduplicateFirstAux seen log).length ≤ log.length := by
  intro log
  induction log generalizing seen with
  | nil => simp [deduplicateFirstAux]
  | cons input rest inductionHypothesis =>
      simp only [deduplicateFirstAux]
      split
      · exact (inductionHypothesis seen).trans (Nat.le_succ _)
      · simp only [List.length_cons]
        exact Nat.succ_le_succ (inductionHypothesis (input :: seen))

theorem deduplicateFirst_length_le (log : OrderedRawQueryLog) :
    (deduplicateFirst log).length ≤ log.length := by
  exact deduplicateFirstAux_length_le [] log

/-- The extractor's combined two-tree collision universe has at most the
shared raw-log length plus exactly 38 canonical-default slots.  Cross-tree and
cross-grammar collisions remain in this one universe. -/
theorem collision_universe_length_le_shared_log_add_thirty_eight
    (truncateSha256 : RawHashInput → Digest208)
    (sharedLog : OrderedRawQueryLog) :
    (collisionUniverse truncateSha256 sharedLog).length ≤
      sharedLog.length + 38 := by
  unfold collisionUniverse
  calc
    (deduplicateFirst
        (sharedLog ++ defaultC1SubtreeInputs truncateSha256 treeDepth ++
          defaultC2SubtreeInputs truncateSha256 treeDepth)).length ≤
        (sharedLog ++ defaultC1SubtreeInputs truncateSha256 treeDepth ++
          defaultC2SubtreeInputs truncateSha256 treeDepth).length :=
      deduplicateFirst_length_le _
    _ = sharedLog.length + 38 := by
      simp only [List.length_append]
      rw [default_c1_subtree_inputs_length,
        default_c2_subtree_inputs_length]
      norm_num [treeDepth]

theorem classifier_collision_universe_length_le_ordered_log_add_thirty_eight
    (truncateSha256 : RawHashInput → Digest208)
    (orderedQueries : OrderedRawQueryLog) :
    (collisionUniverse truncateSha256
        (deduplicateFirst orderedQueries)).length ≤
      orderedQueries.length + 38 := by
  calc
    (collisionUniverse truncateSha256
        (deduplicateFirst orderedQueries)).length ≤
      (deduplicateFirst orderedQueries).length + 38 :=
        collision_universe_length_le_shared_log_add_thirty_eight _ _
    _ ≤ orderedQueries.length + 38 := by
      exact Nat.add_le_add_right (deduplicateFirst_length_le _) 38

/-! ## One shared all-call resource cap -/

/-- All SHA calls visible to the K1.2 prefix projection.  `G` already counts
the adversary, transcript and restoration calls.  Every initial/replayed
verifier additionally contributes at most 468 typed-tree calls. -/
def globalSharedShaCallCap
    (parameters : ExactCompilerResourceParameters) : Nat :=
  globalFull256OracleCallCap parameters +
    (parameters.forkRequestCap + 1) * deployedTypedMerkleVerifierCallCap

theorem global_shared_sha_call_cap_expanded
    (parameters : ExactCompilerResourceParameters) :
    globalSharedShaCallCap parameters =
      parameters.q1ShaCallCap + 1511 +
        parameters.forkRequestCap *
          (2 * parameters.q1ShaCallCap + 1511) +
        (parameters.forkRequestCap + 1) * 468 := by
  rfl

/-- Resource ceiling for all shared SHA inputs plus both canonical-default
chains evaluated by the deterministic K1.2 extractor. -/
def k12CollisionUniverseExposureCap
    (parameters : ExactCompilerResourceParameters) : Nat :=
  globalSharedShaCallCap parameters + 38

theorem k12_collision_universe_exposure_cap_expanded
    (parameters : ExactCompilerResourceParameters) :
    k12CollisionUniverseExposureCap parameters =
      parameters.q1ShaCallCap + 1511 +
        parameters.forkRequestCap *
          (2 * parameters.q1ShaCallCap + 1511) +
        (parameters.forkRequestCap + 1) * 468 + 38 := by
  rfl

/-! ## First-principles adaptive prefix-collision law -/

def prefixCollisionTargetTreeFrom (step remaining : Nat)
    (seen : Finset Digest208) (seenCardLe : seen.card ≤ step) :
    CausalTargetTree Digest208 (List.range' step remaining) := by
  induction remaining generalizing step seen with
  | zero => exact .done
  | succ remaining inductionHypothesis =>
      rw [List.range'_succ]
      exact .step seen seenCardLe fun output =>
        inductionHypothesis (step + 1) (insert output seen)
          ((Finset.card_insert_le output seen).trans
            (Nat.add_le_add_right seenCardLe 1))

def prefixCollisionTargetTree (freshExposures : Nat) :
    CausalTargetTree Digest208 (List.range' 0 freshExposures) :=
  prefixCollisionTargetTreeFrom 0 freshExposures ∅ (by simp)

theorem prefix_collision_caps_sum_exact (freshExposures : Nat) :
    (List.range' 0 freshExposures).sum = freshExposures.choose 2 := by
  rw [List.sum_range', Nat.choose_two_right]
  simp

theorem prefix_collision_tree_hit_count_le_choose_two
    (freshExposures : Nat) :
    causalHitCount (prefixCollisionTargetTree freshExposures) ≤
      freshExposures.choose 2 *
        (2 ^ 208) ^ (freshExposures - 1) := by
  have bound := causal_hit_count_le_target_caps
    (prefixCollisionTargetTree freshExposures)
  rw [prefix_collision_caps_sum_exact,
    merkle_digest208_cardinality] at bound
  simp only [List.length_range'] at bound
  exact bound

noncomputable def uniformMerkleDigest208FreshTape (steps : Nat) :
    PMF (FreshAnswerTape Digest208 steps) :=
  PMF.uniformOfFintype (FreshAnswerTape Digest208 steps)

theorem uniform_merkle_digest208_collision_probability_eq
    (freshExposures : Nat) :
    (uniformMerkleDigest208FreshTape
        (List.range' 0 freshExposures).length).toOuterMeasure
        (causalHitEvent (prefixCollisionTargetTree freshExposures)) =
      (causalHitCount (prefixCollisionTargetTree freshExposures) : ENNReal) /
        (((2 : ENNReal) ^ 208) ^ freshExposures) := by
  classical
  unfold uniformMerkleDigest208FreshTape
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  simp only [List.length_range']
  change
    (causalHitCount (prefixCollisionTargetTree freshExposures) : ENNReal) /
        (Fintype.card (FreshAnswerTape Digest208 freshExposures) : ENNReal) = _
  rw [fresh_answer_tape_card, merkle_digest208_cardinality]
  norm_num

/-- Exact-count birthday bound for the shared 208-bit output stream.  This
form also handles zero exposures without a cancellation side condition. -/
theorem uniform_merkle_digest208_collision_probability_le_exact_count
    (freshExposures : Nat) :
    (uniformMerkleDigest208FreshTape
        (List.range' 0 freshExposures).length).toOuterMeasure
        (causalHitEvent (prefixCollisionTargetTree freshExposures)) ≤
      ((freshExposures.choose 2 *
          (2 ^ 208) ^ (freshExposures - 1) : Nat) : ENNReal) /
        (((2 : ENNReal) ^ 208) ^ freshExposures) := by
  rw [uniform_merkle_digest208_collision_probability_eq]
  apply ENNReal.div_le_div_right
  exact_mod_cast prefix_collision_tree_hit_count_le_choose_two freshExposures

#print axioms merkle_digest208_cardinality
#print axioms two_tree_default_input_slots_exact
#print axioms collision_universe_length_le_shared_log_add_thirty_eight
#print axioms global_shared_sha_call_cap_expanded
#print axioms prefix_collision_tree_hit_count_le_choose_two
#print axioms uniform_merkle_digest208_collision_probability_le_exact_count

end

end AspisK1.V7Tag73K12Merkle208CollisionProbability
