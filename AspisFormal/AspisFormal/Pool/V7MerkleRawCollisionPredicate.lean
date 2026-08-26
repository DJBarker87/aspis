import AspisFormal.Pool.V7MerkleQueryExtractor

/-!
# Executable/raw collision equivalence for Tag-73 K1.2

The deployed K1.2 extractor branches on a Boolean scan of the combined raw
SHA log.  Probability accounting uses the corresponding existential event.
This module proves that those are exactly the same event, including
collisions involving malformed or cross-tree inputs.
-/

set_option autoImplicit false

namespace AspisPool.V7MerkleRawCollisionPredicate

open AspisPool.V7MerkleQueryGrammar
open AspisPool.V7MerkleQueryExtractor

theorem has_raw_truncated_collision_iff
    (truncateSha256 : RawHashInput → Digest208) :
    ∀ log : OrderedRawQueryLog,
      hasRawTruncatedCollision truncateSha256 log = true ↔
        RawLogTruncatedDigestCollision truncateSha256 log := by
  intro log
  induction log with
  | nil => simp [hasRawTruncatedCollision, RawLogTruncatedDigestCollision]
  | cons input rest inductionHypothesis =>
      simp only [hasRawTruncatedCollision, Bool.or_eq_true,
        List.any_eq_true, decide_eq_true_eq, inductionHypothesis]
      constructor
      · rintro (⟨other, otherIn, inputNe, digestEqual⟩ | collisionInRest)
        · exact ⟨input, by simp, other, by simp [otherIn], inputNe, digestEqual⟩
        · rcases collisionInRest with
            ⟨left, leftIn, right, rightIn, distinct, digestEqual⟩
          exact ⟨left, by simp [leftIn], right, by simp [rightIn], distinct,
            digestEqual⟩
      · rintro ⟨left, leftIn, right, rightIn, distinct, digestEqual⟩
        simp only [List.mem_cons] at leftIn rightIn
        rcases leftIn with rfl | leftIn
        · rcases rightIn with rfl | rightIn
          · exact False.elim (distinct rfl)
          · exact Or.inl ⟨right, rightIn, distinct, digestEqual⟩
        · rcases rightIn with rfl | rightIn
          · exact Or.inl ⟨left, leftIn, Ne.symm distinct, digestEqual.symm⟩
          · exact Or.inr ⟨left, leftIn, right, rightIn, distinct, digestEqual⟩

theorem no_raw_truncated_collision_iff
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) :
    hasRawTruncatedCollision truncateSha256 log = false ↔
      ¬ RawLogTruncatedDigestCollision truncateSha256 log := by
  rw [← has_raw_truncated_collision_iff truncateSha256 log]
  exact Bool.eq_false_iff

#print axioms has_raw_truncated_collision_iff
#print axioms no_raw_truncated_collision_iff

end AspisPool.V7MerkleRawCollisionPredicate
