import AspisFormal.Pool.V7MerklePartialPathExtractor

/-!
# Prefix-locality of first-unresolved Merkle targets

The partial-path classifier receives a total hash function, but its
first-unresolved traversal evaluates that function only on inputs already in
the supplied prefix log.  This module makes that locality exact: any two hash
views agreeing on the log produce the same resolver, first-unresolved target,
and complete two-tree target set.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisPool.V7MerklePrefixTargetCongruence

open AspisPool.V7MerkleQueryGrammar
open AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerklePartialPathExtractor

theorem resolveInput_eq_of_agree_on_log
    (left right : RawHashInput → Digest208)
    (log : OrderedRawQueryLog)
    (agree : ∀ input ∈ log, left input = right input)
    (target : Digest208) :
    resolveInput left target log = resolveInput right target log := by
  induction log with
  | nil => rfl
  | cons head tail ih =>
      have headAgree : left head = right head := agree head (by simp)
      have tailAgree : ∀ input ∈ tail, left input = right input := by
        intro input member
        exact agree input (by simp [member])
      simp only [resolveInput, List.find?_cons]
      rw [headAgree]
      by_cases hit : right head = target
      · simp [hit]
      · simpa [resolveInput, hit] using ih tailAgree

theorem firstUnresolvedTarget_eq_of_agree_on_log
    {Leaf : Type} (parseLeaf : RawHashInput → Option Leaf)
    (left right : RawHashInput → Digest208)
    (log : OrderedRawQueryLog)
    (agree : ∀ input ∈ log, left input = right input) :
    ∀ (height : Nat) (target : Digest208) (position : Nat),
      firstUnresolvedTarget parseLeaf left log height target position =
        firstUnresolvedTarget parseLeaf right log height target position := by
  intro height
  induction height with
  | zero =>
      intro target position
      have resolved := resolveInput_eq_of_agree_on_log left right log agree
        target
      simp only [firstUnresolvedTarget]
      rw [resolved]
  | succ height ih =>
      intro target position
      have resolved := resolveInput_eq_of_agree_on_log left right log agree
        target
      simp only [firstUnresolvedTarget]
      rw [resolved]
      cases inputResult : resolveInput right target log with
      | none => rfl
      | some input =>
          cases typedResult : parseTypedPreimage input with
          | none => simp [typedResult]
          | some typed =>
              cases typed with
              | c1Leaf value salt => simp [typedResult]
              | c2Leaf value salt => simp [typedResult]
              | node childLeft childRight =>
                  cases direction : position.testBit height <;>
                    simp [typedResult, direction, ih]

theorem prefixResolutionTargetSet_eq_of_agree_on_log
    (left right : RawHashInput → Digest208)
    (log : OrderedRawQueryLog)
    (agree : ∀ input ∈ log, left input = right input)
    (roots : Roots) (proof : TwoTreeOpeningProof) :
    prefixResolutionTargetSet left log roots proof =
      prefixResolutionTargetSet right log roots proof := by
  have c1 :
      (fun ordinal : Fin disclosedQueryPairs =>
          firstUnresolvedC1Target left log roots.c1
            (proof ordinal).position) =
        (fun ordinal : Fin disclosedQueryPairs =>
          firstUnresolvedC1Target right log roots.c1
            (proof ordinal).position) := by
    funext ordinal
    exact firstUnresolvedTarget_eq_of_agree_on_log parseC1Leaf left right log
      agree treeDepth roots.c1 (proof ordinal).position.val
  have c2 :
      (fun ordinal : Fin disclosedQueryPairs =>
          firstUnresolvedC2Target left log roots.c2
            (proof ordinal).position) =
        (fun ordinal : Fin disclosedQueryPairs =>
          firstUnresolvedC2Target right log roots.c2
            (proof ordinal).position) := by
    funext ordinal
    exact firstUnresolvedTarget_eq_of_agree_on_log parseC2Leaf left right log
      agree treeDepth roots.c2 (proof ordinal).position.val
  unfold prefixResolutionTargetSet prefixResolutionTargetList
  rw [c1, c2]

#print axioms resolveInput_eq_of_agree_on_log
#print axioms firstUnresolvedTarget_eq_of_agree_on_log
#print axioms prefixResolutionTargetSet_eq_of_agree_on_log

end AspisPool.V7MerklePrefixTargetCongruence
