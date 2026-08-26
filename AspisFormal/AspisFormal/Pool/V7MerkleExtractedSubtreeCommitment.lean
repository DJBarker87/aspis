import AspisFormal.Pool.V7MerkleParserRoundtrip

/-!
# Commitment closure for extracted Tag-73 K1.2 subtrees

Successful query-graph traversal must reconstruct a word whose independent
commitment is the digest carried by the traversed edge.  This module proves
that invariant for both typed trees, including canonical-default subtrees.
It uses the exact parser round trip rather than assuming parsed raw bytes are
the deployed serialization.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisPool.V7MerkleExtractedSubtreeCommitment

open AspisPool.V7MerkleQueryGrammar
open AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerkleParserRoundtrip

/-! ## Canonical-default commitments -/

theorem commit_c1_default_subtree
    (truncateSha256 : RawHashInput → Digest208) : ∀ height : Nat,
    commitTree truncateSha256 (c1LeafDigest truncateSha256) height
        (List.replicate (2 ^ height) defaultC1Leaf) =
      some (defaultC1SubtreeDigest truncateSha256 height) := by
  intro height
  induction height with
  | zero =>
      simp [commitTree, defaultC1SubtreeDigest, c1LeafDigest]
  | succ height inductionHypothesis =>
      have powerPositive : 0 < 2 ^ height := pow_pos (by norm_num) _
      have powerLe : 2 ^ height ≤ 2 ^ height * 2 := by omega
      have powerSub : 2 ^ height * 2 - 2 ^ height = 2 ^ height := by omega
      simp [commitTree, defaultC1SubtreeDigest, inductionHypothesis,
        pow_succ, Nat.min_eq_left powerLe, powerSub]

theorem commit_c2_default_subtree
    (truncateSha256 : RawHashInput → Digest208) : ∀ height : Nat,
    commitTree truncateSha256 (c2LeafDigest truncateSha256) height
        (List.replicate (2 ^ height) defaultC2Leaf) =
      some (defaultC2SubtreeDigest truncateSha256 height) := by
  intro height
  induction height with
  | zero =>
      simp [commitTree, defaultC2SubtreeDigest, c2LeafDigest]
  | succ height inductionHypothesis =>
      have powerPositive : 0 < 2 ^ height := pow_pos (by norm_num) _
      have powerLe : 2 ^ height ≤ 2 ^ height * 2 := by omega
      have powerSub : 2 ^ height * 2 - 2 ^ height = 2 ^ height := by omega
      simp [commitTree, defaultC2SubtreeDigest, inductionHypothesis,
        pow_succ, Nat.min_eq_left powerLe, powerSub]

/-! ## C1 traversal invariant -/

def c1ChildResult (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) (height : Nat) (parentQueryIndex : Nat)
    (child : Digest208) : SubtreeResult C1Leaf :=
  if child = defaultC1SubtreeDigest truncateSha256 height then
    .leaves (List.replicate (2 ^ height) defaultC1Leaf)
  else
    match classifyReference truncateSha256 child parentQueryIndex log with
    | .earlier childIndex =>
        extractC1Subtree truncateSha256 log height child childIndex
    | .forward _ => .failure .forwardReference
    | .missing => .failure .missingPreimageQuery

theorem c1_child_result_commits
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) (height : Nat)
    (inductionHypothesis : ∀ (expectedDigest : Digest208)
      (queryIndex : Nat) (leaves : List C1Leaf),
      extractC1Subtree truncateSha256 log height expectedDigest queryIndex =
          .leaves leaves →
        leaves.length = 2 ^ height ∧
          commitTree truncateSha256 (c1LeafDigest truncateSha256) height
            leaves = some expectedDigest)
    (parentQueryIndex : Nat) (child : Digest208) (leaves : List C1Leaf)
    (success : c1ChildResult truncateSha256 log height parentQueryIndex child =
      .leaves leaves) :
    leaves.length = 2 ^ height ∧
      commitTree truncateSha256 (c1LeafDigest truncateSha256) height leaves =
        some child := by
  unfold c1ChildResult at success
  split at success
  · rename_i childDefault
    simp only [SubtreeResult.leaves.injEq] at success
    subst leaves
    exact ⟨by simp, by simpa [childDefault] using
      commit_c1_default_subtree truncateSha256 height⟩
  · split at success
    · rename_i childIndex reference
      exact inductionHypothesis child childIndex leaves success
    · contradiction
    · contradiction

theorem extracted_c1_subtree_commits_to_expected
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) : ∀
    (height : Nat) (expectedDigest : Digest208) (queryIndex : Nat)
    (leaves : List C1Leaf),
    extractC1Subtree truncateSha256 log height expectedDigest queryIndex =
        .leaves leaves →
      leaves.length = 2 ^ height ∧
        commitTree truncateSha256 (c1LeafDigest truncateSha256) height leaves =
          some expectedDigest := by
  intro height
  induction height with
  | zero =>
      intro expectedDigest queryIndex leaves success
      cases inputAt : log[queryIndex]? with
      | none => simp [extractC1Subtree, inputAt] at success
      | some input =>
          by_cases answerExact : truncateSha256 input = expectedDigest
          · cases parsed : parseTypedPreimage input with
            | none =>
                simp [extractC1Subtree, inputAt, answerExact, parsed] at success
            | some typed =>
                cases typed with
                | c1Leaf value salt =>
                    simp [extractC1Subtree, inputAt, answerExact, parsed] at success
                    subst leaves
                    have serialized := serialize_parse_typed_preimage input
                      (.c1Leaf value salt) parsed
                    exact ⟨by simp, by
                      simp [commitTree, c1LeafDigest, serialized, answerExact]⟩
                | c2Leaf value salt =>
                    simp [extractC1Subtree, inputAt, answerExact, parsed] at success
                | node left right =>
                    simp [extractC1Subtree, inputAt, answerExact, parsed] at success
          · simp [extractC1Subtree, inputAt, answerExact] at success
  | succ height inductionHypothesis =>
      intro expectedDigest queryIndex leaves success
      cases inputAt : log[queryIndex]? with
      | none => simp [extractC1Subtree, inputAt] at success
      | some input =>
          by_cases answerExact : truncateSha256 input = expectedDigest
          · cases parsed : parseTypedPreimage input with
            | none =>
                simp [extractC1Subtree, inputAt, answerExact, parsed] at success
            | some typed =>
                cases typed with
                | c1Leaf value salt =>
                    simp [extractC1Subtree, inputAt, answerExact, parsed] at success
                | c2Leaf value salt =>
                    simp [extractC1Subtree, inputAt, answerExact, parsed] at success
                | node left right =>
                    simp only [extractC1Subtree, inputAt, answerExact, parsed,
                      ↓reduceIte] at success
                    change
                      (match c1ChildResult truncateSha256 log height queryIndex
                          left with
                      | SubtreeResult.failure reason =>
                          SubtreeResult.failure reason
                      | SubtreeResult.leaves leftLeaves =>
                          match c1ChildResult truncateSha256 log height
                              queryIndex right with
                          | SubtreeResult.failure reason =>
                              SubtreeResult.failure reason
                          | SubtreeResult.leaves rightLeaves =>
                              SubtreeResult.leaves
                                (leftLeaves ++ rightLeaves)) =
                        SubtreeResult.leaves leaves at success
                    cases leftResult : c1ChildResult truncateSha256 log height
                        queryIndex left with
                    | failure reason => simp [leftResult] at success
                    | leaves leftLeaves =>
                        cases rightResult : c1ChildResult truncateSha256 log
                            height queryIndex right with
                        | failure reason =>
                            simp [leftResult, rightResult] at success
                        | leaves rightLeaves =>
                            simp [leftResult, rightResult] at success
                            subst leaves
                            obtain ⟨leftLength, leftCommit⟩ :=
                              c1_child_result_commits truncateSha256 log height
                                inductionHypothesis queryIndex left leftLeaves
                                  leftResult
                            obtain ⟨rightLength, rightCommit⟩ :=
                              c1_child_result_commits truncateSha256 log height
                                inductionHypothesis queryIndex right rightLeaves
                                  rightResult
                            have serialized := serialize_parse_typed_preimage
                              input (.node left right) parsed
                            have nodeAnswer :
                                nodeDigest truncateSha256 left right =
                                  expectedDigest := by
                              rw [nodeDigest, serialized]
                              exact answerExact
                            constructor
                            · simp [leftLength, rightLength, pow_succ]
                              omega
                            · simp [commitTree, leftLength, rightLength,
                                leftCommit, rightCommit, pow_succ, nodeAnswer]
                              omega
          · simp [extractC1Subtree, inputAt, answerExact] at success

/-! The C2 invariant has the same graph shape and the distinct typed leaf. -/

def c2ChildResult (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) (height : Nat) (parentQueryIndex : Nat)
    (child : Digest208) : SubtreeResult C2Leaf :=
  if child = defaultC2SubtreeDigest truncateSha256 height then
    .leaves (List.replicate (2 ^ height) defaultC2Leaf)
  else
    match classifyReference truncateSha256 child parentQueryIndex log with
    | .earlier childIndex =>
        extractC2Subtree truncateSha256 log height child childIndex
    | .forward _ => .failure .forwardReference
    | .missing => .failure .missingPreimageQuery

theorem c2_child_result_commits
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) (height : Nat)
    (inductionHypothesis : ∀ (expectedDigest : Digest208)
      (queryIndex : Nat) (leaves : List C2Leaf),
      extractC2Subtree truncateSha256 log height expectedDigest queryIndex =
          .leaves leaves →
        leaves.length = 2 ^ height ∧
          commitTree truncateSha256 (c2LeafDigest truncateSha256) height
            leaves = some expectedDigest)
    (parentQueryIndex : Nat) (child : Digest208) (leaves : List C2Leaf)
    (success : c2ChildResult truncateSha256 log height parentQueryIndex child =
      .leaves leaves) :
    leaves.length = 2 ^ height ∧
      commitTree truncateSha256 (c2LeafDigest truncateSha256) height leaves =
        some child := by
  unfold c2ChildResult at success
  split at success
  · rename_i childDefault
    simp only [SubtreeResult.leaves.injEq] at success
    subst leaves
    exact ⟨by simp, by simpa [childDefault] using
      commit_c2_default_subtree truncateSha256 height⟩
  · split at success
    · rename_i childIndex reference
      exact inductionHypothesis child childIndex leaves success
    · contradiction
    · contradiction

theorem extracted_c2_subtree_commits_to_expected
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) : ∀
    (height : Nat) (expectedDigest : Digest208) (queryIndex : Nat)
    (leaves : List C2Leaf),
    extractC2Subtree truncateSha256 log height expectedDigest queryIndex =
        .leaves leaves →
      leaves.length = 2 ^ height ∧
        commitTree truncateSha256 (c2LeafDigest truncateSha256) height leaves =
          some expectedDigest := by
  intro height
  induction height with
  | zero =>
      intro expectedDigest queryIndex leaves success
      cases inputAt : log[queryIndex]? with
      | none => simp [extractC2Subtree, inputAt] at success
      | some input =>
          by_cases answerExact : truncateSha256 input = expectedDigest
          · cases parsed : parseTypedPreimage input with
            | none =>
                simp [extractC2Subtree, inputAt, answerExact, parsed] at success
            | some typed =>
                cases typed with
                | c1Leaf value salt =>
                    simp [extractC2Subtree, inputAt, answerExact, parsed] at success
                | c2Leaf value salt =>
                    simp [extractC2Subtree, inputAt, answerExact, parsed] at success
                    subst leaves
                    have serialized := serialize_parse_typed_preimage input
                      (.c2Leaf value salt) parsed
                    exact ⟨by simp, by
                      simp [commitTree, c2LeafDigest, serialized, answerExact]⟩
                | node left right =>
                    simp [extractC2Subtree, inputAt, answerExact, parsed] at success
          · simp [extractC2Subtree, inputAt, answerExact] at success
  | succ height inductionHypothesis =>
      intro expectedDigest queryIndex leaves success
      cases inputAt : log[queryIndex]? with
      | none => simp [extractC2Subtree, inputAt] at success
      | some input =>
          by_cases answerExact : truncateSha256 input = expectedDigest
          · cases parsed : parseTypedPreimage input with
            | none =>
                simp [extractC2Subtree, inputAt, answerExact, parsed] at success
            | some typed =>
                cases typed with
                | c1Leaf value salt =>
                    simp [extractC2Subtree, inputAt, answerExact, parsed] at success
                | c2Leaf value salt =>
                    simp [extractC2Subtree, inputAt, answerExact, parsed] at success
                | node left right =>
                    simp only [extractC2Subtree, inputAt, answerExact, parsed,
                      ↓reduceIte] at success
                    change
                      (match c2ChildResult truncateSha256 log height queryIndex
                          left with
                      | SubtreeResult.failure reason =>
                          SubtreeResult.failure reason
                      | SubtreeResult.leaves leftLeaves =>
                          match c2ChildResult truncateSha256 log height
                              queryIndex right with
                          | SubtreeResult.failure reason =>
                              SubtreeResult.failure reason
                          | SubtreeResult.leaves rightLeaves =>
                              SubtreeResult.leaves
                                (leftLeaves ++ rightLeaves)) =
                        SubtreeResult.leaves leaves at success
                    cases leftResult : c2ChildResult truncateSha256 log height
                        queryIndex left with
                    | failure reason => simp [leftResult] at success
                    | leaves leftLeaves =>
                        cases rightResult : c2ChildResult truncateSha256 log
                            height queryIndex right with
                        | failure reason =>
                            simp [leftResult, rightResult] at success
                        | leaves rightLeaves =>
                            simp [leftResult, rightResult] at success
                            subst leaves
                            obtain ⟨leftLength, leftCommit⟩ :=
                              c2_child_result_commits truncateSha256 log height
                                inductionHypothesis queryIndex left leftLeaves
                                  leftResult
                            obtain ⟨rightLength, rightCommit⟩ :=
                              c2_child_result_commits truncateSha256 log height
                                inductionHypothesis queryIndex right rightLeaves
                                  rightResult
                            have serialized := serialize_parse_typed_preimage
                              input (.node left right) parsed
                            have nodeAnswer :
                                nodeDigest truncateSha256 left right =
                                  expectedDigest := by
                              rw [nodeDigest, serialized]
                              exact answerExact
                            constructor
                            · simp [leftLength, rightLength, pow_succ]
                              omega
                            · simp [commitTree, leftLength, rightLength,
                                leftCommit, rightCommit, pow_succ, nodeAnswer]
                              omega
          · simp [extractC2Subtree, inputAt, answerExact] at success

/-! ## Complete two-tree closure -/

theorem extract_complete_words_success_matches_roots
    (truncateSha256 : RawHashInput → Digest208)
    (roots : Roots) (log : OrderedRawQueryLog) (words : ExtractedWords)
    (success : extractCompleteWords truncateSha256 roots log = .words words) :
    completeWordsMatchRoots truncateSha256 words roots := by
  obtain ⟨c1RootIndex, c2RootIndex, _c1RootQuery, _c2RootQuery,
      c1Extraction, c2Extraction⟩ :=
    extractCompleteWords_success_yields_root_queries
      truncateSha256 roots log words success
  obtain ⟨c1Length, c1Commitment⟩ :=
    extracted_c1_subtree_commits_to_expected truncateSha256 log treeDepth
      roots.c1 c1RootIndex words.c1 c1Extraction
  obtain ⟨c2Length, c2Commitment⟩ :=
    extracted_c2_subtree_commits_to_expected truncateSha256 log treeDepth
      roots.c2 c2RootIndex words.c2 c2Extraction
  exact ⟨c1Length, c2Length,
    by simpa [commitC1Word] using c1Commitment,
    by simpa [commitC2Word] using c2Commitment⟩

#print axioms commit_c1_default_subtree
#print axioms commit_c2_default_subtree
#print axioms extracted_c1_subtree_commits_to_expected
#print axioms extracted_c2_subtree_commits_to_expected
#print axioms extract_complete_words_success_matches_roots

end AspisPool.V7MerkleExtractedSubtreeCommitment
