import AspisFormal.Pool.V7MerkleCanonicalOpening

/-!
# Accepted Tag-73 openings are extracted-word projections or collisions

An independently committed complete word supplies its own canonical path.
Comparing that path with a verifier-accepted supplied path at the same public
position yields the disclosed leaf exactly, unless two explicit raw inputs in
the shared collision universe have the same 208-bit SHA prefix.

Trace-inclusion premises are deliberately separated.  K1.2's causal graph
proves coverage of canonical extracted paths; the Rust/Aeneas verifier bridge
proves coverage of supplied authentication paths.
-/

set_option autoImplicit false

namespace AspisPool.V7MerkleAcceptedOpeningProjection

open AspisPool.V7MerkleQueryGrammar
open AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerkleOpeningBinding
open AspisPool.V7MerkleCanonicalOpening

def C1CanonicalTraceCoverage
    (truncateSha256 : RawHashInput → Digest208)
    (words : List C1Leaf) (root : Digest208) (position : Position)
    (log : OrderedRawQueryLog) : Prop :=
  ∀ (leaf : C1Leaf) (siblings : SiblingPath),
    words[position.val]? = some leaf →
    foldPath truncateSha256 position (c1LeafDigest truncateSha256 leaf)
        siblings = root →
    TraceIncludedInLog
      (openingInputTrace truncateSha256 position
        (.c1Leaf leaf.value leaf.salt) siblings) log

def C2CanonicalTraceCoverage
    (truncateSha256 : RawHashInput → Digest208)
    (words : List C2Leaf) (root : Digest208) (position : Position)
    (log : OrderedRawQueryLog) : Prop :=
  ∀ (leaf : C2Leaf) (siblings : SiblingPath),
    words[position.val]? = some leaf →
    foldPath truncateSha256 position (c2LeafDigest truncateSha256 leaf)
        siblings = root →
    TraceIncludedInLog
      (openingInputTrace truncateSha256 position
        (.c2Leaf leaf.value leaf.salt) siblings) log

theorem c1_accepted_opening_is_projection_or_raw_collision
    (truncateSha256 : RawHashInput → Digest208)
    (words : List C1Leaf) (root : Digest208) (opening : PairedOpening)
    (log : OrderedRawQueryLog)
    (commitment : commitC1Word truncateSha256 words = some root)
    (accepted :
      foldPath truncateSha256 opening.position
          (c1DisclosedLeafDigest truncateSha256 opening)
          opening.c1Siblings = root)
    (canonicalCovered : C1CanonicalTraceCoverage truncateSha256 words root
      opening.position log)
    (suppliedCovered : TraceIncludedInLog
      (openingInputTrace truncateSha256 opening.position
        (.c1Leaf opening.c1Value opening.sharedSalt) opening.c1Siblings) log) :
    words[opening.position.val]? = some
        ⟨opening.c1Value, opening.sharedSalt⟩ ∨
      RawLogTruncatedDigestCollision truncateSha256 log := by
  obtain ⟨canonicalLeaf, canonicalSiblings, canonicalLeafAt,
      canonicalRoot⟩ :=
    commitTree_success_yields_canonical_opening truncateSha256
      (c1LeafDigest truncateSha256) words root opening.position
      (by simpa [commitC1Word] using commitment)
  let canonicalTyped : TypedPreimage :=
    .c1Leaf canonicalLeaf.value canonicalLeaf.salt
  let suppliedTyped : TypedPreimage :=
    .c1Leaf opening.c1Value opening.sharedSalt
  by_cases sameLeaf : canonicalTyped = suppliedTyped
  · left
    have leafExact : canonicalLeaf =
        ⟨opening.c1Value, opening.sharedSalt⟩ := by
      cases canonicalLeaf with
      | mk value salt =>
          simp [canonicalTyped, suppliedTyped] at sameLeaf
          rcases sameLeaf with ⟨rfl, rfl⟩
          rfl
    rw [leafExact] at canonicalLeafAt
    exact canonicalLeafAt
  · right
    have canonicalCoveredExact := canonicalCovered canonicalLeaf
      canonicalSiblings canonicalLeafAt canonicalRoot
    have sameRoot :
        foldPath truncateSha256 opening.position
            (truncateSha256 (serialize canonicalTyped)) canonicalSiblings =
          foldPath truncateSha256 opening.position
            (truncateSha256 (serialize suppliedTyped)) opening.c1Siblings := by
      simpa [canonicalTyped, suppliedTyped, c1LeafDigest,
        c1DisclosedLeafDigest] using canonicalRoot.trans accepted.symm
    exact same_position_distinct_typed_leaves_in_log_expose_collision
      truncateSha256 log opening.position canonicalTyped suppliedTyped
      canonicalSiblings opening.c1Siblings
      (by simpa [canonicalTyped] using canonicalCoveredExact)
      (by simpa [suppliedTyped] using suppliedCovered)
      sameLeaf sameRoot

theorem c2_accepted_opening_is_projection_or_raw_collision
    (truncateSha256 : RawHashInput → Digest208)
    (words : List C2Leaf) (root : Digest208) (opening : PairedOpening)
    (log : OrderedRawQueryLog)
    (commitment : commitC2Word truncateSha256 words = some root)
    (accepted :
      foldPath truncateSha256 opening.position
          (c2DisclosedLeafDigest truncateSha256 opening)
          opening.c2Siblings = root)
    (canonicalCovered : C2CanonicalTraceCoverage truncateSha256 words root
      opening.position log)
    (suppliedCovered : TraceIncludedInLog
      (openingInputTrace truncateSha256 opening.position
        (.c2Leaf opening.c2Value opening.sharedSalt) opening.c2Siblings) log) :
    words[opening.position.val]? = some
        ⟨opening.c2Value, opening.sharedSalt⟩ ∨
      RawLogTruncatedDigestCollision truncateSha256 log := by
  obtain ⟨canonicalLeaf, canonicalSiblings, canonicalLeafAt,
      canonicalRoot⟩ :=
    commitTree_success_yields_canonical_opening truncateSha256
      (c2LeafDigest truncateSha256) words root opening.position
      (by simpa [commitC2Word] using commitment)
  let canonicalTyped : TypedPreimage :=
    .c2Leaf canonicalLeaf.value canonicalLeaf.salt
  let suppliedTyped : TypedPreimage :=
    .c2Leaf opening.c2Value opening.sharedSalt
  by_cases sameLeaf : canonicalTyped = suppliedTyped
  · left
    have leafExact : canonicalLeaf =
        ⟨opening.c2Value, opening.sharedSalt⟩ := by
      cases canonicalLeaf with
      | mk value salt =>
          simp [canonicalTyped, suppliedTyped] at sameLeaf
          rcases sameLeaf with ⟨rfl, rfl⟩
          rfl
    rw [leafExact] at canonicalLeafAt
    exact canonicalLeafAt
  · right
    have canonicalCoveredExact := canonicalCovered canonicalLeaf
      canonicalSiblings canonicalLeafAt canonicalRoot
    have sameRoot :
        foldPath truncateSha256 opening.position
            (truncateSha256 (serialize canonicalTyped)) canonicalSiblings =
          foldPath truncateSha256 opening.position
            (truncateSha256 (serialize suppliedTyped)) opening.c2Siblings := by
      simpa [canonicalTyped, suppliedTyped, c2LeafDigest,
        c2DisclosedLeafDigest] using canonicalRoot.trans accepted.symm
    exact same_position_distinct_typed_leaves_in_log_expose_collision
      truncateSha256 log opening.position canonicalTyped suppliedTyped
      canonicalSiblings opening.c2Siblings
      (by simpa [canonicalTyped] using canonicalCoveredExact)
      (by simpa [suppliedTyped] using suppliedCovered)
      sameLeaf sameRoot

/-- Combined two-tree, all-sixteen conclusion.  The collision event is shared
across both typed trees rather than split into independent assumptions. -/
theorem accepted_openings_are_extracted_projections_outside_raw_collision
    (truncateSha256 : RawHashInput → Digest208)
    (words : ExtractedWords) (roots : Roots)
    (proof : TwoTreeOpeningProof) (log : OrderedRawQueryLog)
    (rootsMatch : completeWordsMatchRoots truncateSha256 words roots)
    (accepted : accepted_two_tree_openings truncateSha256 roots proof)
    (c1CanonicalCovered : ∀ ordinal : Fin disclosedQueryPairs,
      C1CanonicalTraceCoverage truncateSha256 words.c1 roots.c1
        (proof ordinal).position log)
    (c2CanonicalCovered : ∀ ordinal : Fin disclosedQueryPairs,
      C2CanonicalTraceCoverage truncateSha256 words.c2 roots.c2
        (proof ordinal).position log)
    (c1SuppliedCovered : ∀ ordinal : Fin disclosedQueryPairs,
      TraceIncludedInLog
        (openingInputTrace truncateSha256 (proof ordinal).position
          (.c1Leaf (proof ordinal).c1Value (proof ordinal).sharedSalt)
          (proof ordinal).c1Siblings) log)
    (c2SuppliedCovered : ∀ ordinal : Fin disclosedQueryPairs,
      TraceIncludedInLog
        (openingInputTrace truncateSha256 (proof ordinal).position
          (.c2Leaf (proof ordinal).c2Value (proof ordinal).sharedSalt)
          (proof ordinal).c2Siblings) log)
    (noCollision :
      ¬ RawLogTruncatedDigestCollision truncateSha256 log) :
    disclosuresAreProjections words proof := by
  intro ordinal
  have acceptedAt := accepted.2 ordinal
  have c1Projection :=
    (c1_accepted_opening_is_projection_or_raw_collision truncateSha256
      words.c1 roots.c1 (proof ordinal) log rootsMatch.2.2.1
      acceptedAt.1 (c1CanonicalCovered ordinal)
      (c1SuppliedCovered ordinal)).resolve_right noCollision
  have c2Projection :=
    (c2_accepted_opening_is_projection_or_raw_collision truncateSha256
      words.c2 roots.c2 (proof ordinal) log rootsMatch.2.2.2
      acceptedAt.2 (c2CanonicalCovered ordinal)
      (c2SuppliedCovered ordinal)).resolve_right noCollision
  exact ⟨c1Projection, c2Projection⟩

#print axioms c1_accepted_opening_is_projection_or_raw_collision
#print axioms c2_accepted_opening_is_projection_or_raw_collision
#print axioms
  accepted_openings_are_extracted_projections_outside_raw_collision

end AspisPool.V7MerkleAcceptedOpeningProjection
