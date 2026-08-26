import AspisFormal.Pool.V7MerkleExtractedTreeCoverage
import AspisFormal.Pool.V7MerkleRawCollisionPredicate

/-!
# Deterministic closure of accepted V7 Merkle extraction

Once the causal graph has reconstructed both complete words, no later K1.2
failure is possible outside the one shared 208-bit collision event, provided
the production-supplied opening hash calls are present in that same universe.
The canonical path is derived from the extracted perfect tree; it is never
identified with the supplied path by assumption.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisPool.V7MerkleAcceptedExtractionClosure

open AspisPool.V7MerkleQueryGrammar
open AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerkleOpeningBinding
open AspisPool.V7MerkleRawCollisionPredicate
open AspisPool.V7MerkleAcceptedOpeningProjection
open AspisPool.V7MerkleExtractedSubtreeCommitment
open AspisPool.V7MerkleExtractedTreeCoverage

theorem disclosures_yield_no_projection_failure
    (words : ExtractedWords) (proof : TwoTreeOpeningProof)
    (projections : disclosuresAreProjections words proof) :
    firstProjectionFailure words (openingList proof) = none := by
  apply (firstProjectionFailure_none_iff words (openingList proof)).mpr
  intro opening openingIn
  simp only [openingList, List.mem_ofFn] at openingIn
  obtain ⟨ordinal, openingExact⟩ := openingIn
  subst opening
  exact projections ordinal

theorem finishExtraction_succeeds_of_roots_and_projections
    (truncateSha256 : RawHashInput → Digest208)
    (roots : Roots) (proof : TwoTreeOpeningProof) (words : ExtractedWords)
    (rootsMatch : completeWordsMatchRoots truncateSha256 words roots)
    (projections : disclosuresAreProjections words proof) :
    finishExtraction truncateSha256 roots proof words = .words words := by
  have noProjectionFailure :=
    disclosures_yield_no_projection_failure words proof projections
  have rootsAccepted :=
    (completeWordsMatchRootsB_eq_true_iff truncateSha256 words roots).mpr
      rootsMatch
  simp [finishExtraction, noProjectionFailure, rootsAccepted]

/-- Exact deterministic reduction used by the source-facing K1.2 theorem.
The only hypotheses not produced by the pure query-graph walk are literal
opening acceptance and coverage of the supplied production hash traces. -/
theorem extractV7Words_succeeds_of_complete_graph_and_covered_paths
    (truncateSha256 : RawHashInput → Digest208)
    (roots : Roots) (proof : TwoTreeOpeningProof)
    (orderedQueries : OrderedRawQueryLog) (words : ExtractedWords)
    (accepted : accepted_two_tree_openings truncateSha256 roots proof)
    (graphSuccess : extractCompleteWords truncateSha256 roots
      (deduplicateFirst orderedQueries) = .words words)
    (c1SuppliedCovered : ∀ ordinal : Fin disclosedQueryPairs,
      TraceIncludedInLog
        (openingInputTrace truncateSha256 (proof ordinal).position
          (.c1Leaf (proof ordinal).c1Value (proof ordinal).sharedSalt)
          (proof ordinal).c1Siblings)
        (collisionUniverse truncateSha256
          (deduplicateFirst orderedQueries)))
    (c2SuppliedCovered : ∀ ordinal : Fin disclosedQueryPairs,
      TraceIncludedInLog
        (openingInputTrace truncateSha256 (proof ordinal).position
          (.c2Leaf (proof ordinal).c2Value (proof ordinal).sharedSalt)
          (proof ordinal).c2Siblings)
        (collisionUniverse truncateSha256
          (deduplicateFirst orderedQueries)))
    (noCollision : ¬ RawLogTruncatedDigestCollision truncateSha256
      (collisionUniverse truncateSha256
        (deduplicateFirst orderedQueries))) :
    extractV7Words truncateSha256 roots proof orderedQueries = .words words ∧
      wordsMatchRootsAndAllAcceptedOpenings truncateSha256 words roots proof := by
  have coveredTrees := extractCompleteWords_success_yields_covered_trees
    truncateSha256 roots (deduplicateFirst orderedQueries) words graphSuccess
  obtain ⟨c1Canonical, c2Canonical⟩ :=
    covered_complete_trees_yield_all_canonical_openings truncateSha256 roots
      words (collisionUniverse truncateSha256
        (deduplicateFirst orderedQueries)) coveredTrees
  have projections := accepted_openings_are_projections_of_covered_paths
    truncateSha256 words roots proof
    (collisionUniverse truncateSha256 (deduplicateFirst orderedQueries))
    accepted (fun ordinal => c1Canonical (proof ordinal).position)
    (fun ordinal => c2Canonical (proof ordinal).position)
    c1SuppliedCovered c2SuppliedCovered noCollision
  have rootsMatch := extract_complete_words_success_matches_roots
    truncateSha256 roots (deduplicateFirst orderedQueries) words graphSuccess
  have finishSuccess := finishExtraction_succeeds_of_roots_and_projections
    truncateSha256 roots proof words rootsMatch projections
  have collisionFalse := (no_raw_truncated_collision_iff truncateSha256
    (collisionUniverse truncateSha256
      (deduplicateFirst orderedQueries))).mpr noCollision
  constructor
  · simp [extractV7Words, collisionFalse, graphSuccess, finishSuccess]
  · exact ⟨rootsMatch, projections⟩

#print axioms disclosures_yield_no_projection_failure
#print axioms finishExtraction_succeeds_of_roots_and_projections
#print axioms extractV7Words_succeeds_of_complete_graph_and_covered_paths

end AspisPool.V7MerkleAcceptedExtractionClosure
