import AspisFormal.K1.V7Tag73ExactFixedK12MerkleClassifier
import AspisFormal.Pool.V7MerkleExtractedTreeCoverage
import AspisFormal.Pool.V7MerkleRawCollisionPredicate

/-!
# Covered deterministic output of the exact fixed-run K1.2 classifier

The literal scheduler classifier's success branch now carries more than an
independent recommitment equation.  Its causal extraction constructs both
perfect typed trees, covers every canonical leaf/node SHA preimage by the one
shared collision universe, and therefore supplies a covered canonical opening
at every deployed position.  The same executable collision check excludes one
shared cross-tree 208-bit collision event.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactFixedK12CoveredClassifier

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisPool.V7MerkleQueryGrammar
open AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerkleOpeningBinding
open AspisPool.V7MerkleRawCollisionPredicate
open AspisPool.V7MerkleAcceptedOpeningProjection
open AspisPool.V7MerkleExtractedTreeCoverage

noncomputable section

theorem exact_k12_certificate_yields_collision_free_covered_trees
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    (certificate : ExactK12Certificate input) :
    let log := deduplicateFirst (exactK12OrderedQueries input)
    ¬ RawLogTruncatedDigestCollision (exactK12Truncate input)
        (collisionUniverse (exactK12Truncate input) log) ∧
      CoveredCompleteTrees (exactK12Truncate input) (exactK12Roots input)
        certificate.words
        (collisionUniverse (exactK12Truncate input) log) := by
  dsimp only
  obtain ⟨noCollision, coveredTrees⟩ :=
    extractV7Words_success_yields_collision_free_covered_trees
      (exactK12Truncate input) (exactK12Roots input)
      (exactK12Openings input) (exactK12OrderedQueries input)
      certificate.words certificate.extracted
  exact ⟨(no_raw_truncated_collision_iff
    (exactK12Truncate input)
    (collisionUniverse (exactK12Truncate input)
      (deduplicateFirst (exactK12OrderedQueries input)))).mp noCollision,
    coveredTrees⟩

theorem exact_k12_certificate_yields_all_covered_canonical_openings
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    (certificate : ExactK12Certificate input) :
    let log := deduplicateFirst (exactK12OrderedQueries input)
    ¬ RawLogTruncatedDigestCollision (exactK12Truncate input)
        (collisionUniverse (exactK12Truncate input) log) ∧
      (∀ position : Position,
        C1CoveredCanonicalOpening (exactK12Truncate input)
          certificate.words.c1 (exactK12Roots input).c1 position
          (collisionUniverse (exactK12Truncate input) log)) ∧
      (∀ position : Position,
        C2CoveredCanonicalOpening (exactK12Truncate input)
          certificate.words.c2 (exactK12Roots input).c2 position
          (collisionUniverse (exactK12Truncate input) log)) := by
  dsimp only
  obtain ⟨noCollision, coveredTrees⟩ :=
    exact_k12_certificate_yields_collision_free_covered_trees certificate
  obtain ⟨c1Openings, c2Openings⟩ :=
    covered_complete_trees_yield_all_canonical_openings
      (exactK12Truncate input) (exactK12Roots input) certificate.words
      (collisionUniverse (exactK12Truncate input)
        (deduplicateFirst (exactK12OrderedQueries input))) coveredTrees
  exact ⟨noCollision, c1Openings, c2Openings⟩

#print axioms exact_k12_certificate_yields_collision_free_covered_trees
#print axioms exact_k12_certificate_yields_all_covered_canonical_openings

end

end AspisK1.V7Tag73ExactFixedK12CoveredClassifier
