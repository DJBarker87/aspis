import AspisFormal.K1.V7Tag73ExactRestoredQ16SemanticNoninterference
import AspisFormal.Pool.V7MerkleUntypedErasureStability

/-!
# Canonical restored K1.2 word congruence

The complete-tree extractor uses the supplied openings only in its final
projection check.  If two opening sets both succeed against the same hash
view, roots, and ordered query log, they return the same complete words.  This
is the exact congruence needed to keep q16-dependent openings out of the K1.3
consistency-set target.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73RestoredK12CanonicalWordCongruence

open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactRestoredQ16ResidualFactorization
open AspisK1.V7Tag73ExactRestoredQ16SemanticNoninterference
open AspisK1.V7Tag73RestoredNodeK13Classifier
open AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerkleQueryGrammar
open AspisPool.V7MerkleUntypedErasureStability

noncomputable section

/-- Successful complete-tree extraction is independent of which supplied
opening proof passed the final projection check. -/
theorem extract_v7_words_success_words_eq_of_same_source
    (truncateSha256 : RawHashInput → Digest208)
    (roots : Roots) (leftProof rightProof : TwoTreeOpeningProof)
    (orderedQueries : OrderedRawQueryLog)
    (leftWords rightWords : ExtractedWords)
    (leftSuccess : extractV7Words truncateSha256 roots leftProof
      orderedQueries = .words leftWords)
    (rightSuccess : extractV7Words truncateSha256 roots rightProof
      orderedQueries = .words rightWords) :
    leftWords = rightWords := by
  by_cases collision : hasRawTruncatedCollision truncateSha256
      (collisionUniverse truncateSha256 (deduplicateFirst orderedQueries))
  · simp [extractV7Words, collision] at leftSuccess
  · cases graph : extractCompleteWords truncateSha256 roots
        (deduplicateFirst orderedQueries) with
    | failure reason => simp [extractV7Words, collision, graph] at leftSuccess
    | words candidate =>
        have leftFinished : finishExtraction truncateSha256 roots leftProof
            candidate = .words leftWords := by
          simpa [extractV7Words, collision, graph] using leftSuccess
        have rightFinished : finishExtraction truncateSha256 roots rightProof
            candidate = .words rightWords := by
          simpa [extractV7Words, collision, graph] using rightSuccess
        have leftExact := (finishExtraction_success_yields_match
          truncateSha256 roots leftProof candidate leftWords leftFinished).1
        have rightExact := (finishExtraction_success_yields_match
          truncateSha256 roots rightProof candidate rightWords rightFinished).1
        exact leftExact.trans rightExact.symm

/-- More general form: the two executions may have different later query
logs and supplied openings.  It suffices that their complete-tree resolution
returns the same pre-q16 committed candidate. -/
theorem extract_v7_words_success_words_eq_of_same_complete_candidate
    (leftTruncate rightTruncate : RawHashInput → Digest208)
    (leftRoots rightRoots : Roots)
    (leftProof rightProof : TwoTreeOpeningProof)
    (leftQueries rightQueries : OrderedRawQueryLog)
    (candidate leftWords rightWords : ExtractedWords)
    (leftGraph : extractCompleteWords leftTruncate leftRoots
      (deduplicateFirst leftQueries) = .words candidate)
    (rightGraph : extractCompleteWords rightTruncate rightRoots
      (deduplicateFirst rightQueries) = .words candidate)
    (leftSuccess : extractV7Words leftTruncate leftRoots leftProof leftQueries =
      .words leftWords)
    (rightSuccess : extractV7Words rightTruncate rightRoots rightProof
      rightQueries = .words rightWords) :
    leftWords = rightWords := by
  by_cases leftCollision : hasRawTruncatedCollision leftTruncate
      (collisionUniverse leftTruncate (deduplicateFirst leftQueries))
  · simp [extractV7Words, leftCollision] at leftSuccess
  · by_cases rightCollision : hasRawTruncatedCollision rightTruncate
        (collisionUniverse rightTruncate (deduplicateFirst rightQueries))
    · simp [extractV7Words, rightCollision] at rightSuccess
    · have leftFinished : finishExtraction leftTruncate leftRoots leftProof
          candidate = .words leftWords := by
        simpa [extractV7Words, leftCollision, leftGraph] using leftSuccess
      have rightFinished : finishExtraction rightTruncate rightRoots rightProof
          candidate = .words rightWords := by
        simpa [extractV7Words, rightCollision, rightGraph] using rightSuccess
      have leftExact := (finishExtraction_success_yields_match leftTruncate
        leftRoots leftProof candidate leftWords leftFinished).1
      have rightExact := (finishExtraction_success_yields_match rightTruncate
        rightRoots rightProof candidate rightWords rightFinished).1
      exact leftExact.trans rightExact.symm

/-- The restored literal root uses exactly the fixed operational input's
roots. -/
theorem restored_root_k12_roots_eq_exact
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : AspisK1.V7Tag73ExactCompilerResources.ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : AspisK1.V7Tag73ExactPlainRomRun.ExactPlainRomConfiguration
      HiddenTape TapeIdentity Observation Statement Tag73K12ParsedProof Payload
      Result parameters}
    {projection : AspisK1.V7Tag73ExactSourceAcceptanceModel.AcceptedTapeProjection Statement
      Tag73K12ParsedProof Payload}
    {fixedInstance : AspisK1.V7FsAokExperiment.PublicInstance Statement}
    {sample : AspisK1.V7Tag73ExactCompilerResources.ExactCompilerSample
      HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    restoredNodeK12Roots input.package.root.fixedRoot.base.runtime.node =
      exactK12Roots input := by
  rfl

theorem restored_root_k12_openings_eq_exact
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : AspisK1.V7Tag73ExactCompilerResources.ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : AspisK1.V7Tag73ExactPlainRomRun.ExactPlainRomConfiguration
      HiddenTape TapeIdentity Observation Statement Tag73K12ParsedProof Payload
      Result parameters}
    {projection : AspisK1.V7Tag73ExactSourceAcceptanceModel.AcceptedTapeProjection Statement
      Tag73K12ParsedProof Payload}
    {fixedInstance : AspisK1.V7FsAokExperiment.PublicInstance Statement}
    {sample : AspisK1.V7Tag73ExactCompilerResources.ExactCompilerSample
      HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    restoredNodeK12Openings input.package.root.fixedRoot.base.runtime.node =
      exactK12Openings input := by
  rfl

theorem restored_root_k12_queries_eq_exact
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : AspisK1.V7Tag73ExactCompilerResources.ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : AspisK1.V7Tag73ExactPlainRomRun.ExactPlainRomConfiguration
      HiddenTape TapeIdentity Observation Statement Tag73K12ParsedProof Payload
      Result parameters}
    {projection : AspisK1.V7Tag73ExactSourceAcceptanceModel.AcceptedTapeProjection Statement
      Tag73K12ParsedProof Payload}
    {fixedInstance : AspisK1.V7FsAokExperiment.PublicInstance Statement}
    {sample : AspisK1.V7Tag73ExactCompilerResources.ExactCompilerSample
      HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    restoredNodeK12OrderedQueries input.package.root.fixedRoot.base.runtime.node =
      exactK12OrderedQueries input := by
  rfl

theorem restored_root_k12_truncate_eq_exact
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : AspisK1.V7Tag73ExactCompilerResources.ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : AspisK1.V7Tag73ExactPlainRomRun.ExactPlainRomConfiguration
      HiddenTape TapeIdentity Observation Statement Tag73K12ParsedProof Payload
      Result parameters}
    {projection : AspisK1.V7Tag73ExactSourceAcceptanceModel.AcceptedTapeProjection Statement
      Tag73K12ParsedProof Payload}
    {fixedInstance : AspisK1.V7FsAokExperiment.PublicInstance Statement}
    {sample : AspisK1.V7Tag73ExactCompilerResources.ExactCompilerSample
      HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    restoredNodeK12Truncate input.package.root.fixedRoot.base.runtime.node =
      exactK12Truncate input := by
  rfl

/-- Once the pre-q16 hash view, roots, and ordered source log are fixed, two
successful restored-root certificates have the same complete words even when
their q16-selected supplied openings differ. -/
theorem restored_root_k12_certificate_words_eq_of_exact_source
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : AspisK1.V7Tag73ExactCompilerResources.ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : AspisK1.V7Tag73ExactPlainRomRun.ExactPlainRomConfiguration
      HiddenTape TapeIdentity Observation Statement Tag73K12ParsedProof Payload
      Result parameters}
    {projection :
      AspisK1.V7Tag73ExactSourceAcceptanceModel.AcceptedTapeProjection Statement
        Tag73K12ParsedProof Payload}
    {fixedInstance : AspisK1.V7FsAokExperiment.PublicInstance Statement}
    {leftSample rightSample :
      AspisK1.V7Tag73ExactCompilerResources.ExactCompilerSample HiddenTape
        parameters}
    (left : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance leftSample)
    (right : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance rightSample)
    (leftK12 : RestoredNodeK12Certificate
      left.package.root.fixedRoot.base.runtime.node)
    (rightK12 : RestoredNodeK12Certificate
      right.package.root.fixedRoot.base.runtime.node)
    (truncateExact : exactK12Truncate left = exactK12Truncate right)
    (rootsExact : exactK12Roots left = exactK12Roots right)
    (queriesExact : exactK12OrderedQueries left = exactK12OrderedQueries right) :
    leftK12.words = rightK12.words := by
  apply extract_v7_words_success_words_eq_of_same_source
    (exactK12Truncate left) (exactK12Roots left)
    (exactK12Openings left) (exactK12Openings right)
    (exactK12OrderedQueries left)
  · simpa [restored_root_k12_truncate_eq_exact,
      restored_root_k12_roots_eq_exact,
      restored_root_k12_openings_eq_exact,
      restored_root_k12_queries_eq_exact] using leftK12.extracted
  · simpa [restored_root_k12_truncate_eq_exact,
      restored_root_k12_roots_eq_exact,
      restored_root_k12_openings_eq_exact,
      restored_root_k12_queries_eq_exact, truncateExact, rootsExact,
      queriesExact] using rightK12.extracted

/-- Complete-tree resolution attached to the literal restored root, before
the q16-dependent supplied-opening projection is checked. -/
def exactRestoredRootCompleteWords
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : AspisK1.V7Tag73ExactCompilerResources.ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : AspisK1.V7Tag73ExactPlainRomRun.ExactPlainRomConfiguration
      HiddenTape TapeIdentity Observation Statement Tag73K12ParsedProof Payload
      Result parameters}
    {projection :
      AspisK1.V7Tag73ExactSourceAcceptanceModel.AcceptedTapeProjection Statement
        Tag73K12ParsedProof Payload}
    {fixedInstance : AspisK1.V7FsAokExperiment.PublicInstance Statement}
    {sample : AspisK1.V7Tag73ExactCompilerResources.ExactCompilerSample
      HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : CompleteWordsResult :=
  let node := input.package.root.fixedRoot.base.runtime.node
  extractCompleteWords (restoredNodeK12Truncate node)
    (restoredNodeK12Roots node)
    (deduplicateFirst (restoredNodeK12OrderedQueries node))

/-- Two successful restored roots have one common committed complete-tree
candidate as soon as their hash view, roots, and retained typed query
subsequence agree.  Arbitrarily interleaved transcript-only SHA queries are
irrelevant by the order-preserving erasure theorem. -/
theorem restored_root_common_complete_candidate_of_typed_source
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : AspisK1.V7Tag73ExactCompilerResources.ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : AspisK1.V7Tag73ExactPlainRomRun.ExactPlainRomConfiguration
      HiddenTape TapeIdentity Observation Statement Tag73K12ParsedProof Payload
      Result parameters}
    {projection :
      AspisK1.V7Tag73ExactSourceAcceptanceModel.AcceptedTapeProjection Statement
        Tag73K12ParsedProof Payload}
    {fixedInstance : AspisK1.V7FsAokExperiment.PublicInstance Statement}
    {leftSample rightSample :
      AspisK1.V7Tag73ExactCompilerResources.ExactCompilerSample HiddenTape
        parameters}
    (left : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance leftSample)
    (right : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance rightSample)
    (leftK12 : RestoredNodeK12Certificate
      left.package.root.fixedRoot.base.runtime.node)
    (rightK12 : RestoredNodeK12Certificate
      right.package.root.fixedRoot.base.runtime.node)
    (truncateExact : restoredNodeK12Truncate
        left.package.root.fixedRoot.base.runtime.node =
      restoredNodeK12Truncate right.package.root.fixedRoot.base.runtime.node)
    (rootsExact : restoredNodeK12Roots
        left.package.root.fixedRoot.base.runtime.node =
      restoredNodeK12Roots right.package.root.fixedRoot.base.runtime.node)
    (typedQueriesExact :
      retainTypedMerkleQueries (deduplicateFirst (restoredNodeK12OrderedQueries
        left.package.root.fixedRoot.base.runtime.node)) =
      retainTypedMerkleQueries (deduplicateFirst (restoredNodeK12OrderedQueries
        right.package.root.fixedRoot.base.runtime.node))) :
    ∃ candidate : ExtractedWords,
      exactRestoredRootCompleteWords left = .words candidate ∧
      exactRestoredRootCompleteWords right = .words candidate := by
  let leftNode := left.package.root.fixedRoot.base.runtime.node
  let rightNode := right.package.root.fixedRoot.base.runtime.node
  have leftTyped := extractV7Words_success_yields_typed_complete
    (restoredNodeK12Truncate leftNode) (restoredNodeK12Roots leftNode)
    (restoredNodeK12Openings leftNode) (restoredNodeK12OrderedQueries leftNode)
    leftK12.words leftK12.extracted
  have rightTyped := extractV7Words_success_yields_typed_complete
    (restoredNodeK12Truncate rightNode) (restoredNodeK12Roots rightNode)
    (restoredNodeK12Openings rightNode)
    (restoredNodeK12OrderedQueries rightNode) rightK12.words rightK12.extracted
  have rightTypedOnLeft :
      extractCompleteWords (restoredNodeK12Truncate leftNode)
          (restoredNodeK12Roots leftNode)
          (retainTypedMerkleQueries
            (deduplicateFirst (restoredNodeK12OrderedQueries leftNode))) =
        .words rightK12.words := by
    simpa [leftNode, rightNode, truncateExact, rootsExact,
      typedQueriesExact] using rightTyped
  have wordsExact : leftK12.words = rightK12.words := by
    rw [leftTyped] at rightTypedOnLeft
    injection rightTypedOnLeft
  have leftGraph := extractV7Words_success_yields_complete
    (restoredNodeK12Truncate leftNode) (restoredNodeK12Roots leftNode)
    (restoredNodeK12Openings leftNode) (restoredNodeK12OrderedQueries leftNode)
    leftK12.words leftK12.extracted
  have rightGraph := extractV7Words_success_yields_complete
    (restoredNodeK12Truncate rightNode) (restoredNodeK12Roots rightNode)
    (restoredNodeK12Openings rightNode)
    (restoredNodeK12OrderedQueries rightNode) rightK12.words rightK12.extracted
  refine ⟨leftK12.words, ?_, ?_⟩
  · simpa [exactRestoredRootCompleteWords, leftNode] using leftGraph
  · simpa [exactRestoredRootCompleteWords, rightNode, wordsExact] using
      rightGraph

/-- The exact remaining pre-q16 source condition after canonical-word
pinning.  It asks for one common committed-tree resolution and equality of
the three verifier-derived transcript fields; q16-selected openings and
query positions may differ. -/
def ExactRestoredRootCommittedPreQ16Invariant
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : AspisK1.V7Tag73ExactCompilerResources.ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : AspisK1.V7Tag73ExactClientKnowledgeComposition.ExactPlainRomWitnessConfiguration
      HiddenTape TapeIdentity Observation Statement Tag73K12ParsedProof Payload
      Witness parameters)
    (projection :
      AspisK1.V7Tag73ExactSourceAcceptanceModel.AcceptedTapeProjection Statement
        Tag73K12ParsedProof Payload)
    (fixedInstance : AspisK1.V7FsAokExperiment.PublicInstance Statement)
    (decoder : AspisPool.AlgorithmicCircleDecoderV7.ExactDecoderInstantiation
      AspisV5ComponentCQM31TowerExact.QM31Exact) : Prop :=
  ∀ (trial : AspisK1.V7Tag73AdaptiveQ16TrialAccounting.ExactCompilerExposureTrial
        parameters)
      (hidden : HiddenTape)
      (left right : AspisK1.V7Tag73AdaptiveLazyOracle.FreshAnswerTape
        AspisK1.V7Tag73TranscriptSchedule.Digest256
        (AspisK1.V7Tag73ExactCompilerResources.exactCompilerTargetCaps
          parameters).length)
      (leftWitness : ExactRestoredRootK13JointTrialWitness transitionFuel
        configuration projection fixedInstance decoder (hidden, left) trial)
      (rightWitness : ExactRestoredRootK13JointTrialWitness transitionFuel
        configuration projection fixedInstance decoder (hidden, right) trial),
    (exactRestoredRootK13TrialCoordinates transitionFuel configuration trial
        (hidden, left)).1 =
      (exactRestoredRootK13TrialCoordinates transitionFuel configuration trial
        (hidden, right)).1 →
    ∃ candidate : ExtractedWords,
      exactRestoredRootCompleteWords leftWitness.input = .words candidate ∧
      exactRestoredRootCompleteWords rightWitness.input = .words candidate ∧
      (exactRestoredRootK13View leftWitness.input).gamma =
        (exactRestoredRootK13View rightWitness.input).gamma ∧
      (exactRestoredRootK13View leftWitness.input).disclosedFinal =
        (exactRestoredRootK13View rightWitness.input).disclosedFinal ∧
      (exactRestoredRootK13View leftWitness.input).schedule =
        (exactRestoredRootK13View rightWitness.input).schedule

/-- Source-shaped form of the remaining restored q16 noninterference gate.
Unlike the older whole-log equality condition, it asks only for the
authenticated hash view, roots, retained typed-Merkle subsequence, and the
three semantic transcript fields. -/
def ExactRestoredRootTypedPreQ16SourceInvariant
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : AspisK1.V7Tag73ExactCompilerResources.ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : AspisK1.V7Tag73ExactClientKnowledgeComposition.ExactPlainRomWitnessConfiguration
      HiddenTape TapeIdentity Observation Statement Tag73K12ParsedProof Payload
      Witness parameters)
    (projection :
      AspisK1.V7Tag73ExactSourceAcceptanceModel.AcceptedTapeProjection Statement
        Tag73K12ParsedProof Payload)
    (fixedInstance : AspisK1.V7FsAokExperiment.PublicInstance Statement)
    (decoder : AspisPool.AlgorithmicCircleDecoderV7.ExactDecoderInstantiation
      AspisV5ComponentCQM31TowerExact.QM31Exact) : Prop :=
  ∀ (trial : AspisK1.V7Tag73AdaptiveQ16TrialAccounting.ExactCompilerExposureTrial
        parameters)
      (hidden : HiddenTape)
      (left right : AspisK1.V7Tag73AdaptiveLazyOracle.FreshAnswerTape
        AspisK1.V7Tag73TranscriptSchedule.Digest256
        (AspisK1.V7Tag73ExactCompilerResources.exactCompilerTargetCaps
          parameters).length)
      (leftWitness : ExactRestoredRootK13JointTrialWitness transitionFuel
        configuration projection fixedInstance decoder (hidden, left) trial)
      (rightWitness : ExactRestoredRootK13JointTrialWitness transitionFuel
        configuration projection fixedInstance decoder (hidden, right) trial),
    (exactRestoredRootK13TrialCoordinates transitionFuel configuration trial
        (hidden, left)).1 =
      (exactRestoredRootK13TrialCoordinates transitionFuel configuration trial
        (hidden, right)).1 →
    let leftNode := leftWitness.input.package.root.fixedRoot.base.runtime.node
    let rightNode := rightWitness.input.package.root.fixedRoot.base.runtime.node
    restoredNodeK12Truncate leftNode = restoredNodeK12Truncate rightNode ∧
      restoredNodeK12Roots leftNode = restoredNodeK12Roots rightNode ∧
      retainTypedMerkleQueries (deduplicateFirst
          (restoredNodeK12OrderedQueries leftNode)) =
        retainTypedMerkleQueries (deduplicateFirst
          (restoredNodeK12OrderedQueries rightNode)) ∧
      (exactRestoredRootK13View leftWitness.input).gamma =
        (exactRestoredRootK13View rightWitness.input).gamma ∧
      (exactRestoredRootK13View leftWitness.input).disclosedFinal =
        (exactRestoredRootK13View rightWitness.input).disclosedFinal ∧
      (exactRestoredRootK13View leftWitness.input).schedule =
        (exactRestoredRootK13View rightWitness.input).schedule

/-- Typed source noninterference is sufficient for the exact committed
candidate invariant consumed by the restored one-forest probability bound. -/
theorem exact_restored_committed_invariant_of_typed_source
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : AspisK1.V7Tag73ExactCompilerResources.ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : AspisK1.V7Tag73ExactClientKnowledgeComposition.ExactPlainRomWitnessConfiguration
      HiddenTape TapeIdentity Observation Statement Tag73K12ParsedProof Payload
      Witness parameters}
    {projection :
      AspisK1.V7Tag73ExactSourceAcceptanceModel.AcceptedTapeProjection Statement
        Tag73K12ParsedProof Payload}
    {fixedInstance : AspisK1.V7FsAokExperiment.PublicInstance Statement}
    {decoder : AspisPool.AlgorithmicCircleDecoderV7.ExactDecoderInstantiation
      AspisV5ComponentCQM31TowerExact.QM31Exact}
    (source : ExactRestoredRootTypedPreQ16SourceInvariant transitionFuel
      configuration projection fixedInstance decoder) :
    ExactRestoredRootCommittedPreQ16Invariant transitionFuel configuration
      projection fixedInstance decoder := by
  intro trial hidden left right leftWitness rightWitness residualExact
  obtain ⟨truncateExact, rootsExact, typedQueriesExact, gammaExact,
      finalExact, scheduleExact⟩ := source trial hidden left right leftWitness
        rightWitness residualExact
  obtain ⟨candidate, leftGraph, rightGraph⟩ :=
    restored_root_common_complete_candidate_of_typed_source leftWitness.input
      rightWitness.input leftWitness.k12 rightWitness.k12 truncateExact
        rootsExact typedQueriesExact
  exact ⟨candidate, leftGraph, rightGraph, gammaExact, finalExact,
    scheduleExact⟩

theorem exact_restored_pre_q16_semantics_of_committed_invariant
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : AspisK1.V7Tag73ExactCompilerResources.ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : AspisK1.V7Tag73ExactClientKnowledgeComposition.ExactPlainRomWitnessConfiguration
      HiddenTape TapeIdentity Observation Statement Tag73K12ParsedProof Payload
      Witness parameters}
    {projection :
      AspisK1.V7Tag73ExactSourceAcceptanceModel.AcceptedTapeProjection Statement
        Tag73K12ParsedProof Payload}
    {fixedInstance : AspisK1.V7FsAokExperiment.PublicInstance Statement}
    {decoder : AspisPool.AlgorithmicCircleDecoderV7.ExactDecoderInstantiation
      AspisV5ComponentCQM31TowerExact.QM31Exact}
    (invariant : ExactRestoredRootCommittedPreQ16Invariant transitionFuel
      configuration projection fixedInstance decoder) :
    ExactRestoredRootK13PreQ16SemanticInvariant transitionFuel configuration
      projection fixedInstance decoder := by
  intro trial hidden left right leftWitness rightWitness residualExact
  obtain ⟨candidate, leftGraph, rightGraph, gammaExact, finalExact,
      scheduleExact⟩ := invariant trial hidden left right leftWitness
        rightWitness residualExact
  have wordsExact : leftWitness.k12.words = rightWitness.k12.words := by
    apply extract_v7_words_success_words_eq_of_same_complete_candidate
      (restoredNodeK12Truncate
        leftWitness.input.package.root.fixedRoot.base.runtime.node)
      (restoredNodeK12Truncate
        rightWitness.input.package.root.fixedRoot.base.runtime.node)
      (restoredNodeK12Roots
        leftWitness.input.package.root.fixedRoot.base.runtime.node)
      (restoredNodeK12Roots
        rightWitness.input.package.root.fixedRoot.base.runtime.node)
      (restoredNodeK12Openings
        leftWitness.input.package.root.fixedRoot.base.runtime.node)
      (restoredNodeK12Openings
        rightWitness.input.package.root.fixedRoot.base.runtime.node)
      (restoredNodeK12OrderedQueries
        leftWitness.input.package.root.fixedRoot.base.runtime.node)
      (restoredNodeK12OrderedQueries
        rightWitness.input.package.root.fixedRoot.base.runtime.node)
      candidate
    · simpa [exactRestoredRootCompleteWords] using leftGraph
    · simpa [exactRestoredRootCompleteWords] using rightGraph
    · exact leftWitness.k12.extracted
    · exact rightWitness.k12.extracted
  exact ⟨wordsExact, gammaExact, finalExact, scheduleExact⟩

theorem exact_restored_root_residual_invariant_of_committed_invariant
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : AspisK1.V7Tag73ExactCompilerResources.ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : AspisK1.V7Tag73ExactClientKnowledgeComposition.ExactPlainRomWitnessConfiguration
      HiddenTape TapeIdentity Observation Statement Tag73K12ParsedProof Payload
      Witness parameters}
    {projection :
      AspisK1.V7Tag73ExactSourceAcceptanceModel.AcceptedTapeProjection Statement
        Tag73K12ParsedProof Payload}
    {fixedInstance : AspisK1.V7FsAokExperiment.PublicInstance Statement}
    {decoder : AspisPool.AlgorithmicCircleDecoderV7.ExactDecoderInstantiation
      AspisV5ComponentCQM31TowerExact.QM31Exact}
    (invariant : ExactRestoredRootCommittedPreQ16Invariant transitionFuel
      configuration projection fixedInstance decoder) :
    ExactRestoredRootK13ResidualInvariant transitionFuel configuration
      projection fixedInstance decoder :=
  exact_restored_root_k13_residual_invariant_of_pre_q16_semantics
    (exact_restored_pre_q16_semantics_of_committed_invariant invariant)

#print axioms extract_v7_words_success_words_eq_of_same_source
#print axioms
  extract_v7_words_success_words_eq_of_same_complete_candidate
#print axioms restored_root_k12_roots_eq_exact
#print axioms restored_root_k12_openings_eq_exact
#print axioms restored_root_k12_queries_eq_exact
#print axioms restored_root_k12_truncate_eq_exact
#print axioms restored_root_k12_certificate_words_eq_of_exact_source
#print axioms restored_root_common_complete_candidate_of_typed_source
#print axioms ExactRestoredRootTypedPreQ16SourceInvariant
#print axioms exact_restored_committed_invariant_of_typed_source
#print axioms exact_restored_pre_q16_semantics_of_committed_invariant
#print axioms exact_restored_root_residual_invariant_of_committed_invariant

end

end AspisK1.V7Tag73RestoredK12CanonicalWordCongruence
