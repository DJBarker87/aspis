import AspisFormal.K1.V7Tag73ExactRestoredQ16ResidualFactorization

/-!
# Canonical restored K1.3 semantic noninterference

The restored q16 event now retains the actual K1.2 certificate returned by the
total classifier.  Consequently the consistency-set target depends only on
four pre-q16 semantic fields: those canonical words, gamma, disclosed final,
and the one-fold schedule.  This file isolates exactly that condition and
reduces the probability-facing residual invariant to it.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactRestoredQ16SemanticNoninterference

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ParsedK13K14Classifier
open AspisK1.V7Tag73ExactRestoredOperationalK13Classifier
open AspisK1.V7Tag73ExactRestoredQ16ResidualFactorization
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73RestoredDerivedK13View
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact
open AspisV6OneFoldCandidateExtraction

noncomputable section

/-- The intrinsic verifier-derived view on the literal accepted root. -/
def exactRestoredRootK13View
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : Tag73K12ParsedProof :=
  restoredOperationalK13View
    ((exact_restored_operational_k13_provider input).data
      input.package.root.fixedRoot.base.runtime.node
      (exact_restoration_accumulator_contains_root input)
      (exact_restoration_accumulator_root_is_done input))

/-- The restored consistency set ignores openings and the selected query
vector.  Equality of its four semantic inputs is sufficient. -/
theorem exact_restored_root_k13_intrinsic_bad_congr_of_semantic_fields
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {leftSample rightSample : ExactCompilerSample HiddenTape parameters}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (left : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance leftSample)
    (right : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance rightSample)
    (leftWords rightWords : AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (wordsExact : leftWords = rightWords)
    (gammaExact : (exactRestoredRootK13View left).gamma =
      (exactRestoredRootK13View right).gamma)
    (finalExact : (exactRestoredRootK13View left).disclosedFinal =
      (exactRestoredRootK13View right).disclosedFinal)
    (scheduleExact : (exactRestoredRootK13View left).schedule =
      (exactRestoredRootK13View right).schedule) :
    exactRestoredRootK13IntrinsicBad decoder left leftWords =
      exactRestoredRootK13IntrinsicBad decoder right rightWords := by
  change consistencySet (exactRestoredRootK13View left).schedule
      (AspisPool.V7CoherentTraceExtraction.decoderCodeEncoders decoder)
      (parsedK13Transcript leftWords (exactRestoredRootK13View left)) =
    consistencySet (exactRestoredRootK13View right).schedule
      (AspisPool.V7CoherentTraceExtraction.decoderCodeEncoders decoder)
      (parsedK13Transcript rightWords (exactRestoredRootK13View right))
  rw [wordsExact, scheduleExact]
  simp only [parsedK13Transcript,
    AspisPool.V7CoherentTraceExtraction.extractedIdealTranscript]
  rw [gammaExact, finalExact]

/-- The smallest cross-fibre condition consumed by the restored q16 bound.
The K1.2 word vectors are now the canonical certificate fields, rather than
arbitrary existential witnesses. -/
def ExactRestoredRootK13PreQ16SemanticInvariant
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) : Prop :=
  ∀ (trial : ExactCompilerExposureTrial parameters) (hidden : HiddenTape)
      (left right : FreshAnswerTape Digest256
        (exactCompilerTargetCaps parameters).length)
      (leftWitness : ExactRestoredRootK13JointTrialWitness transitionFuel
        configuration projection fixedInstance decoder (hidden, left) trial)
      (rightWitness : ExactRestoredRootK13JointTrialWitness transitionFuel
        configuration projection fixedInstance decoder (hidden, right) trial),
    (exactRestoredRootK13TrialCoordinates transitionFuel configuration trial
        (hidden, left)).1 =
      (exactRestoredRootK13TrialCoordinates transitionFuel configuration trial
        (hidden, right)).1 →
    leftWitness.k12.words = rightWitness.k12.words ∧
      (exactRestoredRootK13View leftWitness.input).gamma =
        (exactRestoredRootK13View rightWitness.input).gamma ∧
      (exactRestoredRootK13View leftWitness.input).disclosedFinal =
        (exactRestoredRootK13View rightWitness.input).disclosedFinal ∧
      (exactRestoredRootK13View leftWitness.input).schedule =
        (exactRestoredRootK13View rightWitness.input).schedule

set_option maxHeartbeats 800000 in
theorem exact_restored_root_k13_residual_invariant_of_pre_q16_semantics
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (semanticInvariant : ExactRestoredRootK13PreQ16SemanticInvariant
      transitionFuel configuration projection fixedInstance decoder) :
    ExactRestoredRootK13ResidualInvariant transitionFuel configuration
      projection fixedInstance decoder := by
  intro trial hidden left right leftMember rightMember residualExact
  let leftWitness := Classical.choice leftMember
  let rightWitness := Classical.choice rightMember
  obtain ⟨wordsExact, gammaExact, finalExact, scheduleExact⟩ :=
    semanticInvariant trial hidden left right leftWitness rightWitness
      residualExact
  have intrinsicExact :=
    exact_restored_root_k13_intrinsic_bad_congr_of_semantic_fields decoder
      leftWitness.input rightWitness.input leftWitness.k12.words
      rightWitness.k12.words wordsExact gammaExact finalExact scheduleExact
  have leftPointwise :
      exactRestoredRootK13PointwiseBad transitionFuel configuration projection
          fixedInstance decoder trial (hidden, left) = leftWitness.bad := by
    simpa [leftWitness] using
      (exact_restored_root_k13_pointwise_bad_eq_choice
        (configuration := configuration) (projection := projection)
        (fixedInstance := fixedInstance) (decoder := decoder) trial
        (hidden, left) leftMember)
  have rightPointwise :
      exactRestoredRootK13PointwiseBad transitionFuel configuration projection
          fixedInstance decoder trial (hidden, right) = rightWitness.bad := by
    simpa [rightWitness] using
      (exact_restored_root_k13_pointwise_bad_eq_choice
        (configuration := configuration) (projection := projection)
        (fixedInstance := fixedInstance) (decoder := decoder) trial
        (hidden, right) rightMember)
  rw [leftPointwise, rightPointwise, leftWitness.badExact,
    rightWitness.badExact]
  exact intrinsicExact

#print axioms exact_restored_root_k13_intrinsic_bad_congr_of_semantic_fields
#print axioms
  exact_restored_root_k13_residual_invariant_of_pre_q16_semantics

end

end AspisK1.V7Tag73ExactRestoredQ16SemanticNoninterference
