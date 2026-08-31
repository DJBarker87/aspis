import AspisFormal.K1.V7Tag73ExactFixedQ16SourceNoninterference

/-!
# Semantic noninterference endpoint for fixed K1.3 q16

The finite q16 probability theorem needs one fixed consistency set on each
residual fibre.  The old source-shaped endpoint expressed this by requiring
equality of an entire opaque parsed proof.  That proof object also contains
Merkle openings and query fields which the consistency set never reads.

This leaf states and proves the exact smaller condition: equality only of
K1.2 words, gamma, disclosed final-256, and the one-fold schedule.  It is the
right target for a verifier-derived/source-causal q16 bridge.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactFixedQ16SemanticNoninterference

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactFixedQ16ResidualFactorization
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- The exact fixed-root consistency set ignores openings and selected query
positions.  Equality of the four semantic inputs is therefore sufficient. -/
theorem exact_fixed_k13_intrinsic_bad_congr_of_semantic_fields
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
    (wordsExact : exactPrefixK12Words left = exactPrefixK12Words right)
    (gammaExact : (exactK13ParsedProof left).gamma =
      (exactK13ParsedProof right).gamma)
    (finalExact : (exactK13ParsedProof left).disclosedFinal =
      (exactK13ParsedProof right).disclosedFinal)
    (scheduleExact : (exactK13ParsedProof left).schedule =
      (exactK13ParsedProof right).schedule) :
    exactFixedK13IntrinsicBad decoder left =
      exactFixedK13IntrinsicBad decoder right := by
  simp only [exactFixedK13IntrinsicBad]
  rw [wordsExact, gammaExact, finalExact, scheduleExact]

/-- The smallest residual-fibre condition actually consumed by K1.3's q16
probability package.  It intentionally says nothing about opaque openings or
the parser-owned selected-query field. -/
def ExactFixedK13PreQ16SemanticInvariant
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
      (leftWitness : ExactFixedK13JointTrialWitness transitionFuel configuration
        projection fixedInstance decoder (hidden, left) trial)
      (rightWitness : ExactFixedK13JointTrialWitness transitionFuel configuration
        projection fixedInstance decoder (hidden, right) trial),
    (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, left)).1 =
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, right)).1 →
    exactPrefixK12Words leftWitness.input =
        exactPrefixK12Words rightWitness.input ∧
      (exactK13ParsedProof leftWitness.input).gamma =
        (exactK13ParsedProof rightWitness.input).gamma ∧
      (exactK13ParsedProof leftWitness.input).disclosedFinal =
        (exactK13ParsedProof rightWitness.input).disclosedFinal ∧
      (exactK13ParsedProof leftWitness.input).schedule =
        (exactK13ParsedProof rightWitness.input).schedule

-- Dependent event witnesses require normalizing two source-indexed inputs.
set_option maxHeartbeats 800000 in
/-- The semantic condition discharges the existing residual-fibre invariant,
so all established finite q16 accounting remains reusable. -/
theorem exact_fixed_k13_residual_invariant_of_pre_q16_semantics
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (semanticInvariant : ExactFixedK13PreQ16SemanticInvariant transitionFuel
      configuration projection fixedInstance decoder) :
    ExactFixedK13ResidualInvariant transitionFuel configuration projection
      fixedInstance decoder := by
  intro trial hidden left right leftMember rightMember residualExact
  let leftWitness := Classical.choice leftMember
  let rightWitness := Classical.choice rightMember
  obtain ⟨wordsExact, gammaExact, finalExact, scheduleExact⟩ :=
    semanticInvariant trial hidden left right leftWitness rightWitness residualExact
  have intrinsicExact :
      exactFixedK13IntrinsicBad decoder leftWitness.input =
        exactFixedK13IntrinsicBad decoder rightWitness.input :=
    exact_fixed_k13_intrinsic_bad_congr_of_semantic_fields decoder
      leftWitness.input rightWitness.input wordsExact gammaExact finalExact
      scheduleExact
  have leftPointwise :
      exactFixedK13PointwiseBad transitionFuel configuration projection
          fixedInstance decoder trial (hidden, left) = leftWitness.bad := by
    simpa [leftWitness] using
      (exact_fixed_k13_pointwise_bad_eq_choice
        (configuration := configuration) (projection := projection)
        (fixedInstance := fixedInstance) (decoder := decoder) trial
        (hidden, left) leftMember)
  have rightPointwise :
      exactFixedK13PointwiseBad transitionFuel configuration projection
          fixedInstance decoder trial (hidden, right) = rightWitness.bad := by
    simpa [rightWitness] using
      (exact_fixed_k13_pointwise_bad_eq_choice
        (configuration := configuration) (projection := projection)
        (fixedInstance := fixedInstance) (decoder := decoder) trial
        (hidden, right) rightMember)
  rw [leftPointwise, rightPointwise, leftWitness.badExact,
    rightWitness.badExact]
  exact intrinsicExact

#print axioms exact_fixed_k13_intrinsic_bad_congr_of_semantic_fields
#print axioms exact_fixed_k13_residual_invariant_of_pre_q16_semantics

end

end AspisK1.V7Tag73ExactFixedQ16SemanticNoninterference
