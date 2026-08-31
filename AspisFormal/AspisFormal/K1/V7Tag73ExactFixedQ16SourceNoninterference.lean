import AspisFormal.K1.V7Tag73ExactFixedQ16ResidualFactorization

/-!
# Source-shaped noninterference endpoint for fixed-root K1.3 q16

The residual probability package needs equality of one finite consistency set.
That set depends only on two values committed before final work and q16:

* the parsed prover proof; and
* the canonical K1.2 words extracted from the completed prover prefix.

This module removes all `Classical.choice` and event-packaging noise from the
remaining obligation.  A source/scheduler proof of equality for those two
values now constructs the exact residual invariant used by the probability
theorem.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactFixedQ16SourceNoninterference

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73CausalQ16FinalWorkProbability
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactFixedQ16ResidualFactorization
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7MerkleQueryExtractor
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Equality of the two pre-q16 source values is sufficient for equality of
the canonical fixed-root consistency sets. -/
theorem exact_fixed_k13_intrinsic_bad_congr
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
    (proofExact : exactK13ParsedProof left = exactK13ParsedProof right)
    (wordsExact : exactPrefixK12Words left = exactPrefixK12Words right) :
    exactFixedK13IntrinsicBad decoder left =
      exactFixedK13IntrinsicBad decoder right := by
  simp only [exactFixedK13IntrinsicBad]
  rw [proofExact, wordsExact]

/-- The smallest execution-facing noninterference proposition.  Within one
chronological trial and one hidden adversary tape, equality of the retained
residual must preserve the parsed prover proof and canonical K1.2 words.

Both witnesses are genuine event witnesses, so no claim is made about failed
or incomplete executions. -/
def ExactFixedK13PreQ16SourceInvariant
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
    exactK13ParsedProof leftWitness.input =
        exactK13ParsedProof rightWitness.input ∧
      exactPrefixK12Words leftWitness.input =
        exactPrefixK12Words rightWitness.input

-- Dependent event witnesses require normalizing two source-indexed structures.
set_option maxHeartbeats 800000 in
/-- A source proof of pre-q16 value preservation discharges the exact
residual-fibre invariant used by the q16 probability package. -/
theorem exact_fixed_k13_residual_invariant_of_pre_q16_source
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (sourceInvariant : ExactFixedK13PreQ16SourceInvariant transitionFuel
      configuration projection fixedInstance decoder) :
    ExactFixedK13ResidualInvariant transitionFuel configuration projection
      fixedInstance decoder := by
  intro trial hidden left right leftMember rightMember residualExact
  let leftWitness := Classical.choice leftMember
  let rightWitness := Classical.choice rightMember
  obtain ⟨proofExact, wordsExact⟩ := sourceInvariant trial hidden left right
    leftWitness rightWitness residualExact
  have intrinsicExact :
      exactFixedK13IntrinsicBad decoder leftWitness.input =
        exactFixedK13IntrinsicBad decoder rightWitness.input :=
    exact_fixed_k13_intrinsic_bad_congr decoder leftWitness.input
      rightWitness.input proofExact wordsExact
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

#print axioms exact_fixed_k13_intrinsic_bad_congr
#print axioms exact_fixed_k13_residual_invariant_of_pre_q16_source

end

end AspisK1.V7Tag73ExactFixedQ16SourceNoninterference
