import AspisFormal.K1.V7Tag73ExactFixedQ16DerivedProfileInvariant
import AspisFormal.K1.V7Tag73ExactFixedQ16VerifierAnchorInvariant
import AspisFormal.K1.V7Tag73ExactClientKnowledgeComposition
import AspisFormal.K1.V7Tag73AdaptiveQ16TrialAccounting
import AspisFormal.K1.V7Tag73ExactFixedK12MerkleClassifier
import AspisFormal.K1.V7Tag73ExactParsedProofSourceBinding
import AspisFormal.K1.V7Tag73ExactFixedK13K14Classifier

/-!
# Verifier-anchor closure for the minimal fixed K1.3 q16 profile

The q16 consistency set needs only the four semantic values packaged by
`ExactFixedK13Q16SemanticProfile`.  A verifier-owned chronological anchor
already preserves the legacy parsed proof and K1.2 words on a residual fibre.
The explicit parsed-source binding turns that preserved parsed proof into the
operational gamma and alpha-zero values used by the minimal profile.

This closes the verifier-owned half without relabelling the adversary-first
cache-hit half as fresh.  The latter remains a separate source/causal theorem.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactFixedQ16VerifierDerivedProfile

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedQ16DerivedProfileInvariant
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactFixedQ16VerifierAnchorInvariant
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Within a genuine chronological trial, a verifier-owned selected anchor
fixes the exact four-value q16 semantic profile.  The `source` premise is the
explicit parser/Aeneas boundary; no raw checked-return interface is treated as
if it supplied this equality. -/
theorem exact_fixed_k13_derived_profile_of_left_verifier_anchor
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (source : ExactFixedK13ParsedSourceProvider transitionFuel configuration
      projection fixedInstance)
    (trial : ExactCompilerExposureTrial parameters) (hidden : HiddenTape)
    (left right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (leftWitness : ExactFixedK13JointTrialWitness transitionFuel configuration
      projection fixedInstance decoder (hidden, left) trial)
    (rightWitness : ExactFixedK13JointTrialWitness transitionFuel configuration
      projection fixedInstance decoder (hidden, right) trial)
    (anchor : ExactFixedK13VerifierAnchor leftWitness.input trial)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (coordinateExact :
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, left)).1 =
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, right)).1) :
    exactFixedK13Q16SemanticProfileOf leftWitness.input =
      exactFixedK13Q16SemanticProfileOf rightWitness.input := by
  obtain ⟨parsedExact, wordsExact⟩ :=
    exact_fixed_k13_joint_trial_pre_q16_values_of_left_verifier_anchor trial
      hidden left right leftWitness rightWitness anchor programmedCover
      coordinateExact
  obtain ⟨leftDecoded, leftBinding⟩ := source _ leftWitness.input
  obtain ⟨rightDecoded, rightBinding⟩ := source _ rightWitness.input
  have gammaExact :
      exactOperationalChallenge leftWitness.input .gamma =
        exactOperationalChallenge rightWitness.input .gamma := by
    calc
      exactOperationalChallenge leftWitness.input .gamma =
          (exactK13ParsedProof leftWitness.input).gamma :=
        leftBinding.gammaExact.symm
      _ = (exactK13ParsedProof rightWitness.input).gamma := by
        exact congrArg Tag73K12ParsedProof.gamma parsedExact.symm
      _ = exactOperationalChallenge rightWitness.input .gamma :=
        rightBinding.gammaExact
  have finalExact :
      (exactK13ParsedProof leftWitness.input).disclosedFinal =
        (exactK13ParsedProof rightWitness.input).disclosedFinal :=
    congrArg Tag73K12ParsedProof.disclosedFinal parsedExact.symm
  have alphaExact :
      exactOperationalChallenge leftWitness.input (.alpha 0) =
        exactOperationalChallenge rightWitness.input (.alpha 0) := by
    calc
      exactOperationalChallenge leftWitness.input (.alpha 0) =
          (exactK13ParsedProof leftWitness.input).schedule.alpha :=
        leftBinding.alphaZeroExact.symm
      _ = (exactK13ParsedProof rightWitness.input).schedule.alpha := by
        exact congrArg (fun proof => proof.schedule.alpha) parsedExact.symm
      _ = exactOperationalChallenge rightWitness.input (.alpha 0) :=
        rightBinding.alphaZeroExact
  change ExactFixedK13Q16SemanticProfile.mk
      (exactPrefixK12Words leftWitness.input)
      (exactOperationalChallenge leftWitness.input .gamma)
      (exactK13ParsedProof leftWitness.input).disclosedFinal
      (exactOperationalChallenge leftWitness.input (.alpha 0)) =
    ExactFixedK13Q16SemanticProfile.mk
      (exactPrefixK12Words rightWitness.input)
      (exactOperationalChallenge rightWitness.input .gamma)
      (exactK13ParsedProof rightWitness.input).disclosedFinal
      (exactOperationalChallenge rightWitness.input (.alpha 0))
  rw [wordsExact.symm, gammaExact, finalExact, alphaExact]

/-- The profile invariant restricted to the verifier-owned chronological
partition.  Its complement is intentionally not claimed here. -/
def ExactFixedK13DerivedPreQ16ProfileInvariantOnVerifierAnchors
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
    ExactFixedK13VerifierAnchor leftWitness.input trial →
    (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, left)).1 =
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, right)).1 →
    exactFixedK13Q16SemanticProfileOf leftWitness.input =
      exactFixedK13Q16SemanticProfileOf rightWitness.input

theorem exact_fixed_k13_derived_profile_invariant_on_verifier_anchors
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (source : ExactFixedK13ParsedSourceProvider transitionFuel configuration
      projection fixedInstance)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap) :
    ExactFixedK13DerivedPreQ16ProfileInvariantOnVerifierAnchors transitionFuel
      configuration projection fixedInstance decoder := by
  intro trial hidden left right leftWitness rightWitness anchor coordinateExact
  exact exact_fixed_k13_derived_profile_of_left_verifier_anchor source trial
    hidden left right leftWitness rightWitness anchor programmedCover
    coordinateExact

#print axioms exact_fixed_k13_derived_profile_of_left_verifier_anchor
#print axioms exact_fixed_k13_derived_profile_invariant_on_verifier_anchors

end

end AspisK1.V7Tag73ExactFixedQ16VerifierDerivedProfile
