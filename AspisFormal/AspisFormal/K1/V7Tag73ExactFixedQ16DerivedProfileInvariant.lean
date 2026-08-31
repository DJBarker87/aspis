import AspisFormal.K1.V7Tag73ExactFixedQ16SemanticNoninterference
import AspisFormal.K1.V7Tag73ExactClientKnowledgeComposition
import AspisFormal.K1.V7Tag73AdaptiveQ16TrialAccounting
import AspisFormal.K1.V7Tag73OperationalSemanticReplay
import AspisFormal.K1.V7Tag73ExactParsedProofSourceBinding

/-!
# Minimal derived-profile endpoint for fixed Tag-73 K1.3 q16 causality

The q16 consistency set reads exactly four pre-q16 semantic values: K1.2
words, gamma, final-256, and alpha zero (which determines the canonical total
one-fold schedule). It does not read the remaining 385 fixed-field values,
openings, an opaque parser object, or the q16-selected positions themselves.

This module joins that minimal profile to the existing finite probability
package. The remaining source/causality statement is correspondingly exact:
equal non-q16 residual coordinates must preserve those four values. The
separate source schedule-functionality condition remains explicit rather than
pulling the large canonical-schedule aggregate into the q16 boundary.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactFixedQ16DerivedProfileInvariant

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactFixedQ16ResidualFactorization
open AspisK1.V7Tag73ExactFixedQ16SemanticNoninterference
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7MerkleQueryExtractor
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- The literal semantic data read by the fixed K1.3 q16 consistency set.
The selected q16 schedule and the parser's openings are deliberately absent.
-/
structure ExactFixedK13Q16SemanticProfile where
  words : ExtractedWords
  gamma : QM31Exact
  disclosedFinal : FinalMessage QM31Exact
  alphaZero : QM31Exact

/-- Form the profile from the completed K1.2 prefix, verifier-owned challenge
state, and the pre-q16 disclosed final message. -/
def exactFixedK13Q16SemanticProfileOf
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : ExactFixedK13Q16SemanticProfile where
  words := exactPrefixK12Words input
  gamma := exactOperationalChallenge input .gamma
  disclosedFinal := (exactK13ParsedProof input).disclosedFinal
  alphaZero := exactOperationalChallenge input (.alpha 0)

/-- Exact remaining K1.3 q16 source obligation. This is an equality of the
four semantic values, not an equality of returned proofs, parser objects, or
q16 schedules. -/
def ExactFixedK13DerivedPreQ16ProfileInvariant
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
    exactFixedK13Q16SemanticProfileOf leftWitness.input =
      exactFixedK13Q16SemanticProfileOf rightWitness.input

/-- At the explicit parsed-source boundary, a total one-fold schedule is a
function of the operational round-zero alpha.  The separate canonical bridge
discharges this from the two inverse-table equations; this lightweight q16
module keeps the obligation named rather than trusting a parser field. -/
def ExactFixedK13SourceScheduleFunctional
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement) : Prop :=
  ∀ {leftSample rightSample : ExactCompilerSample HiddenTape parameters}
      (left : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance leftSample)
      (leftDecoded : Fin 641 → QM31Exact)
      (_leftBinding : ExactParsedProofSourceBinding left leftDecoded)
      (right : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance rightSample)
      (rightDecoded : Fin 641 → QM31Exact)
      (_rightBinding : ExactParsedProofSourceBinding right rightDecoded),
    exactOperationalChallenge left (.alpha 0) =
      exactOperationalChallenge right (.alpha 0) →
    (exactK13ParsedProof left).schedule =
      (exactK13ParsedProof right).schedule

-- Source bindings normalize gamma and the total schedule. The profile
-- equality remains the sole q16 state-restoration/source theorem.
set_option maxHeartbeats 800000 in
theorem exact_fixed_k13_semantic_invariant_of_derived_profile
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
    (scheduleFunctional : ExactFixedK13SourceScheduleFunctional transitionFuel
      configuration projection fixedInstance)
    (profileInvariant : ExactFixedK13DerivedPreQ16ProfileInvariant
      transitionFuel configuration projection fixedInstance decoder) :
    ExactFixedK13PreQ16SemanticInvariant transitionFuel configuration
      projection fixedInstance decoder := by
  intro trial hidden left right leftWitness rightWitness residualExact
  have profileExact := profileInvariant trial hidden left right leftWitness
    rightWitness residualExact
  obtain ⟨leftDecoded, leftBinding⟩ := source _ leftWitness.input
  obtain ⟨rightDecoded, rightBinding⟩ := source _ rightWitness.input
  have wordsExact := congrArg ExactFixedK13Q16SemanticProfile.words profileExact
  have gammaOperationalExact :=
    congrArg ExactFixedK13Q16SemanticProfile.gamma profileExact
  have finalExact :=
    congrArg ExactFixedK13Q16SemanticProfile.disclosedFinal profileExact
  have alphaOperationalExact :=
    congrArg ExactFixedK13Q16SemanticProfile.alphaZero profileExact
  have gammaExact :
      (exactK13ParsedProof leftWitness.input).gamma =
        (exactK13ParsedProof rightWitness.input).gamma := by
    calc
      (exactK13ParsedProof leftWitness.input).gamma =
          exactOperationalChallenge leftWitness.input .gamma :=
        leftBinding.gammaExact
      _ = exactOperationalChallenge rightWitness.input .gamma :=
        gammaOperationalExact
      _ = (exactK13ParsedProof rightWitness.input).gamma :=
        rightBinding.gammaExact.symm
  have scheduleExact :
      (exactK13ParsedProof leftWitness.input).schedule =
        (exactK13ParsedProof rightWitness.input).schedule := by
    exact scheduleFunctional leftWitness.input leftDecoded leftBinding
      rightWitness.input rightDecoded rightBinding alphaOperationalExact
  exact ⟨wordsExact, gammaExact, finalExact, scheduleExact⟩

/-- The minimal derived-profile condition discharges the existing finite q16
residual invariant, preserving all already checked q16 probability algebra. -/
theorem exact_fixed_k13_residual_invariant_of_derived_profile
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
    (scheduleFunctional : ExactFixedK13SourceScheduleFunctional transitionFuel
      configuration projection fixedInstance)
    (profileInvariant : ExactFixedK13DerivedPreQ16ProfileInvariant
      transitionFuel configuration projection fixedInstance decoder) :
    ExactFixedK13ResidualInvariant transitionFuel configuration projection
      fixedInstance decoder := by
  exact exact_fixed_k13_residual_invariant_of_pre_q16_semantics
    (exact_fixed_k13_semantic_invariant_of_derived_profile source
      scheduleFunctional
      profileInvariant)

#print axioms exact_fixed_k13_semantic_invariant_of_derived_profile
#print axioms exact_fixed_k13_residual_invariant_of_derived_profile

end

end AspisK1.V7Tag73ExactFixedQ16DerivedProfileInvariant
