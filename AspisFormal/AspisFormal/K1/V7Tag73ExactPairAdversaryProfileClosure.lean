import AspisFormal.K1.V7Tag73ExactPairCoordinateProfileInvariant
import AspisFormal.K1.V7Tag73ExactFixedQ16ScheduleFunctional

/-!
# Adversary-first semantic-profile closure for the fold-armed K1.3 router

The complete pair-coordinate proof already fixes the disclosed final vector
at an adversary-owned final-work anchor.  This leaf isolates the exact
remaining pre-final statement: equality of the K1.2 words, operational gamma,
and operational alpha-zero challenge.  Those three equalities, together with
the canonical parsed-source certificate, mechanically imply equality of the
entire K1.3 intrinsic bad set.

No probability, source, or cryptographic premise is hidden in the definition
below.  It is the smallest protocol-specific endpoint still needed by the
existing one-forest theorem.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace AspisK1.V7Tag73ExactPairAdversaryProfileClosure

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73ExactAdversaryAnchorFinalProfile
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactFixedInstanceEvent
open AspisK1.V7Tag73ExactFinal256DigestRootOrigin
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactFixedQ16SemanticNoninterference
open AspisK1.V7Tag73ExactFixedQ16VerifierAnchorInvariant
open AspisK1.V7Tag73ExactFixedQ16ScheduleFunctional
open AspisK1.V7Tag73ExactPairCoordinateProfileInvariant
open AspisK1.V7Tag73ExactPairTrialProbabilityClosure
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7MerkleQueryExtractor
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- The semantic data that is already fixed when the deployed prover reaches
the selected final-work request.  Keeping this as one source snapshot avoids
three unrelated, conclusion-shaped stability assumptions. -/
structure Tag73PreFinalSemanticSnapshot where
  words : ExtractedWords
  gamma : QM31Exact
  alphaZero : QM31Exact

/-- Read the pre-final semantic snapshot from one exact accepted execution. -/
def exactTag73PreFinalSemanticSnapshot
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : Tag73PreFinalSemanticSnapshot where
  words := exactPrefixK12Words input
  gamma := (exactK13ParsedProof input).gamma
  alphaZero := exactOperationalChallenge input (.alpha 0)

/-- Cryptographic binding boundary at the pre-final transcript digest.  This
is deliberately not an honest-prover control-flow premise: the K1 adversary is
arbitrary.  In the classical ROM it is discharged outside the collision event;
for deployed SHA-256 it is the corresponding transcript-binding assumption. -/
def ExactTag73PrefinalDigestSemanticBinding
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement) : Prop :=
  ∀ {leftSample rightSample : ExactCompilerSample HiddenTape parameters}
      (leftInput : ExactK12OperationalInput transitionFuel configuration
        projection fixedInstance leftSample)
      (rightInput : ExactK12OperationalInput transitionFuel configuration
        projection fixedInstance rightSample)
      (leftDigest rightDigest : Digest256),
    ExactOperationalPrefinalDigest leftInput leftDigest →
    ExactOperationalPrefinalDigest rightInput rightDigest →
    leftDigest = rightDigest →
    exactTag73PreFinalSemanticSnapshot leftInput =
      exactTag73PreFinalSemanticSnapshot rightInput

/-- The exact pre-final semantic data still to transport across an
adversary-first complete-coordinate fibre.  The disclosed final vector is
absent because `exact_fixed_clean_pair_k13_adversary_anchor_disclosed_final_eq`
already proves it from the same coordinate hypotheses. -/
def ExactFixedCleanK13PairPreFinalInvariantOnAdversaryAnchors
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) : Prop :=
  ∀ (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
      (hidden : HiddenTape)
      (left right : FreshAnswerTape Digest256
        (exactCompilerTargetCaps parameters).length)
      (leftWitness : ExactFixedCleanK13PairTrialWitness transitionFuel
        configuration projection fixedInstance decoder (hidden, left)
          foldTrial finalTrial)
      (rightWitness : ExactFixedCleanK13PairTrialWitness transitionFuel
        configuration projection fixedInstance decoder (hidden, right)
          foldTrial finalTrial),
    ExactFixedK13AdversaryAnchor leftWitness.joint.input finalTrial →
    (let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
      transitionFuel foldTrial.val finalTrial.val
      (exactPlainRomCursor configuration hidden).erase
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        left).1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        right).1) →
    (let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
      transitionFuel foldTrial.val finalTrial.val
      (exactPlainRomCursor configuration hidden).erase
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        left).2.1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        right).2.1) →
    exactPrefixK12Words leftWitness.joint.input =
        exactPrefixK12Words rightWitness.joint.input ∧
      (exactK13ParsedProof leftWitness.joint.input).gamma =
        (exactK13ParsedProof rightWitness.joint.input).gamma ∧
      exactOperationalChallenge leftWitness.joint.input (.alpha 0) =
      exactOperationalChallenge rightWitness.joint.input (.alpha 0)

/-- Prefinal transcript binding supplies the complete pre-final invariant on
every fold-armed coordinate fibre.  The existing clean prefix theorem proves
that both accepted executions reach the same source-bound pre-final digest. -/
theorem exact_fixed_clean_pair_k13_pre_final_invariant_of_digest_binding
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (digestBinding :
      ExactTag73PrefinalDigestSemanticBinding transitionFuel
        configuration projection fixedInstance) :
    ExactFixedCleanK13PairPreFinalInvariantOnAdversaryAnchors transitionFuel
      configuration projection fixedInstance decoder := by
  intro foldTrial finalTrial hidden left right leftWitness rightWitness anchor
    contextExact foldExact
  obtain ⟨_selectedInput, leftDigest, rightDigest, _leftPrefix, _rightPrefix,
      digestExact, leftOrigin, rightOrigin⟩ :=
    exact_fixed_clean_pair_k13_adversary_anchor_selected_input_and_digest_eq
      foldTrial finalTrial hidden left right leftWitness rightWitness anchor
        programmedCover contextExact foldExact
  have snapshotExact := digestBinding leftWitness.joint.input
    rightWitness.joint.input leftDigest rightDigest leftOrigin rightOrigin
      digestExact
  have wordsExact :=
    congrArg Tag73PreFinalSemanticSnapshot.words snapshotExact
  have gammaExact :=
    congrArg Tag73PreFinalSemanticSnapshot.gamma snapshotExact
  have alphaExact :=
    congrArg Tag73PreFinalSemanticSnapshot.alphaZero snapshotExact
  change exactPrefixK12Words leftWitness.joint.input =
    exactPrefixK12Words rightWitness.joint.input at wordsExact
  change (exactK13ParsedProof leftWitness.joint.input).gamma =
    (exactK13ParsedProof rightWitness.joint.input).gamma at gammaExact
  change exactOperationalChallenge leftWitness.joint.input (.alpha 0) =
    exactOperationalChallenge rightWitness.joint.input (.alpha 0) at alphaExact
  exact ⟨wordsExact, gammaExact, alphaExact⟩

/-- Once the exact pre-final profile is transported, the existing canonical
source binding supplies schedule equality and the already-proved final-vector
lemma supplies disclosed-final equality.  This closes precisely the
adversary-owned premise consumed by the complete pair-coordinate invariant. -/
theorem exact_fixed_clean_pair_k13_adversary_bad_invariant_of_pre_final_profile
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (source : ExactFixedK13DecodedParsedSourceProvider transitionFuel
      configuration projection fixedInstance)
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (preFinalInvariant :
      ExactFixedCleanK13PairPreFinalInvariantOnAdversaryAnchors transitionFuel
        configuration projection fixedInstance decoder) :
    ExactFixedCleanK13PairBadInvariantOnAdversaryAnchors transitionFuel
      configuration projection fixedInstance decoder := by
  intro foldTrial finalTrial hidden left right leftWitness rightWitness anchor
    contextExact foldExact _workExact
  obtain ⟨wordsExact, gammaExact, alphaExact⟩ :=
    preFinalInvariant foldTrial finalTrial hidden left right leftWitness
      rightWitness anchor contextExact foldExact
  have finalExact :=
    exact_fixed_clean_pair_k13_adversary_anchor_disclosed_final_eq source
      transitionRoom foldTrial finalTrial hidden left right leftWitness
      rightWitness anchor programmedCover contextExact foldExact
  obtain ⟨leftDecoded, _leftDecode, leftBinding⟩ :=
    source (hidden, left) leftWitness.joint.input
  obtain ⟨rightDecoded, _rightDecode, rightBinding⟩ :=
    source (hidden, right) rightWitness.joint.input
  have scheduleExact := exact_fixed_k13_schedule_eq_of_source_bindings
    leftWitness.joint.input leftDecoded leftBinding rightWitness.joint.input
      rightDecoded rightBinding alphaExact
  rw [leftWitness.joint.badExact, rightWitness.joint.badExact]
  exact exact_fixed_k13_intrinsic_bad_congr_of_semantic_fields decoder
    leftWitness.joint.input rightWitness.joint.input wordsExact gammaExact
      finalExact scheduleExact

/-- Complete K1.3 coordinate noninterference, conditional only on the parsed
source bridge and the explicit pre-final digest binding boundary. -/
theorem exact_fixed_clean_k13_pair_coordinate_invariant_of_digest_binding
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (source : ExactFixedK13DecodedParsedSourceProvider transitionFuel
      configuration projection fixedInstance)
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (digestBinding : ExactTag73PrefinalDigestSemanticBinding transitionFuel
      configuration projection fixedInstance) :
    ExactFixedCleanK13PairCoordinateInvariant transitionFuel configuration
      projection fixedInstance decoder := by
  apply exact_fixed_clean_k13_pair_coordinate_invariant_of_adversary_anchors
    programmedCover
  apply exact_fixed_clean_pair_k13_adversary_bad_invariant_of_pre_final_profile
    source transitionRoom programmedCover
  exact exact_fixed_clean_pair_k13_pre_final_invariant_of_digest_binding
    programmedCover digestBinding

/-- End-to-end K1.3 one-forest probability bound under the exact parsed-source
provider and the explicit SHA/ROM pre-final transcript-binding boundary. -/
theorem exact_fixed_clean_pair_k13_query_probability_le_one_forest_of_digest_binding
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (source : ExactFixedK13DecodedParsedSourceProvider transitionFuel
      configuration projection fixedInstance)
    (digestBinding : ExactTag73PrefinalDigestSemanticBinding transitionFuel
      configuration projection fixedInstance)
    (frontierExact : ∀
      (sample : ExactCompilerSample HiddenTape parameters)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (schedule : QuerySchedule),
      (exactOperationalTape input).frontierNodes schedule =
        semanticFrontierNodes schedule.positions)
    (reference : AdmittedResult SemanticCap203Admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        reference.1))
    (foldExposureCap : unifiedFull256ExposureCap parameters ≤ 2 ^ 31)
    (finalExposureCap : unifiedFull256ExposureCap parameters ≤ 2 ^ 34) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
            projection fixedInstance ∩
          exactTag73K13QueryEvent transitionFuel configuration projection
            fixedInstance decoder) ≤ q16SemanticOneForestRawError := by
  have parsedSource : ExactFixedK13ParsedSourceProvider transitionFuel
      configuration projection fixedInstance := by
    intro sample input
    obtain ⟨decoded, _decode, binding⟩ := source sample input
    exact ⟨decoded, binding⟩
  have invariant :=
    exact_fixed_clean_k13_pair_coordinate_invariant_of_digest_binding
      (decoder := decoder) source transitionRoom programmedCover digestBinding
  exact exact_fixed_clean_pair_k13_query_probability_le_one_forest hiddenLaw
    transitionRoom programmedCover parsedSource frontierExact invariant
      reference traceExists foldExposureCap finalExposureCap

#print axioms
  ExactFixedCleanK13PairPreFinalInvariantOnAdversaryAnchors
#print axioms
  ExactTag73PrefinalDigestSemanticBinding
#print axioms
  exact_fixed_clean_pair_k13_pre_final_invariant_of_digest_binding
#print axioms
  exact_fixed_clean_pair_k13_adversary_bad_invariant_of_pre_final_profile
#print axioms
  exact_fixed_clean_k13_pair_coordinate_invariant_of_digest_binding
#print axioms
  exact_fixed_clean_pair_k13_query_probability_le_one_forest_of_digest_binding

end

end AspisK1.V7Tag73ExactPairAdversaryProfileClosure
