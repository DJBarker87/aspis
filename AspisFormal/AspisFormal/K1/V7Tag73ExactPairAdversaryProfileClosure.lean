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

/-- K1.2 coherence needed by the K1.3 q16 fibre argument.  This is separate
from transcript binding because the words are reconstructed from authenticated
Merkle openings and the oracle prefix, rather than serialized in the pre-final
digest. -/
def ExactFixedCleanK13PairWordsInvariantOnAdversaryAnchors
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
      exactPrefixK12Words rightWitness.joint.input

/-- Transcript coherence needed by the adversary-owned K1.3 fibre.  This is
restricted to the already target-clean, same-hidden-tape pair witness and its
exact fold-armed coordinates.  A global equal-digest/injective-SHA premise is
strictly stronger than the measured K1.6 collision event and is not used. -/
def ExactFixedCleanK13PairTranscriptInvariantOnAdversaryAnchors
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
    (exactK13ParsedProof leftWitness.joint.input).gamma =
        (exactK13ParsedProof rightWitness.joint.input).gamma ∧
      exactOperationalChallenge leftWitness.joint.input (.alpha 0) =
        exactOperationalChallenge rightWitness.joint.input (.alpha 0)

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

/-- The separately typed K1.2-word and transcript-source endpoints supply the
complete pre-final invariant on every fold-armed coordinate fibre. -/
theorem exact_fixed_clean_pair_k13_pre_final_invariant_of_components
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (wordsInvariant :
      ExactFixedCleanK13PairWordsInvariantOnAdversaryAnchors transitionFuel
        configuration projection fixedInstance decoder)
    (transcriptInvariant :
      ExactFixedCleanK13PairTranscriptInvariantOnAdversaryAnchors
        transitionFuel configuration projection fixedInstance decoder) :
    ExactFixedCleanK13PairPreFinalInvariantOnAdversaryAnchors transitionFuel
      configuration projection fixedInstance decoder := by
  intro foldTrial finalTrial hidden left right leftWitness rightWitness anchor
    contextExact foldExact
  have wordsExact := wordsInvariant foldTrial finalTrial hidden left right
    leftWitness rightWitness anchor contextExact foldExact
  obtain ⟨gammaExact, alphaExact⟩ := transcriptInvariant foldTrial finalTrial
    hidden left right leftWitness rightWitness anchor contextExact foldExact
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
theorem exact_fixed_clean_k13_pair_coordinate_invariant_of_components
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
    (wordsInvariant :
      ExactFixedCleanK13PairWordsInvariantOnAdversaryAnchors transitionFuel
        configuration projection fixedInstance decoder)
    (transcriptInvariant :
      ExactFixedCleanK13PairTranscriptInvariantOnAdversaryAnchors
        transitionFuel configuration projection fixedInstance decoder) :
    ExactFixedCleanK13PairCoordinateInvariant transitionFuel configuration
      projection fixedInstance decoder := by
  apply exact_fixed_clean_k13_pair_coordinate_invariant_of_adversary_anchors
    programmedCover
  apply exact_fixed_clean_pair_k13_adversary_bad_invariant_of_pre_final_profile
    source transitionRoom programmedCover
  exact exact_fixed_clean_pair_k13_pre_final_invariant_of_components
    wordsInvariant transcriptInvariant

/-- End-to-end K1.3 one-forest probability bound under the exact parsed-source
provider and the explicitly typed pre-final semantic-binding boundary. -/
theorem exact_fixed_clean_pair_k13_query_probability_le_one_forest_of_components
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
    (wordsInvariant :
      ExactFixedCleanK13PairWordsInvariantOnAdversaryAnchors transitionFuel
        configuration projection fixedInstance decoder)
    (transcriptInvariant :
      ExactFixedCleanK13PairTranscriptInvariantOnAdversaryAnchors
        transitionFuel configuration projection fixedInstance decoder)
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
    exact_fixed_clean_k13_pair_coordinate_invariant_of_components
      (decoder := decoder) source transitionRoom programmedCover wordsInvariant
        transcriptInvariant
  exact exact_fixed_clean_pair_k13_query_probability_le_one_forest hiddenLaw
    transitionRoom programmedCover parsedSource frontierExact invariant
      reference traceExists foldExposureCap finalExposureCap

#print axioms
  ExactFixedCleanK13PairPreFinalInvariantOnAdversaryAnchors
#print axioms
  ExactFixedCleanK13PairWordsInvariantOnAdversaryAnchors
#print axioms
  ExactFixedCleanK13PairTranscriptInvariantOnAdversaryAnchors
#print axioms
  exact_fixed_clean_pair_k13_pre_final_invariant_of_components
#print axioms
  exact_fixed_clean_pair_k13_adversary_bad_invariant_of_pre_final_profile
#print axioms
  exact_fixed_clean_k13_pair_coordinate_invariant_of_components
#print axioms
  exact_fixed_clean_pair_k13_query_probability_le_one_forest_of_components

end

end AspisK1.V7Tag73ExactPairAdversaryProfileClosure
