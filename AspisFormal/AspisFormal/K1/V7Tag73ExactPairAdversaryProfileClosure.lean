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

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73ExactAdversaryAnchorFinalProfile
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactFixedQ16SemanticNoninterference
open AspisK1.V7Tag73ExactFixedQ16VerifierAnchorInvariant
open AspisK1.V7Tag73ExactFixedQ16ScheduleFunctional
open AspisK1.V7Tag73ExactPairCoordinateProfileInvariant
open AspisK1.V7Tag73ExactPairTrialProbabilityClosure
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

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

#print axioms
  ExactFixedCleanK13PairPreFinalInvariantOnAdversaryAnchors
#print axioms
  exact_fixed_clean_pair_k13_adversary_bad_invariant_of_pre_final_profile

end

end AspisK1.V7Tag73ExactPairAdversaryProfileClosure
