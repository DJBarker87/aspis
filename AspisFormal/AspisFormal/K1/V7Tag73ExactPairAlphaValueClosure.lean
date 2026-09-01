import AspisFormal.K1.V7Tag73ExactPairAdversaryProfileClosure

/-!
# Pair-specific alpha-zero value closure

The fold-armed router has a genuine adversary-first split. Alpha queries first
exposed before the selected fold occur in the residual coordinate; post-fold
alpha queries use the four named slots. It would therefore be wrong to identify
every accepted alpha block with the named `Fin 4` array.

This leaf records the honest source endpoint: hybrid residual/named routing
must reconstruct one common four-block tape for the two clean fibres. Bounded
first-success decoding then makes alpha-zero equality mechanical.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactPairAlphaValueClosure

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactFixedQ16VerifierAnchorInvariant
open AspisK1.V7Tag73ExactPairAdversaryProfileClosure
open AspisK1.V7Tag73ExactPairCoordinateProfileInvariant
open AspisK1.V7Tag73ExactPairTrialProbabilityClosure
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Output of the hybrid residual/named alpha routing proof. Both deployed
decoders consume prefixes of one common four-block tape. -/
structure ExactPairAlphaCommonPrefixBinding
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {leftSample rightSample : ExactCompilerSample HiddenTape parameters}
    (leftInput : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance leftSample)
    (rightInput : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance rightSample) where
  full : Fin 4 → Digest256
  leftBlocks : List Digest256
  rightBlocks : List Digest256
  leftRaw : Qm31Bytes
  rightRaw : Qm31Bytes
  leftValue : QM31Exact
  rightValue : QM31Exact
  leftPrefix : leftBlocks = (List.ofFn full).take leftBlocks.length
  rightPrefix : rightBlocks = (List.ofFn full).take rightBlocks.length
  leftAccepted :
    decodeChallengeParameter exactSecureCircleParameterMap (.alpha 0)
      leftBlocks = some leftRaw
  rightAccepted :
    decodeChallengeParameter exactSecureCircleParameterMap (.alpha 0)
      rightBlocks = some rightRaw
  leftDecode : decodeTagQM31ExactLE leftRaw = some leftValue
  rightDecode : decodeTagQM31ExactLE rightRaw = some rightValue
  leftOperational : exactOperationalChallenge leftInput (.alpha 0) = leftValue
  rightOperational :
    exactOperationalChallenge rightInput (.alpha 0) = rightValue

/-- The common-prefix endpoint implies equal operational alpha-zero values;
no hash injectivity or probability argument appears. -/
theorem exact_pair_operational_alpha_zero_eq_of_common_prefix
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {leftSample rightSample : ExactCompilerSample HiddenTape parameters}
    {leftInput : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance leftSample}
    {rightInput : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance rightSample}
    (binding : ExactPairAlphaCommonPrefixBinding leftInput rightInput) :
    exactOperationalChallenge leftInput (.alpha 0) =
      exactOperationalChallenge rightInput (.alpha 0) := by
  obtain ⟨_blocksExact, rawExact⟩ :=
    exact_challenge_prefixes_of_same_four_blocks_eq
      exactSecureCircleParameterMap (.alpha 0) binding.full
      binding.leftBlocks binding.rightBlocks binding.leftRaw binding.rightRaw
      binding.leftPrefix binding.rightPrefix binding.leftAccepted
      binding.rightAccepted
  have valueExact : binding.leftValue = binding.rightValue := by
    apply Option.some.inj
    calc
      some binding.leftValue = decodeTagQM31ExactLE binding.leftRaw :=
        binding.leftDecode.symm
      _ = decodeTagQM31ExactLE binding.rightRaw := by rw [rawExact]
      _ = some binding.rightValue := binding.rightDecode
  exact binding.leftOperational.trans
    (valueExact.trans binding.rightOperational.symm)

/-- Deterministic source endpoint still missing from the fold-armed controller.
Its proof must split each root-ordered alpha query at the fold ordinal:
residual-prefix replay before the fold and live named-producer routing after it. -/
def ExactFixedCleanK13PairAlphaCommonPrefixOnAdversaryAnchors
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
    Nonempty (ExactPairAlphaCommonPrefixBinding leftWitness.joint.input
      rightWitness.joint.input)

/-- The only other remaining transcript endpoint is parsed-gamma equality on
the same clean fibre. -/
def ExactFixedCleanK13PairGammaInvariantOnAdversaryAnchors
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
      (exactK13ParsedProof rightWitness.joint.input).gamma

/-- The two deterministic endpoints construct the transcript invariant
consumed by the measured K1.3 probability theorem. -/
theorem exact_fixed_clean_pair_k13_transcript_invariant_of_gamma_and_alpha_source
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (alphaSource :
      ExactFixedCleanK13PairAlphaCommonPrefixOnAdversaryAnchors transitionFuel
        configuration projection fixedInstance decoder)
    (gammaInvariant : ExactFixedCleanK13PairGammaInvariantOnAdversaryAnchors
      transitionFuel configuration projection fixedInstance decoder) :
    ExactFixedCleanK13PairTranscriptInvariantOnAdversaryAnchors transitionFuel
      configuration projection fixedInstance decoder := by
  intro foldTrial finalTrial hidden left right leftWitness rightWitness anchor
    contextExact foldExact
  have gammaExact := gammaInvariant foldTrial finalTrial hidden left right
    leftWitness rightWitness anchor contextExact foldExact
  obtain ⟨alphaBinding⟩ := alphaSource foldTrial finalTrial hidden left right
    leftWitness rightWitness anchor contextExact foldExact
  exact ⟨gammaExact,
    exact_pair_operational_alpha_zero_eq_of_common_prefix alphaBinding⟩

#print axioms ExactPairAlphaCommonPrefixBinding
#print axioms exact_pair_operational_alpha_zero_eq_of_common_prefix
#print axioms ExactFixedCleanK13PairAlphaCommonPrefixOnAdversaryAnchors
#print axioms ExactFixedCleanK13PairGammaInvariantOnAdversaryAnchors
#print axioms
  exact_fixed_clean_pair_k13_transcript_invariant_of_gamma_and_alpha_source

end

end AspisK1.V7Tag73ExactPairAlphaValueClosure
