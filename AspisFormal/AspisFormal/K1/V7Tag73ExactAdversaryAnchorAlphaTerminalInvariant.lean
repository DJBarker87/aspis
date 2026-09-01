import AspisFormal.K1.V7Tag73ExactAdversaryAnchorSelectedInputInvariant
import AspisFormal.K1.V7Tag73ExactAlphaZeroActualTrialPrefinal

/-!
# Cross-fibre alpha-zero terminal invariant

Equal clean residual fibres at an adversary-owned final-work anchor have the
same actual alpha-zero successor digest.  The proof retains both consumed
duplex chains and identifies each work-erased final-nonce input with the
source trial's recorded final-nonce input through q16-base answer uniqueness.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactAdversaryAnchorAlphaTerminalInvariant

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactAdversaryAnchorSelectedInputInvariant
open AspisK1.V7Tag73ExactAlphaZeroActualTrialPrefinal
open AspisK1.V7Tag73ExactAlphaZeroRootOrder
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerGammaPrefixCoordinates
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactFixedCleanQ16ProfileInvariant
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactFixedQ16VerifierAnchorInvariant
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactQ16CausalCoordinateOrder
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73SqueezeInputStateInjectivity
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Both accepted alpha-zero chains reach the same pre-final state under the
exact clean adversary-anchor comparison. -/
theorem exact_fixed_clean_k13_adversary_anchor_alpha_terminal_eq
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (transitionRoom : 2 ≤ transitionFuel)
    (trial : ExactCompilerExposureTrial parameters) (hidden : HiddenTape)
    (left right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (leftWitness : ExactFixedK13JointTrialWitness transitionFuel configuration
      projection fixedInstance decoder (hidden, left) trial)
    (rightWitness : ExactFixedK13JointTrialWitness transitionFuel configuration
      projection fixedInstance decoder (hidden, right) trial)
    (anchor : ExactFixedK13AdversaryAnchor leftWitness.input trial)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (coordinateExact :
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, left)).1 =
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, right)).1) :
    ∃ (leftProducer rightProducer : ShaInput)
        (leftBeforeAlpha rightBeforeAlpha leftAfterAlpha rightAfterAlpha
          leftAfterBlocks rightAfterBlocks leftAfterFinal256 rightAfterFinal256 :
          EvalState)
        (leftOutputs leftAdvances rightOutputs rightAdvances : List Digest256)
        (leftValue rightValue : QM31Exact),
      ExactRootOrderedQ16Chain leftWitness.input leftProducer
          leftBeforeAlpha.digest leftOutputs leftAdvances ∧
      ExactRootOrderedQ16Chain rightWitness.input rightProducer
          rightBeforeAlpha.digest rightOutputs rightAdvances ∧
      0 < leftOutputs.length ∧
      0 < rightOutputs.length ∧
      leftAdvances.length = leftOutputs.length ∧
      rightAdvances.length = rightOutputs.length ∧
      leftAfterBlocks.digest =
        gammaTerminalDigest leftBeforeAlpha.digest leftAdvances ∧
      rightAfterBlocks.digest =
        gammaTerminalDigest rightBeforeAlpha.digest rightAdvances ∧
      leftAfterAlpha.digest = leftAfterBlocks.digest ∧
      rightAfterAlpha.digest = rightAfterBlocks.digest ∧
      leftAfterAlpha.digest = rightAfterAlpha.digest ∧
      leftAfterFinal256.digest = rightAfterFinal256.digest ∧
      decodeTagQM31ExactLE
          ((exactOperationalTape leftWitness.input).messages.challengeValue
            (.alpha 0)) = some leftValue ∧
      decodeTagQM31ExactLE
          ((exactOperationalTape rightWitness.input).messages.challengeValue
            (.alpha 0)) = some rightValue ∧
      exactOperationalChallenge leftWitness.input (.alpha 0) = leftValue ∧
      exactOperationalChallenge rightWitness.input (.alpha 0) = rightValue := by
  obtain ⟨leftCanonicalBefore, rightCanonicalBefore, digest, leftBase,
      rightBase, leftAbsorbActor, rightAbsorbActor, canonicalInputExact,
      leftCanonicalLookup, rightCanonicalLookup, leftBaseExact, rightBaseExact,
      leftAbsorbMember, rightAbsorbMember⟩ :=
    exact_fixed_clean_k13_adversary_anchor_final256_input_eq transitionRoom trial
      hidden left right leftWitness rightWitness anchor programmedCover
      coordinateExact
  obtain ⟨leftProducer, leftFinal256Input, leftBeforeAlpha, leftAfterAlpha,
      leftAfterBlocks, leftAfterFinal256, leftOutputs, leftAdvances, leftValue,
      _leftWorkAnswer, leftQ16Base, _leftProducerLookup, _leftProducerBoundary,
      leftOrdered,
      _leftOutputsLength, leftOutputsPositive, leftAdvancesLength,
      leftTerminalExact, leftAfterAlphaExact, leftFinal256InputExact,
      leftFinal256Lookup, _leftWorkLookup, _leftWorkAccepted,
      leftFinalNonceLookup, leftQ16BaseExact, leftDecode, leftOperational⟩ :=
    exact_compiler_alpha_zero_chain_has_root_order transitionRoom
      leftWitness.input
  obtain ⟨rightProducer, rightFinal256Input, rightBeforeAlpha, rightAfterAlpha,
      rightAfterBlocks, rightAfterFinal256, rightOutputs, rightAdvances,
      rightValue, _rightWorkAnswer, rightQ16Base, _rightProducerLookup,
      _rightProducerBoundary, rightOrdered, _rightOutputsLength,
      rightOutputsPositive,
      rightAdvancesLength, rightTerminalExact, rightAfterAlphaExact,
      rightFinal256InputExact, rightFinal256Lookup, _rightWorkLookup,
      _rightWorkAccepted, rightFinalNonceLookup, rightQ16BaseExact,
      rightDecode, rightOperational⟩ :=
    exact_compiler_alpha_zero_chain_has_root_order transitionRoom
      rightWitness.input
  have leftPrefinalExact : leftAfterFinal256.digest = digest :=
    final_nonce_lookup_and_root_record_fix_digest leftWitness.input
      leftAfterFinal256.digest digest leftQ16Base leftBase leftAbsorbActor
      leftFinalNonceLookup (leftQ16BaseExact.trans leftBaseExact.symm)
      leftAbsorbMember
  have rightPrefinalExact : rightAfterFinal256.digest = digest :=
    final_nonce_lookup_and_root_record_fix_digest rightWitness.input
      rightAfterFinal256.digest digest rightQ16Base rightBase
      rightAbsorbActor rightFinalNonceLookup
      (rightQ16BaseExact.trans rightBaseExact.symm) rightAbsorbMember
  have terminalSuccessorExact :
      leftAfterFinal256.digest = rightAfterFinal256.digest :=
    leftPrefinalExact.trans rightPrefinalExact.symm
  let leftCanonicalInput : ShaInput :=
    bytes leftCanonicalBefore.digest ++
      [domAbsorb,
        (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
          (exactOperationalTape leftWitness.input).messages.finalValues).label] ++
      (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
        (exactOperationalTape leftWitness.input).messages.finalValues).data
  let rightCanonicalInput : ShaInput :=
    bytes rightCanonicalBefore.digest ++
      [domAbsorb,
        (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
          (exactOperationalTape rightWitness.input).messages.finalValues).label] ++
      (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
        (exactOperationalTape rightWitness.input).messages.finalValues).data
  obtain ⟨leftAlphaActor, leftAlphaMember⟩ :=
    exact_final_table_lookup_has_root_record leftWitness.input leftFinal256Input
      digest (by simpa [leftPrefinalExact] using leftFinal256Lookup)
  obtain ⟨leftCanonicalActor, leftCanonicalMember⟩ :=
    exact_final_table_lookup_has_root_record leftWitness.input leftCanonicalInput
      digest (by simpa [leftCanonicalInput] using leftCanonicalLookup)
  have leftInputExact : leftFinal256Input = leftCanonicalInput := by
    have recordExact :
        (.machineFresh leftAlphaActor leftFinal256Input digest :
            UnifiedExposureRecord) =
          (.machineFresh leftCanonicalActor leftCanonicalInput digest :
            UnifiedExposureRecord) :=
      List.inj_on_of_nodup_map (exact_root_record_answers_nodup leftWitness.input)
        leftAlphaMember leftCanonicalMember rfl
    injection recordExact
  obtain ⟨rightAlphaActor, rightAlphaMember⟩ :=
    exact_final_table_lookup_has_root_record rightWitness.input rightFinal256Input
      digest (by simpa [rightPrefinalExact] using rightFinal256Lookup)
  obtain ⟨rightCanonicalActor, rightCanonicalMember⟩ :=
    exact_final_table_lookup_has_root_record rightWitness.input
      rightCanonicalInput digest (by
        simpa [rightCanonicalInput] using rightCanonicalLookup)
  have rightInputExact : rightFinal256Input = rightCanonicalInput := by
    have recordExact :
        (.machineFresh rightAlphaActor rightFinal256Input digest :
            UnifiedExposureRecord) =
          (.machineFresh rightCanonicalActor rightCanonicalInput digest :
            UnifiedExposureRecord) :=
      List.inj_on_of_nodup_map (exact_root_record_answers_nodup rightWitness.input)
        rightAlphaMember rightCanonicalMember rfl
    injection recordExact
  have canonicalInputExact' : leftCanonicalInput = rightCanonicalInput := by
    simpa [leftCanonicalInput, rightCanonicalInput] using canonicalInputExact
  have alphaFinal256InputExact : leftFinal256Input = rightFinal256Input :=
    leftInputExact.trans (canonicalInputExact'.trans rightInputExact.symm)
  have alphaTerminalExact : leftAfterAlpha.digest = rightAfterAlpha.digest := by
    rw [leftFinal256InputExact, rightFinal256InputExact] at alphaFinal256InputExact
    apply digest_bytes_injective
    have prefixExact := congrArg (List.take 32) alphaFinal256InputExact
    simpa using prefixExact
  exact ⟨leftProducer, rightProducer, leftBeforeAlpha, rightBeforeAlpha,
    leftAfterAlpha, rightAfterAlpha, leftAfterBlocks, rightAfterBlocks,
    leftAfterFinal256, rightAfterFinal256, leftOutputs, leftAdvances,
    rightOutputs, rightAdvances, leftValue, rightValue, leftOrdered,
    rightOrdered, leftOutputsPositive, rightOutputsPositive,
    leftAdvancesLength, rightAdvancesLength, leftTerminalExact,
    rightTerminalExact, leftAfterAlphaExact, rightAfterAlphaExact,
    alphaTerminalExact, terminalSuccessorExact, leftDecode, rightDecode, leftOperational,
    rightOperational⟩

#print axioms exact_fixed_clean_k13_adversary_anchor_alpha_terminal_eq

end

end AspisK1.V7Tag73ExactAdversaryAnchorAlphaTerminalInvariant
