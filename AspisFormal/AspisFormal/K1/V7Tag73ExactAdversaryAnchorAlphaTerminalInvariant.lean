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
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactAdversaryAnchorSelectedInputInvariant
open AspisK1.V7Tag73ExactAlphaZeroActualTrialPrefinal
open AspisK1.V7Tag73ExactAlphaZeroRootOrder
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerGammaPrefixCoordinates
open AspisK1.V7Tag73ExactCompilerResources
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
      leftAfterFinal256.digest = rightAfterFinal256.digest ∧
      decodeTagQM31ExactLE
          ((exactOperationalTape leftWitness.input).messages.challengeValue
            (.alpha 0)) = some leftValue ∧
      decodeTagQM31ExactLE
          ((exactOperationalTape rightWitness.input).messages.challengeValue
            (.alpha 0)) = some rightValue ∧
      exactOperationalChallenge leftWitness.input (.alpha 0) = leftValue ∧
      exactOperationalChallenge rightWitness.input (.alpha 0) = rightValue := by
  obtain ⟨_selectedInput, leftDigest, rightDigest, leftBase, rightBase,
      leftAbsorbActor, rightAbsorbActor, _leftPrefix, _rightPrefix,
      digestExact, _leftOrigin, _rightOrigin, leftBaseExact, rightBaseExact,
      leftAbsorbMember, rightAbsorbMember⟩ :=
    exact_fixed_clean_k13_adversary_anchor_selected_input_and_digest_eq trial
      hidden left right leftWitness rightWitness anchor programmedCover
      coordinateExact
  obtain ⟨leftProducer, _leftFinal256Input, leftBeforeAlpha, leftAfterAlpha,
      leftAfterBlocks, leftAfterFinal256, leftOutputs, leftAdvances, leftValue,
      _leftWorkAnswer, leftQ16Base, _leftProducerLookup, leftOrdered,
      _leftOutputsLength, leftOutputsPositive, leftAdvancesLength,
      leftTerminalExact, leftAfterAlphaExact, _leftFinal256InputExact,
      _leftFinal256Lookup, _leftWorkLookup, _leftWorkAccepted,
      leftFinalNonceLookup, leftQ16BaseExact, leftDecode, leftOperational⟩ :=
    exact_compiler_alpha_zero_chain_has_root_order transitionRoom
      leftWitness.input
  obtain ⟨rightProducer, _rightFinal256Input, rightBeforeAlpha, rightAfterAlpha,
      rightAfterBlocks, rightAfterFinal256, rightOutputs, rightAdvances,
      rightValue, _rightWorkAnswer, rightQ16Base, _rightProducerLookup,
      rightOrdered, _rightOutputsLength, rightOutputsPositive,
      rightAdvancesLength, rightTerminalExact, rightAfterAlphaExact,
      _rightFinal256InputExact, _rightFinal256Lookup, _rightWorkLookup,
      _rightWorkAccepted, rightFinalNonceLookup, rightQ16BaseExact,
      rightDecode, rightOperational⟩ :=
    exact_compiler_alpha_zero_chain_has_root_order transitionRoom
      rightWitness.input
  have leftPrefinalExact : leftAfterFinal256.digest = leftDigest :=
    final_nonce_lookup_and_root_record_fix_digest leftWitness.input
      leftAfterFinal256.digest leftDigest leftQ16Base leftBase leftAbsorbActor
      leftFinalNonceLookup (leftQ16BaseExact.trans leftBaseExact.symm)
      leftAbsorbMember
  have rightPrefinalExact : rightAfterFinal256.digest = rightDigest :=
    final_nonce_lookup_and_root_record_fix_digest rightWitness.input
      rightAfterFinal256.digest rightDigest rightQ16Base rightBase
      rightAbsorbActor rightFinalNonceLookup
      (rightQ16BaseExact.trans rightBaseExact.symm) rightAbsorbMember
  have terminalSuccessorExact :
      leftAfterFinal256.digest = rightAfterFinal256.digest :=
    leftPrefinalExact.trans (digestExact.trans rightPrefinalExact.symm)
  exact ⟨leftProducer, rightProducer, leftBeforeAlpha, rightBeforeAlpha,
    leftAfterAlpha, rightAfterAlpha, leftAfterBlocks, rightAfterBlocks,
    leftAfterFinal256, rightAfterFinal256, leftOutputs, leftAdvances,
    rightOutputs, rightAdvances, leftValue, rightValue, leftOrdered,
    rightOrdered, leftOutputsPositive, rightOutputsPositive,
    leftAdvancesLength, rightAdvancesLength, leftTerminalExact,
    rightTerminalExact, leftAfterAlphaExact, rightAfterAlphaExact,
    terminalSuccessorExact, leftDecode, rightDecode, leftOperational,
    rightOperational⟩

#print axioms exact_fixed_clean_k13_adversary_anchor_alpha_terminal_eq

end

end AspisK1.V7Tag73ExactAdversaryAnchorAlphaTerminalInvariant
