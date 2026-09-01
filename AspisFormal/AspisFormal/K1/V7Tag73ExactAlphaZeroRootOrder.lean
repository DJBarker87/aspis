import AspisFormal.K1.V7Tag73ExactAlphaZeroPrefixCoordinates
import AspisFormal.K1.V7Tag73ExactQ16CausalCoordinateOrder

/-!
# Exact root order of the consumed alpha-zero duplex chain

The accepted alpha-zero sampler is not merely a final-table computation.  Its
boundary absorption, every consumed output/advance pair, and the immediately
following `final256` absorption are all source-backed.  This leaf packages the
duplex chain with its exact root ordering and terminal digest, ready for the
cross-fibre adversary-anchor transport proof.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactAlphaZeroRootOrder

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactAlphaZeroPrefixCoordinates
open AspisK1.V7Tag73ExactCompilerGammaPrefixCoordinates
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactQ16CausalCoordinateOrder
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73TranscriptSchedule
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- The exact accepted alpha-zero chain starts at its fold-nonce absorption,
is strictly root ordered through every consumed duplex block, reaches the
digest used by `final256`, and decodes to the operational alpha-zero value. -/
theorem exact_compiler_alpha_zero_chain_has_root_order
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    ∃ (producerInput final256Input : ShaInput)
      (beforeAlpha afterAlpha afterBlocks afterFinal256 : EvalState)
      (outputs advances : List Digest256) (exactValue : QM31Exact),
      tableLookup (exactOperationalTable input) producerInput =
          some beforeAlpha.digest ∧
      ExactRootOrderedQ16Chain input producerInput beforeAlpha.digest
          outputs advances ∧
      outputs.length =
          ((exactOperationalTape input).messages.challengeUse
            (.alpha 0)).blocksUsed ∧
      0 < outputs.length ∧
      advances.length = outputs.length ∧
      afterBlocks.digest =
          gammaTerminalDigest beforeAlpha.digest advances ∧
      afterAlpha.digest = afterBlocks.digest ∧
      final256Input =
        bytes afterAlpha.digest ++
          [domAbsorb,
            AspisK1.V7Tag73TranscriptSchedule.Payload.label
              (.final256 (exactOperationalTape input).messages.finalValues)] ++
          AspisK1.V7Tag73TranscriptSchedule.Payload.data
            (.final256 (exactOperationalTape input).messages.finalValues) ∧
      tableLookup (exactOperationalTable input) final256Input =
          some afterFinal256.digest ∧
      decodeTagQM31ExactLE
          ((exactOperationalTape input).messages.challengeValue (.alpha 0)) =
        some exactValue ∧
      exactOperationalChallenge input (.alpha 0) = exactValue := by
  obtain ⟨_evaluator, _segments, beforeAlphaProducer, beforeAlpha,
      afterAlpha, afterBlocks, afterFinal256, outputs, advances, exactValue,
      _producerPrefixRun, _boundaryRun, boundaryLookup, _squeezeRun,
      afterAlphaExact, _final256Run, outputsLength, advancesLength,
      coordinates, terminalExact, _callsExact, exactDecode, operationalValue,
      final256Lookup⟩ :=
    exact_compiler_constructs_alpha_zero_prefix_coordinates input
  let producerInput : ShaInput :=
    bytes beforeAlphaProducer.digest ++
      [domAbsorb,
        (alphaZeroBoundaryPayload
          (exactOperationalTape input).messages).label] ++
      (alphaZeroBoundaryPayload
        (exactOperationalTape input).messages).data
  let final256Input : ShaInput :=
    bytes afterAlpha.digest ++
      [domAbsorb,
        AspisK1.V7Tag73TranscriptSchedule.Payload.label
          (.final256 (exactOperationalTape input).messages.finalValues)] ++
      AspisK1.V7Tag73TranscriptSchedule.Payload.data
        (.final256 (exactOperationalTape input).messages.finalValues)
  have ordered : ExactRootOrderedQ16Chain input producerInput
      beforeAlpha.digest outputs advances :=
    gamma_table_coordinate_chain_has_exact_root_order transitionRoom input
      producerInput beforeAlpha.digest (by
        simpa [producerInput] using boundaryLookup) coordinates
  have afterDigest : afterAlpha.digest = afterBlocks.digest := by
    simpa using congrArg EvalState.digest afterAlphaExact
  have outputsPositive : 0 < outputs.length := by
    rw [outputsLength]
    exact ((exactOperationalTape input).messages.challengeUse
      (.alpha 0)).consumesBlock
  refine ⟨producerInput, final256Input, beforeAlpha, afterAlpha, afterBlocks,
    afterFinal256, outputs, advances, exactValue, ?_, ordered, outputsLength,
    outputsPositive, advancesLength, terminalExact, afterDigest, rfl, ?_,
    exactDecode, operationalValue⟩
  · simpa [producerInput] using boundaryLookup
  · simpa [final256Input] using final256Lookup

#print axioms exact_compiler_alpha_zero_chain_has_root_order

end

end AspisK1.V7Tag73ExactAlphaZeroRootOrder
