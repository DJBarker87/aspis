import AspisFormal.K1.V7Tag73ExactAlphaZeroPrefixCoordinates
import AspisFormal.K1.V7Tag73ExactDagCandidateLabeledRootRouting
import AspisFormal.K1.V7Tag73ExactQ16CausalCoordinateOrder
import AspisFormal.K1.V7Tag73SqueezeInputStateInjectivity

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
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactAlphaZeroPrefixCoordinates
open AspisK1.V7Tag73ExactCompilerGammaPrefixCoordinates
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFinal256DigestRootOrigin
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactQ16CausalCoordinateOrder
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkDigestProbability
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73SqueezeInputStateInjectivity
open AspisK1.V7Tag73TranscriptSchedule
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Two canonical final-nonce absorptions returning the same clean root answer
have the same pre-final state digest.  This uses answer uniqueness in the
literal root, not injectivity of SHA-256. -/
theorem same_final_nonce_answer_fixes_prefinal_digest
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (leftDigest rightDigest answer : Digest256)
    (leftLookup : tableLookup (exactOperationalTable input)
        (bytes leftDigest ++ [domAbsorb, finalWorkNonceLabel] ++
          bytes (exactOperationalTape input).messages.finalGrinding.selected) =
      some answer)
    (rightLookup : tableLookup (exactOperationalTable input)
        (bytes rightDigest ++ [domAbsorb, finalWorkNonceLabel] ++
          bytes (exactOperationalTape input).messages.finalGrinding.selected) =
      some answer) :
    leftDigest = rightDigest := by
  let leftInput : ShaInput :=
    bytes leftDigest ++ [domAbsorb, finalWorkNonceLabel] ++
      bytes (exactOperationalTape input).messages.finalGrinding.selected
  let rightInput : ShaInput :=
    bytes rightDigest ++ [domAbsorb, finalWorkNonceLabel] ++
      bytes (exactOperationalTape input).messages.finalGrinding.selected
  obtain ⟨leftActor, leftMember⟩ :=
    exact_final_table_lookup_has_root_record input leftInput answer (by
      simpa [leftInput] using leftLookup)
  obtain ⟨rightActor, rightMember⟩ :=
    exact_final_table_lookup_has_root_record input rightInput answer (by
      simpa [rightInput] using rightLookup)
  have recordExact :
      (.machineFresh leftActor leftInput answer : UnifiedExposureRecord) =
        (.machineFresh rightActor rightInput answer : UnifiedExposureRecord) :=
    List.inj_on_of_nodup_map (exact_root_record_answers_nodup input)
      leftMember rightMember rfl
  have inputExact : leftInput = rightInput := by injection recordExact
  apply digest_bytes_injective
  have prefixExact := congrArg (List.take 32) inputExact
  simpa [leftInput, rightInput] using prefixExact

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
      (outputs advances : List Digest256) (exactValue : QM31Exact)
      (workAnswer q16Base : Digest256),
      tableLookup (exactOperationalTable input) producerInput =
          some beforeAlpha.digest ∧
      (∃ (producerDigest : Digest256),
        producerInput =
          bytes producerDigest ++
            [domAbsorb,
              (alphaZeroBoundaryPayload
                (exactOperationalTape input).messages).label] ++
            (alphaZeroBoundaryPayload
              (exactOperationalTape input).messages).data) ∧
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
      tableLookup (exactOperationalTable input)
          (bytes afterFinal256.digest ++ [domGrind] ++
            bytes
              (exactOperationalTape input).messages.finalGrinding.selected) =
        some workAnswer ∧
      FinalWork34Accepted workAnswer ∧
      tableLookup (exactOperationalTable input)
          (bytes afterFinal256.digest ++ [domAbsorb, finalWorkNonceLabel] ++
            bytes
              (exactOperationalTape input).messages.finalGrinding.selected) =
        some q16Base ∧
      q16Base = (exactOperationalRawTrace input).q16BaseDigest ∧
      decodeChallengeParameter exactSecureCircleParameterMap (.alpha 0)
          outputs =
        some ((exactOperationalTape input).messages.challengeValue (.alpha 0)) ∧
      decodeTagQM31ExactLE
          ((exactOperationalTape input).messages.challengeValue (.alpha 0)) =
        some exactValue ∧
      exactOperationalChallenge input (.alpha 0) = exactValue := by
  obtain ⟨_evaluator, _segments, beforeAlphaProducer, beforeAlpha,
      afterAlpha, afterBlocks, afterFinal256, outputs, advances, exactValue,
      _producerPrefixRun, _boundaryRun, boundaryLookup, _squeezeRun,
      afterAlphaExact, _final256Run, outputsLength, advancesLength,
      coordinates, terminalExact, _callsExact, acceptedParameter, exactDecode,
      operationalValue, final256Lookup, alphaFinalNonceLookup,
      alphaQ16BaseExact⟩ :=
    exact_compiler_constructs_alpha_zero_prefix_coordinates input
  obtain ⟨strictBeforeFinal256, strictPrefinalDigest, workAnswer, q16Base,
      _strictFinal256Lookup, workLookup, workAccepted, strictFinalNonceLookup,
      strictQ16BaseExact, _strictPrefixRun⟩ :=
    exact_operational_final256_and_work_lookups input
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
  have prefinalExact : afterFinal256.digest = strictPrefinalDigest := by
    apply same_final_nonce_answer_fixes_prefinal_digest input
      afterFinal256.digest strictPrefinalDigest q16Base
    · simpa [strictQ16BaseExact, alphaQ16BaseExact] using
        alphaFinalNonceLookup
    · exact strictFinalNonceLookup
  refine ⟨producerInput, final256Input, beforeAlpha, afterAlpha, afterBlocks,
    afterFinal256, outputs, advances, exactValue, workAnswer, q16Base, ?_,
    ⟨beforeAlphaProducer.digest, rfl⟩, ordered, outputsLength, outputsPositive,
    advancesLength, terminalExact,
    afterDigest, rfl, ?_, ?_, workAccepted, ?_, strictQ16BaseExact,
    acceptedParameter, exactDecode, operationalValue⟩
  · simpa [producerInput] using boundaryLookup
  · simpa [final256Input] using final256Lookup
  · simpa [prefinalExact] using workLookup
  · simpa [prefinalExact] using strictFinalNonceLookup

#print axioms same_final_nonce_answer_fixes_prefinal_digest
#print axioms exact_compiler_alpha_zero_chain_has_root_order

end

end AspisK1.V7Tag73ExactAlphaZeroRootOrder
