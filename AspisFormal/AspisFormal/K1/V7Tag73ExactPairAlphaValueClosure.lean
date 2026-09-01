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
open AspisK1.V7Tag73ExactAdversaryAnchorFinalProfile
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

/-- Pointwise realization of every consumed alpha slot determines the exact
chronological prefix of the four-block tape.  This is the alpha analogue of
the already checked q16 decoder-prefix bridge, specialized to the deployed
four-block cap. -/
theorem alpha_blocks_eq_full_tape_take_of_every_slot
    (full : Fin 4 → Digest256) (blocks : List Digest256)
    (withinTape : blocks.length ≤ 4)
    (slotExact : ∀ (block : Fin 4)
      (consumed : block.val < blocks.length),
      full block = blocks[block.val]'consumed) :
    blocks = (List.ofFn full).take blocks.length := by
  apply List.ext_getElem
  · simp [withinTape]
  · intro index leftBound rightBound
    have indexBound : index < 4 := Nat.lt_of_lt_of_le leftBound withinTape
    simp only [List.getElem_take, List.getElem_ofFn]
    exact (slotExact ⟨index, indexBound⟩ leftBound).symm

/-- Once both literal accepted decoders are routed slot by slot to one common
four-block coordinate, all remaining fields of the cross-fibre alpha binding
are source facts.  The unresolved controller proof now only has to establish
the two `slotExact` hypotheses; list-prefix and first-success reasoning are no
longer mixed into that causal argument. -/
def exact_pair_alpha_common_prefix_binding_of_every_slot
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
    (full : Fin 4 → Digest256)
    (leftBlocks rightBlocks : List Digest256)
    (leftRaw rightRaw : Qm31Bytes)
    (leftValue rightValue : QM31Exact)
    (leftWithin : leftBlocks.length ≤ 4)
    (rightWithin : rightBlocks.length ≤ 4)
    (leftSlotExact : ∀ (block : Fin 4)
      (consumed : block.val < leftBlocks.length),
      full block = leftBlocks[block.val]'consumed)
    (rightSlotExact : ∀ (block : Fin 4)
      (consumed : block.val < rightBlocks.length),
      full block = rightBlocks[block.val]'consumed)
    (leftAccepted :
      decodeChallengeParameter exactSecureCircleParameterMap (.alpha 0)
        leftBlocks = some leftRaw)
    (rightAccepted :
      decodeChallengeParameter exactSecureCircleParameterMap (.alpha 0)
        rightBlocks = some rightRaw)
    (leftDecode : decodeTagQM31ExactLE leftRaw = some leftValue)
    (rightDecode : decodeTagQM31ExactLE rightRaw = some rightValue)
    (leftOperational : exactOperationalChallenge leftInput (.alpha 0) =
      leftValue)
    (rightOperational : exactOperationalChallenge rightInput (.alpha 0) =
      rightValue) :
    ExactPairAlphaCommonPrefixBinding leftInput rightInput := by
  exact
    { full := full
      leftBlocks := leftBlocks
      rightBlocks := rightBlocks
      leftRaw := leftRaw
      rightRaw := rightRaw
      leftValue := leftValue
      rightValue := rightValue
      leftPrefix := alpha_blocks_eq_full_tape_take_of_every_slot full leftBlocks
        leftWithin leftSlotExact
      rightPrefix := alpha_blocks_eq_full_tape_take_of_every_slot full
        rightBlocks rightWithin rightSlotExact
      leftAccepted := leftAccepted
      rightAccepted := rightAccepted
      leftDecode := leftDecode
      rightDecode := rightDecode
      leftOperational := leftOperational
      rightOperational := rightOperational }

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
    (let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
      transitionFuel foldTrial.val finalTrial.val
      (exactPlainRomCursor configuration hidden).erase
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        left).2.2.1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        right).2.2.1) →
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
    (let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
      transitionFuel foldTrial.val finalTrial.val
      (exactPlainRomCursor configuration hidden).erase
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        left).2.2.1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        right).2.2.1) →
    (exactK13ParsedProof leftWitness.joint.input).gamma =
      (exactK13ParsedProof rightWitness.joint.input).gamma

/-- Source-neutral form of the remaining gamma endpoint.  This is the theorem
the causal query-DAG replay must establish; it mentions neither the parsed
proof nor a source-provider certificate. -/
def ExactFixedCleanK13PairOperationalGammaInvariantOnAdversaryAnchors
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
    (let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
      transitionFuel foldTrial.val finalTrial.val
      (exactPlainRomCursor configuration hidden).erase
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        left).2.2.1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        right).2.2.1) →
    exactOperationalChallenge leftWitness.joint.input .gamma =
      exactOperationalChallenge rightWitness.joint.input .gamma

/-- The current production-source certificate converts the source-neutral
operational gamma theorem to the parsed gamma equality consumed by K1.3.  The
provider is already required by the surrounding K1.3 assembly, so this adds
no trust boundary. -/
theorem exact_fixed_clean_pair_k13_gamma_invariant_of_operational
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
    (operational :
      ExactFixedCleanK13PairOperationalGammaInvariantOnAdversaryAnchors
        transitionFuel configuration projection fixedInstance decoder) :
    ExactFixedCleanK13PairGammaInvariantOnAdversaryAnchors transitionFuel
      configuration projection fixedInstance decoder := by
  intro foldTrial finalTrial hidden left right leftWitness rightWitness anchor
    contextExact foldExact workExact
  obtain ⟨_leftDecoded, _leftDecode, leftBinding⟩ :=
    source (hidden, left) leftWitness.joint.input
  obtain ⟨_rightDecoded, _rightDecode, rightBinding⟩ :=
    source (hidden, right) rightWitness.joint.input
  exact leftBinding.gammaExact.trans
    ((operational foldTrial finalTrial hidden left right leftWitness
      rightWitness anchor contextExact foldExact workExact).trans
        rightBinding.gammaExact.symm)

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
    contextExact foldExact workExact
  have gammaExact := gammaInvariant foldTrial finalTrial hidden left right
    leftWitness rightWitness anchor contextExact foldExact workExact
  obtain ⟨alphaBinding⟩ := alphaSource foldTrial finalTrial hidden left right
    leftWitness rightWitness anchor contextExact foldExact workExact
  exact ⟨gammaExact,
    exact_pair_operational_alpha_zero_eq_of_common_prefix alphaBinding⟩

#print axioms ExactPairAlphaCommonPrefixBinding
#print axioms alpha_blocks_eq_full_tape_take_of_every_slot
#print axioms exact_pair_alpha_common_prefix_binding_of_every_slot
#print axioms exact_pair_operational_alpha_zero_eq_of_common_prefix
#print axioms ExactFixedCleanK13PairAlphaCommonPrefixOnAdversaryAnchors
#print axioms ExactFixedCleanK13PairGammaInvariantOnAdversaryAnchors
#print axioms
  ExactFixedCleanK13PairOperationalGammaInvariantOnAdversaryAnchors
#print axioms exact_fixed_clean_pair_k13_gamma_invariant_of_operational
#print axioms
  exact_fixed_clean_pair_k13_transcript_invariant_of_gamma_and_alpha_source

end

end AspisK1.V7Tag73ExactPairAlphaValueClosure
