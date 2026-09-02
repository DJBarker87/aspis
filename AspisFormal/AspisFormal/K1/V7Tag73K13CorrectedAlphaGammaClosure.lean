import AspisFormal.K1.V7Tag73K13CorrectedPairProfileInvariant
import AspisFormal.K1.V7Tag73ExactAlphaZeroActualTrialPrefinal
import AspisFormal.K1.V7Tag73ExactPairAlphaAdvanceChainClosure
import AspisFormal.K1.V7Tag73ExactAlphaZeroRootOrder
import AspisFormal.K1.V7Tag73ExactCompilerGammaPrefixCoordinates

/-!
# Corrected K1.3 alpha/gamma causal closure

This leaf works only with the corrected pre-q16 witness.  It exposes the
common canonical final256 record retained by the equal selected prefixes, then
uses that record as the terminal anchor for variable-prefix alpha and gamma
duplex replay.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73K13CorrectedAlphaGammaClosure

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactAdversaryAnchorSelectedInputInvariant
open AspisK1.V7Tag73ExactAlphaZeroActualTrialPrefinal
open AspisK1.V7Tag73ExactAlphaZeroRootOrder
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open AspisK1.V7Tag73ExactCompilerGammaPrefixCoordinates
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactQ16CausalCoordinateOrder
open AspisK1.V7Tag73ExactRootCausalChain
open AspisK1.V7Tag73ExactPairAlphaAdvanceChainClosure
open AspisK1.V7Tag73ExactPairCoordinateProfileInvariant
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K13CorrectedPairProfileInvariant
open AspisK1.V7Tag73K13CorrectedPairTrialProbability
open AspisK1.V7Tag73K13PreQ16JointEventHandoff
open AspisK1.V7Tag73K13PreQ16RootInvariant
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73RootAbsorbInputInjectivity
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73SqueezeInputStateInjectivity
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- The two canonical final256 producer records have the same input and
answer inside the shared pre-anchor prefix. -/
theorem exact_preQ16_clean_pair_common_final256_record
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (transitionRoom : 2 ≤ transitionFuel)
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (left right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (leftWitness : ExactPreQ16CleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, left) foldTrial
        finalTrial)
    (rightWitness : ExactPreQ16CleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, right) foldTrial
        finalTrial)
    (priorExact : leftWitness.joint.prior = rightWitness.joint.prior) :
    ∃ (leftBefore rightBefore : EvalState) (digest : Digest256)
        (leftActor rightActor : QueryActor),
      let leftInput := bytes leftBefore.digest ++ [domAbsorb, final256Label] ++
        encodeBlocks
          (exactOperationalTape leftWitness.joint.input).messages.finalValues
      let rightInput := bytes rightBefore.digest ++ [domAbsorb, final256Label] ++
        encodeBlocks
          (exactOperationalTape rightWitness.joint.input).messages.finalValues
      leftInput = rightInput ∧
        tableLookup (exactOperationalTable leftWitness.joint.input) leftInput =
          some digest ∧
        tableLookup (exactOperationalTable rightWitness.joint.input) rightInput =
          some digest ∧
        (.machineFresh leftActor leftInput digest : UnifiedExposureRecord) ∈
          leftWitness.joint.prior ∧
        (.machineFresh rightActor rightInput digest : UnifiedExposureRecord) ∈
          rightWitness.joint.prior ∧
        HasLiteralStatePrefix digest leftWitness.joint.pivotInput ∧
        HasLiteralStatePrefix digest rightWitness.joint.pivotInput := by
  classical
  obtain ⟨leftBefore, leftDigest, leftActor, leftLookup, leftMember,
      leftPrefix⟩ := exact_preQ16_k13_final256_record_mem_prior
        transitionRoom finalTrial leftWitness.joint
  obtain ⟨rightBefore, rightDigest, rightActor, rightLookup, rightMember,
      rightPrefix⟩ := exact_preQ16_k13_final256_record_mem_prior
        transitionRoom finalTrial rightWitness.joint
  have selectedInputExact := exact_preQ16_clean_pair_selected_input_eq foldTrial
    finalTrial hidden left right leftWitness rightWitness priorExact
  have digestExact : leftDigest = rightDigest :=
    literal_prefix_input_eq_fixes_digest leftPrefix rightPrefix
      selectedInputExact
  let leftInput : ShaInput := bytes leftBefore.digest ++ [domAbsorb,
    final256Label] ++ encodeBlocks
      (exactOperationalTape leftWitness.joint.input).messages.finalValues
  let rightInput : ShaInput := bytes rightBefore.digest ++ [domAbsorb,
    final256Label] ++ encodeBlocks
      (exactOperationalTape rightWitness.joint.input).messages.finalValues
  have rightMemberCommon :
      (.machineFresh rightActor rightInput leftDigest : UnifiedExposureRecord) ∈
        leftWitness.joint.prior := by
    rw [priorExact]
    simpa [rightInput, digestExact,
      AspisK1.V7Tag73TranscriptSchedule.Payload.label,
      AspisK1.V7Tag73TranscriptSchedule.Payload.data] using rightMember
  have priorAnswersNodup :
      (leftWitness.joint.prior.map UnifiedExposureRecord.answer).Nodup := by
    have fullNodup := exact_root_record_answers_nodup leftWitness.joint.input
    rw [leftWitness.joint.rootExact, List.map_append, List.map_cons] at fullNodup
    exact (List.nodup_append.mp fullNodup).1
  have inputExact : leftInput = rightInput := by
    have recordExact :
        (.machineFresh leftActor leftInput leftDigest : UnifiedExposureRecord) =
          .machineFresh rightActor rightInput leftDigest :=
      List.inj_on_of_nodup_map priorAnswersNodup
        (by simpa [leftInput,
          AspisK1.V7Tag73TranscriptSchedule.Payload.label,
          AspisK1.V7Tag73TranscriptSchedule.Payload.data] using leftMember)
        rightMemberCommon rfl
    injection recordExact
  refine ⟨leftBefore, rightBefore, leftDigest, leftActor, rightActor, ?_⟩
  exact ⟨inputExact,
    by simpa [leftInput,
      AspisK1.V7Tag73TranscriptSchedule.Payload.label,
      AspisK1.V7Tag73TranscriptSchedule.Payload.data] using leftLookup,
    by simpa [rightInput, digestExact,
      AspisK1.V7Tag73TranscriptSchedule.Payload.label,
      AspisK1.V7Tag73TranscriptSchedule.Payload.data] using rightLookup,
    by simpa [leftInput,
      AspisK1.V7Tag73TranscriptSchedule.Payload.label,
      AspisK1.V7Tag73TranscriptSchedule.Payload.data] using leftMember,
    by simpa [rightInput, digestExact,
      AspisK1.V7Tag73TranscriptSchedule.Payload.label,
      AspisK1.V7Tag73TranscriptSchedule.Payload.data] using rightMember,
    leftPrefix, by simpa [digestExact] using rightPrefix⟩

/-- One accepted alpha chain reaches the state prefix carried by its retained
canonical final256 producer record.  The equality is recovered by the actual
final-nonce pair and root-record uniqueness, never by reversing SHA-256. -/
theorem exact_preQ16_alpha_chain_reaches_final256_record
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (witness : ExactPreQ16CleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder sample foldTrial
        finalTrial)
    (canonicalBefore : EvalState) (canonicalDigest : Digest256)
    (canonicalActor : QueryActor)
    (canonicalLookup : tableLookup (exactOperationalTable witness.joint.input)
      (bytes canonicalBefore.digest ++ [domAbsorb, final256Label] ++
        encodeBlocks
          (exactOperationalTape witness.joint.input).messages.finalValues) =
        some canonicalDigest)
    (canonicalMember :
      (.machineFresh canonicalActor
        (bytes canonicalBefore.digest ++ [domAbsorb, final256Label] ++
          encodeBlocks
            (exactOperationalTape witness.joint.input).messages.finalValues)
        canonicalDigest : UnifiedExposureRecord) ∈ witness.joint.prior)
    (canonicalPrefix :
      HasLiteralStatePrefix canonicalDigest witness.joint.pivotInput) :
    ∃ (producerInput : ShaInput) (beforeAlpha : EvalState)
        (outputs advances : List Digest256) (exactValue : QM31Exact),
      ExactRootOrderedQ16Chain witness.joint.input producerInput
          beforeAlpha.digest outputs advances ∧
      (∀ state, producerInput ≠ gammaAdvanceInput state) ∧
      0 < outputs.length ∧
      outputs.length ≤ 4 ∧
      gammaTerminalDigest beforeAlpha.digest advances =
        canonicalBefore.digest ∧
      decodeChallengeParameter exactSecureCircleParameterMap (.alpha 0)
          outputs = some
            ((exactOperationalTape witness.joint.input).messages.challengeValue
              (.alpha 0)) ∧
      decodeTagQM31ExactLE
          ((exactOperationalTape witness.joint.input).messages.challengeValue
            (.alpha 0)) = some exactValue ∧
      exactOperationalChallenge witness.joint.input (.alpha 0) = exactValue := by
  obtain ⟨producerInput, final256Input, beforeAlpha, afterAlpha, afterBlocks,
      afterFinal256, outputs, advances, exactValue, _workAnswer, q16Base,
      _producerLookup, producerBoundary, chain, outputsLength, outputsPositive,
      _advancesLength, terminalExact, afterAlphaExact, final256InputExact,
      final256Lookup, _workLookup, _workAccepted, finalNonceLookup,
      q16BaseExact, acceptedParameter, exactDecode, operationalExact⟩ :=
    exact_compiler_alpha_zero_chain_has_root_order transitionRoom
      witness.joint.input
  obtain ⟨actualPrior, actualLater, selectedActor, selectedInput,
      selectedAnswer, selectedDigest, selectedBase, absorbActor, actualRootExact,
      actualTrialExact, selectedPrefix, _prefinalOrigin, selectedBaseExact,
      absorbMember⟩ :=
    exact_fixed_k13_actual_trial_has_selected_prefinal_prefix
      witness.joint.input finalTrial witness.joint.actualTrial
  have selectedRecordExact :
      (.machineFresh witness.joint.pivotActor witness.joint.pivotInput
          witness.joint.pivotAnswer : UnifiedExposureRecord) =
        .machineFresh selectedActor selectedInput selectedAnswer := by
    have witnessAt :
        (exactFixedRootRecords witness.joint.input.package.root)[finalTrial.val]? =
          some (.machineFresh witness.joint.pivotActor witness.joint.pivotInput
            witness.joint.pivotAnswer : UnifiedExposureRecord) := by
      rw [witness.joint.rootExact, witness.joint.trialExact]
      simp
    have actualAt :
        (exactFixedRootRecords witness.joint.input.package.root)[finalTrial.val]? =
          some (.machineFresh selectedActor selectedInput selectedAnswer :
            UnifiedExposureRecord) := by
      rw [actualRootExact, actualTrialExact]
      simp
    rw [witnessAt] at actualAt
    exact Option.some.inj actualAt
  have selectedInputExact : witness.joint.pivotInput = selectedInput := by
    injection selectedRecordExact
  have afterFinalExact : afterFinal256.digest = selectedDigest :=
    final_nonce_lookup_and_root_record_fix_digest witness.joint.input
      afterFinal256.digest selectedDigest q16Base selectedBase absorbActor
      finalNonceLookup (q16BaseExact.trans selectedBaseExact.symm) absorbMember
  have selectedDigestExact : canonicalDigest = selectedDigest :=
    literal_prefix_input_eq_fixes_digest canonicalPrefix selectedPrefix
      selectedInputExact
  have finalAnswerExact : afterFinal256.digest = canonicalDigest :=
    afterFinalExact.trans selectedDigestExact.symm
  obtain ⟨finalActor, finalMemberRaw⟩ :=
    exact_final_table_lookup_has_root_record witness.joint.input final256Input
      afterFinal256.digest final256Lookup
  have finalMember :
      (.machineFresh finalActor final256Input canonicalDigest :
        UnifiedExposureRecord) ∈
          exactFixedRootRecords witness.joint.input.package.root := by
    simpa [finalAnswerExact] using finalMemberRaw
  have canonicalRootMember :
      (.machineFresh canonicalActor
        (bytes canonicalBefore.digest ++ [domAbsorb, final256Label] ++
          encodeBlocks
            (exactOperationalTape witness.joint.input).messages.finalValues)
        canonicalDigest : UnifiedExposureRecord) ∈
          exactFixedRootRecords witness.joint.input.package.root := by
    rw [witness.joint.rootExact]
    exact List.mem_append_left _ canonicalMember
  have finalInputExact : final256Input =
      bytes canonicalBefore.digest ++ [domAbsorb, final256Label] ++
        encodeBlocks
          (exactOperationalTape witness.joint.input).messages.finalValues := by
    have recordExact := List.inj_on_of_nodup_map
      (exact_root_record_answers_nodup witness.joint.input) finalMember
        canonicalRootMember rfl
    injection recordExact
  have terminalDigestExact :
      gammaTerminalDigest beforeAlpha.digest advances =
        canonicalBefore.digest := by
    rw [← terminalExact, ← afterAlphaExact]
    apply digest_bytes_injective
    have prefixExact := congrArg (List.take 32) finalInputExact
    simpa [final256InputExact] using prefixExact
  have outputsBound : outputs.length ≤ 4 := by
    rw [outputsLength]
    simpa [samplerMode, samplerBlockCap] using
      ((exactOperationalTape witness.joint.input).messages.challengeUse
        (.alpha 0)).withinDeployedCap
  have producerDisjoint : ∀ state,
      producerInput ≠ gammaAdvanceInput state :=
    alpha_zero_boundary_ne_gamma_advance
      (exactOperationalTape witness.joint.input).messages producerInput
        producerBoundary
  exact ⟨producerInput, beforeAlpha, outputs, advances, exactValue, chain,
    producerDisjoint, outputsPositive, outputsBound, terminalDigestExact,
    acceptedParameter, exactDecode, operationalExact⟩

/-- Equal corrected pre-q16 prefixes force identical alpha initial and advance
states and the same consumed block count.  Pointwise output lookups are then
at one common literal SHA input; answer equality is intentionally left to the
cached/named router join. -/
theorem exact_preQ16_clean_pair_alpha_advance_states_eq
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (transitionRoom : 2 ≤ transitionFuel)
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (left right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (leftWitness : ExactPreQ16CleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, left) foldTrial
        finalTrial)
    (rightWitness : ExactPreQ16CleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, right) foldTrial
        finalTrial)
    (priorExact : leftWitness.joint.prior = rightWitness.joint.prior) :
    ∃ (leftOutputs leftAdvances rightOutputs rightAdvances : List Digest256),
      leftAdvances = rightAdvances ∧
      leftOutputs.length = rightOutputs.length ∧
      (∀ index (leftBound : index < leftOutputs.length),
        ∀ rightBound : index < rightOutputs.length,
          ∃ state,
            tableLookup (exactOperationalTable leftWitness.joint.input)
                (gammaOutputInput state) = some leftOutputs[index] ∧
              tableLookup (exactOperationalTable rightWitness.joint.input)
                (gammaOutputInput state) = some rightOutputs[index]) := by
  obtain ⟨leftCanonicalBefore, rightCanonicalBefore, canonicalDigest,
      leftCanonicalActor, rightCanonicalActor, canonicalInputExact,
      leftCanonicalLookup, rightCanonicalLookup, leftCanonicalMember,
      rightCanonicalMember, _leftCanonicalPivotPrefix,
      _rightCanonicalPivotPrefix⟩ :=
    exact_preQ16_clean_pair_common_final256_record transitionRoom foldTrial
      finalTrial hidden left right leftWitness rightWitness priorExact
  obtain ⟨leftProducer, leftBeforeAlpha, leftOutputs, leftAdvances,
      _leftValue, leftChain, leftBoundary, leftPositive, leftBound,
      leftTerminal, _leftAccepted, _leftDecode, _leftOperational⟩ :=
    exact_preQ16_alpha_chain_reaches_final256_record transitionRoom foldTrial
      finalTrial leftWitness leftCanonicalBefore canonicalDigest
        leftCanonicalActor leftCanonicalLookup leftCanonicalMember
        _leftCanonicalPivotPrefix
  obtain ⟨rightProducer, rightBeforeAlpha, rightOutputs, rightAdvances,
      _rightValue, rightChain, rightBoundary, rightPositive, rightBound,
      rightTerminal, _rightAccepted, _rightDecode, _rightOperational⟩ :=
    exact_preQ16_alpha_chain_reaches_final256_record transitionRoom foldTrial
      finalTrial rightWitness rightCanonicalBefore canonicalDigest
        rightCanonicalActor rightCanonicalLookup rightCanonicalMember
        _rightCanonicalPivotPrefix
  have canonicalBeforeExact :
      leftCanonicalBefore.digest = rightCanonicalBefore.digest := by
    apply digest_bytes_injective
    have prefixExact := congrArg (List.take 32) canonicalInputExact
    simpa using prefixExact
  let leftFinalInput : ShaInput :=
    bytes leftCanonicalBefore.digest ++ [domAbsorb, final256Label] ++
      encodeBlocks
        (exactOperationalTape leftWitness.joint.input).messages.finalValues
  let rightFinalInput : ShaInput :=
    bytes rightCanonicalBefore.digest ++ [domAbsorb, final256Label] ++
      encodeBlocks
        (exactOperationalTape rightWitness.joint.input).messages.finalValues
  have leftFinalPrefix : HasLiteralStatePrefix
      (gammaTerminalDigest leftBeforeAlpha.digest leftAdvances)
        leftFinalInput := by
    rw [leftTerminal]
    simp [leftFinalInput, HasLiteralStatePrefix]
  have rightFinalPrefix : HasLiteralStatePrefix
      (gammaTerminalDigest rightBeforeAlpha.digest rightAdvances)
        rightFinalInput := by
    rw [rightTerminal]
    simp [rightFinalInput, HasLiteralStatePrefix]
  obtain ⟨leftBlock, _leftOutput, leftAdvanceActor, _leftOutputLookup,
      leftAdvanceLookup, leftAdvanceMember⟩ :=
    exact_alpha_terminal_advance_mem_anchor_prior transitionRoom
      leftWitness.joint.input leftWitness.joint.prior leftWitness.joint.later
      (.machineFresh leftWitness.joint.pivotActor leftWitness.joint.pivotInput
        leftWitness.joint.pivotAnswer) leftWitness.joint.rootExact leftProducer
      leftBeforeAlpha.digest leftOutputs leftAdvances leftChain leftPositive
      leftFinalInput canonicalDigest leftFinalPrefix
      (by simpa [leftFinalInput] using leftCanonicalLookup)
      leftCanonicalActor (by simpa [leftFinalInput] using leftCanonicalMember)
  obtain ⟨rightBlock, _rightOutput, rightAdvanceActor, _rightOutputLookup,
      rightAdvanceLookup, rightAdvanceMember⟩ :=
    exact_alpha_terminal_advance_mem_anchor_prior transitionRoom
      rightWitness.joint.input rightWitness.joint.prior rightWitness.joint.later
      (.machineFresh rightWitness.joint.pivotActor rightWitness.joint.pivotInput
        rightWitness.joint.pivotAnswer) rightWitness.joint.rootExact rightProducer
      rightBeforeAlpha.digest rightOutputs rightAdvances rightChain rightPositive
      rightFinalInput canonicalDigest rightFinalPrefix
      (by simpa [rightFinalInput] using rightCanonicalLookup)
      rightCanonicalActor (by simpa [rightFinalInput] using rightCanonicalMember)
  have rightTerminalCommon :
      gammaTerminalDigest rightBeforeAlpha.digest rightAdvances =
        leftCanonicalBefore.digest :=
    rightTerminal.trans canonicalBeforeExact.symm
  have rightAdvanceLookupCommon :
      tableLookup (exactOperationalTable rightWitness.joint.input)
          (gammaAdvanceInput rightBlock) =
        some leftCanonicalBefore.digest := by
    simpa [rightTerminal, canonicalBeforeExact] using rightAdvanceLookup
  have rightAdvanceMemberCommon :
      (.machineFresh rightAdvanceActor (gammaAdvanceInput rightBlock)
          leftCanonicalBefore.digest : UnifiedExposureRecord) ∈
        rightWitness.joint.prior := by
    simpa [rightTerminal, canonicalBeforeExact] using rightAdvanceMember
  obtain ⟨initialExact, advancesExact, lengthsExact⟩ :=
    exact_equal_root_priors_ordered_chain_advance_states_eq
      leftWitness.joint.input rightWitness.joint.input leftWitness.joint.prior
      rightWitness.joint.prior leftWitness.joint.later rightWitness.joint.later
      (.machineFresh leftWitness.joint.pivotActor leftWitness.joint.pivotInput
        leftWitness.joint.pivotAnswer)
      (.machineFresh rightWitness.joint.pivotActor rightWitness.joint.pivotInput
        rightWitness.joint.pivotAnswer)
      leftWitness.joint.rootExact rightWitness.joint.rootExact priorExact
      leftProducer rightProducer leftBeforeAlpha.digest rightBeforeAlpha.digest
      leftOutputs leftAdvances rightOutputs rightAdvances leftChain rightChain
      leftBoundary rightBoundary (gammaAdvanceInput leftBlock)
      (gammaAdvanceInput rightBlock) leftCanonicalBefore.digest leftTerminal
      rightTerminalCommon (by simpa [leftTerminal] using leftAdvanceLookup)
      rightAdvanceLookupCommon leftAdvanceActor rightAdvanceActor
      (by simpa [leftTerminal] using leftAdvanceMember)
      rightAdvanceMemberCommon 4 leftBound rightBound
  have pointwise := exact_pair_ordered_chains_output_lookups_at_common_states
    leftChain rightChain initialExact advancesExact lengthsExact
  refine ⟨leftOutputs, leftAdvances, rightOutputs, rightAdvances,
    advancesExact, lengthsExact, ?_⟩
  intro index leftIndex rightIndex
  exact pointwise index leftIndex

/-- Once the causal router has identified equal answers at every consumed
alpha coordinate, the deployed first-success decoder forces one common
alpha-zero value.  This lemma deliberately separates the remaining causal
answer-routing problem from list extensionality and field decoding. -/
theorem exact_operational_alpha_zero_eq_of_pointwise_outputs
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {leftSample rightSample : ExactCompilerSample HiddenTape parameters}
    (leftInput : ExactK12OperationalInput transitionFuel configuration
      projection fixedInstance leftSample)
    (rightInput : ExactK12OperationalInput transitionFuel configuration
      projection fixedInstance rightSample)
    (leftOutputs rightOutputs : List Digest256)
    (leftRaw rightRaw : Qm31Bytes)
    (leftValue rightValue : QM31Exact)
    (lengthsExact : leftOutputs.length = rightOutputs.length)
    (pointwise : ∀ index (leftBound : index < leftOutputs.length),
      let rightBound : index < rightOutputs.length := by omega
      leftOutputs[index] = rightOutputs[index])
    (leftAccepted :
      decodeChallengeParameter exactSecureCircleParameterMap (.alpha 0)
        leftOutputs = some leftRaw)
    (rightAccepted :
      decodeChallengeParameter exactSecureCircleParameterMap (.alpha 0)
        rightOutputs = some rightRaw)
    (leftDecode : decodeTagQM31ExactLE leftRaw = some leftValue)
    (rightDecode : decodeTagQM31ExactLE rightRaw = some rightValue)
    (leftOperational : exactOperationalChallenge leftInput (.alpha 0) =
      leftValue)
    (rightOperational : exactOperationalChallenge rightInput (.alpha 0) =
      rightValue) :
    exactOperationalChallenge leftInput (.alpha 0) =
      exactOperationalChallenge rightInput (.alpha 0) := by
  have outputsExact : leftOutputs = rightOutputs := by
    apply List.ext_getElem
    · exact lengthsExact
    · intro index leftBound rightBound
      exact pointwise index leftBound
  have rawExact : leftRaw = rightRaw := by
    apply decodeChallengeParameter_functional exactSecureCircleParameterMap
      (.alpha 0) leftOutputs leftRaw rightRaw leftAccepted
    simpa [outputsExact] using rightAccepted
  have valueExact : leftValue = rightValue := by
    apply Option.some.inj
    calc
      some leftValue = decodeTagQM31ExactLE leftRaw := leftDecode.symm
      _ = decodeTagQM31ExactLE rightRaw := by rw [rawExact]
      _ = some rightValue := rightDecode
  exact leftOperational.trans (valueExact.trans rightOperational.symm)

#print axioms exact_preQ16_clean_pair_common_final256_record
#print axioms exact_preQ16_alpha_chain_reaches_final256_record
#print axioms exact_preQ16_clean_pair_alpha_advance_states_eq
#print axioms exact_operational_alpha_zero_eq_of_pointwise_outputs

end

end AspisK1.V7Tag73K13CorrectedAlphaGammaClosure
