import AspisFormal.K1.V7Tag73ExactAlphaZeroRootOrder
import AspisFormal.K1.V7Tag73ExactFixedQ16JointEventHandoff

/-!
# Alpha-zero successor equals the actual-trial pre-final digest

The work-erased semantic evaluator and the strict source trial both absorb the
selected final nonce into the same recorded q16 base.  Clean root-answer
uniqueness therefore identifies their literal absorb records and fixes the
pre-final digest carried in those inputs.  No SHA-256 injectivity is used.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactAlphaZeroActualTrialPrefinal

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactAlphaZeroRootOrder
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerGammaPrefixCoordinates
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactFinal256DigestRootOrigin
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactQ16CausalCoordinateOrder
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SamplerExactValue
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73SqueezeInputStateInjectivity
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- A canonical final-nonce lookup and an already-recorded final-nonce query
with the same q16-base answer carry the same pre-final digest. -/
theorem final_nonce_lookup_and_root_record_fix_digest
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
    (candidateDigest selectedDigest candidateBase selectedBase : Digest256)
    (selectedActor : QueryActor)
    (candidateLookup : tableLookup (exactOperationalTable input)
        (bytes candidateDigest ++ [domAbsorb, finalWorkNonceLabel] ++
          bytes (exactOperationalTape input).messages.finalGrinding.selected) =
      some candidateBase)
    (baseExact : candidateBase = selectedBase)
    (selectedMember :
      (.machineFresh selectedActor
        (literalFinalWorkKey selectedDigest
          (exactOperationalTape input).messages.finalGrinding.selected).absorbInput
        selectedBase : UnifiedExposureRecord) ∈
        exactFixedRootRecords input.package.root) :
    candidateDigest = selectedDigest := by
  let candidateInput : ShaInput :=
    bytes candidateDigest ++ [domAbsorb, finalWorkNonceLabel] ++
      bytes (exactOperationalTape input).messages.finalGrinding.selected
  obtain ⟨candidateActor, candidateMemberRaw⟩ :=
    exact_final_table_lookup_has_root_record input candidateInput candidateBase
      (by simpa [candidateInput] using candidateLookup)
  have candidateMember :
      (.machineFresh candidateActor candidateInput selectedBase :
          UnifiedExposureRecord) ∈
        exactFixedRootRecords input.package.root := by
    simpa [baseExact] using candidateMemberRaw
  have recordExact :
      (.machineFresh candidateActor candidateInput selectedBase :
          UnifiedExposureRecord) =
        (.machineFresh selectedActor
          (literalFinalWorkKey selectedDigest
            (exactOperationalTape input).messages.finalGrinding.selected).absorbInput
          selectedBase : UnifiedExposureRecord) :=
    List.inj_on_of_nodup_map (exact_root_record_answers_nodup input)
      candidateMember selectedMember rfl
  have inputExact : candidateInput =
      (literalFinalWorkKey selectedDigest
        (exactOperationalTape input).messages.finalGrinding.selected).absorbInput := by
    injection recordExact
  apply digest_bytes_injective
  have prefixExact := congrArg (List.take 32) inputExact
  simpa [candidateInput, RawFinalWorkKey.absorbInput, literalFinalWorkKey]
    using prefixExact

/-- Any final-nonce lookup returning the accepted trial's q16 base starts from
the exact pre-final digest carried by that trial. -/
theorem exact_fixed_k13_actual_trial_prefinal_eq_of_q16_base_lookup
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (trial : ExactCompilerExposureTrial parameters)
    (actual : ExactFixedK13ActualJointTrial input trial)
    (candidateDigest q16Base : Digest256)
    (candidateLookup : tableLookup (exactOperationalTable input)
        (bytes candidateDigest ++ [domAbsorb, finalWorkNonceLabel] ++
          bytes (exactOperationalTape input).messages.finalGrinding.selected) =
      some q16Base)
    (candidateBaseExact : q16Base =
      (exactOperationalRawTrace input).q16BaseDigest) :
    ∃ digest,
      ExactOperationalPrefinalDigest input digest ∧
      candidateDigest = digest := by
  obtain ⟨digest, workAnswer, base, _workAccepted, prefinalOrigin,
      baseExact, pairLabeled, _workLabeled, _workCoordinate, _realized⟩ :=
    actual
  let candidateInput : ShaInput :=
    bytes candidateDigest ++ [domAbsorb, finalWorkNonceLabel] ++
      bytes (exactOperationalTape input).messages.finalGrinding.selected
  obtain ⟨candidateActor, candidateMember⟩ :=
    exact_final_table_lookup_has_root_record input candidateInput q16Base (by
      simpa [candidateInput] using candidateLookup)
  have baseCandidateExact : base = q16Base :=
    baseExact.trans candidateBaseExact.symm
  -- Recover the actual absorb actor without assigning semantic meaning to it.
  rcases pairLabeled with
      ⟨prior, middle, later, workActor, absorbActor, pairExact, _index⟩ |
      ⟨prior, middle, later, workActor, absorbActor, pairExact, _index⟩
  · have absorbMember :
        (.machineFresh absorbActor
          (literalFinalWorkKey digest
            (exactOperationalTape input).messages.finalGrinding.selected).absorbInput
          q16Base : UnifiedExposureRecord) ∈
        exactFixedRootRecords input.package.root := by
      rw [pairExact]
      simp [baseCandidateExact]
    have recordExact :
        (.machineFresh candidateActor candidateInput q16Base :
            UnifiedExposureRecord) =
          (.machineFresh absorbActor
            (literalFinalWorkKey digest
              (exactOperationalTape input).messages.finalGrinding.selected).absorbInput
            q16Base : UnifiedExposureRecord) :=
      List.inj_on_of_nodup_map (exact_root_record_answers_nodup input)
        candidateMember absorbMember rfl
    have inputExact : candidateInput =
        (literalFinalWorkKey digest
          (exactOperationalTape input).messages.finalGrinding.selected).absorbInput := by
      injection recordExact
    refine ⟨digest, prefinalOrigin, ?_⟩
    apply digest_bytes_injective
    have prefixExact := congrArg (List.take 32) inputExact
    simpa [candidateInput, RawFinalWorkKey.absorbInput, literalFinalWorkKey]
      using prefixExact
  · have absorbMember :
        (.machineFresh absorbActor
          (literalFinalWorkKey digest
            (exactOperationalTape input).messages.finalGrinding.selected).absorbInput
          q16Base : UnifiedExposureRecord) ∈
        exactFixedRootRecords input.package.root := by
      rw [pairExact]
      simp [baseCandidateExact]
    have recordExact :
        (.machineFresh candidateActor candidateInput q16Base :
            UnifiedExposureRecord) =
          (.machineFresh absorbActor
            (literalFinalWorkKey digest
              (exactOperationalTape input).messages.finalGrinding.selected).absorbInput
            q16Base : UnifiedExposureRecord) :=
      List.inj_on_of_nodup_map (exact_root_record_answers_nodup input)
        candidateMember absorbMember rfl
    have inputExact : candidateInput =
        (literalFinalWorkKey digest
          (exactOperationalTape input).messages.finalGrinding.selected).absorbInput := by
      injection recordExact
    refine ⟨digest, prefinalOrigin, ?_⟩
    apply digest_bytes_injective
    have prefixExact := congrArg (List.take 32) inputExact
    simpa [candidateInput, RawFinalWorkKey.absorbInput, literalFinalWorkKey]
      using prefixExact

/-- Compact alpha-zero certificate at a proof-relevant K1.3 trial.  The
terminal successor is now identified with the trial's actual pre-final digest,
which is the endpoint needed by the adversary-anchor transport proof. -/
theorem exact_fixed_k13_actual_trial_has_alpha_zero_terminal_profile
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (trial : ExactCompilerExposureTrial parameters)
    (actual : ExactFixedK13ActualJointTrial input trial) :
    ∃ (producerInput : ShaInput)
        (beforeAlpha afterAlpha afterBlocks afterFinal256 : EvalState)
        (outputs advances : List Digest256) (exactValue : QM31Exact)
        (prefinalDigest : Digest256),
      ExactRootOrderedQ16Chain input producerInput beforeAlpha.digest
          outputs advances ∧
      0 < outputs.length ∧
      advances.length = outputs.length ∧
      afterBlocks.digest = gammaTerminalDigest beforeAlpha.digest advances ∧
      afterAlpha.digest = afterBlocks.digest ∧
      afterFinal256.digest = prefinalDigest ∧
      ExactOperationalPrefinalDigest input prefinalDigest ∧
      decodeTagQM31ExactLE
          ((exactOperationalTape input).messages.challengeValue (.alpha 0)) =
        some exactValue ∧
      exactOperationalChallenge input (.alpha 0) = exactValue := by
  obtain ⟨producerInput, _final256Input, beforeAlpha, afterAlpha, afterBlocks,
      afterFinal256, outputs, advances, exactValue, _workAnswer, q16Base,
      _producerLookup, _producerBoundary, ordered, _outputsLength,
      outputsPositive,
      advancesLength, terminalExact, afterAlphaExact, _final256InputExact,
      _final256Lookup, _workLookup, _workAccepted, finalNonceLookup,
      q16BaseExact, _acceptedParameter, exactDecode, operationalExact⟩ :=
    exact_compiler_alpha_zero_chain_has_root_order transitionRoom input
  obtain ⟨prefinalDigest, prefinalOrigin, prefinalExact⟩ :=
    exact_fixed_k13_actual_trial_prefinal_eq_of_q16_base_lookup input trial
      actual afterFinal256.digest q16Base finalNonceLookup q16BaseExact
  exact ⟨producerInput, beforeAlpha, afterAlpha, afterBlocks, afterFinal256,
    outputs, advances, exactValue, prefinalDigest, ordered, outputsPositive,
    advancesLength, terminalExact, afterAlphaExact, prefinalExact,
    prefinalOrigin, exactDecode, operationalExact⟩

#print axioms exact_fixed_k13_actual_trial_prefinal_eq_of_q16_base_lookup
#print axioms exact_fixed_k13_actual_trial_has_alpha_zero_terminal_profile
#print axioms final_nonce_lookup_and_root_record_fix_digest

end

end AspisK1.V7Tag73ExactAlphaZeroActualTrialPrefinal
