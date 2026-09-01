import AspisFormal.K1.V7Tag73ExactCompilerGammaPrefixCoordinates
import AspisFormal.K1.V7Tag73ExactFinal256DigestRootOrigin
import AspisFormal.K1.V7Tag73ExactParsedProofSourceBinding

/-!
# Exact compiler coordinates of the consumed alpha-zero prefix

This file cuts the first fold challenge out of the literal accepted Tag-73
semantic tail.  It retains every consumed output/advance coordinate, the
logical alpha-zero owner in the evaluator call trace, the exact decoded tower
value, and the immediately following `final256` absorption.  It does not try
to recover a logical role from an unlabelled SHA input.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactAlphaZeroPrefixCoordinates

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AcceptedSemanticExecution
open AspisK1.V7Tag73CheckedRefinementFullFutureFreePath
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactCompilerFinalWorkTraceOccurrence
open AspisK1.V7Tag73ExactCompilerGammaPrefixCoordinates
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SamplerExactValue
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73SemanticRoundReplay
open AspisK1.V7Tag73TranscriptSchedule
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Exact accepted semantic-tail events before the alpha-zero sampler. -/
def beforeAlphaZeroTailEvents (messages : Messages) : List MachineEvent :=
  beforeGammaTailEvents messages ++
  [challengeEvent messages .gamma,
   .absorb (.inactiveClaim messages.inactiveClaim),
   challengeEvent messages .kappa] ++
  oodEvents messages ++
  [.absorb (.relationRound 0 (messages.relationSent 0)),
   .grind .fold messages.foldGrinding,
   .check .foldWork,
   .absorb (.foldNonce messages.foldGrinding.selected)]

/-- Prefix ending immediately before the fold-nonce absorption that produces
the alpha-zero sampler's initial digest. -/
def beforeAlphaZeroProducerTailEvents (messages : Messages) :
    List MachineEvent :=
  beforeGammaTailEvents messages ++
  [challengeEvent messages .gamma,
   .absorb (.inactiveClaim messages.inactiveClaim),
   challengeEvent messages .kappa] ++
  oodEvents messages ++
  [.absorb (.relationRound 0 (messages.relationSent 0)),
   .grind .fold messages.foldGrinding,
   .check .foldWork]

def alphaZeroBoundaryPayload (messages : Messages) :
    AspisK1.V7Tag73TranscriptSchedule.Payload :=
  .foldNonce messages.foldGrinding.selected

theorem before_alpha_zero_tail_producer_split (messages : Messages) :
    beforeAlphaZeroTailEvents messages =
      beforeAlphaZeroProducerTailEvents messages ++
        [.absorb (alphaZeroBoundaryPayload messages)] := by
  simp [beforeAlphaZeroTailEvents, beforeAlphaZeroProducerTailEvents,
    alphaZeroBoundaryPayload]

/-- Exact suffix beginning with the value that alpha-zero immediately binds. -/
def afterAlphaZeroTailEvents (messages : Messages) : List MachineEvent :=
  [.absorb (.final256 messages.finalValues),
   .grind .final messages.finalGrinding,
   .check .finalWork,
   .absorb (.finalNonce messages.finalGrinding.selected)]

theorem after_semantic_tail_events_alpha_zero_split (messages : Messages) :
    afterSemanticTailEvents messages =
      beforeAlphaZeroTailEvents messages ++
        challengeEvent messages (.alpha 0) ::
          afterAlphaZeroTailEvents messages := by
  simp [afterSemanticTailEvents, beforeAlphaZeroTailEvents,
    beforeGammaTailEvents, afterAlphaZeroTailEvents]

/-- The accepted operational run exposes the exact alpha-zero duplex prefix
and its causal successor.  The final lookup is the `final256` absorption whose
input begins at the post-alpha digest. -/
theorem exact_compiler_constructs_alpha_zero_prefix_coordinates
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    ∃ (evaluator : CompleteWorkErasedEvaluatorRun (exactOperationalTable input)
        (exactOperationalTape input) (exactOperationalRawTrace input))
      (segments : SemanticExecutionSegments (exactOperationalTable input)
        (exactOperationalTape input).messages evaluator.afterC2
        evaluator.prefixState)
      (beforeAlphaProducer beforeAlpha afterAlpha afterBlocks afterFinal256 :
        EvalState)
      (outputs advances : List Digest256) (exactValue : QM31Exact),
      runMachineEventsWorkErased (exactOperationalTable input)
          (beforeAlphaZeroProducerTailEvents
            (exactOperationalTape input).messages)
          segments.afterSemantic =
        some beforeAlphaProducer ∧
      runMachineEventWorkErased (exactOperationalTable input)
          beforeAlphaProducer
          (.absorb (alphaZeroBoundaryPayload
            (exactOperationalTape input).messages)) =
        some beforeAlpha ∧
      tableLookup (exactOperationalTable input)
          (bytes beforeAlphaProducer.digest ++
            [domAbsorb,
              (alphaZeroBoundaryPayload
                (exactOperationalTape input).messages).label] ++
            (alphaZeroBoundaryPayload
              (exactOperationalTape input).messages).data) =
        some beforeAlpha.digest ∧
      squeezeMany (exactOperationalTable input) (.challenge (.alpha 0))
          ((exactOperationalTape input).messages.challengeUse
            (.alpha 0)).blocksUsed beforeAlpha =
        some (outputs, afterBlocks) ∧
      afterAlpha = { afterBlocks with
        samples := afterBlocks.samples ++
          [{ id := .alpha 0, blocks := outputs }] } ∧
      runMachineEventWorkErased (exactOperationalTable input) afterAlpha
          (.absorb (.final256
            (exactOperationalTape input).messages.finalValues)) =
        some afterFinal256 ∧
      outputs.length =
        ((exactOperationalTape input).messages.challengeUse
          (.alpha 0)).blocksUsed ∧
      advances.length = outputs.length ∧
      GammaTableCoordinateChain (exactOperationalTable input)
        beforeAlpha.digest outputs advances ∧
      afterBlocks.digest =
        gammaTerminalDigest beforeAlpha.digest advances ∧
      afterBlocks.calls = beforeAlpha.calls ++
        gammaConsumedRawCallsFrom (.challenge (.alpha 0)) 0
          beforeAlpha.digest outputs advances ∧
      decodeTagQM31ExactLE
          ((exactOperationalTape input).messages.challengeValue (.alpha 0)) =
        some exactValue ∧
      exactOperationalChallenge input (.alpha 0) = exactValue ∧
      tableLookup (exactOperationalTable input)
          (bytes afterAlpha.digest ++
            [domAbsorb,
              AspisK1.V7Tag73TranscriptSchedule.Payload.label
                (.final256
                  (exactOperationalTape input).messages.finalValues)] ++
            AspisK1.V7Tag73TranscriptSchedule.Payload.data
              (.final256
                (exactOperationalTape input).messages.finalValues)) =
        some afterFinal256.digest ∧
      tableLookup (exactOperationalTable input)
          (bytes afterFinal256.digest ++ [domAbsorb, finalWorkNonceLabel] ++
            bytes
              (exactOperationalTape input).messages.finalGrinding.selected) =
        some evaluator.prefixState.digest ∧
      evaluator.prefixState.digest =
        (exactOperationalRawTrace input).q16BaseDigest := by
  obtain ⟨evaluator⟩ :=
    exact_operational_input_constructs_complete_evaluator input
  obtain ⟨segments⟩ := complete_evaluator_exposes_semantic_segments
    (exactOperationalTable input) (exactOperationalTape input)
      (exactOperationalRawTrace input) evaluator
  have finalDecoded := exact_operational_input_final_samples_decode input
    evaluator
  have splitRun := segments.afterSemanticRun
  rw [after_semantic_tail_events_alpha_zero_split] at splitRun
  obtain ⟨beforeAlpha, prefixRun, restRun⟩ :=
    (run_machine_events_work_erased_append_iff
      (exactOperationalTable input)
      (beforeAlphaZeroTailEvents (exactOperationalTape input).messages)
      (challengeEvent (exactOperationalTape input).messages (.alpha 0) ::
        afterAlphaZeroTailEvents (exactOperationalTape input).messages)
      segments.afterSemantic evaluator.prefixState).mp splitRun
  rw [before_alpha_zero_tail_producer_split] at prefixRun
  obtain ⟨beforeAlphaProducer, producerPrefixRun, boundaryTailRun⟩ :=
    (run_machine_events_work_erased_append_iff
      (exactOperationalTable input)
      (beforeAlphaZeroProducerTailEvents
        (exactOperationalTape input).messages)
      [.absorb (alphaZeroBoundaryPayload
        (exactOperationalTape input).messages)]
      segments.afterSemantic beforeAlpha).mp prefixRun
  simp only [runMachineEventsWorkErased] at boundaryTailRun
  obtain ⟨boundaryAfter, boundaryRun, boundaryDone⟩ :=
    Option.bind_eq_some_iff.mp boundaryTailRun
  have boundaryAfterExact : boundaryAfter = beforeAlpha := by
    simpa [runMachineEventsWorkErased] using Option.some.inj boundaryDone
  subst boundaryAfter
  have boundaryAbsorb : absorbStep (exactOperationalTable input)
      beforeAlphaProducer
      (alphaZeroBoundaryPayload (exactOperationalTape input).messages) =
        some beforeAlpha := by
    simpa [runMachineEventWorkErased] using boundaryRun
  have boundaryLookup := absorb_step_exposes_literal_lookup
    (exactOperationalTable input) beforeAlphaProducer beforeAlpha
      (alphaZeroBoundaryPayload (exactOperationalTape input).messages)
      boundaryAbsorb
  simp only [runMachineEventsWorkErased] at restRun
  obtain ⟨afterAlpha, alphaRun, suffixRun⟩ :=
    Option.bind_eq_some_iff.mp restRun
  have alphaRun' : runMachineEventWorkErased (exactOperationalTable input)
      beforeAlpha (.challenge (.alpha 0)
        ((exactOperationalTape input).messages.challengeUse (.alpha 0))) =
        some afterAlpha := by
    simpa [challengeEvent] using alphaRun
  obtain ⟨outputs, afterBlocks, squeezeRun, afterAlphaExact, outputsLength,
      recordMember⟩ := challenge_event_work_erased_exposes_record
    (exactOperationalTable input) beforeAlpha afterAlpha (.alpha 0)
      ((exactOperationalTape input).messages.challengeUse (.alpha 0)) alphaRun'
  obtain ⟨advances, advancesLength, coordinates, terminalExact,
      callsExact⟩ :=
    squeeze_many_coordinates_with_terminal (exactOperationalTable input)
      (.challenge (.alpha 0))
      ((exactOperationalTape input).messages.challengeUse (.alpha 0)).blocksUsed
      beforeAlpha afterBlocks outputs squeezeRun
  have suffixIncluded : SamplesIncluded afterAlpha evaluator.prefixState :=
    machine_events_work_erased_samples_included (exactOperationalTable input)
      (afterAlphaZeroTailEvents (exactOperationalTape input).messages)
      afterAlpha evaluator.prefixState (by
        simpa [afterAlphaZeroTailEvents] using suffixRun)
  have throughQ16 : SamplesIncluded evaluator.prefixState evaluator.afterQ16 :=
    run_q16_preserves_prior_samples (exactOperationalTable input)
      evaluator.prefixState evaluator.afterQ16
      (q16TapeOfSearch (exactOperationalTape input).search) evaluator.q16Run
  have afterQ16 : SamplesIncluded evaluator.afterQ16 evaluator.finalState :=
    machine_events_work_erased_samples_included (exactOperationalTable input)
      (afterAcceptedQueryScan (exactOperationalTape input).messages)
      evaluator.afterQ16 evaluator.finalState evaluator.afterQ16Run
  have recordFinal :
      ({ id := .alpha 0, blocks := outputs } : SampleRecord) ∈
        evaluator.finalState.samples :=
    afterQ16 _ (throughQ16 _ (suffixIncluded _ recordMember))
  have acceptedParameter :
      decodeChallengeParameter exactSecureCircleParameterMap (.alpha 0)
          outputs =
        some ((exactOperationalTape input).messages.challengeValue (.alpha 0)) :=
    finalDecoded ({ id := .alpha 0, blocks := outputs } : SampleRecord)
      recordFinal
  obtain ⟨exactValue, exactDecode⟩ :=
    decodeChallengeParameter_has_exact_tower_value
      exactSecureCircleParameterMap (.alpha 0) outputs
      ((exactOperationalTape input).messages.challengeValue (.alpha 0))
      acceptedParameter
  have operationalValue : exactOperationalChallenge input (.alpha 0) =
      exactValue := by
    simp [exactOperationalChallenge, exactChallengeValue, exactDecode]
  change runMachineEventsWorkErased (exactOperationalTable input)
      [.absorb (.final256 (exactOperationalTape input).messages.finalValues),
       .grind .final (exactOperationalTape input).messages.finalGrinding,
       .check .finalWork,
       .absorb (.finalNonce
        (exactOperationalTape input).messages.finalGrinding.selected)]
      afterAlpha = some evaluator.prefixState at suffixRun
  simp only [runMachineEventsWorkErased] at suffixRun
  obtain ⟨afterFinal256, final256Run, remainingRun⟩ :=
    Option.bind_eq_some_iff.mp suffixRun
  have final256Absorb : absorbStep (exactOperationalTable input) afterAlpha
      (.final256 (exactOperationalTape input).messages.finalValues) =
        some afterFinal256 := by
    simpa [runMachineEventWorkErased] using final256Run
  have final256Lookup := absorb_step_exposes_literal_lookup
    (exactOperationalTable input) afterAlpha afterFinal256
      (.final256 (exactOperationalTape input).messages.finalValues)
      final256Absorb
  obtain ⟨afterGrind, grindRun, remainingRun⟩ :=
    Option.bind_eq_some_iff.mp remainingRun
  obtain ⟨afterCheck, checkRun, remainingRun⟩ :=
    Option.bind_eq_some_iff.mp remainingRun
  have afterCheckExact : afterCheck = afterGrind := by
    simpa [runMachineEventWorkErased] using (Option.some.inj checkRun).symm
  subst afterCheck
  obtain ⟨afterAbsorb, finalNonceRun, finalDone⟩ :=
    Option.bind_eq_some_iff.mp remainingRun
  have afterAbsorbExact : afterAbsorb = evaluator.prefixState := by
    simpa [runMachineEventsWorkErased] using Option.some.inj finalDone
  subst afterAbsorb
  have finalNonceAbsorb : absorbStep (exactOperationalTable input) afterGrind
      (.finalNonce
        (exactOperationalTape input).messages.finalGrinding.selected) =
        some evaluator.prefixState := by
    simpa [runMachineEventWorkErased] using finalNonceRun
  have stableDigest : afterGrind.digest = afterFinal256.digest :=
    by
      change runGrindingChoiceWorkErased (exactOperationalTable input)
        afterFinal256 .final
          (exactOperationalTape input).messages.finalGrinding =
        some afterGrind at grindRun
      rw [runGrindingChoiceWorkErased] at grindRun
      obtain ⟨queried, probesRun, grindRun⟩ :=
        Option.bind_eq_some_iff.mp grindRun
      obtain ⟨selectedPair, selectedRun, result⟩ :=
        Option.bind_eq_some_iff.mp grindRun
      rcases selectedPair with ⟨selectedOutput, afterSelected⟩
      have afterSelectedExact : afterSelected = afterGrind := by
        simpa only [pure, Option.some.injEq] using result
      subst afterSelected
      have probesDigest := grinding_probes_do_not_advance
        (exactOperationalTable input) .final
        (exactOperationalTape input).messages.finalGrinding.probesBeforeSelected
        afterFinal256 queried probesRun
      obtain ⟨_lookup, _calls, selectedDigest⟩ := query_step_appends_one
        (exactOperationalTable input) queried afterGrind
        (.grind .final
          (exactOperationalTape input).messages.finalGrinding.selected)
        selectedOutput selectedRun
      have selectedUnchanged : afterGrind.digest = queried.digest := by
        simpa only [RawQueryRole.nextDigest] using selectedDigest
      exact selectedUnchanged.trans probesDigest
  have finalNonceLookup := absorb_step_exposes_literal_lookup
    (exactOperationalTable input) afterGrind evaluator.prefixState
      (.finalNonce
        (exactOperationalTape input).messages.finalGrinding.selected)
      finalNonceAbsorb
  rw [stableDigest] at finalNonceLookup
  have q16BaseExact : evaluator.prefixState.digest =
      (exactOperationalRawTrace input).q16BaseDigest := by
    simpa using congrArg InteractiveRawTrace.q16BaseDigest evaluator.rawTraceEq
  refine ⟨evaluator, segments, beforeAlphaProducer, beforeAlpha, afterAlpha,
    afterBlocks, afterFinal256, outputs, advances, exactValue,
    producerPrefixRun, boundaryRun, boundaryLookup, squeezeRun,
    afterAlphaExact,
    final256Run, outputsLength, advancesLength, coordinates, terminalExact,
    callsExact, exactDecode, operationalValue, final256Lookup, ?_, q16BaseExact⟩
  simpa [AspisK1.V7Tag73TranscriptSchedule.Payload.label,
    AspisK1.V7Tag73TranscriptSchedule.Payload.data] using finalNonceLookup

#print axioms after_semantic_tail_events_alpha_zero_split
#print axioms before_alpha_zero_tail_producer_split
#print axioms exact_compiler_constructs_alpha_zero_prefix_coordinates

end

end AspisK1.V7Tag73ExactAlphaZeroPrefixCoordinates
