import AspisFormal.K1.V7Tag73ExactCompilerGammaPrefixCoordinates
import AspisFormal.K1.V7Tag73ExactCompilerFinalWorkTraceOccurrence
import AspisFormal.K1.V7Tag73ExactQ16CausalCoordinateOrder
import AspisFormal.K1.V7Tag73GammaPrefixCausalController

/-!
# Exact source origin of the root gamma boundary

This leaf exposes the batch-nonce absorption immediately preceding the root
gamma sampler. Its answer is exactly the initial digest used by the gamma
output/advance chain and is recognized by the pre-answer controller's literal
boundary grammar.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactGammaPrefixBoundaryOrigin

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73CheckedRefinementFullFutureFreePath
open AspisK1.V7Tag73AcceptedSemanticExecution
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactCompilerGammaPrefixCoordinates
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open AspisK1.V7Tag73ExactCompilerFinalWorkTraceOccurrence
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactQ16CausalCoordinateOrder
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73GammaPrefixCausalController
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

def beforeBatchNonceTailEvents (messages : Messages) : List MachineEvent :=
  [.absorb (.pointClaims messages.pointClaims),
   .check .semanticTerminal,
   .grind .batch messages.batchGrinding,
   .check .batchWork]

theorem before_gamma_tail_batch_nonce_split (messages : Messages) :
    beforeGammaTailEvents messages =
      beforeBatchNonceTailEvents messages ++
        [.absorb (.batchNonce messages.batchGrinding.selected)] := by
  simp [beforeGammaTailEvents, beforeBatchNonceTailEvents]

/-- The exact accepted root execution reaches gamma at the digest returned by
the immediately preceding literal batch-nonce absorption. -/
theorem exact_operational_batch_nonce_produces_gamma_digest
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
    ∃ (beforeBatch beforeGamma : EvalState),
      tableLookup (exactOperationalTable input)
          (bytes beforeBatch.digest ++ [domAbsorb, batchWorkNonceLabel] ++
            bytes (exactOperationalTape input).messages.batchGrinding.selected) =
        some beforeGamma.digest ∧
      isGammaPrefixBoundaryInput
          (bytes beforeBatch.digest ++ [domAbsorb, batchWorkNonceLabel] ++
            bytes (exactOperationalTape input).messages.batchGrinding.selected) =
        true := by
  obtain ⟨evaluator⟩ :=
    exact_operational_input_constructs_complete_evaluator input
  obtain ⟨segments⟩ := complete_evaluator_exposes_semantic_segments
    (exactOperationalTable input) (exactOperationalTape input)
      (exactOperationalRawTrace input) evaluator
  have splitRun := segments.afterSemanticRun
  rw [after_semantic_tail_events_gamma_split] at splitRun
  obtain ⟨beforeGamma, prefixRun, _restRun⟩ :=
    (run_machine_events_work_erased_append_iff
      (exactOperationalTable input)
      (beforeGammaTailEvents (exactOperationalTape input).messages)
      (challengeEvent (exactOperationalTape input).messages .gamma ::
        ([.absorb (.inactiveClaim
            (exactOperationalTape input).messages.inactiveClaim),
          challengeEvent (exactOperationalTape input).messages .kappa] ++
          oodEvents (exactOperationalTape input).messages ++
          [.absorb (.relationRound 0
            ((exactOperationalTape input).messages.relationSent 0)),
           .grind .fold (exactOperationalTape input).messages.foldGrinding,
           .check .foldWork,
           .absorb (.foldNonce
            (exactOperationalTape input).messages.foldGrinding.selected),
           challengeEvent (exactOperationalTape input).messages (.alpha 0),
           .absorb (.final256
            (exactOperationalTape input).messages.finalValues),
           .grind .final (exactOperationalTape input).messages.finalGrinding,
           .check .finalWork,
           .absorb (.finalNonce
            (exactOperationalTape input).messages.finalGrinding.selected)]))
      segments.afterSemantic evaluator.prefixState).mp splitRun
  rw [before_gamma_tail_batch_nonce_split] at prefixRun
  obtain ⟨beforeBatch, _beforeBatchRun, nonceRun⟩ :=
    (run_machine_events_work_erased_append_iff
      (exactOperationalTable input)
      (beforeBatchNonceTailEvents (exactOperationalTape input).messages)
      [.absorb (.batchNonce
        (exactOperationalTape input).messages.batchGrinding.selected)]
      segments.afterSemantic beforeGamma).mp prefixRun
  simp only [runMachineEventsWorkErased] at nonceRun
  obtain ⟨afterNonce, absorbRun, nonceDone⟩ :=
    Option.bind_eq_some_iff.mp nonceRun
  have afterNonceExact : afterNonce = beforeGamma := by
    simpa [runMachineEventsWorkErased] using Option.some.inj nonceDone
  subst afterNonce
  have lookup := absorb_step_exposes_literal_lookup
    (exactOperationalTable input) beforeBatch beforeGamma
      (.batchNonce
        (exactOperationalTape input).messages.batchGrinding.selected)
      absorbRun
  refine ⟨beforeBatch, beforeGamma, ?_, ?_⟩
  · simpa [AspisK1.V7Tag73TranscriptSchedule.Payload.label,
      AspisK1.V7Tag73TranscriptSchedule.Payload.data] using lookup
  · exact literal_batch_nonce_is_gamma_prefix_boundary beforeBatch.digest
      (exactOperationalTape input).messages.batchGrinding.selected

/-- One evaluator witness supplies both the literal batch-nonce producer and
the complete consumed gamma duplex chain.  Keeping them in one existential
prevents an illicit join between independently selected pre-gamma states. -/
theorem exact_operational_batch_nonce_and_gamma_chain
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
    ∃ (producerInput : ShaInput) (initialDigest : Digest256)
        (outputs advances : List Digest256),
      tableLookup (exactOperationalTable input) producerInput =
          some initialDigest ∧
      (∃ beforeBatch : EvalState,
        producerInput =
          bytes beforeBatch.digest ++ [domAbsorb, batchWorkNonceLabel] ++
            bytes
              (exactOperationalTape input).messages.batchGrinding.selected) ∧
      ExactRootOrderedQ16Chain input producerInput initialDigest outputs
        advances ∧
      outputs.length =
        ((exactOperationalTape input).messages.challengeUse .gamma).blocksUsed ∧
      advances.length = outputs.length := by
  obtain ⟨evaluator⟩ :=
    exact_operational_input_constructs_complete_evaluator input
  obtain ⟨segments⟩ := complete_evaluator_exposes_semantic_segments
    (exactOperationalTable input) (exactOperationalTape input)
      (exactOperationalRawTrace input) evaluator
  have splitRun := segments.afterSemanticRun
  rw [after_semantic_tail_events_gamma_split] at splitRun
  obtain ⟨beforeGamma, prefixRun, restRun⟩ :=
    (run_machine_events_work_erased_append_iff
      (exactOperationalTable input)
      (beforeGammaTailEvents (exactOperationalTape input).messages)
      (challengeEvent (exactOperationalTape input).messages .gamma ::
        ([.absorb (.inactiveClaim
            (exactOperationalTape input).messages.inactiveClaim),
          challengeEvent (exactOperationalTape input).messages .kappa] ++
          oodEvents (exactOperationalTape input).messages ++
          [.absorb (.relationRound 0
            ((exactOperationalTape input).messages.relationSent 0)),
           .grind .fold (exactOperationalTape input).messages.foldGrinding,
           .check .foldWork,
           .absorb (.foldNonce
            (exactOperationalTape input).messages.foldGrinding.selected),
           challengeEvent (exactOperationalTape input).messages (.alpha 0),
           .absorb (.final256
            (exactOperationalTape input).messages.finalValues),
           .grind .final (exactOperationalTape input).messages.finalGrinding,
           .check .finalWork,
           .absorb (.finalNonce
            (exactOperationalTape input).messages.finalGrinding.selected)]))
      segments.afterSemantic evaluator.prefixState).mp splitRun
  rw [before_gamma_tail_batch_nonce_split] at prefixRun
  obtain ⟨beforeBatch, _beforeBatchRun, nonceRun⟩ :=
    (run_machine_events_work_erased_append_iff
      (exactOperationalTable input)
      (beforeBatchNonceTailEvents (exactOperationalTape input).messages)
      [.absorb (.batchNonce
        (exactOperationalTape input).messages.batchGrinding.selected)]
      segments.afterSemantic beforeGamma).mp prefixRun
  simp only [runMachineEventsWorkErased] at nonceRun
  obtain ⟨afterNonce, absorbRun, nonceDone⟩ :=
    Option.bind_eq_some_iff.mp nonceRun
  have afterNonceExact : afterNonce = beforeGamma := by
    simpa [runMachineEventsWorkErased] using Option.some.inj nonceDone
  subst afterNonce
  let producerInput : ShaInput :=
    bytes beforeBatch.digest ++ [domAbsorb, batchWorkNonceLabel] ++
      bytes (exactOperationalTape input).messages.batchGrinding.selected
  have producerLookup : tableLookup (exactOperationalTable input)
      producerInput = some beforeGamma.digest := by
    have lookup := absorb_step_exposes_literal_lookup
      (exactOperationalTable input) beforeBatch beforeGamma
        (.batchNonce
          (exactOperationalTape input).messages.batchGrinding.selected)
        absorbRun
    simpa [producerInput,
      AspisK1.V7Tag73TranscriptSchedule.Payload.label,
      AspisK1.V7Tag73TranscriptSchedule.Payload.data] using lookup
  simp only [runMachineEventsWorkErased] at restRun
  obtain ⟨afterGamma, gammaRun, _tailRun⟩ :=
    Option.bind_eq_some_iff.mp restRun
  have gammaRun' : runMachineEventWorkErased (exactOperationalTable input)
      beforeGamma (.challenge .gamma
        ((exactOperationalTape input).messages.challengeUse .gamma)) =
      some afterGamma := by
    simpa [challengeEvent] using gammaRun
  obtain ⟨outputs, afterBlocks, squeezeRun, _afterGammaExact, outputsLength,
      _recordMember⟩ := challenge_event_work_erased_exposes_record
    (exactOperationalTable input) beforeGamma afterGamma .gamma
      ((exactOperationalTape input).messages.challengeUse .gamma) gammaRun'
  obtain ⟨advances, advancesLength, coordinates, _callsExact⟩ :=
    squeeze_many_gamma_coordinates (exactOperationalTable input)
      ((exactOperationalTape input).messages.challengeUse .gamma).blocksUsed
      beforeGamma afterBlocks outputs squeezeRun
  have ordered : ExactRootOrderedQ16Chain input producerInput
      beforeGamma.digest outputs advances :=
    gamma_table_coordinate_chain_has_exact_root_order transitionRoom input
      producerInput beforeGamma.digest producerLookup coordinates
  exact ⟨producerInput, beforeGamma.digest, outputs, advances, producerLookup,
    ⟨beforeBatch, rfl⟩, ordered, outputsLength, advancesLength⟩

#print axioms before_gamma_tail_batch_nonce_split
#print axioms exact_operational_batch_nonce_produces_gamma_digest
#print axioms exact_operational_batch_nonce_and_gamma_chain

end

end AspisK1.V7Tag73ExactGammaPrefixBoundaryOrigin
