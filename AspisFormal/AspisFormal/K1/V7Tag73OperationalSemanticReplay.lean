import AspisFormal.K1.V7Tag73AcceptedSemanticExecution
import AspisFormal.K1.V7Tag73ExactFixedK12MerkleClassifier

/-!
# Exact operational Tag-73 semantic replay

This file connects the literal successful scheduler/refinement input used by
K1.2 to the compact accepted semantic transcript consumed by K1.5.  The only
additional input is the exact decoding of the 641 fixed QM31 wire values; that
is a byte-layout/source-parser certificate, not an acceptance or soundness
premise.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73OperationalSemanticReplay

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SamplerExactValue
open AspisK1.V7Tag73CoupledReplayAlignment
open AspisK1.V7Tag73RefinementExecutionBridge
open AspisK1.V7Tag73CheckedRefinementFullFutureFreePath
open AspisK1.V7Tag73AcceptedSemanticExecution
open AspisK1.V7Tag73FixedFieldMessageBridge
open AspisK1.V7Tag73SemanticRoundReplay
open AspisK1.V7Tag73RawProverMessages
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisV5ComponentCQM31TowerExact
open AspisV6AcceptedPathObligations

noncomputable section

def exactOperationalTape
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : DeployedFixedTape :=
  input.package.root.fixedRoot.base.tape

def exactOperationalRawTrace
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : InteractiveRawTrace :=
  input.package.root.fixedRoot.base.raw

def exactOperationalTable
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : FixedOracleTable :=
  fixedTableOfOracleState (exactK12Runtime input).verifierFinalOracle

/-- The strict checked refinement stored in the actual operational input
constructs the complete work-erased evaluator run used by semantic replay. -/
theorem exact_operational_input_constructs_complete_evaluator
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
    Nonempty (CompleteWorkErasedEvaluatorRun (exactOperationalTable input)
      (exactOperationalTape input) (exactOperationalRawTrace input)) := by
  have checkedErased : checkedRefineWorkErased (exactOperationalTable input)
      exactDeterministicDecoders (exactOperationalTape input) =
        some (exactOperationalRawTrace input) :=
    checked_refinement_success_survives_work_erasure
      (exactOperationalTable input) exactDeterministicDecoders
      (exactOperationalTape input) (exactOperationalRawTrace input)
      input.package.root.fixedRoot.base.strictRefinement
  have erased : refineWorkErased (exactOperationalTable input)
      (exactOperationalTape input) = some (exactOperationalRawTrace input) :=
    checked_refine_work_erased_forgets_check (exactOperationalTable input)
      exactDeterministicDecoders (exactOperationalTape input)
      (exactOperationalRawTrace input) checkedErased
  exact refine_work_erased_exposes_complete_evaluator_run
    (exactOperationalTable input) (exactOperationalTape input)
    (exactOperationalRawTrace input) erased

/-- The literal checked refinement also supplies the final deterministic
decoder ledger needed to transport every challenge back to its causal round. -/
theorem exact_operational_input_final_samples_decode
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
    (evaluator : CompleteWorkErasedEvaluatorRun (exactOperationalTable input)
      (exactOperationalTape input) (exactOperationalRawTrace input)) :
    StateSamplesDecodeAs (exactOperationalTape input).messages
      evaluator.finalState := by
  have wellFormed : TraceWellFormed (exactOperationalTable input)
      exactDeterministicDecoders (exactOperationalTape input)
      (exactOperationalRawTrace input) :=
    (checked_refinement_is_well_formed (exactOperationalTable input)
      exactDeterministicDecoders (exactOperationalTape input)
      (exactOperationalRawTrace input)
      input.package.root.fixedRoot.base.strictRefinement).2
  exact complete_evaluator_final_samples_decode (exactOperationalTable input)
    (exactOperationalTape input) (exactOperationalRawTrace input) wellFormed
    evaluator

/-- Exact end product of the operational-to-semantic bridge.  The transcript,
all ten round challenges, and the nonzero eta fact are derived from the actual
fixed-table run. -/
theorem exact_operational_input_constructs_compact_semantic_replay
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
    (decoded : Fin 641 -> QM31Exact)
    (fixedDecode : FixedFieldDecodeExact
      (rawOfMessages (exactOperationalTape input).messages) decoded) :
    ExactCompactSemanticReplay
      (semanticPreEtaOf (exactOperationalTable input)
        (exactOperationalTape input).messages)
      (exactChallengeValue
        (exactOperationalTape input).messages.challengeValue .eta)
      (decodedFixedFieldView decoded)
      (fun round => exactChallengeValue
        (exactOperationalTape input).messages.challengeValue
        (.semantic round)) := by
  obtain ⟨evaluator⟩ :=
    exact_operational_input_constructs_complete_evaluator input
  obtain ⟨segments⟩ := complete_evaluator_exposes_semantic_segments
    (exactOperationalTable input) (exactOperationalTape input)
    (exactOperationalRawTrace input) evaluator
  have finalDecoded := exact_operational_input_final_samples_decode input evaluator
  exact complete_evaluator_constructs_exactCompactSemanticReplay
    (exactOperationalTable input) (exactOperationalTape input)
    (exactOperationalRawTrace input) evaluator segments finalDecoded decoded
    fixedDecode

/-! ## Exact nonzero challenges outside the semantic subsegment -/

/-- A challenge emitted by any successful work-erased event list remains in
that list's final sample ledger.  Unlike the causal replay lemma, this applies
across the positioned work checks in the actual Tag-73 tail. -/
theorem challenge_record_in_work_erased_final_of_event_mem
    (table : FixedOracleTable) (events : List MachineEvent)
    (state final : EvalState) (id : ChallengeId) (use : SamplerUse id)
    (member : .challenge id use ∈ events)
    (run : runMachineEventsWorkErased table events state = some final) :
    ∃ blocks, { id := id, blocks := blocks } ∈ final.samples := by
  induction events generalizing state with
  | nil => simp at member
  | cons event rest ih =>
      simp only [runMachineEventsWorkErased] at run
      obtain ⟨next, eventRun, restRun⟩ := Option.bind_eq_some_iff.mp run
      have included := machine_events_work_erased_samples_included table rest
        next final restRun
      rcases List.mem_cons.mp member with head | tail
      · subst event
        obtain ⟨blocks, _afterBlocks, _squeezeRun, _nextExact, _length,
            emitted⟩ :=
          challenge_event_work_erased_exposes_record table state next id use
            eventRun
        exact ⟨blocks, included _ emitted⟩
      · exact ih (state := next) tail restRun

/-- A literal nonzero-mode challenge event in a successful work-erased tail
has a nonzero value in the exact QM31 tower, using the final checked decoder
ledger of that same execution. -/
theorem exact_challenge_ne_zero_of_work_erased_event
    (table : FixedOracleTable) (messages : Messages)
    (events : List MachineEvent) (state tail global : EvalState)
    (id : ChallengeId) (use : SamplerUse id)
    (mode : samplerMode id = .nonzeroQm31)
    (member : .challenge id use ∈ events)
    (run : runMachineEventsWorkErased table events state = some tail)
    (included : SamplesIncluded tail global)
    (finalDecoded : StateSamplesDecodeAs messages global) :
    exactChallengeValue messages.challengeValue id ≠ 0 := by
  obtain ⟨blocks, emitted⟩ :=
    challenge_record_in_work_erased_final_of_event_mem table events state tail
      id use member run
  have parameterDecoded := finalDecoded { id := id, blocks := blocks }
    (included _ emitted)
  have nonzeroRun : decodeNonzeroExact blocks =
      some (messages.challengeValue id) := by
    simpa [decodeChallengeParameter, mode] using parameterDecoded
  obtain ⟨value, valueRun⟩ := decodeChallengeParameter_has_exact_tower_value
    exactSecureCircleParameterMap id blocks (messages.challengeValue id)
      parameterDecoded
  have exactDecode : decodeTagQM31ExactLE (messages.challengeValue id) =
      some (exactChallengeValue messages.challengeValue id) := by
    simp [exactChallengeValue, valueRun]
  exact exactChallengeValue_ne_zero_of_nonzero_run messages.challengeValue id
    blocks nonzeroRun exactDecode

theorem complete_evaluator_gamma_ne_zero
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (rawTrace : InteractiveRawTrace)
    (evaluator : CompleteWorkErasedEvaluatorRun table tape rawTrace)
    (segments : SemanticExecutionSegments table tape.messages
      evaluator.afterC2 evaluator.prefixState)
    (finalDecoded : StateSamplesDecodeAs tape.messages evaluator.finalState) :
    exactChallengeValue tape.messages.challengeValue .gamma ≠ 0 := by
  have throughQ16 := run_q16_preserves_prior_samples table evaluator.prefixState
    evaluator.afterQ16 (q16TapeOfSearch tape.search) evaluator.q16Run
  have afterQ16 := machine_events_work_erased_samples_included table
    (afterAcceptedQueryScan tape.messages) evaluator.afterQ16
    evaluator.finalState evaluator.afterQ16Run
  exact exact_challenge_ne_zero_of_work_erased_event table tape.messages
    (afterSemanticTailEvents tape.messages) segments.afterSemantic
    evaluator.prefixState evaluator.finalState .gamma
    (tape.messages.challengeUse .gamma) rfl
    (by simp [afterSemanticTailEvents, challengeEvent])
    segments.afterSemanticRun (samples_included_trans throughQ16 afterQ16)
    finalDecoded

theorem complete_evaluator_kappa_ne_zero
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (rawTrace : InteractiveRawTrace)
    (evaluator : CompleteWorkErasedEvaluatorRun table tape rawTrace)
    (segments : SemanticExecutionSegments table tape.messages
      evaluator.afterC2 evaluator.prefixState)
    (finalDecoded : StateSamplesDecodeAs tape.messages evaluator.finalState) :
    exactChallengeValue tape.messages.challengeValue .kappa ≠ 0 := by
  have throughQ16 := run_q16_preserves_prior_samples table evaluator.prefixState
    evaluator.afterQ16 (q16TapeOfSearch tape.search) evaluator.q16Run
  have afterQ16 := machine_events_work_erased_samples_included table
    (afterAcceptedQueryScan tape.messages) evaluator.afterQ16
    evaluator.finalState evaluator.afterQ16Run
  exact exact_challenge_ne_zero_of_work_erased_event table tape.messages
    (afterSemanticTailEvents tape.messages) segments.afterSemantic
    evaluator.prefixState evaluator.finalState .kappa
    (tape.messages.challengeUse .kappa) rfl
    (by simp [afterSemanticTailEvents, challengeEvent])
    segments.afterSemanticRun (samples_included_trans throughQ16 afterQ16)
    finalDecoded

theorem complete_evaluator_queryBatch_ne_zero
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (rawTrace : InteractiveRawTrace)
    (evaluator : CompleteWorkErasedEvaluatorRun table tape rawTrace)
    (finalDecoded : StateSamplesDecodeAs tape.messages evaluator.finalState) :
    exactChallengeValue tape.messages.challengeValue .queryBatch ≠ 0 := by
  exact exact_challenge_ne_zero_of_work_erased_event table tape.messages
    (afterAcceptedQueryScan tape.messages) evaluator.afterQ16
    evaluator.finalState evaluator.finalState .queryBatch
    (tape.messages.challengeUse .queryBatch) rfl
    (by simp [afterAcceptedQueryScan, challengeEvent]) evaluator.afterQ16Run
    (fun _ member => member) finalDecoded

/-- All three nonzero challenges after eta are obtained from the one literal
operational run, with no caller-supplied sampler-success proposition. -/
theorem exact_operational_input_constructs_post_eta_nonzero_challenges
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
    exactChallengeValue
        (exactOperationalTape input).messages.challengeValue .gamma ≠ 0 ∧
      exactChallengeValue
        (exactOperationalTape input).messages.challengeValue .kappa ≠ 0 ∧
      exactChallengeValue
        (exactOperationalTape input).messages.challengeValue .queryBatch ≠ 0 := by
  obtain ⟨evaluator⟩ :=
    exact_operational_input_constructs_complete_evaluator input
  obtain ⟨segments⟩ := complete_evaluator_exposes_semantic_segments
    (exactOperationalTable input) (exactOperationalTape input)
    (exactOperationalRawTrace input) evaluator
  have finalDecoded := exact_operational_input_final_samples_decode input evaluator
  exact ⟨
    complete_evaluator_gamma_ne_zero (exactOperationalTable input)
      (exactOperationalTape input) (exactOperationalRawTrace input) evaluator
      segments finalDecoded,
    complete_evaluator_kappa_ne_zero (exactOperationalTable input)
      (exactOperationalTape input) (exactOperationalRawTrace input) evaluator
      segments finalDecoded,
    complete_evaluator_queryBatch_ne_zero (exactOperationalTable input)
      (exactOperationalTape input) (exactOperationalRawTrace input) evaluator
      finalDecoded⟩

#print axioms exact_operational_input_constructs_complete_evaluator
#print axioms exact_operational_input_final_samples_decode
#print axioms exact_operational_input_constructs_compact_semantic_replay
#print axioms challenge_record_in_work_erased_final_of_event_mem
#print axioms exact_challenge_ne_zero_of_work_erased_event
#print axioms complete_evaluator_gamma_ne_zero
#print axioms complete_evaluator_kappa_ne_zero
#print axioms complete_evaluator_queryBatch_ne_zero
#print axioms exact_operational_input_constructs_post_eta_nonzero_challenges

end

end AspisK1.V7Tag73OperationalSemanticReplay
