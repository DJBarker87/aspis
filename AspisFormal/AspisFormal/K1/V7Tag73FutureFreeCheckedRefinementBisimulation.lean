import AspisFormal.K1.V7Tag73FutureFreeFullControl
import AspisFormal.K1.V7Tag73RawSameTapeSource

/-!
# Fixed-run refinement data for the future-free Tag-73 verifier

This module begins the deterministic bisimulation between one successful
strict deployed `checkedRefine` execution and the future-free verifier.  It
first removes exactly the action metadata that is not an interactive verifier
message:

* exploratory grinding probes are adversary history and disappear;
* the fixed-tape q16 candidate outcome/selected bit disappears, leaving the
  exact candidate-counter absorb that the live verifier performs; and
* every selected work query, checkpoint, nonce absorb, paired squeeze and
  terminal marker remains in order.

The concrete decoder and q16 frontier environment are then recovered from the
successful checked refinement.  No acceptance, witness, extraction, replay
cover or caller-selected restore operation is a field of this construction.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73FutureFreeCheckedRefinementBisimulation

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73RawProverMessages
open AspisK1.V7Tag73RawSameTapeSource

noncomputable section

/-! ## The exact raw fixed-run projection -/

def fixedTapeRawMessages (tape : DeployedFixedTape) :
    RawTag73ProverMessages :=
  rawOfMessages tape.messages

def fixedTapeFutureFreeEnvironment (tape : DeployedFixedTape) :
    FutureFreeEnvironment where
  frontierNodes := tape.frontierNodes

@[simp] theorem fixed_tape_environment_uses_exact_decoder
    (tape : DeployedFixedTape) :
    (fixedTapeFutureFreeEnvironment tape).decoders =
      exactDeterministicDecoders := by
  rfl

@[simp] theorem fixed_tape_raw_context (tape : DeployedFixedTape) :
    (fixedTapeRawMessages tape).context = tape.messages.context := by
  rfl

@[simp] theorem fixed_tape_raw_c1_root (tape : DeployedFixedTape) :
    (rawC1Root (fixedTapeRawMessages tape)).value = tape.messages.c1Root := by
  rfl

/-- The old fixed tape's C2 bytes are projected as raw bytes and only then
reindexed at the live pair.  The indices in this theorem are intentionally
arbitrary. -/
@[simp] theorem fixed_tape_raw_c2_reindexes_at_live_pair
    (tape : DeployedFixedTape) (lambda chi : Qm31Bytes) :
    ((fixedTapeRawMessages tape).c2Commitment lambda chi).root =
      tape.messages.c2.root := by
  rfl

theorem strict_checked_refinement_exposes_erased_run_and_exact_decoders
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (raw : InteractiveRawTrace)
    (run : checkedRefine table exactDeterministicDecoders tape = some raw) :
    checkedRefineWorkErased table exactDeterministicDecoders tape = some raw ∧
      TraceWellFormed table exactDeterministicDecoders tape raw := by
  exact ⟨checked_refinement_success_survives_work_erasure table
      exactDeterministicDecoders tape raw run,
    (checked_refinement_is_well_formed table exactDeterministicDecoders tape raw
      run).2⟩

/-! ## Remove only non-verifier action metadata -/

def futureFreeVisibleAction : VerifierAction → Option VerifierAction
  | .workProbe _ _ .adversaryHistory => none
  | .q16CandidateAbsorb counter _ _ =>
      some (.absorb (.queryCandidate counter))
  | action => some action

def futureFreeVisibleActions (actions : List VerifierAction) :
    List VerifierAction :=
  actions.filterMap futureFreeVisibleAction

@[simp] theorem future_free_visible_actions_append
    (first second : List VerifierAction) :
    futureFreeVisibleActions (first ++ second) =
      futureFreeVisibleActions first ++ futureFreeVisibleActions second := by
  simp [futureFreeVisibleActions]

@[simp] theorem exploratory_work_probes_are_not_verifier_actions
    (stage : WorkStage) (probes : List NonceBytes) :
    futureFreeVisibleActions
        (probes.map fun nonce =>
          VerifierAction.workProbe stage nonce .adversaryHistory) = [] := by
  induction probes with
  | nil => rfl
  | cons nonce rest ih =>
      simp [futureFreeVisibleActions, futureFreeVisibleAction]

@[simp] theorem selected_work_probe_remains_visible
    (stage : WorkStage) (nonce : NonceBytes) :
    futureFreeVisibleActions
        [.workProbe stage nonce .verifierSelected] =
      [.workProbe stage nonce .verifierSelected] := by
  rfl

theorem grinding_actions_project_to_one_selected_verifier_query
    (stage : WorkStage) (choice : GrindingChoice stage) :
    futureFreeVisibleActions (grindingActions stage choice) =
      [.workProbe stage choice.selected .verifierSelected] := by
  simp [grindingActions]

theorem candidate_actions_project_to_live_counter_absorb_and_squeezes
    (spec : CandidateSpec) (selected : Bool) :
    futureFreeVisibleActions (candidateActions spec selected) =
      [.absorb (.queryCandidate spec.counter)] ++
        (List.range spec.outcome.blocksUsed).map fun block =>
          .squeezePair (.queryCandidate spec.counter) block := by
  simp [candidateActions, futureFreeVisibleActions, futureFreeVisibleAction]

theorem discarded_candidate_projection_retains_protocol_restore
    (spec : CandidateSpec) :
    futureFreeVisibleActions (discardedCandidateActions spec) =
      [.absorb (.queryCandidate spec.counter)] ++
        (List.range spec.outcome.blocksUsed).map
          (fun block => .squeezePair (.queryCandidate spec.counter) block) ++
        [.q16Restore spec.counter] := by
  rw [discardedCandidateActions, future_free_visible_actions_append,
    candidate_actions_project_to_live_counter_absorb_and_squeezes]
  rfl

/-! ## Exact slot expansion for the already completed fixed run -/

def fixedTapeSlotActions (tape : DeployedFixedTape) :
    FutureFreeSlot → List VerifierAction
  | .fixed action => [action]
  | .challenge id => challengeActions id (tape.messages.challengeUse id)
  | .payload site =>
      [.absorb (rawPayloadAt (fixedTapeRawMessages tape) site)]
  | .work stage =>
      let nonce := rawWorkNonceAt (fixedTapeRawMessages tape) stage
      [.workProbe stage nonce .verifierSelected,
       .checkpoint (checkpointOfWorkStage stage),
       .absorb (workNoncePayload stage nonce)]
  | .beginQ16 => futureFreeVisibleActions (q16Plan tape)

def fixedTapeSlotPlan (tape : DeployedFixedTape)
    (slots : List FutureFreeSlot) : List VerifierAction :=
  slots.flatMap (fixedTapeSlotActions tape)

@[simp] theorem fixed_tape_slot_plan_append (tape : DeployedFixedTape)
    (first second : List FutureFreeSlot) :
    fixedTapeSlotPlan tape (first ++ second) =
      fixedTapeSlotPlan tape first ++ fixedTapeSlotPlan tape second := by
  simp [fixedTapeSlotPlan]

@[simp] theorem fixed_tape_payload_initial_claim (tape : DeployedFixedTape) :
    rawPayloadAt (fixedTapeRawMessages tape) .initialMaskClaim =
      .initialMaskClaim tape.messages.initialClaim := by
  rfl

@[simp] theorem fixed_tape_payload_semantic_round
    (tape : DeployedFixedTape) (round : Fin 10) :
    rawPayloadAt (fixedTapeRawMessages tape) (.semanticRound round) =
      .semanticRound round (tape.messages.semanticSent round) := by
  rfl

@[simp] theorem fixed_tape_payload_point_claims (tape : DeployedFixedTape) :
    rawPayloadAt (fixedTapeRawMessages tape) .pointClaims =
      .pointClaims tape.messages.pointClaims := by
  rfl

@[simp] theorem fixed_tape_payload_inactive_claim
    (tape : DeployedFixedTape) :
    rawPayloadAt (fixedTapeRawMessages tape) .inactiveClaim =
      .inactiveClaim tape.messages.inactiveClaim := by
  rfl

@[simp] theorem fixed_tape_payload_ood
    (tape : DeployedFixedTape) (sample : Fin 2) :
    rawPayloadAt (fixedTapeRawMessages tape) (.circleOodValue sample) =
      .circleOodValue sample (tape.messages.oodValue sample) := by
  rfl

@[simp] theorem fixed_tape_payload_relation
    (tape : DeployedFixedTape) (round : Fin 4) :
    rawPayloadAt (fixedTapeRawMessages tape) (.relationRound round) =
      .relationRound round (tape.messages.relationSent round) := by
  rfl

@[simp] theorem fixed_tape_payload_final256 (tape : DeployedFixedTape) :
    rawPayloadAt (fixedTapeRawMessages tape) .final256 =
      .final256 tape.messages.finalValues := by
  rfl

@[simp] theorem fixed_tape_payload_query_batch_claim
    (tape : DeployedFixedTape) :
    rawPayloadAt (fixedTapeRawMessages tape) .queryBatchClaim =
      .queryBatchClaim tape.messages.queryBatchClaim := by
  rfl

@[simp] theorem fixed_tape_batch_nonce (tape : DeployedFixedTape) :
    rawWorkNonceAt (fixedTapeRawMessages tape) .batch =
      tape.messages.batchGrinding.selected := by
  rfl

@[simp] theorem fixed_tape_fold_nonce (tape : DeployedFixedTape) :
    rawWorkNonceAt (fixedTapeRawMessages tape) .fold =
      tape.messages.foldGrinding.selected := by
  rfl

@[simp] theorem fixed_tape_final_nonce (tape : DeployedFixedTape) :
    rawWorkNonceAt (fixedTapeRawMessages tape) .final =
      tape.messages.finalGrinding.selected := by
  rfl

/-! ## Decoder evidence is attached to actual operational records -/

theorem well_formed_trace_has_exact_candidate_blocks
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (raw : InteractiveRawTrace)
    (wellFormed : TraceWellFormed table exactDeterministicDecoders tape raw)
    (spec : CandidateSpec) (member : spec ∈ expectedCandidateSpecs tape) :
    ∃ record ∈ raw.candidates,
      record.counter = spec.counter ∧
      record.outcome = spec.outcome ∧
      exactDeterministicDecoders.candidate spec.counter record.blocks =
        some spec.outcome := by
  have expectedMember : (spec.counter, spec.outcome) ∈
      (expectedCandidateSpecs tape).map
        (fun candidate => (candidate.counter, candidate.outcome)) :=
    List.mem_map.mpr ⟨spec, member, rfl⟩
  rw [← wellFormed.candidateProjection] at expectedMember
  rcases List.mem_map.mp expectedMember with
    ⟨record, recordMember, pairEqual⟩
  have counterEqual : record.counter = spec.counter :=
    congrArg Prod.fst pairEqual
  have outcomeEqual : record.outcome = spec.outcome :=
    congrArg Prod.snd pairEqual
  refine ⟨record, recordMember, counterEqual, outcomeEqual, ?_⟩
  rw [← counterEqual, ← outcomeEqual]
  exact wellFormed.candidatesDecode record recordMember

theorem strict_checked_refinement_has_exact_candidate_blocks
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (raw : InteractiveRawTrace)
    (run : checkedRefine table exactDeterministicDecoders tape = some raw)
    (spec : CandidateSpec) (member : spec ∈ expectedCandidateSpecs tape) :
    ∃ record ∈ raw.candidates,
      record.counter = spec.counter ∧
      record.outcome = spec.outcome ∧
      exactDeterministicDecoders.candidate spec.counter record.blocks =
        some spec.outcome := by
  exact well_formed_trace_has_exact_candidate_blocks table tape raw
    (checked_refinement_is_well_formed table exactDeterministicDecoders tape raw
      run).2 spec member

/-! `FutureFreeScheduleExhausted` is intentionally absent from the conclusion
above: decoder/action bisimulation is not semantic, Merkle or terminal
acceptance.  The external obligations remain exactly
`futureFreeExternalAcceptanceObligations`. -/

#print axioms strict_checked_refinement_exposes_erased_run_and_exact_decoders
#print axioms grinding_actions_project_to_one_selected_verifier_query
#print axioms candidate_actions_project_to_live_counter_absorb_and_squeezes
#print axioms discarded_candidate_projection_retains_protocol_restore
#print axioms well_formed_trace_has_exact_candidate_blocks
#print axioms strict_checked_refinement_has_exact_candidate_blocks

end

end AspisK1.V7Tag73FutureFreeCheckedRefinementBisimulation
