import AspisFormal.K1.V7Tag73ReplayReturnedVerifier

/-!
# Replay-tagged historical work evidence for Tag-73

The literal shared-oracle verifier treats an earlier grinding probe as cached
historical evidence.  Its current selector searches only adversary-tagged Q1.
A same-tape replay, however, records every replayed call with actor
`extractorReplay`.  Erasing the selected-work rejection predicate does not
erase this evidence-selection gate.

This file isolates that mismatch operationally.  It provides a chronological
prover-history selector accepting exactly `adversary` or `extractorReplay`,
proves exact specialization to the current selector on plain histories, and
proves an executable one-call counterexample: a coherent, reachable
replay-tagged cached answer advances the work-erased ancestor but the current
historical-work program refuses it.

No record is relabelled.  Selected work nonces still issue their exact
deployed verifier query.  This module does not assert that all work probes of
an adaptively returned proof occur in its replay history; that separate
schedule/history alignment remains necessary before a full-plan return can be
derived.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ReplayWorkEvidenceBridge

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73SharedOracleVerifierRunner
open AspisK1.V7Tag73ReplayReturnedVerifier
open AspisK1.V7FsAokExperiment

/-! ## Actor-preserving historical evidence -/

/-- The exact SHA input checked for a work nonce at the current transcript
state.  The three stages stay distinct through their distinct saved cores and
action positions; the deployed input grammar itself contains the digest,
grinding domain byte, and nonce. -/
def historicalWorkInput (core : RuntimeCore) (nonce : NonceBytes) : ShaInput :=
  bytes core.digest ++ [domGrind] ++ bytes nonce

/-- Actor-indexed analogue of the current frozen adversary-Q1 selector.  It
searches the immutable history projection for the requested actor and still
requires agreement with the immutable table's first-hit answer. -/
def frozenActorEvidenceRecord (actor : QueryActor) (evidence : OracleState)
    (input : ShaInput) : Option QueryRecord :=
  (actorHistory actor evidence).find? fun record => decide
    (record.input = input ∧ record.actor = actor ∧
      cachedEvidenceOutput evidence input = some record.output)

def frozenActorEvidenceOutput (actor : QueryActor) (evidence : OracleState)
    (input : ShaInput) : Option ShaOutput :=
  (frozenActorEvidenceRecord actor evidence input).map QueryRecord.output

/-- The existing selector is definitionally the adversary specialization;
the generalization changes no current plain-run behavior. -/
theorem frozen_actor_evidence_record_adversary_specializes_exactly
    (evidence : OracleState) (input : ShaInput) :
    frozenActorEvidenceRecord .adversary evidence input =
      frozenAdversaryEvidenceRecord evidence input := by
  rfl

theorem frozen_actor_evidence_output_adversary_specializes_exactly
    (evidence : OracleState) (input : ShaInput) :
    frozenActorEvidenceOutput .adversary evidence input =
      frozenAdversaryEvidenceOutput evidence input := by
  rfl

/-- Selection retains the actual actor tag; it does not manufacture or
rewrite provenance. -/
theorem frozen_actor_evidence_has_exact_record
    (actor : QueryActor) (evidence : OracleState)
    (input : ShaInput) (output : ShaOutput)
    (found : frozenActorEvidenceOutput actor evidence input = some output) :
    ∃ record : QueryRecord,
      record ∈ actorHistory actor evidence ∧
      record.actor = actor ∧ record.input = input ∧
      record.output = output ∧
      cachedEvidenceOutput evidence input = some output := by
  unfold frozenActorEvidenceOutput at found
  cases selected : frozenActorEvidenceRecord actor evidence input with
  | none => simp [selected] at found
  | some record =>
      simp only [selected, Option.map_some, Option.some.injEq] at found
      subst output
      unfold frozenActorEvidenceRecord at selected
      have predicate := List.find?_some selected
      have decoded :
          record.input = input ∧ record.actor = actor ∧
            cachedEvidenceOutput evidence input = some record.output :=
        of_decide_eq_true predicate
      exact ⟨record, List.mem_of_find?_eq_some selected, decoded.2.1,
        decoded.1, rfl, decoded.2.2⟩

/-! ## Concrete mixed prover-history selector -/

/-- Exactly the two actors that can represent prover calls: the original run
and a same-tape replay.  Simulator and verifier calls are excluded. -/
def IsProverHistoryActor : QueryActor → Prop
  | .adversary => True
  | .extractorReplay => True
  | .simulator => False
  | .verifier => False

instance (actor : QueryActor) : Decidable (IsProverHistoryActor actor) := by
  cases actor with
  | adversary => exact isTrue trivial
  | simulator => exact isFalse (fun falseProof => falseProof.elim)
  | verifier => exact isFalse (fun falseProof => falseProof.elim)
  | extractorReplay => exact isTrue trivial

private def proverEvidenceCandidate (evidence : OracleState)
    (input : ShaInput) (record : QueryRecord) : Bool :=
  decide (IsProverHistoryActor record.actor ∧ record.input = input ∧
    cachedEvidenceOutput evidence input = some record.output)

private def adversaryEvidenceCandidate (evidence : OracleState)
    (input : ShaInput) (record : QueryRecord) : Bool :=
  decide (record.input = input ∧ record.actor = .adversary ∧
    cachedEvidenceOutput evidence input = some record.output)

/-- Search the original chronological history, accepting either legitimate
prover actor and requiring agreement with the immutable first-hit table. -/
def frozenProverEvidenceRecord (evidence : OracleState)
    (input : ShaInput) : Option QueryRecord :=
  evidence.history.find? (proverEvidenceCandidate evidence input)

def frozenProverEvidenceOutput (evidence : OracleState)
    (input : ShaInput) : Option ShaOutput :=
  (frozenProverEvidenceRecord evidence input).map QueryRecord.output

theorem frozen_prover_evidence_has_exact_record
    (evidence : OracleState) (input : ShaInput) (output : ShaOutput)
    (found : frozenProverEvidenceOutput evidence input = some output) :
    ∃ record : QueryRecord,
      record ∈ evidence.history ∧
      (record.actor = .adversary ∨ record.actor = .extractorReplay) ∧
      record.input = input ∧ record.output = output ∧
      cachedEvidenceOutput evidence input = some output := by
  unfold frozenProverEvidenceOutput at found
  cases selected : frozenProverEvidenceRecord evidence input with
  | none => simp [selected] at found
  | some record =>
      simp only [selected, Option.map_some, Option.some.injEq] at found
      subst output
      unfold frozenProverEvidenceRecord at selected
      have predicate := List.find?_some selected
      unfold proverEvidenceCandidate at predicate
      have decoded :
          IsProverHistoryActor record.actor ∧ record.input = input ∧
            cachedEvidenceOutput evidence input = some record.output :=
        of_decide_eq_true predicate
      have actorCases :
          record.actor = .adversary ∨ record.actor = .extractorReplay := by
        cases actorEq : record.actor <;>
          simp [IsProverHistoryActor, actorEq] at decoded ⊢
      exact ⟨record, List.mem_of_find?_eq_some selected, actorCases,
        decoded.2.1, rfl, decoded.2.2⟩

/-- A state with no replay-tagged record is an ordinary first-run evidence
state for purposes of historical work selection. -/
def HasNoExtractorReplayHistory (evidence : OracleState) : Prop :=
  ∀ record ∈ evidence.history, record.actor ≠ .extractorReplay

private theorem find_filtered_adversary_eq_find_conjoined
    (evidence : OracleState) (input : ShaInput)
    (records : List QueryRecord) :
    (records.filter fun record => record.actor = .adversary).find?
        (adversaryEvidenceCandidate evidence input) =
      records.find? (fun record =>
        decide (record.actor = .adversary) &&
          adversaryEvidenceCandidate evidence input record) := by
  induction records with
  | nil => rfl
  | cons record rest ih =>
      by_cases adversary : record.actor = .adversary
      · cases candidate : adversaryEvidenceCandidate evidence input record <;>
          simp [List.find?, adversary, candidate, ih]
      · simp [List.find?, adversary, ih]

private theorem find_prover_eq_find_adversary_of_no_replay
    (evidence : OracleState) (input : ShaInput)
    (records : List QueryRecord)
    (noReplay : ∀ record ∈ records, record.actor ≠ .extractorReplay) :
    records.find? (proverEvidenceCandidate evidence input) =
    (records.filter fun record => record.actor = .adversary).find?
      (adversaryEvidenceCandidate evidence input) := by
  rw [find_filtered_adversary_eq_find_conjoined]
  apply List.find?_congr
  intro record member
  have notReplay := noReplay record member
  cases actorEq : record.actor with
  | adversary =>
      simp [proverEvidenceCandidate, adversaryEvidenceCandidate,
        IsProverHistoryActor, actorEq]
  | simulator =>
      simp [proverEvidenceCandidate, adversaryEvidenceCandidate,
        IsProverHistoryActor, actorEq]
  | verifier =>
      simp [proverEvidenceCandidate, adversaryEvidenceCandidate,
        IsProverHistoryActor, actorEq]
  | extractorReplay =>
      exact False.elim (notReplay actorEq)

/-- On histories containing no replay calls, the union selector is exactly
the old adversary-Q1 selector. -/
theorem frozen_prover_evidence_record_plain_specialization
    (evidence : OracleState) (input : ShaInput)
    (plain : HasNoExtractorReplayHistory evidence) :
    frozenProverEvidenceRecord evidence input =
      frozenAdversaryEvidenceRecord evidence input := by
  unfold frozenProverEvidenceRecord frozenAdversaryEvidenceRecord
    freezeAdversaryQ1 actorHistory
  change evidence.history.find? (proverEvidenceCandidate evidence input) =
    (evidence.history.filter fun record => record.actor = .adversary).find?
      (adversaryEvidenceCandidate evidence input)
  exact find_prover_eq_find_adversary_of_no_replay evidence input
    evidence.history plain

theorem frozen_prover_evidence_output_plain_specialization
    (evidence : OracleState) (input : ShaInput)
    (plain : HasNoExtractorReplayHistory evidence) :
    frozenProverEvidenceOutput evidence input =
      frozenAdversaryEvidenceOutput evidence input := by
  unfold frozenProverEvidenceOutput frozenAdversaryEvidenceOutput
  rw [frozen_prover_evidence_record_plain_specialization evidence input plain]

/-! ## Mixed-history verifier-plan refactor -/

/-- Only the historical-work evidence selector changes.  Every nonhistorical
reply shape is the deployed one. -/
def replyFromVerifierOutputsForProverHistory (evidence : OracleState)
    (bindings : FixedBindings) (core : RuntimeCore)
    (action : VerifierAction) (outputs : List ShaOutput) :
    Option VerifierReply :=
  match action, outputs with
  | .workProbe _ nonce .adversaryHistory, [] =>
      (frozenProverEvidenceOutput evidence
        (historicalWorkInput core nonce)).map .single
  | action, outputs =>
      replyFromVerifierOutputs evidence bindings core action outputs

def verifierActionProgramForProverHistory (evidence : OracleState)
    (bindings : FixedBindings) (core : RuntimeCore)
    (action : VerifierAction) : OracleMachine VerifierReply :=
  queryInputsFor (verifierIssuedInputs bindings core action)
    (replyFromVerifierOutputsForProverHistory evidence bindings core action)

def verifierPlanProgramForProverHistory (frozenEvidence : OracleState)
    (bindings : FixedBindings) :
    RuntimeCore → List VerifierAction → OracleMachine VerifierPlanResult
  | core, [] => .pure { finalCore := core, actionReplies := [] }
  | core, action :: rest =>
      bindOracleMachine
        (verifierActionProgramForProverHistory frozenEvidence bindings core
          action)
        fun reply =>
          match applyActionWorkErased core action reply with
          | none => .abort .controllerRefused
          | some nextCore =>
              bindOracleMachine
                (verifierPlanProgramForProverHistory frozenEvidence bindings
                  nextCore rest)
                fun tail => .pure
                  { finalCore := tail.finalCore
                    actionReplies := (action, reply) :: tail.actionReplies }

def runFullVerifierPlanForProverHistory
    (controller : AdaptiveController) (limits : OracleLimits) (fuel : Nat)
    (frozenEvidence shared : OracleState) (tape : DeployedFixedTape) :
    MachineRun VerifierPlanResult :=
  runMachine controller limits .verifier fuel shared
    (verifierPlanProgramForProverHistory frozenEvidence
      (FixedBindings.ofContext tape.messages.context) initialCore
        (fullPlan tape))

theorem historical_work_program_for_prover_history_is_pure_or_abort
    (evidence : OracleState) (bindings : FixedBindings) (core : RuntimeCore)
    (stage : WorkStage) (nonce : NonceBytes) :
    verifierActionProgramForProverHistory evidence bindings core
        (.workProbe stage nonce .adversaryHistory) =
      match frozenProverEvidenceOutput evidence
          (historicalWorkInput core nonce) with
      | some output => .pure (.single output)
      | none => .abort .controllerRefused := by
  unfold verifierActionProgramForProverHistory
  simp only [verifierIssuedInputs, queryInputsFor,
    replyFromVerifierOutputsForProverHistory]
  cases frozenProverEvidenceOutput evidence
      (historicalWorkInput core nonce) <;> rfl

/-- Selected work remains the exact verifier-issued query, independently of
the mixed historical selector. -/
theorem selected_work_program_is_unchanged
    (evidence : OracleState) (bindings : FixedBindings) (core : RuntimeCore)
    (stage : WorkStage) (nonce : NonceBytes) :
    verifierActionProgramForProverHistory evidence bindings core
        (.workProbe stage nonce .verifierSelected) =
      .query (historicalWorkInput core nonce)
        (fun output => .pure (.single output)) := by
  change verifierActionProgram evidence bindings core
      (.workProbe stage nonce .verifierSelected) = _
  simpa [historicalWorkInput] using
    selected_work_program_issues_the_exact_deployed_query evidence bindings
      core stage nonce

/-- On an ordinary history, every refactored action is exactly the current
action program. -/
theorem verifier_action_program_plain_specialization
    (evidence : OracleState) (bindings : FixedBindings) (core : RuntimeCore)
    (action : VerifierAction) (plain : HasNoExtractorReplayHistory evidence) :
    verifierActionProgramForProverHistory evidence bindings core action =
      verifierActionProgram evidence bindings core action := by
  cases action <;> try rfl
  next stage nonce kind =>
    cases kind with
    | verifierSelected => rfl
    | adversaryHistory =>
        rw [historical_work_program_for_prover_history_is_pure_or_abort,
          adversary_history_program_uses_only_frozen_q1_evidence]
        simp only [historicalWorkInput]
        rw [frozen_prover_evidence_output_plain_specialization evidence
          (bytes core.digest ++ [domGrind] ++ bytes nonce) plain]
        rfl

/-- The complete mixed-history plan is a conservative extension on ordinary
first-run histories. -/
theorem verifier_plan_program_plain_specialization
    (evidence : OracleState) (bindings : FixedBindings) (core : RuntimeCore)
    (actions : List VerifierAction)
    (plain : HasNoExtractorReplayHistory evidence) :
    verifierPlanProgramForProverHistory evidence bindings core actions =
      verifierPlanProgram evidence bindings core actions := by
  induction actions generalizing core with
  | nil => rfl
  | cons action rest ih =>
      change
        bindOracleMachine
            (verifierActionProgramForProverHistory evidence bindings core
              action)
            (fun reply =>
              match applyActionWorkErased core action reply with
              | none =>
                  (OracleMachine.abort .controllerRefused :
                    OracleMachine VerifierPlanResult)
              | some nextCore =>
                  bindOracleMachine
                    (verifierPlanProgramForProverHistory evidence bindings
                      nextCore rest)
                    fun tail : VerifierPlanResult => .pure
                      ({ finalCore := tail.finalCore
                         actionReplies :=
                           (action, reply) :: tail.actionReplies } :
                        VerifierPlanResult)) =
          bindOracleMachine
            (verifierActionProgram evidence bindings core action)
            (fun reply =>
              match applyActionWorkErased core action reply with
              | none =>
                  (OracleMachine.abort .controllerRefused :
                    OracleMachine VerifierPlanResult)
              | some nextCore =>
                  bindOracleMachine
                    (verifierPlanProgram evidence bindings nextCore rest)
                    fun tail : VerifierPlanResult => .pure
                      ({ finalCore := tail.finalCore
                         actionReplies :=
                           (action, reply) :: tail.actionReplies } :
                        VerifierPlanResult))
      rw [verifier_action_program_plain_specialization evidence bindings core
        action plain]
      have continuationEqual :
          (fun reply =>
            match applyActionWorkErased core action reply with
            | none =>
                (OracleMachine.abort .controllerRefused :
                  OracleMachine VerifierPlanResult)
            | some nextCore =>
                bindOracleMachine
                  (verifierPlanProgramForProverHistory evidence bindings
                    nextCore rest)
                  fun tail : VerifierPlanResult => .pure
                    ({ finalCore := tail.finalCore
                       actionReplies :=
                         (action, reply) :: tail.actionReplies } :
                      VerifierPlanResult)) =
          (fun reply =>
            match applyActionWorkErased core action reply with
            | none =>
                (OracleMachine.abort .controllerRefused :
                  OracleMachine VerifierPlanResult)
            | some nextCore =>
                bindOracleMachine
                  (verifierPlanProgram evidence bindings nextCore rest)
                  fun tail : VerifierPlanResult => .pure
                    ({ finalCore := tail.finalCore
                       actionReplies :=
                         (action, reply) :: tail.actionReplies } :
                      VerifierPlanResult)) := by
        funext reply
        cases applied : applyActionWorkErased core action reply with
        | none => rfl
        | some nextCore =>
            change
              bindOracleMachine
                  (verifierPlanProgramForProverHistory evidence bindings
                    nextCore rest) _ =
                bindOracleMachine
                  (verifierPlanProgram evidence bindings nextCore rest) _
            rw [ih nextCore]
      rw [continuationEqual]

theorem run_full_verifier_plan_plain_specialization
    (controller : AdaptiveController) (limits : OracleLimits) (fuel : Nat)
    (frozenEvidence shared : OracleState) (tape : DeployedFixedTape)
    (plain : HasNoExtractorReplayHistory frozenEvidence) :
    runFullVerifierPlanForProverHistory controller limits fuel frozenEvidence
        shared tape =
      runFullVerifierPlan controller limits fuel frozenEvidence shared tape := by
  unfold runFullVerifierPlanForProverHistory runFullVerifierPlan runVerifierPlan
  rw [verifier_plan_program_plain_specialization _ _ _ _ plain]

/-- Once a historical answer is available, work-erased execution retains the
nonce/action but does not test its rejection predicate and does not advance
the transcript core. -/
theorem historical_work_answer_advances_erased_ancestor
    (core : RuntimeCore) (stage : WorkStage) (nonce : NonceBytes)
    (output : ShaOutput) :
    applyActionWorkErased core (.workProbe stage nonce .adversaryHistory)
      (.single output) = some core := by
  rfl

/-! ## A reachable extractor-only evidence state -/

/-- One coherent oracle call, retaining its actual actor tag. -/
def singleActorCallState (actor : QueryActor) (input : ShaInput)
    (output : ShaOutput) : OracleState where
  table := [{ input := input, output := output, source := .fresh }]
  history :=
    [{ input := input, output := output, actor := actor, origin := .fresh }]
  programmingHistory := []
  totalCalls := 1
  freshCalls := 1

def singleCallController (output : ShaOutput) : AdaptiveController :=
  fun _history _input => .answer output

def singleCallLimits : OracleLimits where
  totalCalls := 1
  freshCalls := 1
  programmedPoints := 0

/-- The counterexample state is operationally reachable from the empty lazy
oracle by one replay-tagged query. -/
theorem single_extractor_call_state_is_reachable
    (input : ShaInput) (output : ShaOutput) :
    queryOracle (singleCallController output) singleCallLimits
        .extractorReplay emptyOracle input =
      .ok (output, singleActorCallState .extractorReplay input output) := by
  simp [queryOracle, singleCallController, singleCallLimits, emptyOracle,
    lookupEntry, singleActorCallState]

@[simp] theorem single_actor_call_has_cached_answer
    (actor : QueryActor) (input : ShaInput) (output : ShaOutput) :
    cachedEvidenceOutput (singleActorCallState actor input output) input =
      some output := by
  simp [cachedEvidenceOutput, lookupEntry, singleActorCallState]

@[simp] theorem single_extractor_call_has_no_adversary_q1
    (input : ShaInput) (output : ShaOutput) :
    freezeAdversaryQ1
        (singleActorCallState .extractorReplay input output) =
      [] := by
  simp [freezeAdversaryQ1, actorHistory, singleActorCallState]

/-- The generalized replay selector finds the real replay-tagged record. -/
theorem single_extractor_call_is_extractor_evidence
    (input : ShaInput) (output : ShaOutput) :
    frozenActorEvidenceOutput .extractorReplay
        (singleActorCallState .extractorReplay input output) input =
      some output := by
  simp [frozenActorEvidenceOutput, frozenActorEvidenceRecord, actorHistory,
    cachedEvidenceOutput, lookupEntry, singleActorCallState]

/-- The chronological mixed prover selector also finds the replay record. -/
theorem single_extractor_call_is_prover_evidence
    (input : ShaInput) (output : ShaOutput) :
    frozenProverEvidenceOutput
        (singleActorCallState .extractorReplay input output) input =
      some output := by
  simp [frozenProverEvidenceOutput, frozenProverEvidenceRecord,
    proverEvidenceCandidate, IsProverHistoryActor, cachedEvidenceOutput, lookupEntry,
    singleActorCallState]

/-- The current adversary-only selector cannot use that same record. -/
theorem single_extractor_call_is_not_adversary_evidence
    (input : ShaInput) (output : ShaOutput) :
    frozenAdversaryEvidenceOutput
        (singleActorCallState .extractorReplay input output) input = none := by
  simp [frozenAdversaryEvidenceOutput, frozenAdversaryEvidenceRecord,
    freezeAdversaryQ1, actorHistory, singleActorCallState]

def extractorOnlyWorkEvidence (core : RuntimeCore) (nonce : NonceBytes)
    (output : ShaOutput) : OracleState :=
  singleActorCallState .extractorReplay (historicalWorkInput core nonce) output

/-- The mixed prover-history leaf consumes the coherent replay record without
changing its actor. -/
theorem extractor_work_evidence_runs_refactored_leaf
    (bindings : FixedBindings) (core : RuntimeCore)
    (stage : WorkStage) (nonce : NonceBytes) (output : ShaOutput) :
    verifierActionProgramForProverHistory
        (extractorOnlyWorkEvidence core nonce output) bindings core
        (.workProbe stage nonce .adversaryHistory) =
      .pure (.single output) := by
  rw [historical_work_program_for_prover_history_is_pure_or_abort]
  simp [extractorOnlyWorkEvidence, historicalWorkInput,
    single_extractor_call_is_prover_evidence]

/-- On exactly the same coherent state, the current leaf aborts solely because
it searches adversary-tagged Q1. -/
theorem extractor_work_evidence_aborts_current_leaf
    (bindings : FixedBindings) (core : RuntimeCore)
    (stage : WorkStage) (nonce : NonceBytes) (output : ShaOutput) :
    verifierActionProgram (extractorOnlyWorkEvidence core nonce output)
        bindings core (.workProbe stage nonce .adversaryHistory) =
      .abort .controllerRefused := by
  rw [adversary_history_program_uses_only_frozen_q1_evidence]
  simp [extractorOnlyWorkEvidence, historicalWorkInput,
    single_extractor_call_is_not_adversary_evidence]

/-- Work erasure alone cannot bridge the actor mismatch: the erased ancestor
has a valid transition for the answer, while the current verifier leaf cannot
obtain that answer from the replay-tagged evidence state. -/
theorem work_erasure_does_not_remove_actor_gate
    (bindings : FixedBindings) (core : RuntimeCore)
    (stage : WorkStage) (nonce : NonceBytes) (output : ShaOutput) :
    applyActionWorkErased core (.workProbe stage nonce .adversaryHistory)
        (.single output) = some core ∧
      verifierActionProgramForProverHistory
          (extractorOnlyWorkEvidence core nonce output) bindings core
          (.workProbe stage nonce .adversaryHistory) =
        .pure (.single output) ∧
      verifierActionProgram (extractorOnlyWorkEvidence core nonce output)
          bindings core (.workProbe stage nonce .adversaryHistory) =
        .abort .controllerRefused := by
  exact ⟨historical_work_answer_advances_erased_ancestor core stage nonce output,
    extractor_work_evidence_runs_refactored_leaf bindings core stage nonce output,
    extractor_work_evidence_aborts_current_leaf bindings core stage nonce output⟩

/-- The refusal is visible at the machine level and costs no query or step;
it is not a work-threshold failure or an oracle-budget failure. -/
theorem extractor_work_evidence_current_run_refuses_without_call
    (controller : AdaptiveController) (limits : OracleLimits) (fuel : Nat)
    (shared : OracleState) (bindings : FixedBindings) (core : RuntimeCore)
    (stage : WorkStage) (nonce : NonceBytes) (output : ShaOutput) :
    let run := runVerifierAction controller limits fuel
      (extractorOnlyWorkEvidence core nonce output) shared bindings core
      (.workProbe stage nonce .adversaryHistory)
    run.halt = .oracleAbort .controllerRefused ∧
      run.oracle = shared ∧ run.steps = 0 := by
  unfold runVerifierAction
  rw [show verifierActionProgram (extractorOnlyWorkEvidence core nonce output)
      bindings core (.workProbe stage nonce .adversaryHistory) =
        .abort .controllerRefused from
      extractor_work_evidence_aborts_current_leaf bindings core stage nonce
        output]
  simp [runMachine]

#print axioms frozen_actor_evidence_has_exact_record
#print axioms frozen_prover_evidence_has_exact_record
#print axioms frozen_prover_evidence_record_plain_specialization
#print axioms verifier_plan_program_plain_specialization
#print axioms run_full_verifier_plan_plain_specialization
#print axioms selected_work_program_is_unchanged
#print axioms single_extractor_call_state_is_reachable
#print axioms work_erasure_does_not_remove_actor_gate
#print axioms extractor_work_evidence_current_run_refuses_without_call

end AspisK1.V7Tag73ReplayWorkEvidenceBridge
