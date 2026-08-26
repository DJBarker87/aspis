import AspisFormal.K1.V7Tag73CoupledReplayAlignment
import AspisFormal.K1.V7Tag73ResourceLazyOracle

/-!
# Shared-oracle runner for one deployed Tag-73 verifier action

This module executes a literal `VerifierAction` as an `OracleMachine` over an
arbitrary shared `OracleState`.  Calls issued by the deployed verifier are run
with actor `.verifier` and in the exact `actionInputs` order.  The frozen
post-adversary evidence state is a separate argument from the evolving shared
state, so later verifier calls cannot fabricate historical grinding evidence.

The historical grinding probes are the important exception: they were made by
the adversary while searching for a nonce, and the deployed verifier does not
repeat them.  A `.workProbe ... .adversaryHistory` action therefore reads
required evidence from the frozen post-adversary table without issuing an
oracle call.  Only `.verifierSelected` issues the one deployed work check.
Thus the three work stages remain separate and contribute exactly three calls
to the existing `1511` full-256 verifier ceiling.

No acceptance, schedule matching, restoration, or extraction statement is an
input or conclusion here.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73SharedOracleVerifierRunner

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73InteractiveExecution
open AspisK1.V7Tag73CoupledReplayAlignment
open AspisK1.V7Tag73ResourceLazyOracle
open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling

/-! ## Exact deployed verifier call selection -/

/-- Calls actually issued by the deployed verifier for one action.  Earlier
grinding probes are evidence, not repeated verifier calls. -/
def verifierIssuedInputs (bindings : FixedBindings) (core : RuntimeCore) :
    VerifierAction → List ShaInput
  | .workProbe _ _ .adversaryHistory => []
  | action => actionInputs bindings core action

def deployedFull256ActionQueryCount : VerifierAction → Nat
  | .absorb _ => 1
  | .requestRootSalt _ => 1
  | .absorbC1 _ => 1
  | .absorbC2 _ _ _ => 1
  | .squeezePair _ _ => 2
  | .workProbe _ _ .adversaryHistory => 0
  | .workProbe _ _ .verifierSelected => 1
  | .checkpoint _ => 0
  | .markQ16Base => 0
  | .q16CandidateAbsorb _ _ _ => 1
  | .q16Restore _ => 0
  | .q16Selected _ => 0
  | .q16SamplerAbortReject _ => 0
  | .q16AllNoncompactReject => 0
  | .terminal => 0

@[simp] theorem adversary_history_issues_no_verifier_query
    (bindings : FixedBindings) (core : RuntimeCore)
    (stage : WorkStage) (nonce : NonceBytes) :
    verifierIssuedInputs bindings core
      (.workProbe stage nonce .adversaryHistory) = [] := by
  rfl

@[simp] theorem selected_work_issues_exactly_one_verifier_query
    (bindings : FixedBindings) (core : RuntimeCore)
    (stage : WorkStage) (nonce : NonceBytes) :
    verifierIssuedInputs bindings core
        (.workProbe stage nonce .verifierSelected) =
      [bytes core.digest ++ [domGrind] ++ bytes nonce] := by
  rfl

theorem three_selected_work_checks_are_three_verifier_calls :
    deployedFull256ActionQueryCount
        (.workProbe .batch (zeroBytes 8) .verifierSelected) +
      deployedFull256ActionQueryCount
        (.workProbe .fold (zeroBytes 8) .verifierSelected) +
      deployedFull256ActionQueryCount
        (.workProbe .final (zeroBytes 8) .verifierSelected) = 3 := by
  rfl

/-- The global ceiling used by this runner is the already audited exact
deployed expression, where historical work probes are absent. -/
theorem shared_runner_full256_verifier_call_cap
    (messages : Messages)
    {frontierNodes : QuerySchedule → Nat}
    (search : FirstCap203Search frontierNodes) :
    tag73Full256VerifierOracleCalls messages search ≤ 1511 :=
  tag73_full256_verifier_oracle_calls_le_1511 messages search

/-! ## Query-list program and reply construction -/

/-- Query a fixed list in order, then run a pure partial decoder on the list
of returned answers. -/
def queryInputsFor {Result : Type*} :
    List ShaInput → (List ShaOutput → Option Result) → OracleMachine Result
  | [], finish =>
      match finish [] with
      | some result => .pure result
      | none => .abort .controllerRefused
  | input :: rest, finish =>
      .query input fun output =>
        queryInputsFor rest fun outputs => finish (output :: outputs)

/-- Read one input from the fixed post-adversary table without making a new
oracle call. -/
def cachedEvidenceOutput (evidence : OracleState)
    (input : ShaInput) : Option ShaOutput :=
  (lookupEntry evidence input).map
    AspisK1.V7FsAokExperiment.TableEntry.output

/-- Historical work is accepted as evidence only when the frozen adversary Q1
contains the call and its answer agrees with the frozen table's first-hit
answer.  Later verifier calls can therefore neither create nor repair this
evidence. -/
def frozenAdversaryEvidenceRecord (evidence : OracleState)
    (input : ShaInput) : Option QueryRecord :=
  (freezeAdversaryQ1 evidence).find? fun record => decide
    (record.input = input ∧ record.actor = .adversary ∧
      cachedEvidenceOutput evidence input = some record.output)

def frozenAdversaryEvidenceOutput (evidence : OracleState)
    (input : ShaInput) : Option ShaOutput :=
  (frozenAdversaryEvidenceRecord evidence input).map QueryRecord.output

theorem frozen_adversary_evidence_has_q1_record
    (evidence : OracleState) (input : ShaInput) (output : ShaOutput)
    (found : frozenAdversaryEvidenceOutput evidence input = some output) :
    ∃ record : QueryRecord,
      record ∈ freezeAdversaryQ1 evidence ∧
      record.actor = .adversary ∧ record.input = input ∧
      record.output = output ∧
      cachedEvidenceOutput evidence input = some output := by
  unfold frozenAdversaryEvidenceOutput at found
  cases selected : frozenAdversaryEvidenceRecord evidence input with
  | none => simp [selected] at found
  | some record =>
      simp only [selected, Option.map_some, Option.some.injEq] at found
      subst output
      unfold frozenAdversaryEvidenceRecord at selected
      have predicate := List.find?_some selected
      have decoded :
          record.input = input ∧ record.actor = .adversary ∧
            cachedEvidenceOutput evidence input = some record.output :=
        of_decide_eq_true predicate
      exact ⟨record, List.mem_of_find?_eq_some selected, decoded.2.1,
        decoded.1, rfl, decoded.2.2⟩

/-- Convert exactly the outputs issued by the verifier into the reply shape
required by the action.  Historical work receives its output only from Q1
evidence and therefore expects no newly issued output. -/
def replyFromVerifierOutputs (evidence : OracleState)
    (bindings : FixedBindings) (core : RuntimeCore) :
    VerifierAction → List ShaOutput → Option VerifierReply
  | .checkpoint _, [] => some .none
  | .markQ16Base, [] => some .none
  | .q16Restore _, [] => some .none
  | .q16Selected _, [] => some .none
  | .q16SamplerAbortReject _, [] => some .none
  | .q16AllNoncompactReject, [] => some .none
  | .terminal, [] => some .none
  | .workProbe stage nonce .adversaryHistory, [] =>
      (frozenAdversaryEvidenceOutput evidence
        (bytes core.digest ++ [domGrind] ++ bytes nonce)).map .single
  | .squeezePair _ _, [output, advance] => some (.squeeze output advance)
  | .absorb _, [output] => some (.single output)
  | .requestRootSalt _, [output] => some (.single output)
  | .absorbC1 _, [output] => some (.single output)
  | .absorbC2 _ _ _, [output] => some (.single output)
  | .workProbe _ _ .verifierSelected, [output] => some (.single output)
  | .q16CandidateAbsorb _ _ _, [output] => some (.single output)
  | _, _ => none

def verifierActionProgram (evidence : OracleState)
    (bindings : FixedBindings) (core : RuntimeCore)
    (action : VerifierAction) : OracleMachine VerifierReply :=
  queryInputsFor (verifierIssuedInputs bindings core action)
    (replyFromVerifierOutputs evidence bindings core action)

def runVerifierAction (controller : AdaptiveController)
    (limits : OracleLimits) (fuel : Nat)
    (frozenEvidence shared : OracleState)
    (bindings : FixedBindings) (core : RuntimeCore)
    (action : VerifierAction) : MachineRun VerifierReply :=
  runMachine controller limits .verifier fuel shared
    (verifierActionProgram frozenEvidence bindings core action)

/-- Sequencing for the deliberately small free oracle language. -/
def bindOracleMachine {First Second : Type*}
    (program : OracleMachine First)
    (next : First → OracleMachine Second) : OracleMachine Second :=
  match program with
  | .pure value => next value
  | .abort reason => .abort reason
  | .query input continuation =>
      .query input fun output => bindOracleMachine (continuation output) next

structure VerifierPlanResult where
  finalCore : RuntimeCore
  actionReplies : List (VerifierAction × VerifierReply)

/-- Execute an action list while threading the exact runtime core.  The frozen
Q1 evidence never changes; only the shared oracle threaded by `runMachine`
changes. -/
def verifierPlanProgram (frozenEvidence : OracleState)
    (bindings : FixedBindings) :
    RuntimeCore → List VerifierAction → OracleMachine VerifierPlanResult
  | core, [] => .pure { finalCore := core, actionReplies := [] }
  | core, action :: rest =>
      bindOracleMachine (verifierActionProgram frozenEvidence bindings core action)
        fun reply =>
          match applyActionWorkErased core action reply with
          | none => .abort .controllerRefused
          | some nextCore =>
              bindOracleMachine
                (verifierPlanProgram frozenEvidence bindings nextCore rest)
                fun tail => .pure
                  { finalCore := tail.finalCore
                    actionReplies := (action, reply) :: tail.actionReplies }

def runVerifierPlan (controller : AdaptiveController)
    (limits : OracleLimits) (fuel : Nat)
    (frozenEvidence shared : OracleState) (bindings : FixedBindings)
    (core : RuntimeCore) (actions : List VerifierAction) :
    MachineRun VerifierPlanResult :=
  runMachine controller limits .verifier fuel shared
    (verifierPlanProgram frozenEvidence bindings core actions)

def runFullVerifierPlan (controller : AdaptiveController)
    (limits : OracleLimits) (fuel : Nat)
    (frozenEvidence shared : OracleState) (tape : DeployedFixedTape) :
    MachineRun VerifierPlanResult :=
  runVerifierPlan controller limits fuel frozenEvidence shared
    (FixedBindings.ofContext tape.messages.context) initialCore (fullPlan tape)

theorem adversary_history_program_uses_only_frozen_q1_evidence
    (evidence : OracleState) (bindings : FixedBindings) (core : RuntimeCore)
    (stage : WorkStage) (nonce : NonceBytes) :
    verifierActionProgram evidence bindings core
        (.workProbe stage nonce .adversaryHistory) =
      match frozenAdversaryEvidenceOutput evidence
          (bytes core.digest ++ [domGrind] ++ bytes nonce) with
      | some output => .pure (.single output)
      | none => .abort .controllerRefused := by
  unfold verifierActionProgram
  simp only [verifierIssuedInputs, queryInputsFor,
    replyFromVerifierOutputs]
  cases frozenAdversaryEvidenceOutput evidence
      (bytes core.digest ++ [domGrind] ++ bytes nonce) <;> rfl

theorem selected_work_program_issues_the_exact_deployed_query
    (evidence : OracleState) (bindings : FixedBindings) (core : RuntimeCore)
    (stage : WorkStage) (nonce : NonceBytes) :
    verifierActionProgram evidence bindings core
        (.workProbe stage nonce .verifierSelected) =
      .query (bytes core.digest ++ [domGrind] ++ bytes nonce)
        (fun output => .pure (.single output)) := by
  rfl

theorem adversary_history_run_makes_zero_verifier_calls
    (controller : AdaptiveController) (limits : OracleLimits) (fuel : Nat)
    (frozenEvidence shared : OracleState) (bindings : FixedBindings)
    (core : RuntimeCore) (stage : WorkStage) (nonce : NonceBytes) :
    (runVerifierAction controller limits fuel frozenEvidence shared bindings core
        (.workProbe stage nonce .adversaryHistory)).oracle = shared ∧
      (runVerifierAction controller limits fuel frozenEvidence shared bindings
        core (.workProbe stage nonce .adversaryHistory)).steps = 0 := by
  rw [runVerifierAction,
    adversary_history_program_uses_only_frozen_q1_evidence]
  split <;> cases fuel <;> simp [runMachine]

theorem returned_adversary_history_reply_has_frozen_q1_evidence
    (controller : AdaptiveController) (limits : OracleLimits) (fuel : Nat)
    (frozenEvidence shared : OracleState) (bindings : FixedBindings)
    (core : RuntimeCore) (stage : WorkStage) (nonce : NonceBytes)
    (output : ShaOutput)
    (returned :
      (runVerifierAction controller limits fuel frozenEvidence shared bindings
        core (.workProbe stage nonce .adversaryHistory)).halt =
          .returned (.single output)) :
    ∃ record : QueryRecord,
      record ∈ freezeAdversaryQ1 frozenEvidence ∧
      record.actor = .adversary ∧
      record.input = bytes core.digest ++ [domGrind] ++ bytes nonce ∧
      record.output = output ∧
      cachedEvidenceOutput frozenEvidence
          (bytes core.digest ++ [domGrind] ++ bytes nonce) = some output := by
  rw [runVerifierAction,
    adversary_history_program_uses_only_frozen_q1_evidence] at returned
  split at returned
  next result evidenceFound =>
    simp only [runMachine, MachineHalt.returned.injEq,
      VerifierReply.single.injEq] at returned
    subst result
    exact frozen_adversary_evidence_has_q1_record frozenEvidence
      (bytes core.digest ++ [domGrind] ++ bytes nonce) output evidenceFound
  next => simp [runMachine] at returned

/-! ## Operational query paths -/

inductive MachineQueryPath {Result : Type*} :
    OracleMachine Result → List (ShaInput × ShaOutput) → Result → Prop where
  | pure (result : Result) : MachineQueryPath (.pure result) [] result
  | query (input : ShaInput) (next : ShaOutput → OracleMachine Result)
      (output : ShaOutput) (pairs : List (ShaInput × ShaOutput))
      (result : Result)
      (tail : MachineQueryPath (next output) pairs result) :
      MachineQueryPath (.query input next) ((input, output) :: pairs) result

theorem query_oracle_success_appends_one_record
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (state nextState : OracleState)
    (input : ShaInput) (output : ShaOutput)
    (success : queryOracle controller limits actor state input =
      .ok (output, nextState)) :
    ∃ origin : AnswerOrigin,
      nextState.history = state.history ++
        [{ input := input, output := output, actor := actor, origin := origin }] := by
  unfold queryOracle at success
  split at success <;> try contradiction
  next _ =>
    split at success
    next entry found =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at success
      rcases success with ⟨rfl, rfl⟩
      exact ⟨cachedOrigin entry.source, rfl⟩
    next missing =>
      split at success <;> try contradiction
      next _ =>
        split at success
        next _ => contradiction
        next answer answered =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at success
          rcases success with ⟨rfl, rfl⟩
          exact ⟨.fresh, rfl⟩

/-! ## The shared table retains every returned answer -/

private theorem projected_table_lookup_eq
    (table : List AspisK1.V7FsAokExperiment.TableEntry)
    (input : ShaInput) :
    tableLookup
        (table.map fun entry =>
          ({ input := entry.input, output := entry.output } :
            AspisK1.V7Tag73DeterministicRefinement.TableEntry)) input =
      (table.find? fun entry => entry.input = input).map
        AspisK1.V7FsAokExperiment.TableEntry.output := by
  unfold tableLookup
  rw [List.find?_map]
  simp [Function.comp_def, Option.map_map]

theorem fixed_table_lookup_eq_lookup_entry_output
    (state : OracleState) (input : ShaInput) :
    tableLookup (fixedTableOfOracleState state) input =
      (lookupEntry state input).map
        AspisK1.V7FsAokExperiment.TableEntry.output := by
  simpa [fixedTableOfOracleState, lookupEntry] using
    projected_table_lookup_eq state.table input

private theorem table_lookup_append_preserves_some
    (table suffix : FixedOracleTable) (input : ShaInput) (output : ShaOutput)
    (found : tableLookup table input = some output) :
    tableLookup (table ++ suffix) input = some output := by
  induction table with
  | nil => simp [tableLookup] at found
  | cons entry rest ih =>
      by_cases hit : entry.input = input
      · simpa [tableLookup, hit] using found
      · have restFound : tableLookup rest input = some output := by
          simpa [tableLookup, hit] using found
        simpa [tableLookup, hit] using ih restFound

private theorem table_lookup_append_fresh
    (table : FixedOracleTable) (input : ShaInput) (output : ShaOutput)
    (missing : tableLookup table input = none) :
    tableLookup
        (table ++
          [({ input := input, output := output } :
            AspisK1.V7Tag73DeterministicRefinement.TableEntry)]) input =
      some output := by
  induction table with
  | nil => simp [tableLookup]
  | cons entry rest ih =>
      by_cases hit : entry.input = input
      · simp [tableLookup, hit] at missing
      · have restMissing : tableLookup rest input = none := by
          simpa [tableLookup, hit] using missing
        simpa [tableLookup, hit] using ih restMissing

theorem query_oracle_success_extends_fixed_table
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (state nextState : OracleState)
    (input : ShaInput) (output : ShaOutput)
    (success : queryOracle controller limits actor state input =
      .ok (output, nextState)) :
    ∃ suffix : FixedOracleTable,
      fixedTableOfOracleState nextState =
        fixedTableOfOracleState state ++ suffix := by
  unfold queryOracle at success
  split at success <;> try contradiction
  next _ =>
    split at success
    next entry found =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at success
      rcases success with ⟨rfl, rfl⟩
      refine ⟨[], ?_⟩
      change fixedTableOfOracleState state =
        fixedTableOfOracleState state ++ []
      simp
    next missing =>
      split at success <;> try contradiction
      next _ =>
        split at success
        next _ => contradiction
        next answer answered =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at success
          rcases success with ⟨rfl, rfl⟩
          refine ⟨[
            ({ input := input, output := answer } :
              AspisK1.V7Tag73DeterministicRefinement.TableEntry)], ?_⟩
          simp [fixedTableOfOracleState]

theorem query_oracle_success_preserves_fixed_table_answer
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (state nextState : OracleState)
    (input : ShaInput) (output : ShaOutput)
    (success : queryOracle controller limits actor state input =
      .ok (output, nextState))
    (priorInput : ShaInput) (priorOutput : ShaOutput)
    (prior : tableLookup (fixedTableOfOracleState state) priorInput =
      some priorOutput) :
    tableLookup (fixedTableOfOracleState nextState) priorInput =
      some priorOutput := by
  obtain ⟨suffix, extension⟩ := query_oracle_success_extends_fixed_table
    controller limits actor state nextState input output success
  rw [extension]
  exact table_lookup_append_preserves_some _ _ _ _ prior

theorem query_oracle_success_fixed_table_has_answer
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (state nextState : OracleState)
    (input : ShaInput) (output : ShaOutput)
    (success : queryOracle controller limits actor state input =
      .ok (output, nextState)) :
    tableLookup (fixedTableOfOracleState nextState) input = some output := by
  unfold queryOracle at success
  split at success <;> try contradiction
  next _ =>
    split at success
    next entry found =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at success
      rcases success with ⟨rfl, rfl⟩
      change tableLookup (fixedTableOfOracleState state) input =
        some entry.output
      rw [fixed_table_lookup_eq_lookup_entry_output, found]
      rfl
    next missing =>
      split at success <;> try contradiction
      next _ =>
        split at success
        next _ => contradiction
        next answer answered =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at success
          rcases success with ⟨rfl, rfl⟩
          have projectedMissing :
              tableLookup (fixedTableOfOracleState state) input = none := by
            rw [fixed_table_lookup_eq_lookup_entry_output, missing]
            rfl
          simpa [fixedTableOfOracleState] using
            table_lookup_append_fresh
              (fixedTableOfOracleState state) input answer projectedMissing

theorem run_machine_preserves_fixed_table_answer
    {Result : Type*} (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (program : OracleMachine Result)
    (priorInput : ShaInput) (priorOutput : ShaOutput)
    (prior : tableLookup (fixedTableOfOracleState state) priorInput =
      some priorOutput) :
    tableLookup
        (fixedTableOfOracleState
          (runMachine controller limits actor fuel state program).oracle)
        priorInput = some priorOutput := by
  induction fuel generalizing state program with
  | zero =>
      cases program with
      | pure result => simpa [runMachine] using prior
      | abort reason => simpa [runMachine] using prior
      | query input next => simpa [runMachine] using prior
  | succ fuel ih =>
      cases program with
      | pure result => simpa [runMachine] using prior
      | abort reason => simpa [runMachine] using prior
      | query input next =>
          cases queryResult : queryOracle controller limits actor state input with
          | error reason => simpa [runMachine, queryResult] using prior
          | ok pair =>
              rcases pair with ⟨output, nextState⟩
              have nextPrior :=
                query_oracle_success_preserves_fixed_table_answer controller
                  limits actor state nextState input output queryResult
                    priorInput priorOutput prior
              simpa [runMachine, queryResult] using
                ih nextState (next output) nextPrior

/-- Every normally returned `runMachine` has a concrete query path, and its
new ordered history is exactly that path. -/
theorem run_machine_returned_has_exact_query_path
    {Result : Type*} (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (program : OracleMachine Result) (result : Result)
    (returned : (runMachine controller limits actor fuel state program).halt =
      .returned result) :
    ∃ pairs : List (ShaInput × ShaOutput),
      MachineQueryPath program pairs result ∧
      queryAnswerTrace
          (historySince state
            (runMachine controller limits actor fuel state program).oracle) =
      pairs ∧
      (∀ record ∈ historySince state
          (runMachine controller limits actor fuel state program).oracle,
        record.actor = actor) ∧
      ∀ pair ∈ pairs,
        tableLookup
            (fixedTableOfOracleState
              (runMachine controller limits actor fuel state program).oracle)
            pair.1 = some pair.2 := by
  induction fuel generalizing state program with
  | zero =>
      cases program with
      | pure value =>
          simp only [runMachine, MachineHalt.returned.injEq] at returned
          subst value
          exact ⟨[], .pure result,
            by simp only [historySince, runMachine, List.drop_length,
              queryAnswerTrace, List.map_nil],
            by simp [historySince, runMachine], by simp⟩
      | abort reason => simp [runMachine] at returned
      | query input next => simp [runMachine] at returned
  | succ fuel ih =>
      cases program with
      | pure value =>
          simp only [runMachine, MachineHalt.returned.injEq] at returned
          subst value
          exact ⟨[], .pure result,
            by simp only [historySince, runMachine, List.drop_length,
              queryAnswerTrace, List.map_nil],
            by simp [historySince, runMachine], by simp⟩
      | abort reason => simp [runMachine] at returned
      | query input next =>
          cases queryResult : queryOracle controller limits actor state input with
          | error reason => simp [runMachine, queryResult] at returned
          | ok pair =>
              rcases pair with ⟨output, nextState⟩
              have recursiveReturned :
                  (runMachine controller limits actor fuel nextState
                    (next output)).halt = .returned result := by
                simpa [runMachine, queryResult] using returned
              obtain ⟨pairs, path, trace, actors, tableAnswers⟩ :=
                ih nextState (next output) recursiveReturned
              obtain ⟨origin, nextHistory⟩ :=
                query_oracle_success_appends_one_record controller limits actor
                  state nextState input output queryResult
              have historyPrefix := postfork_run_history_is_preserved
                controller limits actor fuel nextState (next output)
              rcases historyPrefix with ⟨suffix, finalHistory⟩
              have firstDelta :
                  historySince state
                      (runMachine controller limits actor fuel nextState
                        (next output)).oracle =
                    { input := input, output := output, actor := actor,
                        origin := origin } :: suffix := by
                unfold historySince
                rw [← finalHistory, nextHistory]
                simp [List.append_assoc]
              have tailDelta :
                  historySince nextState
                      (runMachine controller limits actor fuel nextState
                        (next output)).oracle = suffix := by
                unfold historySince
                rw [← finalHistory]
                simp
              have outerOracle :
                  (runMachine controller limits actor (fuel + 1) state
                    (.query input next)).oracle =
                    (runMachine controller limits actor fuel nextState
                      (next output)).oracle := by
                simp [runMachine, queryResult]
              refine ⟨(input, output) :: pairs, .query input next output pairs
                result path, ?_, ?_, ?_⟩
              · rw [outerOracle, firstDelta, ← trace, tailDelta]
                rfl
              · rw [outerOracle]
                intro record member
                rw [firstDelta] at member
                simp only [List.mem_cons] at member
                rcases member with rfl | member
                · rfl
                · exact actors record (by rw [tailDelta]; exact member)
              · intro pair member
                simp only [List.mem_cons] at member
                rcases member with rfl | member
                · have atNext := query_oracle_success_fixed_table_has_answer
                    controller limits actor state nextState input output
                      queryResult
                  simpa [runMachine, queryResult] using
                    run_machine_preserves_fixed_table_answer controller limits
                      actor fuel nextState (next output) input output atNext
                · simpa [runMachine, queryResult] using
                    tableAnswers pair member

/-! ## Syntactic schedule inversion -/

theorem query_inputs_for_path
    {Result : Type*} (inputs : List ShaInput)
    (finish : List ShaOutput → Option Result)
    (pairs : List (ShaInput × ShaOutput)) (result : Result)
    (path : MachineQueryPath (queryInputsFor inputs finish) pairs result) :
    ∃ outputs : List ShaOutput,
      outputs.length = inputs.length ∧
      pairs = inputs.zip outputs ∧
      finish outputs = some result := by
  induction inputs generalizing finish pairs with
  | nil =>
      cases finished : finish [] with
      | none =>
          rw [queryInputsFor, finished] at path
          cases path
      | some value =>
          rw [queryInputsFor, finished] at path
          cases path
          exact ⟨[], rfl, rfl, finished⟩
  | cons input rest ih =>
      change MachineQueryPath
        (.query input fun output =>
          queryInputsFor rest fun outputs => finish (output :: outputs))
        pairs result at path
      cases path with
      | query _ _ output tailPairs _ tail =>
          obtain ⟨outputs, length, equalPairs, finished⟩ :=
            ih (fun values => finish (output :: values)) tailPairs tail
          refine ⟨output :: outputs, by simp [length], ?_, finished⟩
          simp [equalPairs]

/-! ## Exact one-action correspondence -/

theorem returned_verifier_action_has_exact_ordered_history
    (controller : AdaptiveController) (limits : OracleLimits)
    (fuel : Nat) (frozenEvidence shared : OracleState)
    (bindings : FixedBindings)
    (core : RuntimeCore) (action : VerifierAction) (reply : VerifierReply)
    (returned : (runVerifierAction controller limits fuel frozenEvidence shared
      bindings core action).halt = .returned reply) :
    ∃ outputs : List ShaOutput,
      outputs.length = (verifierIssuedInputs bindings core action).length ∧
      queryAnswerTrace
          (historySince shared
            (runVerifierAction controller limits fuel frozenEvidence shared
              bindings core action).oracle) =
        (verifierIssuedInputs bindings core action).zip outputs ∧
      replyFromVerifierOutputs frozenEvidence bindings core action outputs =
        some reply ∧
      (∀ record ∈ historySince shared
          (runVerifierAction controller limits fuel frozenEvidence shared
            bindings core action).oracle,
        record.actor = .verifier) ∧
      ∀ pair ∈ (verifierIssuedInputs bindings core action).zip outputs,
        tableLookup
            (fixedTableOfOracleState
              (runVerifierAction controller limits fuel frozenEvidence shared
                bindings core action).oracle)
            pair.1 = some pair.2 := by
  have path := run_machine_returned_has_exact_query_path
    controller limits .verifier fuel shared
      (verifierActionProgram frozenEvidence bindings core action) reply returned
  obtain ⟨pairs, machinePath, history, actors, tableAnswers⟩ := path
  obtain ⟨outputs, length, pairEquality, finished⟩ :=
    query_inputs_for_path (verifierIssuedInputs bindings core action)
      (replyFromVerifierOutputs frozenEvidence bindings core action) pairs reply
        machinePath
  refine ⟨outputs, length, history.trans pairEquality, finished, actors, ?_⟩
  intro pair member
  apply tableAnswers pair
  rw [pairEquality]
  exact member

/-- A successful sequential action run exposes its literal query path.  This
is the exact verifier-call count (`pairs.length`), the exact ordered history,
and final-table reproduction for every issued call.  Historical grinding
probes can contribute no pair because their action program is query-free. -/
theorem returned_verifier_plan_has_exact_ordered_history
    (controller : AdaptiveController) (limits : OracleLimits)
    (fuel : Nat) (frozenEvidence shared : OracleState)
    (bindings : FixedBindings) (core : RuntimeCore)
    (actions : List VerifierAction) (result : VerifierPlanResult)
    (returned :
      (runVerifierPlan controller limits fuel frozenEvidence shared bindings
        core actions).halt = .returned result) :
    ∃ pairs : List (ShaInput × ShaOutput),
      MachineQueryPath
          (verifierPlanProgram frozenEvidence bindings core actions)
          pairs result ∧
      queryAnswerTrace
          (historySince shared
            (runVerifierPlan controller limits fuel frozenEvidence shared
              bindings core actions).oracle) = pairs ∧
      (historySince shared
          (runVerifierPlan controller limits fuel frozenEvidence shared bindings
            core actions).oracle).length = pairs.length ∧
      (∀ record ∈ historySince shared
          (runVerifierPlan controller limits fuel frozenEvidence shared bindings
            core actions).oracle,
        record.actor = .verifier) ∧
      ∀ pair ∈ pairs,
        tableLookup
            (fixedTableOfOracleState
              (runVerifierPlan controller limits fuel frozenEvidence shared
                bindings core actions).oracle)
            pair.1 = some pair.2 := by
  obtain ⟨pairs, path, history, actors, tableAnswers⟩ :=
    run_machine_returned_has_exact_query_path controller limits .verifier fuel
      shared (verifierPlanProgram frozenEvidence bindings core actions) result
        returned
  refine ⟨pairs, path, history, ?_, actors, tableAnswers⟩
  have lengths := congrArg List.length history
  simpa only [runVerifierPlan, queryAnswerTrace, List.length_map] using lengths

theorem returned_full_verifier_plan_has_exact_ordered_history
    (controller : AdaptiveController) (limits : OracleLimits)
    (fuel : Nat) (frozenEvidence shared : OracleState)
    (tape : DeployedFixedTape) (result : VerifierPlanResult)
    (returned :
      (runFullVerifierPlan controller limits fuel frozenEvidence shared tape).halt =
        .returned result) :
    ∃ pairs : List (ShaInput × ShaOutput),
      MachineQueryPath
          (verifierPlanProgram frozenEvidence
            (FixedBindings.ofContext tape.messages.context) initialCore
              (fullPlan tape)) pairs result ∧
      queryAnswerTrace
          (historySince shared
            (runFullVerifierPlan controller limits fuel frozenEvidence shared
              tape).oracle) = pairs ∧
      (historySince shared
          (runFullVerifierPlan controller limits fuel frozenEvidence shared
            tape).oracle).length = pairs.length ∧
      (∀ record ∈ historySince shared
          (runFullVerifierPlan controller limits fuel frozenEvidence shared
            tape).oracle,
        record.actor = .verifier) ∧
      ∀ pair ∈ pairs,
        tableLookup
            (fixedTableOfOracleState
              (runFullVerifierPlan controller limits fuel frozenEvidence shared
                tape).oracle)
            pair.1 = some pair.2 := by
  simpa [runFullVerifierPlan] using
    returned_verifier_plan_has_exact_ordered_history controller limits fuel
      frozenEvidence shared
        (FixedBindings.ofContext tape.messages.context) initialCore
          (fullPlan tape) result returned

theorem returned_squeeze_is_one_atomic_paired_history
    (controller : AdaptiveController) (limits : OracleLimits)
    (fuel : Nat) (frozenEvidence shared : OracleState)
    (bindings : FixedBindings)
    (core : RuntimeCore) (owner : SqueezeOwner) (block : Nat)
    (reply : VerifierReply)
    (returned : (runVerifierAction controller limits fuel frozenEvidence shared
      bindings core (.squeezePair owner block)).halt = .returned reply) :
    ∃ output advance,
      reply = .squeeze output advance ∧
      queryAnswerTrace
          (historySince shared
            (runVerifierAction controller limits fuel frozenEvidence shared
              bindings core (.squeezePair owner block)).oracle) =
        [(bytes core.digest ++ [domSqueeze], output),
         (bytes core.digest ++ [domAdvance], advance)] ∧
      tableLookup
          (fixedTableOfOracleState
            (runVerifierAction controller limits fuel frozenEvidence shared
              bindings core (.squeezePair owner block)).oracle)
          (bytes core.digest ++ [domSqueeze]) = some output ∧
      tableLookup
          (fixedTableOfOracleState
            (runVerifierAction controller limits fuel frozenEvidence shared
              bindings core (.squeezePair owner block)).oracle)
          (bytes core.digest ++ [domAdvance]) = some advance ∧
      bytes core.digest ++ [domSqueeze] ≠
        bytes core.digest ++ [domAdvance] := by
  obtain ⟨outputs, length, history, decoded, actors, tableAnswers⟩ :=
    returned_verifier_action_has_exact_ordered_history controller limits fuel
      frozenEvidence shared bindings core (.squeezePair owner block) reply
        returned
  simp only [verifierIssuedInputs, actionInputs, List.length_cons,
    List.length_nil, OfNat.ofNat, Nat.reduceAdd] at length
  rcases outputs with _ | ⟨output, outputs⟩
  · contradiction
  rcases outputs with _ | ⟨advance, outputs⟩
  · contradiction
  rcases outputs with _ | ⟨extra, outputs⟩
  · simp only [replyFromVerifierOutputs, Option.some.injEq,
      VerifierReply.squeeze.injEq] at decoded
    rcases decoded with ⟨rfl, rfl⟩
    have outputStored := tableAnswers
      (bytes core.digest ++ [domSqueeze], output) (by
        simp [verifierIssuedInputs, actionInputs])
    have advanceStored := tableAnswers
      (bytes core.digest ++ [domAdvance], advance) (by
        simp [verifierIssuedInputs, actionInputs])
    exact ⟨output, advance, rfl, history, outputStored, advanceStored,
      squeeze_output_and_advance_inputs_are_distinct core.digest⟩
  · simp at length

#print axioms adversary_history_issues_no_verifier_query
#print axioms selected_work_issues_exactly_one_verifier_query
#print axioms three_selected_work_checks_are_three_verifier_calls
#print axioms shared_runner_full256_verifier_call_cap
#print axioms frozen_adversary_evidence_has_q1_record
#print axioms adversary_history_program_uses_only_frozen_q1_evidence
#print axioms selected_work_program_issues_the_exact_deployed_query
#print axioms adversary_history_run_makes_zero_verifier_calls
#print axioms returned_adversary_history_reply_has_frozen_q1_evidence
#print axioms query_oracle_success_appends_one_record
#print axioms fixed_table_lookup_eq_lookup_entry_output
#print axioms query_oracle_success_extends_fixed_table
#print axioms query_oracle_success_preserves_fixed_table_answer
#print axioms query_oracle_success_fixed_table_has_answer
#print axioms run_machine_preserves_fixed_table_answer
#print axioms run_machine_returned_has_exact_query_path
#print axioms query_inputs_for_path
#print axioms returned_verifier_action_has_exact_ordered_history
#print axioms returned_verifier_plan_has_exact_ordered_history
#print axioms returned_full_verifier_plan_has_exact_ordered_history
#print axioms returned_squeeze_is_one_atomic_paired_history

end AspisK1.V7Tag73SharedOracleVerifierRunner
