import AspisFormal.K1.V7Tag73ReplayWorkEvidenceBridge
import AspisFormal.K1.V7Tag73SequentialOracleRuns
import AspisFormal.K1.V7Tag73AtomicPairFork

/-!
# Cumulative oracle history for recursive Tag-73 replays

This module contains only reusable facts about the operational oracle
machine.  It is deliberately independent of any same-tape source, returned
proof, acceptance event, or extraction conclusion.

The initial `OracleState` may already contain arbitrary query and programming
history.  Queries performed by `runPrefix` and `runMachine` append their
actor-labelled records chronologically and leave the existing programming
ledger unchanged.  Successful explicit programming extends that ledger.  The
node-local prover-history view below is exactly the chronological suffix after
the supplied initial state, filtered to the two genuine prover actors:
`adversary` and `extractorReplay`.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73CumulativeReplayHistory

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73AtomicPairFork
open AspisK1.V7Tag73AtomicPairReplay
open AspisK1.V7Tag73SharedOracleVerifierRunner
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73ReplayWorkEvidenceBridge
open AspisK1.V7Tag73SequentialOracleRuns

noncomputable section

/-! ## Programming history -/

theorem query_oracle_success_preserves_cumulative_programming_history
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (state nextState : OracleState)
    (input : ShaInput) (output : ShaOutput)
    (success : queryOracle controller limits actor state input =
      .ok (output, nextState)) :
    nextState.programmingHistory = state.programmingHistory := by
  exact query_oracle_success_preserves_programming_history controller limits
    actor state nextState input output success

/-- Prefix execution may append query records, but it cannot add, remove, or
reorder programming records already present in an arbitrary initial state. -/
theorem run_prefix_preserves_programming_history
    {Result : Type*} (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (program : OracleMachine Result) :
    (runPrefix controller limits actor fuel state
      program).oracle.programmingHistory = state.programmingHistory := by
  induction fuel generalizing state program with
  | zero => rfl
  | succ fuel ih =>
      cases program with
      | pure result => rfl
      | abort reason => rfl
      | query input next =>
          cases queried : queryOracle controller limits actor state input with
          | error reason => simp [runPrefix, queried]
          | ok pair =>
              rcases pair with ⟨output, nextState⟩
              have queryPreserves :=
                query_oracle_success_preserves_cumulative_programming_history
                  controller limits actor state nextState input output queried
              have tailPreserves := ih nextState (next output)
              simpa only [runPrefix, queried] using
                tailPreserves.trans queryPreserves

/-- A complete fuel-bounded run likewise retains the cumulative programming
ledger with which it began. -/
theorem run_machine_preserves_cumulative_programming_history
    {Result : Type*} (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (program : OracleMachine Result) :
    (runMachine controller limits actor fuel state
      program).oracle.programmingHistory = state.programmingHistory := by
  exact run_machine_preserves_programming_history controller limits actor fuel
    state program

/-- One successful programming call appends its exact actor-labelled record
to the existing cumulative ledger. -/
theorem program_oracle_success_appends_exact_programming_record
    (limits : OracleLimits) (actor : QueryActor)
    (state nextState : OracleState) (programming : Programming)
    (success : programOracle limits actor state programming = .ok nextState) :
    nextState.programmingHistory = state.programmingHistory ++
      [({ input := programming.input
          output := programming.output
          actor := actor } : ProgrammingRecord)] := by
  exact (program_oracle_success_exact limits actor state nextState programming
    success).2.1

theorem program_oracle_success_extends_programming_history
    (limits : OracleLimits) (actor : QueryActor)
    (state nextState : OracleState) (programming : Programming)
    (success : programOracle limits actor state programming = .ok nextState) :
    state.programmingHistory <+: nextState.programmingHistory := by
  rw [program_oracle_success_appends_exact_programming_record limits actor
    state nextState programming success]
  exact List.prefix_append _ _

/-- The common recursive-edge shape: execute a prefix, append an explicit
programming delta, then run a continuation.  The final ledger is exactly the
initial cumulative ledger followed by that delta. -/
theorem prefix_programming_then_run_retains_exact_extension
    {PrefixResult Result : Type*}
    (prefixController : AdaptiveController) (prefixLimits : OracleLimits)
    (prefixActor : QueryActor) (prefixFuel : Nat) (initial : OracleState)
    (prefixProgram : OracleMachine PrefixResult)
    (programmed : OracleState) (added : List ProgrammingRecord)
    (programmedExact : programmed.programmingHistory =
      (runPrefix prefixController prefixLimits prefixActor prefixFuel initial
        prefixProgram).oracle.programmingHistory ++ added)
    (continuationController : AdaptiveController)
    (continuationLimits : OracleLimits) (continuationActor : QueryActor)
    (continuationFuel : Nat) (continuation : OracleMachine Result) :
    (runMachine continuationController continuationLimits continuationActor
      continuationFuel programmed continuation).oracle.programmingHistory =
        initial.programmingHistory ++ added := by
  rw [run_machine_preserves_cumulative_programming_history]
  rw [programmedExact, run_prefix_preserves_programming_history]

/-! ## Exact chronological suffixes -/

theorem history_since_eq_of_exact_append
    (initial final : OracleState) (appended : List QueryRecord)
    (exactHistory : final.history = initial.history ++ appended) :
    historySince initial final = appended := by
  unfold historySince
  rw [exactHistory]
  simp

theorem history_eq_initial_append_history_since
    (initial final : OracleState)
    (historyPrefix : initial.history <+: final.history) :
    final.history = initial.history ++ historySince initial final := by
  simpa only [historySince] using List.prefix_append_drop historyPrefix

/-- `runPrefix` exposes the literal actor-labelled records appended after an
arbitrary cumulative initial history. -/
theorem run_prefix_appended_history_exact
    {Result : Type*} (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (program : OracleMachine Result) :
    ∃ appended : List QueryRecord,
      (runPrefix controller limits actor fuel state program).oracle.history =
          state.history ++ appended ∧
        ∀ record ∈ appended, record.actor = actor := by
  induction fuel generalizing state program with
  | zero =>
      exact ⟨[], by simp [runPrefix], by simp⟩
  | succ fuel ih =>
      cases program with
      | pure result => exact ⟨[], by simp [runPrefix], by simp⟩
      | abort reason => exact ⟨[], by simp [runPrefix], by simp⟩
      | query input next =>
          cases queried : queryOracle controller limits actor state input with
          | error reason => exact ⟨[], by simp [runPrefix, queried], by simp⟩
          | ok pair =>
              rcases pair with ⟨output, nextState⟩
              obtain ⟨headRecord, queryHistory, headActor⟩ :=
                query_oracle_success_appends_actor_record controller limits
                  actor state nextState input output queried
              obtain ⟨tail, tailHistory, tailActors⟩ :=
                ih nextState (next output)
              refine ⟨headRecord :: tail, ?_, ?_⟩
              · have combined :
                    (runPrefix controller limits actor fuel nextState
                      (next output)).oracle.history =
                        state.history ++ (headRecord :: tail) := by
                  calc
                    (runPrefix controller limits actor fuel nextState
                        (next output)).oracle.history =
                        nextState.history ++ tail := tailHistory
                    _ = (state.history ++ [headRecord]) ++ tail := by
                      rw [queryHistory]
                    _ = state.history ++ (headRecord :: tail) := by simp
                simpa only [runPrefix, queried] using combined
              · intro record member
                simp only [List.mem_cons] at member
                rcases member with rfl | member
                · exact headActor
                · exact tailActors record member

/-- The corresponding complete-run decomposition, re-exported with a name
that emphasizes that the initial state may already be cumulative. -/
theorem run_machine_appended_history_exact
    {Result : Type*} (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (program : OracleMachine Result) :
    ∃ appended : List QueryRecord,
      (runMachine controller limits actor fuel state program).oracle.history =
          state.history ++ appended ∧
        ∀ record ∈ appended, record.actor = actor := by
  exact run_machine_appended_history_has_actor controller limits actor fuel
    state program

theorem run_prefix_history_since_has_actor
    {Result : Type*} (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (program : OracleMachine Result) :
    ∀ record ∈ historySince state
        (runPrefix controller limits actor fuel state program).oracle,
      record.actor = actor := by
  obtain ⟨appended, exactHistory, actors⟩ :=
    run_prefix_appended_history_exact controller limits actor fuel state program
  have exactSince : historySince state
      (runPrefix controller limits actor fuel state program).oracle =
        appended :=
    history_since_eq_of_exact_append state _ appended exactHistory
  intro record member
  apply actors record
  rw [← exactSince]
  exact member

theorem run_machine_history_since_is_chronological_suffix
    {Result : Type*} (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (program : OracleMachine Result) :
    let run := runMachine controller limits actor fuel state program
    run.oracle.history = state.history ++ historySince state run.oracle ∧
      (∀ record ∈ historySince state run.oracle, record.actor = actor) := by
  let run := runMachine controller limits actor fuel state program
  have historyPrefix := postfork_run_history_is_preserved controller limits actor fuel
    state program
  exact ⟨history_eq_initial_append_history_since state run.oracle historyPrefix,
    run_machine_history_since_has_actor controller limits actor fuel state
      program⟩

theorem run_prefix_history_since_is_chronological_suffix
    {Result : Type*} (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (program : OracleMachine Result) :
    let run := runPrefix controller limits actor fuel state program
    run.oracle.history = state.history ++ historySince state run.oracle ∧
      (∀ record ∈ historySince state run.oracle, record.actor = actor) := by
  let run := runPrefix controller limits actor fuel state program
  have historyPrefix := prefix_run_history_is_preserved controller limits actor fuel
    state program
  exact ⟨history_eq_initial_append_history_since state run.oracle historyPrefix,
    run_prefix_history_since_has_actor controller limits actor fuel state
      program⟩

/-! ## Node-local mixed prover history and occurrence scan -/

theorem is_prover_history_actor_iff (actor : QueryActor) :
    IsProverHistoryActor actor ↔
      actor = .adversary ∨ actor = .extractorReplay := by
  cases actor <;> simp [IsProverHistoryActor]

/-- Chronological calls made after `initial`, retaining original/replay prover
actors while excluding simulator and verifier calls. -/
def proverHistorySince (initial final : OracleState) : List QueryRecord :=
  (historySince initial final).filter fun record =>
    decide (IsProverHistoryActor record.actor)

theorem mem_prover_history_since_iff
    (initial final : OracleState) (record : QueryRecord) :
    record ∈ proverHistorySince initial final ↔
      record ∈ historySince initial final ∧
        (record.actor = .adversary ∨
          record.actor = .extractorReplay) := by
  simp [proverHistorySince, is_prover_history_actor_iff]

private theorem filter_prover_history_eq_self
    (records : List QueryRecord)
    (proverActors : ∀ record ∈ records,
      IsProverHistoryActor record.actor) :
    records.filter (fun record =>
      decide (IsProverHistoryActor record.actor)) = records := by
  induction records with
  | nil => rfl
  | cons head tail ih =>
      have headActor : IsProverHistoryActor head.actor :=
        proverActors head (by simp)
      have tailActors : ∀ record ∈ tail,
          IsProverHistoryActor record.actor := by
        intro record member
        exact proverActors record (by simp [member])
      simp [headActor, ih tailActors]

theorem prover_history_since_run_prefix_eq_history_since
    {Result : Type*} (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (proverActor : IsProverHistoryActor actor)
    (fuel : Nat) (state : OracleState) (program : OracleMachine Result) :
    proverHistorySince state
        (runPrefix controller limits actor fuel state program).oracle =
      historySince state
        (runPrefix controller limits actor fuel state program).oracle := by
  unfold proverHistorySince
  apply filter_prover_history_eq_self
  intro record member
  have exactActor := run_prefix_history_since_has_actor controller limits actor
    fuel state program record member
  rw [exactActor]
  exact proverActor

theorem prover_history_since_run_machine_eq_history_since
    {Result : Type*} (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (proverActor : IsProverHistoryActor actor)
    (fuel : Nat) (state : OracleState) (program : OracleMachine Result) :
    proverHistorySince state
        (runMachine controller limits actor fuel state program).oracle =
      historySince state
        (runMachine controller limits actor fuel state program).oracle := by
  unfold proverHistorySince
  apply filter_prover_history_eq_self
  intro record member
  have exactActor := run_machine_history_since_has_actor controller limits actor
    fuel state program record member
  rw [exactActor]
  exact proverActor

/-- Scan only the chronological node-local prover suffix for the first query
to either half of an atomic squeeze. -/
def firstEitherProverInputOccurrenceSince
    (outputInput advanceInput : ShaInput) (initial final : OracleState) :
    Option PairOccurrenceSplit :=
  firstEitherInputOccurrence outputInput advanceInput
    (proverHistorySince initial final)

theorem first_either_prover_input_occurrence_since_spec
    (outputInput advanceInput : ShaInput) (initial final : OracleState)
    (occurrence : PairOccurrenceSplit)
    (found : firstEitherProverInputOccurrenceSince outputInput advanceInput
      initial final = some occurrence) :
    proverHistorySince initial final =
        occurrence.before ++ occurrence.chosen :: occurrence.after ∧
      (∀ prior ∈ occurrence.before,
        prior.input ≠ outputInput ∧ prior.input ≠ advanceInput) ∧
      (occurrence.chosen.input = outputInput ∨
        occurrence.chosen.input = advanceInput) ∧
      (occurrence.chosen.actor = .adversary ∨
        occurrence.chosen.actor = .extractorReplay) := by
  have spec := first_either_input_occurrence_spec outputInput advanceInput
    (proverHistorySince initial final) occurrence
      (by simpa [firstEitherProverInputOccurrenceSince] using found)
  have chosenMember : occurrence.chosen ∈
      proverHistorySince initial final := by
    rw [spec.1]
    simp
  have chosenActor :=
    (mem_prover_history_since_iff initial final occurrence.chosen).mp
      chosenMember
  exact ⟨spec.1, spec.2.1, spec.2.2, chosenActor.2⟩

theorem first_either_prover_input_occurrence_in_run_has_exact_actor
    {Result : Type*} (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (proverActor : IsProverHistoryActor actor)
    (fuel : Nat) (state : OracleState) (program : OracleMachine Result)
    (outputInput advanceInput : ShaInput) (occurrence : PairOccurrenceSplit)
    (found : firstEitherProverInputOccurrenceSince outputInput advanceInput
      state (runMachine controller limits actor fuel state program).oracle =
        some occurrence) :
    historySince state
        (runMachine controller limits actor fuel state program).oracle =
          occurrence.before ++ occurrence.chosen :: occurrence.after ∧
      (∀ prior ∈ occurrence.before,
        prior.input ≠ outputInput ∧ prior.input ≠ advanceInput) ∧
      (occurrence.chosen.input = outputInput ∨
        occurrence.chosen.input = advanceInput) ∧
      occurrence.chosen.actor = actor := by
  have filtered := prover_history_since_run_machine_eq_history_since controller
    limits actor proverActor fuel state program
  have spec := first_either_prover_input_occurrence_since_spec outputInput
    advanceInput state
      (runMachine controller limits actor fuel state program).oracle occurrence
        found
  have chosenMember : occurrence.chosen ∈ historySince state
      (runMachine controller limits actor fuel state program).oracle := by
    rw [← filtered, spec.1]
    simp
  have decomposition : historySince state
      (runMachine controller limits actor fuel state program).oracle =
        occurrence.before ++ occurrence.chosen :: occurrence.after := by
    rw [← filtered]
    exact spec.1
  exact ⟨decomposition, spec.2.1, spec.2.2.1,
    run_machine_history_since_has_actor controller limits actor fuel state
      program occurrence.chosen chosenMember⟩

/-! ## Exact prefix-pause inversion

The following lemmas invert a *real normally returned execution*.  They do
not posit a checkpoint or a restore function: the replay controller is built
from the literal records appended by that execution, and `runPrefix` executes
the original program from the supplied cumulative state.
-/

/-- If one controller successfully answered a query, then another controller
which supplies that same answer at the same state produces the identical
oracle transition.  Cached answers are controller-independent; the supplied
answer is used only in the genuinely fresh branch. -/
private theorem query_oracle_success_with_matching_controller
    (controller replayController : AdaptiveController)
    (limits : OracleLimits) (actor : QueryActor)
    (state nextState : OracleState) (input : ShaInput) (output : ShaOutput)
    (success : queryOracle controller limits actor state input =
      .ok (output, nextState))
    (replayAnswer : replayController state.history input = .answer output) :
    queryOracle replayController limits actor state input =
      .ok (output, nextState) := by
  unfold queryOracle at success ⊢
  by_cases totalBlocked : state.totalCalls ≥ limits.totalCalls
  · simp [totalBlocked] at success
  · simp only [totalBlocked, if_false] at success ⊢
    cases found : lookupEntry state input with
    | some entry =>
        simpa only [found] using success
    | none =>
        simp only [found] at success ⊢
        by_cases freshBlocked : state.freshCalls ≥ limits.freshCalls
        · simp [freshBlocked] at success
        · simp only [freshBlocked, if_false] at success ⊢
          cases original : controller state.history input with
          | refuse => simp [original] at success
          | answer answer =>
              rw [original] at success
              simp only [Except.ok.injEq, Prod.mk.injEq] at success
              rcases success with ⟨rfl, rfl⟩
              rw [replayAnswer]

/-- A successful query followed by any execution whose final history extends
the query state contributes exactly one leading record to the history suffix.
This is the one-step chronological fact used by the inversion induction. -/
private theorem query_success_history_since_cons_of_final_prefix
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (state nextState finalState : OracleState)
    (input : ShaInput) (output : ShaOutput)
    (success : queryOracle controller limits actor state input =
      .ok (output, nextState))
    (finalPrefix : nextState.history <+: finalState.history) :
    ∃ origin : AnswerOrigin,
      historySince state finalState =
        ({ input := input, output := output, actor := actor, origin := origin } : QueryRecord) ::
          historySince nextState finalState := by
  obtain ⟨origin, nextHistory⟩ :=
    query_oracle_success_appends_one_record controller limits actor state
      nextState input output success
  rcases finalPrefix with ⟨suffix, finalHistory⟩
  refine ⟨origin, ?_⟩
  unfold historySince
  rw [← finalHistory, nextHistory]
  simp [List.append_assoc]

/-- At the state reached after `consumed`, the fixed recorded-prefix
controller selects the literal next record. -/
private theorem recorded_prefix_controller_answers_next
    (initialHistoryLength : Nat) (recorded consumed tail : List QueryRecord)
    (nextRecord : QueryRecord) (state : OracleState)
    (recordedExact : recorded = consumed ++ nextRecord :: tail)
    (stateLength : state.history.length =
      initialHistoryLength + consumed.length) :
    recordedPrefixController initialHistoryLength recorded state.history
      nextRecord.input = .answer nextRecord.output := by
  unfold recordedPrefixController
  simp [stateLength, recordedExact]

/-- Internal strengthened induction.  `consumed` records how far the same
fixed controller has progressed, so the theorem applies recursively without
replacing that controller by a convenient new one. -/
private theorem returned_run_replays_recorded_prefix_to_pause_aux
    {Result : Type*}
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (initialHistoryLength : Nat)
    (recorded consumed remaining : List QueryRecord)
    (state : OracleState) (fuel : Nat) (program : OracleMachine Result)
    (result : Result) (chosen : QueryRecord) (after : List QueryRecord)
    (recordedExact : recorded = consumed ++ remaining)
    (stateLength : state.history.length =
      initialHistoryLength + consumed.length)
    (returned : (runMachine controller limits actor fuel state program).halt =
      .returned result)
    (decomposition :
      historySince state
          (runMachine controller limits actor fuel state program).oracle =
        remaining ++ chosen :: after) :
    let replay := runPrefix
      (recordedPrefixController initialHistoryLength recorded)
      limits actor remaining.length state program
    ∃ pendingContinuation,
      replay.halt = .paused (.query chosen.input pendingContinuation) ∧
      queryAnswerTrace (historySince state replay.oracle) =
        queryAnswerTrace remaining ∧
      (runMachine controller limits actor (fuel - remaining.length)
        replay.oracle (.query chosen.input pendingContinuation)).halt =
          .returned result := by
  induction remaining generalizing consumed state fuel program with
  | nil =>
      cases fuel with
      | zero =>
          cases program with
          | pure value => simp [runMachine, historySince] at decomposition
          | abort reason => simp [runMachine] at returned
          | query input next => simp [runMachine] at returned
      | succ fuel =>
          cases program with
          | pure value => simp [runMachine, historySince] at decomposition
          | abort reason => simp [runMachine] at returned
          | query input next =>
              cases queried : queryOracle controller limits actor state input with
              | error reason => simp [runMachine, queried] at returned
              | ok pair =>
                  rcases pair with ⟨output, nextState⟩
                  let tailRun := runMachine controller limits actor fuel
                    nextState (next output)
                  have tailReturned : tailRun.halt = .returned result := by
                    simpa [tailRun, runMachine, queried] using returned
                  have outerOracle :
                      (runMachine controller limits actor (fuel + 1) state
                        (.query input next)).oracle = tailRun.oracle := by
                    simp [tailRun, runMachine, queried]
                  have tailPrefix : nextState.history <+: tailRun.oracle.history :=
                    postfork_run_history_is_preserved controller limits actor
                      fuel nextState (next output)
                  obtain ⟨origin, firstDelta⟩ :=
                    query_success_history_since_cons_of_final_prefix controller
                      limits actor state nextState tailRun.oracle input output
                        queried tailPrefix
                  have exactDecomposition :
                      ({ input := input, output := output, actor := actor, origin := origin } : QueryRecord) ::
                          historySince nextState tailRun.oracle =
                        chosen :: after := by
                    simpa only [List.nil_append, outerOracle, firstDelta] using
                      decomposition
                  have recordEquality :
                      ({ input := input, output := output, actor := actor, origin := origin } : QueryRecord) = chosen :=
                    (List.cons.inj exactDecomposition).1
                  have inputEquality : input = chosen.input :=
                    congrArg QueryRecord.input recordEquality
                  refine ⟨next, ?_, ?_, ?_⟩
                  · simp [runPrefix, inputEquality]
                  · simp [runPrefix, historySince, queryAnswerTrace]
                  · simpa [runPrefix, inputEquality] using returned
  | cons head tail inductionHypothesis =>
      cases fuel with
      | zero =>
          cases program with
          | pure value => simp [runMachine, historySince] at decomposition
          | abort reason => simp [runMachine] at returned
          | query input next => simp [runMachine] at returned
      | succ fuel =>
          cases program with
          | pure value => simp [runMachine, historySince] at decomposition
          | abort reason => simp [runMachine] at returned
          | query input next =>
              cases queried : queryOracle controller limits actor state input with
              | error reason => simp [runMachine, queried] at returned
              | ok pair =>
                  rcases pair with ⟨output, nextState⟩
                  let tailRun := runMachine controller limits actor fuel
                    nextState (next output)
                  have tailReturned : tailRun.halt = .returned result := by
                    simpa [tailRun, runMachine, queried] using returned
                  have outerOracle :
                      (runMachine controller limits actor (fuel + 1) state
                        (.query input next)).oracle = tailRun.oracle := by
                    simp [tailRun, runMachine, queried]
                  have tailPrefix : nextState.history <+: tailRun.oracle.history :=
                    postfork_run_history_is_preserved controller limits actor
                      fuel nextState (next output)
                  obtain ⟨origin, firstDelta⟩ :=
                    query_success_history_since_cons_of_final_prefix controller
                      limits actor state nextState tailRun.oracle input output
                        queried tailPrefix
                  let firstRecord : QueryRecord :=
                    { input := input
                      output := output
                      actor := actor
                      origin := origin }
                  have exactDecomposition :
                      firstRecord :: historySince nextState tailRun.oracle =
                        head :: (tail ++ chosen :: after) := by
                    simpa only [List.cons_append, outerOracle, firstDelta,
                      firstRecord] using decomposition
                  have firstRecordEquality : firstRecord = head :=
                    (List.cons.inj exactDecomposition).1
                  have tailDecomposition :
                      historySince nextState tailRun.oracle =
                        tail ++ chosen :: after :=
                    (List.cons.inj exactDecomposition).2
                  have replayAnswer :
                      recordedPrefixController initialHistoryLength recorded
                          state.history input = .answer output := by
                    have selected := recorded_prefix_controller_answers_next
                      initialHistoryLength recorded consumed tail head state
                        recordedExact stateLength
                    simpa [firstRecord, ← firstRecordEquality] using selected
                  have replayQueried :
                      queryOracle
                          (recordedPrefixController initialHistoryLength recorded)
                          limits actor state input = .ok (output, nextState) :=
                    query_oracle_success_with_matching_controller controller
                      (recordedPrefixController initialHistoryLength recorded)
                      limits actor state nextState input output queried
                        replayAnswer
                  obtain ⟨_origin, nextHistory⟩ :=
                    query_oracle_success_appends_one_record controller limits
                      actor state nextState input output queried
                  have recursiveRecorded :
                      recorded = (consumed ++ [head]) ++ tail := by
                    simpa only [List.append_assoc, List.singleton_append] using
                      recordedExact
                  have nextLength : nextState.history.length =
                      initialHistoryLength + (consumed ++ [head]).length := by
                    rw [nextHistory]
                    simp only [List.length_append, List.length_singleton]
                    rw [stateLength]
                    omega
                  obtain ⟨pendingContinuation, tailPaused, tailTrace,
                      tailResumes⟩ :=
                    inductionHypothesis (consumed ++ [head]) nextState fuel
                      (next output) recursiveRecorded nextLength tailReturned
                        tailDecomposition
                  let replayController :=
                    recordedPrefixController initialHistoryLength recorded
                  let replayTail := runPrefix replayController limits actor
                    tail.length nextState (next output)
                  have replayTailTrace :
                      queryAnswerTrace
                          (historySince nextState replayTail.oracle) =
                        queryAnswerTrace tail := by
                    simpa [replayTail, replayController] using tailTrace
                  have replayTailPrefix :
                      nextState.history <+: replayTail.oracle.history :=
                    prefix_run_history_is_preserved replayController limits
                      actor tail.length nextState (next output)
                  obtain ⟨replayOrigin, replayDelta⟩ :=
                    query_success_history_since_cons_of_final_prefix
                      replayController limits actor state nextState
                        replayTail.oracle input output
                        (by simpa [replayController] using replayQueried)
                        replayTailPrefix
                  have replayOuterOracle :
                      (runPrefix replayController limits actor
                        (head :: tail).length state (.query input next)).oracle =
                          replayTail.oracle := by
                    simp [replayController, replayTail, runPrefix,
                      replayQueried]
                  refine ⟨pendingContinuation, ?_, ?_, ?_⟩
                  · simpa [replayController, replayTail, runPrefix,
                      replayQueried] using tailPaused
                  · rw [replayOuterOracle, replayDelta]
                    change (input, output) :: queryAnswerTrace
                        (historySince nextState replayTail.oracle) =
                      (head.input, head.output) :: queryAnswerTrace tail
                    rw [replayTailTrace]
                    simpa [firstRecord] using congrArg
                      (fun record : QueryRecord => (record.input, record.output))
                      firstRecordEquality
                  · simpa [replayController, replayTail, runPrefix,
                      replayQueried] using tailResumes

/-- A normal returned run and an exact chronological occurrence split are
sufficient to recover the actual pending query by same-state, same-program
prefix replay.  Empty prefixes are legal and pause at the program start. -/
theorem returned_run_first_occurrence_replays_to_exact_pause
    {Result : Type*}
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (program : OracleMachine Result) (result : Result)
    (occurrence : PairOccurrenceSplit)
    (returned : (runMachine controller limits actor fuel state program).halt =
      .returned result)
    (decomposition :
      historySince state
          (runMachine controller limits actor fuel state program).oracle =
        occurrence.before ++ occurrence.chosen :: occurrence.after) :
    let replay := runPrefix
      (recordedPrefixController state.history.length occurrence.before)
      limits actor occurrence.before.length state program
    ∃ residual pendingInput pendingContinuation,
      replay.halt = .paused residual ∧
      residual = .query pendingInput pendingContinuation ∧
      pendingInput = occurrence.chosen.input ∧
      queryAnswerTrace (historySince state replay.oracle) =
        queryAnswerTrace occurrence.before := by
  obtain ⟨pendingContinuation, paused, trace, _resumes⟩ :=
    returned_run_replays_recorded_prefix_to_pause_aux controller limits actor
      state.history.length occurrence.before [] occurrence.before state fuel
      program result occurrence.chosen occurrence.after (by simp) (by simp)
      returned decomposition
  exact ⟨.query occurrence.chosen.input pendingContinuation,
    occurrence.chosen.input, pendingContinuation, paused, rfl, rfl, trace⟩

/-- The prefix inversion also retains an exact executable resumption fact.
Running the original controller from the reconstructed pause, with exactly
the unused fuel, returns the original result. -/
theorem returned_run_first_occurrence_replays_to_exact_pause_and_resume
    {Result : Type*}
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (program : OracleMachine Result) (result : Result)
    (occurrence : PairOccurrenceSplit)
    (returned : (runMachine controller limits actor fuel state program).halt =
      .returned result)
    (decomposition :
      historySince state
          (runMachine controller limits actor fuel state program).oracle =
        occurrence.before ++ occurrence.chosen :: occurrence.after) :
    let replay := runPrefix
      (recordedPrefixController state.history.length occurrence.before)
      limits actor occurrence.before.length state program
    ∃ pendingContinuation,
      replay.halt =
        .paused (.query occurrence.chosen.input pendingContinuation) ∧
      queryAnswerTrace (historySince state replay.oracle) =
        queryAnswerTrace occurrence.before ∧
      (runMachine controller limits actor
        (fuel - occurrence.before.length) replay.oracle
        (.query occurrence.chosen.input pendingContinuation)).halt =
          .returned result := by
  exact returned_run_replays_recorded_prefix_to_pause_aux controller limits
    actor state.history.length occurrence.before [] occurrence.before state
    fuel program result occurrence.chosen occurrence.after (by simp) (by simp)
    returned decomposition

/-! ## Segmented root-to-node histories

A recursive fork tree cannot in general discard the query records preceding
the current continuation entry: a later child may fork at one of those earlier
queries.  The following data type retains each *actual* cumulative execution
segment, together with its exact `historySince` witness.  Adjacent segments
need agree only on query history; programming between segments may change the
table and programming ledger while leaving query history untouched.
-/

structure ActualProverHistorySegment where
  entryOracle : OracleState
  finalOracle : OracleState
  historyPrefix : entryOracle.history <+: finalOracle.history
  records : List QueryRecord
  recordsExact : records = historySince entryOracle finalOracle
  proverActors : ∀ record ∈ records,
    record.actor = .adversary ∨ record.actor = .extractorReplay

def HistoryLinkedSegments : List ActualProverHistorySegment → Prop
  | [] => True
  | [_] => True
  | first :: second :: rest =>
      first.finalOracle.history = second.entryOracle.history ∧
        HistoryLinkedSegments (second :: rest)

structure SegmentedRootToNodeHistory where
  segments : List ActualProverHistorySegment
  linked : HistoryLinkedSegments segments

def flattenSegmentRecords
    (segments : List ActualProverHistorySegment) : List QueryRecord :=
  segments.flatMap ActualProverHistorySegment.records

def SegmentedRootToNodeHistory.records
    (path : SegmentedRootToNodeHistory) : List QueryRecord :=
  flattenSegmentRecords path.segments

theorem actual_segment_records_eq_prover_history_since
    (segment : ActualProverHistorySegment) :
    segment.records =
      proverHistorySince segment.entryOracle segment.finalOracle := by
  unfold proverHistorySince
  rw [← segment.recordsExact]
  symm
  apply filter_prover_history_eq_self
  intro record member
  rw [is_prover_history_actor_iff]
  exact segment.proverActors record member

theorem flatten_segment_records_are_prover_history
    (segments : List ActualProverHistorySegment) :
    ∀ record ∈ flattenSegmentRecords segments,
      record.actor = .adversary ∨ record.actor = .extractorReplay := by
  intro record member
  rw [flattenSegmentRecords, List.mem_flatMap] at member
  obtain ⟨segment, segmentMember, recordMember⟩ := member
  exact segment.proverActors record recordMember

/-- The executable scan returns both the zero-based segment number and the
ordinary local split inside that segment. -/
structure SegmentedPairOccurrence where
  segmentIndex : Nat
  withinSegment : PairOccurrenceSplit

def firstEitherInputOccurrenceInSegments
    (outputInput advanceInput : ShaInput) :
    List ActualProverHistorySegment → Option SegmentedPairOccurrence
  | [] => none
  | segment :: rest =>
      match firstEitherInputOccurrence outputInput advanceInput segment.records with
      | some localOccurrence =>
          some { segmentIndex := 0, withinSegment := localOccurrence }
      | none =>
          match firstEitherInputOccurrenceInSegments outputInput advanceInput
              rest with
          | none => none
          | some location => some
              { segmentIndex := location.segmentIndex + 1
                withinSegment := location.withinSegment }

def firstEitherInputOccurrenceInRootPath
    (outputInput advanceInput : ShaInput)
    (path : SegmentedRootToNodeHistory) : Option SegmentedPairOccurrence :=
  firstEitherInputOccurrenceInSegments outputInput advanceInput path.segments

/-- Successful segmented search identifies a literal segment decomposition,
the exact local first occurrence, and the absence of either input from every
earlier segment. -/
theorem first_either_input_occurrence_in_segments_spec
    (outputInput advanceInput : ShaInput)
    (segments : List ActualProverHistorySegment)
    (location : SegmentedPairOccurrence)
    (found : firstEitherInputOccurrenceInSegments outputInput advanceInput
      segments = some location) :
    ∃ earlier current later,
      segments = earlier ++ current :: later ∧
      earlier.length = location.segmentIndex ∧
      firstEitherInputOccurrence outputInput advanceInput current.records =
        some location.withinSegment ∧
      ∀ segment ∈ earlier,
        firstEitherInputOccurrence outputInput advanceInput segment.records =
          none := by
  induction segments generalizing location with
  | nil => simp [firstEitherInputOccurrenceInSegments] at found
  | cons segment rest inductionHypothesis =>
      cases localFound : firstEitherInputOccurrence outputInput advanceInput
          segment.records with
      | some localOccurrence =>
          simp only [firstEitherInputOccurrenceInSegments, localFound,
            Option.some.injEq] at found
          cases found
          exact ⟨[], segment, rest, rfl, rfl, localFound, by simp⟩
      | none =>
          cases recursive : firstEitherInputOccurrenceInSegments outputInput
              advanceInput rest with
          | none =>
              simp [firstEitherInputOccurrenceInSegments, localFound,
                recursive] at found
          | some tailLocation =>
              simp only [firstEitherInputOccurrenceInSegments, localFound,
                recursive, Option.some.injEq] at found
              cases found
              obtain ⟨earlier, current, later, segmentsExact, indexExact,
                  currentFound, earlierNone⟩ :=
                inductionHypothesis tailLocation recursive
              refine ⟨segment :: earlier, current, later, ?_, ?_,
                currentFound, ?_⟩
              · simp [segmentsExact]
              · simp [indexExact]
              · intro candidate member
                simp only [List.mem_cons] at member
                rcases member with rfl | member
                · exact localFound
                · exact earlierNone candidate member

/-- Localization also yields the exact global flattened split.  In
particular, `globalBefore` contains all complete earlier segments followed by
the local prefix, while `globalAfter` contains the rest of the selected
segment followed by all later segments. -/
theorem first_either_input_occurrence_in_segments_global_split
    (outputInput advanceInput : ShaInput)
    (segments : List ActualProverHistorySegment)
    (location : SegmentedPairOccurrence)
    (found : firstEitherInputOccurrenceInSegments outputInput advanceInput
      segments = some location) :
    ∃ earlier current later,
      segments = earlier ++ current :: later ∧
      earlier.length = location.segmentIndex ∧
      firstEitherInputOccurrence outputInput advanceInput current.records =
        some location.withinSegment ∧
      flattenSegmentRecords segments =
        (flattenSegmentRecords earlier ++ location.withinSegment.before) ++
          location.withinSegment.chosen ::
            (location.withinSegment.after ++ flattenSegmentRecords later) ∧
      (∀ prior ∈ flattenSegmentRecords earlier ++
          location.withinSegment.before,
        prior.input ≠ outputInput ∧ prior.input ≠ advanceInput) ∧
      (location.withinSegment.chosen.input = outputInput ∨
        location.withinSegment.chosen.input = advanceInput) := by
  obtain ⟨earlier, current, later, segmentsExact, indexExact,
      currentFound, earlierNone⟩ :=
    first_either_input_occurrence_in_segments_spec outputInput advanceInput
      segments location found
  obtain ⟨currentExact, localFresh, chosenInput⟩ :=
    first_either_input_occurrence_spec outputInput advanceInput current.records
      location.withinSegment currentFound
  refine ⟨earlier, current, later, segmentsExact, indexExact,
    currentFound, ?_, ?_, chosenInput⟩
  · rw [segmentsExact]
    simp [flattenSegmentRecords, currentExact, List.append_assoc]
  · intro prior member
    simp only [List.mem_append] at member
    rcases member with earlierMember | localMember
    · change prior ∈
        earlier.flatMap ActualProverHistorySegment.records at earlierMember
      rw [List.mem_flatMap] at earlierMember
      obtain ⟨segment, segmentMember, priorMember⟩ := earlierMember
      have noOccurrence := earlierNone segment segmentMember
      exact (first_either_input_occurrence_none_iff outputInput advanceInput
        segment.records).mp noOccurrence prior priorMember
    · exact localFresh prior localMember

theorem first_either_input_occurrence_in_root_path_global_split
    (outputInput advanceInput : ShaInput)
    (path : SegmentedRootToNodeHistory)
    (location : SegmentedPairOccurrence)
    (found : firstEitherInputOccurrenceInRootPath outputInput advanceInput path =
      some location) :
    ∃ earlier current later,
      path.segments = earlier ++ current :: later ∧
      earlier.length = location.segmentIndex ∧
      firstEitherInputOccurrence outputInput advanceInput current.records =
        some location.withinSegment ∧
      path.records =
        (flattenSegmentRecords earlier ++ location.withinSegment.before) ++
          location.withinSegment.chosen ::
            (location.withinSegment.after ++ flattenSegmentRecords later) := by
  obtain ⟨earlier, current, later, segmentsExact, indexExact, localFound,
      globalSplit, _fresh, _chosen⟩ :=
    first_either_input_occurrence_in_segments_global_split outputInput
      advanceInput path.segments location
        (by simpa [firstEitherInputOccurrenceInRootPath] using found)
  exact ⟨earlier, current, later, segmentsExact, indexExact, localFound,
    globalSplit⟩

#print axioms run_prefix_preserves_programming_history
#print axioms run_machine_preserves_cumulative_programming_history
#print axioms program_oracle_success_appends_exact_programming_record
#print axioms program_oracle_success_extends_programming_history
#print axioms prefix_programming_then_run_retains_exact_extension
#print axioms run_prefix_appended_history_exact
#print axioms run_machine_appended_history_exact
#print axioms run_prefix_history_since_has_actor
#print axioms run_machine_history_since_is_chronological_suffix
#print axioms run_prefix_history_since_is_chronological_suffix
#print axioms mem_prover_history_since_iff
#print axioms prover_history_since_run_prefix_eq_history_since
#print axioms prover_history_since_run_machine_eq_history_since
#print axioms first_either_prover_input_occurrence_since_spec
#print axioms first_either_prover_input_occurrence_in_run_has_exact_actor
#print axioms returned_run_first_occurrence_replays_to_exact_pause
#print axioms returned_run_first_occurrence_replays_to_exact_pause_and_resume
#print axioms first_either_input_occurrence_in_segments_spec
#print axioms first_either_input_occurrence_in_segments_global_split
#print axioms first_either_input_occurrence_in_root_path_global_split

end

end AspisK1.V7Tag73CumulativeReplayHistory
