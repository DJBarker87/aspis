import AspisFormal.K1.V7Tag73ExactPlainRomRun
import AspisFormal.K1.V7Tag73SchedulerMachineFactorization
import AspisFormal.K1.V7Tag73TotalizedMachineReflection
import AspisFormal.K1.V7Tag73VerifierOracleStability

/-!
# Operational resource caps for the exact Tag-73 compiler

This module connects the closed-form `Q,R` resource arithmetic to quantities
that the concrete restoration interpreter actually records.  It keeps four
different counters separate:

* synchronous prefix-replay calls;
* machine-fresh master-tape coordinates;
* the two programmed fork coordinates; and
* zero-query future-free verifier microsteps.

The proofs below first establish the two protocol-local facts needed by the
client induction: a selected recorded prefix cannot be longer than its parent
prover segment, and a returned future-free driver can append at most one
verifier transition per unit of driver fuel.  No acceptance, extraction,
target-event inclusion, or compiler conclusion is assumed.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ExactCompilerOperationalCaps

set_option maxRecDepth 8192

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AtomicPairFork
open AspisK1.V7Tag73AtomicPairReplay
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73ProjectedMachinePrefix
open AspisK1.V7Tag73SchedulerMachineFactorization
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SequentialOracleRuns
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73RawProverMessages
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73RawStrictReplacementSuffix
open AspisK1.V7Tag73ReturnedPlanSemantics
open AspisK1.V7Tag73SharedOracleVerifierRunner
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73TotalizedMachineReflection
open AspisK1.V7Tag73VerifierOracleStability
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun

noncomputable section

/-! ## Prefix replay is bounded by the parent prover segment -/

/-- Every `runPrefix` execution performs at most its supplied fuel many
queries, regardless of whether it returns, pauses, aborts, or exhausts fuel. -/
theorem run_prefix_steps_le_fuel
    {Result : Type*} (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) :
    ∀ fuel state (program : OracleMachine Result),
      (runPrefix controller limits actor fuel state program).steps ≤ fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro state program
      cases program <;> simp [runPrefix]
  | succ fuel ih =>
      intro state program
      cases program with
      | pure result => simp [runPrefix]
      | abort reason => simp [runPrefix]
      | query input next =>
          simp only [runPrefix]
          cases queried : queryOracle controller limits actor state input with
          | error reason => simp
          | ok pair =>
              rcases pair with ⟨output, nextState⟩
              have tail := ih nextState (next output)
              change
                (runPrefix controller limits actor fuel nextState
                    (next output)).steps + 1 ≤ fuel + 1
              omega

/-- A computed first occurrence is a strict prefix of the complete record
list: the chosen record itself follows `before`. -/
theorem first_either_occurrence_before_length_lt
    (outputInput advanceInput : ShaInput) (records : List QueryRecord)
    (occurrence : PairOccurrenceSplit)
    (found : firstEitherInputOccurrence outputInput advanceInput records =
      some occurrence) :
    occurrence.before.length < records.length := by
  have decomposition :=
    (first_either_input_occurrence_spec outputInput advanceInput records
      occurrence found).1
  have lengths := congrArg List.length decomposition
  simp only [List.length_append, List.length_cons] at lengths
  omega

/-- Node-local formulation of the `Q` premise.  It is phrased through
`node?`, so prefix preparation can use the exact lookup equation it just
computed without converting `get?` back to list membership. -/
def AccumulatorProverHistoryBound
    {Statement Proof Payload : Type*} (Q : Nat)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload) :
    Prop :=
  ∀ nodeId node, accumulator.node? nodeId = some node →
    node.proverHistory.length ≤ Q

/-- The root accumulator inherits its prover-history cap directly from the
actual root runtime. -/
theorem initial_accumulator_prover_history_bound
    {Statement Proof Payload : Type*} (Q : Nat)
    (root : ConcreteRestorationNode Statement Proof Payload)
    (rootBound : root.proverHistory.length ≤ Q) :
    AccumulatorProverHistoryBound Q
      (initialRestorationAccumulatorFromRoot root) := by
  intro nodeId node found
  cases nodeId with
  | zero =>
      simp [ConcreteRestorationAccumulator.node?,
        initialRestorationAccumulatorFromRoot] at found
      subst node
      exact rootBound
  | succ nodeId =>
      simp [ConcreteRestorationAccumulator.node?,
        initialRestorationAccumulatorFromRoot] at found

/-- Uniform projection of the synchronous preparation work.  A ready result
charges one restart exactly when it contains a concrete prefix run. -/
def preparationPrefixUse
    {Statement Proof Payload : Type*} :
    ConcretePreparationResult Statement Proof Payload → Nat × Nat
  | .failed _reason steps restarts => (steps, restarts)
  | .ready prepared =>
      (prepared.prefixSteps, if prepared.prefixRun.isSome then 1 else 0)

/-- Prefix preparation never exceeds the parent node's proved `Q`-query
segment cap and uses at most one same-tape start.  Invalid requests use zero;
all returned/abort/pause branches are included. -/
theorem prepare_concrete_restoration_prefix_use_le
    {Statement Proof Payload : Type*}
    (Q : Nat)
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (configuration : ConcreteRestorationConfiguration)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (request : ConcreteRestorationRequest)
    (nodeBound : AccumulatorProverHistoryBound Q accumulator) :
    let use := preparationPrefixUse
      (prepareConcreteRestorationFromStartProgram startProgram configuration
        accumulator request)
    use.1 ≤ Q ∧ use.2 ≤ 1 := by
  cases selectedNode : accumulator.node? request.nodeId with
  | none =>
      simp [prepareConcreteRestorationFromStartProgram, selectedNode,
        preparationPrefixUse]
  | some parentNode =>
      have parentBound := nodeBound request.nodeId parentNode selectedNode
      cases selectedTransition : verifierTransitionAt? parentNode
          request.verifierTransitionIndex with
      | none =>
          simp [prepareConcreteRestorationFromStartProgram, selectedNode,
            selectedTransition, preparationPrefixUse]
      | some transition =>
          cases selectedPair : squeezePairInputsOfTransition transition with
          | none =>
              simp [prepareConcreteRestorationFromStartProgram, selectedNode,
                selectedTransition, selectedPair, preparationPrefixUse]
          | some pair =>
              rcases pair with ⟨outputInput, advanceInput⟩
              cases selectedOccurrence : firstEitherInputOccurrence outputInput
                  advanceInput parentNode.proverHistory with
              | none =>
                  simp [prepareConcreteRestorationFromStartProgram,
                    selectedNode, selectedTransition, selectedPair,
                    selectedOccurrence, preparationPrefixUse]
              | some occurrence =>
                  let prefixRun := runPrefix
                    (recordedPrefixController
                      parentNode.proverEntryOracle.history.length
                      occurrence.before)
                    configuration.oracleLimits .extractorReplay
                    occurrence.before.length parentNode.proverEntryOracle
                    startProgram
                  have beforeLt := first_either_occurrence_before_length_lt
                    outputInput advanceInput parentNode.proverHistory occurrence
                    selectedOccurrence
                  have beforeLeQ : occurrence.before.length ≤ Q := by
                    omega
                  have stepsLe := run_prefix_steps_le_fuel
                    (recordedPrefixController
                      parentNode.proverEntryOracle.history.length
                      occurrence.before)
                    configuration.oracleLimits .extractorReplay
                    occurrence.before.length parentNode.proverEntryOracle
                    startProgram
                  have prefixStepsLe : prefixRun.steps ≤ Q := by
                    exact stepsLe.trans beforeLeQ
                  cases halted : prefixRun.halt with
                  | returned result =>
                      simpa [prepareConcreteRestorationFromStartProgram,
                        selectedNode, selectedTransition, selectedPair,
                        selectedOccurrence, prefixRun, halted,
                        preparationPrefixUse] using
                          And.intro prefixStepsLe (Nat.le_refl 1)
                  | oracleAbort reason =>
                      simpa [prepareConcreteRestorationFromStartProgram,
                        selectedNode, selectedTransition, selectedPair,
                        selectedOccurrence, prefixRun, halted,
                        preparationPrefixUse] using
                          And.intro prefixStepsLe (Nat.le_refl 1)
                  | paused residual =>
                      cases residual with
                      | pure result =>
                          simpa [prepareConcreteRestorationFromStartProgram,
                            selectedNode, selectedTransition, selectedPair,
                            selectedOccurrence, prefixRun, halted,
                            preparationPrefixUse] using
                              And.intro prefixStepsLe (Nat.le_refl 1)
                      | abort reason =>
                          simpa [prepareConcreteRestorationFromStartProgram,
                            selectedNode, selectedTransition, selectedPair,
                            selectedOccurrence, prefixRun, halted,
                            preparationPrefixUse] using
                              And.intro prefixStepsLe (Nat.le_refl 1)
                      | query pendingInput next =>
                          by_cases pendingMismatch :
                              pendingInput ≠ occurrence.chosen.input
                          · simpa [prepareConcreteRestorationFromStartProgram,
                              selectedNode, selectedTransition, selectedPair,
                              selectedOccurrence, prefixRun, halted,
                              pendingMismatch, preparationPrefixUse] using
                                And.intro prefixStepsLe (Nat.le_refl 1)
                          · by_cases traceMismatch : queryAnswerTrace
                                (historySince parentNode.proverEntryOracle
                                  prefixRun.oracle) ≠
                                  queryAnswerTrace occurrence.before
                            · simpa [prepareConcreteRestorationFromStartProgram,
                                selectedNode, selectedTransition, selectedPair,
                                selectedOccurrence, prefixRun, halted,
                                pendingMismatch, traceMismatch,
                                preparationPrefixUse] using
                                  And.intro prefixStepsLe (Nat.le_refl 1)
                            · simpa [prepareConcreteRestorationFromStartProgram,
                                selectedNode, selectedTransition, selectedPair,
                                selectedOccurrence, prefixRun, halted,
                                pendingMismatch, traceMismatch,
                                preparationPrefixUse] using
                                  And.intro prefixStepsLe (Nat.le_refl 1)
/-! ## One future-free driver step appends at most one transition -/

theorem future_free_operational_step_transition_length_le_succ
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (state next : FutureFreeVerifierState)
    (pairs : List (ShaInput × ShaOutput))
    (step : FutureFreeOperationalStep environment raw state pairs next) :
    next.transitions.length ≤ state.transitions.length + 1 := by
  cases step with
  | prover submitted event snapshot appendExact =>
      rw [appendExact]
      simp [appendFutureFreeSnapshot]
  | verifier forced replyPath advanced =>
      obtain ⟨action, snapshot, nextExact⟩ :=
        successful_future_free_advance_is_complete_append environment state
          next _ advanced
      rw [nextExact]
      simp [appendFutureFreeSnapshot]
  | stutter noSubmission noAction =>
      omega

/-- The exact raw driver has no hidden transition multiplier: one unit of
driver fuel performs one microstep, and a microstep appends at most one
snapshot/transition. -/
theorem drive_raw_future_free_transition_growth_le_fuel
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages) :
    ∀ fuel state pairs result,
      MachineQueryPath (driveRawFutureFree environment raw fuel state)
        pairs result →
      result.transitions.length ≤ state.transitions.length + fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro state pairs result path
      cases path
      simp
  | succ fuel ih =>
      intro state pairs result path
      simp only [driveRawFutureFree] at path
      obtain ⟨next, headPairs, tailPairs, headPath, tailPath, _pairsExact⟩ :=
        machine_query_path_bind_split
          (rawFutureFreeMicrostep environment raw state)
          (fun next =>
            if isDriverHalt next.current.control then .pure next
            else driveRawFutureFree environment raw fuel next)
          pairs result path
      have headStep := raw_future_free_microstep_path_is_operational
        environment raw state next headPairs headPath
      have headBound :=
        future_free_operational_step_transition_length_le_succ environment raw
          state next headPairs headStep
      by_cases terminal : isDriverHalt next.current.control
      · simp [terminal] at tailPath
        cases tailPath
        omega
      · simp [terminal] at tailPath
        have tailBound := ih next tailPairs result tailPath
        omega

/-- Restoring an indexed transition deliberately resets the stale transition
suffix, so a successful residual driver contains at most `driverFuel`
transitions in total. -/
theorem restored_drive_transition_count_le_driver_fuel
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (driverFuel : Nat) (transition : FutureFreeTransition)
    (pairs : List (ShaInput × ShaOutput))
    (result : FutureFreeVerifierState)
    (path : MachineQueryPath
      (driveRawFutureFree environment raw driverFuel
        (restoreIndexedTransition transition)) pairs result) :
    result.transitions.length ≤ driverFuel := by
  have growth := drive_raw_future_free_transition_growth_le_fuel environment
    raw driverFuel (restoreIndexedTransition transition) pairs result path
  simpa [restoreIndexedTransition] using growth

/-- A concrete normally returned totalized verifier stage reflects to the
underlying raw driver and therefore inherits the exact transition-fuel cap.
The premise is an operational run equation, not an arbitrary final-state
field. -/
theorem totalized_restored_driver_transition_count_le
    (controller : AdaptiveController) (limits : OracleLimits)
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (verifierFuel driverFuel : Nat) (transition : FutureFreeTransition)
    (oracleEntry finalOracle : OracleState)
    (result : FutureFreeVerifierState)
    (steps : Nat)
    (returned : runMachine controller limits .verifier verifierFuel
        oracleEntry
        (totalizeOracleMachine verifierFuel
          (driveRawFutureFree environment raw driverFuel
            (restoreIndexedTransition transition))) =
      { halt := .returned (.ok result)
        oracle := finalOracle
        steps := steps }) :
    result.transitions.length ≤ driverFuel := by
  have reflected := run_machine_totalized_ok_reflects controller limits
    .verifier verifierFuel oracleEntry
    (driveRawFutureFree environment raw driverFuel
      (restoreIndexedTransition transition))
    result finalOracle steps returned
  have returnedHalt :
      (runMachine controller limits .verifier verifierFuel
        oracleEntry
        (driveRawFutureFree environment raw driverFuel
          (restoreIndexedTransition transition))).halt = .returned result := by
    rw [reflected]
  obtain ⟨pairs, path, _history, _actors, _table⟩ :=
    run_machine_returned_has_exact_query_path controller limits .verifier
      verifierFuel oracleEntry
      (driveRawFutureFree environment raw driverFuel
        (restoreIndexedTransition transition)) result returnedHalt
  exact restored_drive_transition_count_le_driver_fuel environment raw
    driverFuel transition pairs result path

/-- Entry coherence is stored in both constructors of the exact projected
trace. -/
theorem projected_returned_trace_entry_coherent
    {Result : Type*} (limits : OracleLimits) (actor : QueryActor)
    (fuel : Nat) (entry : OracleState) (program : OracleMachine Result)
    (freshQueries : List (ShaInput × Digest256)) (result : Result)
    (finalState : OracleState) (steps : Nat)
    (trace : ProjectedFreshReturnedTrace limits actor fuel entry program
      freshQueries result finalState steps) :
    HistoryTotalCoherent entry := by
  cases trace <;> assumption

/-- A normally returned projected scheduler segment makes no more literal
oracle calls than its machine fuel.  Cached and fresh calls are both present
in `historySince`; this is not merely a bound on fresh coordinates. -/
theorem projected_returned_history_length_le_fuel
    {Result : Type*} (limits : OracleLimits) (actor : QueryActor)
    (fuel : Nat) (entry : OracleState) (program : OracleMachine Result)
    (available : List Digest256)
    (returned : ProjectedMachinePrefixReturned limits actor fuel entry program
      available) :
    (historySince entry returned.finalState).length ≤ fuel := by
  let controller := controllerFromProjectedFreshAnswers entry.history
    (returned.freshQueries.map Prod.snd)
  have entryCoherent : HistoryTotalCoherent entry :=
    projected_returned_trace_entry_coherent limits actor fuel entry program
      returned.freshQueries returned.result returned.finalState returned.steps
      returned.trace
  have runExact := projected_machine_prefix_returned_run_exact limits actor fuel
    entry program available returned entryCoherent
  have extension := run_machine_exact_fresh_extension controller limits actor
    fuel entry program
  have stepBound := run_machine_steps_le_fuel controller limits actor fuel
    entry program
  rw [runExact] at extension stepBound
  exact extension.2.2.trans stepBound

/-! ## Result properties that may use actual machine-segment certificates -/

universe u

/-- Static continuation safety strengthened at machine nodes by the literal
`ProjectedMachinePrefixReturned` certificate produced by the scheduler
factorization.  Unlike `SchedulerNativeCursorAllReturned`, this predicate may
prove bounds on history lengths and protocol transitions because arbitrary
coherent callback states are not admitted. -/
inductive SchedulerNativeCursorAllProjectedReturned
    {globalOracleCalls : Nat} {Result : Type u}
    (P : Result → Prop) :
    SchedulerNativeCursor globalOracleCalls Result → Prop where
  | returned (result : Result) (holds : P result) :
      SchedulerNativeCursorAllProjectedReturned P (.returned result)
  | failed (reason : SchedulerNativeFailure) :
      SchedulerNativeCursorAllProjectedReturned P (.failed reason)
  | machine
      {MachineResult : Type u}
      (limits : OracleLimits)
      (limitBound : limits.totalCalls ≤ globalOracleCalls)
      (actor : QueryActor) (state : OracleState)
      (program : OracleMachine MachineResult) (fuel : Nat)
      (coherent : HistoryTotalCoherent state)
      (onReturned : (result : MachineResult) → (state : OracleState) →
        HistoryTotalCoherent state →
          SchedulerNativeCursor globalOracleCalls Result)
      (safe : ∀ (available : List Digest256)
        (returned : ProjectedMachinePrefixReturned limits actor fuel state
          program available),
        SchedulerNativeCursorAllProjectedReturned P
          (onReturned returned.result returned.finalState
            returned.finalCoherent)) :
      SchedulerNativeCursorAllProjectedReturned P
        (.machine limits limitBound actor state program fuel coherent
          onReturned)
  | forkPair
      (frozenHistory : List QueryRecord)
      (pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls)
      (outputInput advanceInput : ShaInput)
      (template : AtomicPairReplayConfiguration)
      (next : AtomicPairReplayConfiguration →
        SchedulerNativeCursor globalOracleCalls Result)
      (safe : ∀ configuration,
        SchedulerNativeCursorAllProjectedReturned P (next configuration)) :
      SchedulerNativeCursorAllProjectedReturned P
        (.forkPair frozenHistory pairRoom outputInput advanceInput template
          next)
  | forkAdvance
      (frozenHistory : List QueryRecord)
      (pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls)
      (outputInput advanceInput : ShaInput)
      (template : AtomicPairReplayConfiguration)
      (forkOutput : Digest256)
      (next : AtomicPairReplayConfiguration →
        SchedulerNativeCursor globalOracleCalls Result)
      (safe : ∀ configuration,
        SchedulerNativeCursorAllProjectedReturned P (next configuration)) :
      SchedulerNativeCursorAllProjectedReturned P
        (.forkAdvance frozenHistory pairRoom outputInput advanceInput template
          forkOutput next)

/-- The exact list scheduler can return only a result certified by the
projected continuation predicate.  Machine stages are factored through the
proof-producing prefix interpreter; no arbitrary callback-state premise is
used. -/
theorem run_scheduler_native_list_respects_all_projected_returned
    {globalOracleCalls : Nat} {Result : Type u}
    (P : Result → Prop) (transitionFuel : Nat)
    (transitionFuelPositive : 0 < transitionFuel) :
    ∀ (cursor : SchedulerNativeCursor globalOracleCalls Result)
      (safe : SchedulerNativeCursorAllProjectedReturned P cursor)
      (currentTransitionFuel : Nat) (answers : List Digest256)
      (result : Result),
      runSchedulerNativeListTerminalFrom transitionFuel currentTransitionFuel
          cursor answers = .returned result →
      P result := by
  obtain ⟨resetTransitionFuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt transitionFuelPositive)
  intro cursor safe
  induction safe with
  | returned returnedResult holds =>
      intro currentTransitionFuel answers result completed
      cases currentTransitionFuel with
      | zero =>
          cases answers with
          | nil =>
              simp [runSchedulerNativeListTerminalFrom, terminalAtExposureEnd,
                seekSchedulerNativeExposure] at completed
          | cons answer rest =>
              simp only [runSchedulerNativeListTerminalFrom,
                seekSchedulerNativeExposure] at completed
              rw [run_scheduler_native_list_failed_of_positive
                (resetTransitionFuel + 1) (Nat.succ_pos _)
                .transitionLimit rest] at completed
              cases completed
      | succ currentTransitionFuel =>
          have resultExact : result = returnedResult := by
            cases answers with
            | nil =>
                simp [runSchedulerNativeListTerminalFrom,
                  terminalAtExposureEnd, seekSchedulerNativeExposure]
                  at completed
                exact completed.symm
            | cons answer rest =>
                simp only [runSchedulerNativeListTerminalFrom,
                  seekSchedulerNativeExposure] at completed
                rw [run_scheduler_native_list_returned_of_positive
                  (globalOracleCalls := globalOracleCalls)
                  (resetTransitionFuel + 1) (Nat.succ_pos _)
                  returnedResult rest] at completed
                exact SchedulerNativeTerminal.returned.inj completed.symm
          subst result
          exact holds
  | failed reason =>
      intro currentTransitionFuel answers result completed
      cases currentTransitionFuel with
      | zero =>
          cases answers with
          | nil =>
              simp [runSchedulerNativeListTerminalFrom, terminalAtExposureEnd,
                seekSchedulerNativeExposure] at completed
          | cons answer rest =>
              simp only [runSchedulerNativeListTerminalFrom,
                seekSchedulerNativeExposure] at completed
              rw [run_scheduler_native_list_failed_of_positive
                (resetTransitionFuel + 1) (Nat.succ_pos _)
                .transitionLimit rest] at completed
              cases completed
      | succ currentTransitionFuel =>
          cases answers with
          | nil =>
              simp [runSchedulerNativeListTerminalFrom,
                terminalAtExposureEnd, seekSchedulerNativeExposure]
                at completed
          | cons answer rest =>
              simp only [runSchedulerNativeListTerminalFrom,
                seekSchedulerNativeExposure] at completed
              rw [run_scheduler_native_list_failed_of_positive
                (globalOracleCalls := globalOracleCalls)
                (Result := Result)
                (resetTransitionFuel + 1) (Nat.succ_pos _) reason rest]
                at completed
              cases completed
  | @machine MachineResult limits limitBound actor state program fuel coherent
      onReturned safe ih =>
      intro currentTransitionFuel answers result completed
      rw [run_scheduler_native_list_machine_factorization
        (resetTransitionFuel + 1)
        limits limitBound actor state program fuel coherent onReturned
        (Nat.succ_pos _) currentTransitionFuel answers] at completed
      unfold terminalAfterProjectedMachinePrefix
        terminalAfterCertifiedProjectedMachinePrefix at completed
      cases currentTransitionFuel with
      | zero => simp at completed
      | succ current =>
          cases executed : consumeCertifiedProjectedMachinePrefix limits actor
              answers fuel state program coherent
              (certifiedSeekNextFresh limits actor fuel state program coherent)
              rfl with
          | error reason =>
              simp [executed, prefixFailureTerminal] at completed
              cases reason <;> cases completed
          | ok returned =>
              simp only [executed] at completed
              exact ih answers returned
                (machinePrefixContinuationTransitionFuel
                  (resetTransitionFuel + 1)
                  current returned.freshQueries)
                returned.remaining result completed
  | forkPair frozenHistory pairRoom outputInput advanceInput template next safe
      ih =>
      intro currentTransitionFuel answers result completed
      cases currentTransitionFuel with
      | zero =>
          cases answers with
          | nil =>
              simp [runSchedulerNativeListTerminalFrom, terminalAtExposureEnd,
                seekSchedulerNativeExposure] at completed
          | cons answer rest =>
              simp only [runSchedulerNativeListTerminalFrom,
                seekSchedulerNativeExposure] at completed
              rw [run_scheduler_native_list_failed_of_positive
                (resetTransitionFuel + 1) (Nat.succ_pos _)
                .transitionLimit rest] at completed
              cases completed
      | succ current =>
          cases answers with
          | nil =>
              simp [runSchedulerNativeListTerminalFrom, terminalAtExposureEnd,
                seekSchedulerNativeExposure] at completed
          | cons answer rest =>
              simp only [runSchedulerNativeListTerminalFrom,
                seekSchedulerNativeExposure] at completed
              cases rest with
              | nil =>
                  simp [runSchedulerNativeListTerminalFrom,
                    terminalAtExposureEnd, seekSchedulerNativeExposure]
                    at completed
              | cons advance tail =>
                  let scheduled : ScheduledForkCoins :=
                    { frozenHistory := frozenHistory
                      outputInput := outputInput
                      advanceInput := advanceInput
                      template := template
                      forkOutput := answer
                      forkAdvance := advance }
                  simp only [runSchedulerNativeListTerminalFrom,
                    seekSchedulerNativeExposure] at completed
                  apply ih scheduled.configuration (resetTransitionFuel + 1)
                    tail result
                  simpa [scheduled] using completed
  | forkAdvance frozenHistory pairRoom outputInput advanceInput template
      forkOutput next safe ih =>
      intro currentTransitionFuel answers result completed
      cases currentTransitionFuel with
      | zero =>
          cases answers with
          | nil =>
              simp [runSchedulerNativeListTerminalFrom, terminalAtExposureEnd,
                seekSchedulerNativeExposure] at completed
          | cons answer rest =>
              simp only [runSchedulerNativeListTerminalFrom,
                seekSchedulerNativeExposure] at completed
              rw [run_scheduler_native_list_failed_of_positive
                (resetTransitionFuel + 1) (Nat.succ_pos _)
                .transitionLimit rest] at completed
              cases completed
      | succ current =>
          cases answers with
          | nil =>
              simp [runSchedulerNativeListTerminalFrom, terminalAtExposureEnd,
                seekSchedulerNativeExposure] at completed
          | cons answer rest =>
              let scheduled : ScheduledForkCoins :=
                { frozenHistory := frozenHistory
                  outputInput := outputInput
                  advanceInput := advanceInput
                  template := template
                  forkOutput := forkOutput
                  forkAdvance := answer }
              simp only [runSchedulerNativeListTerminalFrom,
                seekSchedulerNativeExposure] at completed
              apply ih scheduled.configuration (resetTransitionFuel + 1)
                rest result
              simpa [scheduled] using completed

/-! ## Accumulator projections are genuinely append-only -/

theorem add_charges_uniform_fork_coordinate_total
    {Statement Proof Payload : Type*}
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (charges : List ConcreteRestorationCharge) :
    (accumulator.addCharges charges).uniformForkCoordinateTotal =
      accumulator.uniformForkCoordinateTotal +
        (charges.map
          ConcreteRestorationCharge.uniformForkCoordinates).sum := by
  simp [ConcreteRestorationAccumulator.addCharges,
    ConcreteRestorationAccumulator.uniformForkCoordinateTotal]

theorem add_charges_restart_total
    {Statement Proof Payload : Type*}
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (charges : List ConcreteRestorationCharge) :
    (accumulator.addCharges charges).restartTotal =
      accumulator.restartTotal +
        (charges.map ConcreteRestorationCharge.restarts).sum := by
  simp [ConcreteRestorationAccumulator.addCharges,
    ConcreteRestorationAccumulator.restartTotal]

theorem add_charges_verifier_transition_total
    {Statement Proof Payload : Type*}
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (charges : List ConcreteRestorationCharge) :
    (accumulator.addCharges charges).verifierTransitionTotal =
      accumulator.verifierTransitionTotal +
        (charges.map ConcreteRestorationCharge.protocolTransitions).sum := by
  simp [ConcreteRestorationAccumulator.addCharges,
    ConcreteRestorationAccumulator.verifierTransitionTotal]

theorem add_failure_preserves_resource_totals
    {Statement Proof Payload : Type*}
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (request : ConcreteRestorationRequest)
    (reason : ConcreteRestorationFailure) :
    (accumulator.addFailure request reason).oracleQueryTotal =
        accumulator.oracleQueryTotal ∧
      (accumulator.addFailure request reason).uniformForkCoordinateTotal =
        accumulator.uniformForkCoordinateTotal ∧
      (accumulator.addFailure request reason).programmedPointTotal =
        accumulator.programmedPointTotal ∧
      (accumulator.addFailure request reason).restartTotal =
        accumulator.restartTotal ∧
      (accumulator.addFailure request reason).verifierTransitionTotal =
        accumulator.verifierTransitionTotal := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem add_node_preserves_resource_totals
    {Statement Proof Payload : Type*}
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (node : ConcreteRestorationNode Statement Proof Payload) :
    let next := (accumulator.addNode node).2
    next.oracleQueryTotal = accumulator.oracleQueryTotal ∧
      next.uniformForkCoordinateTotal =
        accumulator.uniformForkCoordinateTotal ∧
      next.programmedPointTotal = accumulator.programmedPointTotal ∧
      next.restartTotal = accumulator.restartTotal ∧
      next.verifierTransitionTotal = accumulator.verifierTransitionTotal := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Resource delta allowed for one attempted restoration.  This relation is
used only after the actual scheduler stage certificates establish the three
literal query counts and the returned driver transition count. -/
structure OneRestorationAccumulatorDelta
    {Statement Proof Payload : Type*}
    (Q driverFuel : Nat)
    (before after : ConcreteRestorationAccumulator Statement Proof Payload) :
    Prop where
  oracleQueries : after.oracleQueryTotal ≤
    before.oracleQueryTotal + (2 * Q + 1511)
  forkCoordinates : after.uniformForkCoordinateTotal ≤
    before.uniformForkCoordinateTotal + 2
  programmedPoints : after.programmedPointTotal ≤
    before.programmedPointTotal + 2
  restarts : after.restartTotal ≤ before.restartTotal + 2
  verifierTransitions : after.verifierTransitionTotal ≤
    before.verifierTransitionTotal + driverFuel

/-- Per-attempt deltas compose without any independence or probability
reasoning. -/
theorem one_restoration_accumulator_delta_trans
    {Statement Proof Payload : Type*}
    (Q driverFuel : Nat)
    (first middle final :
      ConcreteRestorationAccumulator Statement Proof Payload)
    (firstDelta : OneRestorationAccumulatorDelta Q driverFuel first middle)
    (secondDelta : OneRestorationAccumulatorDelta Q driverFuel middle final) :
    final.oracleQueryTotal ≤ first.oracleQueryTotal + 2 * (2 * Q + 1511) ∧
      final.uniformForkCoordinateTotal ≤
        first.uniformForkCoordinateTotal + 2 * 2 ∧
      final.programmedPointTotal ≤ first.programmedPointTotal + 2 * 2 ∧
      final.restartTotal ≤ first.restartTotal + 2 * 2 ∧
      final.verifierTransitionTotal ≤
        first.verifierTransitionTotal + 2 * driverFuel := by
  rcases firstDelta with
    ⟨firstQueries, firstForks, firstProgrammed, firstRestarts,
      firstTransitions⟩
  rcases secondDelta with
    ⟨secondQueries, secondForks, secondProgrammed, secondRestarts,
      secondTransitions⟩
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  · simp only [two_mul]
    omega

/-- Absolute accumulator envelope after at most `attempts` concrete
restoration requests. -/
structure AccumulatorWithinRestorationAttempts
    {Statement Proof Payload : Type*}
    (Q driverFuel attempts : Nat)
    (initial current :
      ConcreteRestorationAccumulator Statement Proof Payload) : Prop where
  oracleQueries : current.oracleQueryTotal ≤
    initial.oracleQueryTotal + attempts * (2 * Q + 1511)
  forkCoordinates : current.uniformForkCoordinateTotal ≤
    initial.uniformForkCoordinateTotal + attempts * 2
  programmedPoints : current.programmedPointTotal ≤
    initial.programmedPointTotal + attempts * 2
  restarts : current.restartTotal ≤ initial.restartTotal + attempts * 2
  verifierTransitions : current.verifierTransitionTotal ≤
    initial.verifierTransitionTotal + attempts * driverFuel

theorem accumulator_within_zero_restoration_attempts
    {Statement Proof Payload : Type*}
    (Q driverFuel : Nat)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload) :
    AccumulatorWithinRestorationAttempts Q driverFuel 0 accumulator
      accumulator := by
  constructor <;> simp

theorem accumulator_within_restoration_attempts_succ
    {Statement Proof Payload : Type*}
    (Q driverFuel attempts : Nat)
    (initial current next :
      ConcreteRestorationAccumulator Statement Proof Payload)
    (prior : AccumulatorWithinRestorationAttempts Q driverFuel attempts
      initial current)
    (delta : OneRestorationAccumulatorDelta Q driverFuel current next) :
    AccumulatorWithinRestorationAttempts Q driverFuel (attempts + 1)
      initial next := by
  rcases prior with
    ⟨priorQueries, priorForks, priorProgrammed, priorRestarts,
      priorTransitions⟩
  rcases delta with
    ⟨deltaQueries, deltaForks, deltaProgrammed, deltaRestarts,
      deltaTransitions⟩
  constructor <;>
    simp only [Nat.add_mul, Nat.one_mul] <;>
    omega

/-- Closed-form client totals when the initial accumulator has no charges. -/
theorem zero_initial_accumulator_attempt_caps
    {Statement Proof Payload : Type*}
    (Q driverFuel attempts : Nat)
    (root : ConcreteRestorationNode Statement Proof Payload)
    (current : ConcreteRestorationAccumulator Statement Proof Payload)
    (within : AccumulatorWithinRestorationAttempts Q driverFuel attempts
      (initialRestorationAccumulatorFromRoot root) current) :
    current.oracleQueryTotal ≤ attempts * (2 * Q + 1511) ∧
      current.uniformForkCoordinateTotal ≤ 2 * attempts ∧
      current.programmedPointTotal ≤ 2 * attempts ∧
      current.restartTotal ≤ 2 * attempts ∧
      current.verifierTransitionTotal ≤ attempts * driverFuel := by
  rcases within with ⟨queries, forks, programmed, restarts, transitions⟩
  simpa [ConcreteRestorationAccumulator.oracleQueryTotal,
    ConcreteRestorationAccumulator.uniformForkCoordinateTotal,
    ConcreteRestorationAccumulator.programmedPointTotal,
    ConcreteRestorationAccumulator.restartTotal,
    ConcreteRestorationAccumulator.verifierTransitionTotal,
    initialRestorationAccumulatorFromRoot, Nat.mul_comm] using
      And.intro queries
        (And.intro forks
          (And.intro programmed (And.intro restarts transitions)))

/-! ## Exact closed-form arithmetic used after client induction -/

/-- Per restoration, at most one recorded-prefix start and one complete
from-start replay each use `Q` calls, while the residual verifier uses at most
1511. -/
def perRestorationFull256CallCap (Q : Nat) : Nat := 2 * Q + 1511

def clientMachineFreshCap (Q R : Nat) : Nat := R * (Q + 1511)

def clientForkCoordinateCap (R : Nat) : Nat := 2 * R

def clientRestartCap (R : Nat) : Nat := 2 * R

def clientProtocolTransitionCap (driverFuel R : Nat) : Nat :=
  R * driverFuel

/-- Three units are sufficient to normalize the root prover, root verifier,
and a terminal/fork request when no master-tape coordinate intervenes.  The
concrete-client theorem below must establish that its cursor never contains a
longer consecutive chain of normally returned machine constructors. -/
def exactCompilerSufficientTransitionFuel : Nat := 3

/-! ## Resource-limit adequacy is separate from an upper-bound fit -/

/-- Sufficient *reserve* conditions for the executable plain-ROM machine.
The existing `ExactPlainRomOperationalBounds` fields point in the opposite
direction (`configured limit ≤ G`) and only justify the scheduler's type
index; they cannot prove `StageHasOracleRoom`.  This predicate records the
needed lower reserves and stage fuels without asserting that an adversarial
program returns, accepts, or extracts.

`canonicalDriverFuel` is supplied by the independent literal future-free
control-path count (currently the canonical 1442-step theorem), rather than
invented here. -/
structure ExactPlainRomOperationalAdequacy
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (canonicalDriverFuel transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters) : Prop where
  adversaryTotalReserve : parameters.q1ShaCallCap ≤
    configuration.machine.adversaryLimits.totalCalls
  adversaryFreshReserve : parameters.q1ShaCallCap ≤
    configuration.machine.adversaryLimits.freshCalls
  rootVerifierTotalReserve :
    parameters.q1ShaCallCap + deployedFull256VerifierCallCap ≤
      configuration.machine.verifierLimits.totalCalls
  rootVerifierFreshReserve :
    parameters.q1ShaCallCap + deployedFull256VerifierCallCap ≤
      configuration.machine.verifierLimits.freshCalls
  replayTotalReserve : globalFull256OracleCallCap parameters ≤
    configuration.restorationConfiguration.oracleLimits.totalCalls
  replayFreshReserve : unifiedFull256ExposureCap parameters ≤
    configuration.restorationConfiguration.oracleLimits.freshCalls
  replayProgrammingReserve : 2 * parameters.forkRequestCap ≤
    configuration.restorationConfiguration.oracleLimits.programmedPoints
  adversaryFuelExact : configuration.machine.adversaryFuel =
    parameters.q1ShaCallCap
  rootVerifierFuelExact : configuration.machine.verifierFuel =
    deployedFull256VerifierCallCap
  replayAdversaryFuelExact :
    configuration.restorationConfiguration.proverReplayFuel =
      parameters.q1ShaCallCap
  replayVerifierFuelExact :
    configuration.restorationConfiguration.verifierFuel =
      deployedFull256VerifierCallCap
  rootDriverFuel : canonicalDriverFuel ≤ configuration.machine.driverFuel
  replayDriverFuel : canonicalDriverFuel ≤
    configuration.restorationConfiguration.driverFuel
  schedulerTransitionFuel : exactCompilerSufficientTransitionFuel ≤
    transitionFuel

/-- For the replay oracle the upper type-fit bound and lower adequacy reserve
force the exact global total-call limit `G`. -/
theorem adequate_replay_total_limit_eq_G
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {canonicalDriverFuel transitionFuel : Nat}
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (adequate : ExactPlainRomOperationalAdequacy canonicalDriverFuel
      transitionFuel configuration) :
    configuration.restorationConfiguration.oracleLimits.totalCalls =
      globalFull256OracleCallCap parameters := by
  exact Nat.le_antisymm configuration.bounds.replayTotalCalls
    adequate.replayTotalReserve

theorem exact_operational_cap_expansions
    (parameters : ExactCompilerResourceParameters) :
    parameters.q1ShaCallCap + 1511 +
        parameters.forkRequestCap *
          perRestorationFull256CallCap parameters.q1ShaCallCap =
      globalFull256OracleCallCap parameters ∧
    parameters.q1ShaCallCap + 1511 +
        clientMachineFreshCap parameters.q1ShaCallCap
          parameters.forkRequestCap =
      full256MachineFreshCap parameters ∧
    clientForkCoordinateCap parameters.forkRequestCap =
      sameTapeStartCap parameters ∧
    clientRestartCap parameters.forkRequestCap =
      sameTapeStartCap parameters := by
  unfold perRestorationFull256CallCap clientMachineFreshCap
    clientForkCoordinateCap clientRestartCap globalFull256OracleCallCap
    full256MachineFreshCap sameTapeStartCap deployedFull256VerifierCallCap
  omega

#print axioms run_prefix_steps_le_fuel
#print axioms first_either_occurrence_before_length_lt
#print axioms initial_accumulator_prover_history_bound
#print axioms prepare_concrete_restoration_prefix_use_le
#print axioms future_free_operational_step_transition_length_le_succ
#print axioms drive_raw_future_free_transition_growth_le_fuel
#print axioms restored_drive_transition_count_le_driver_fuel
#print axioms totalized_restored_driver_transition_count_le
#print axioms projected_returned_trace_entry_coherent
#print axioms projected_returned_history_length_le_fuel
#print axioms run_scheduler_native_list_respects_all_projected_returned
#print axioms add_charges_uniform_fork_coordinate_total
#print axioms add_charges_restart_total
#print axioms add_charges_verifier_transition_total
#print axioms add_failure_preserves_resource_totals
#print axioms add_node_preserves_resource_totals
#print axioms one_restoration_accumulator_delta_trans
#print axioms accumulator_within_zero_restoration_attempts
#print axioms accumulator_within_restoration_attempts_succ
#print axioms zero_initial_accumulator_attempt_caps
#print axioms exact_operational_cap_expansions
#print axioms adequate_replay_total_limit_eq_G

end

end AspisK1.V7Tag73ExactCompilerOperationalCaps
