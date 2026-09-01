import AspisFormal.K1.V7Tag73CumulativeReplayHistory
import AspisFormal.K1.V7Tag73CompletedFullRunProjection

/-!
# Exact preparation of every literal root squeeze request

The production root sweep requests every verifier transition index. This
module proves that an indexed root transition which is a literal paired
squeeze has an executable `.ready` preparation.

The replay changes only the audit actor label from `adversary` to
`extractorReplay`; table contents, counters, controller decisions and machine
continuations are unchanged.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73RootSqueezePreparationClosure

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicPairFork
open AspisK1.V7Tag73CompletedFullRunProjection
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73CumulativeReplayHistory
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73RawStrictReplacementSuffix
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SequentialOracleRuns
open AspisK1.V7Tag73SharedOracleVerifierRunner
open AspisK1.V7Tag73TotalizedMachineReflection
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73UniformRawVerifierExecution

noncomputable section

universe u

/-! ## Actor-renamed prefix replay -/

structure OracleCoreAgreement (source replay : OracleState) : Prop where
  table : source.table = replay.table
  programmingHistory :
    source.programmingHistory = replay.programmingHistory
  totalCalls : source.totalCalls = replay.totalCalls
  freshCalls : source.freshCalls = replay.freshCalls
  historyLength : source.history.length = replay.history.length

@[simp] theorem oracle_core_agreement_refl (state : OracleState) :
    OracleCoreAgreement state state := by
  constructor <;> rfl

theorem recorded_prefix_controller_eq_of_core_agreement
    (initialHistoryLength : Nat) (recorded : List QueryRecord)
    (source replay : OracleState) (input : ShaInput)
    (agreement : OracleCoreAgreement source replay) :
    recordedPrefixController initialHistoryLength recorded source.history
        input =
      recordedPrefixController initialHistoryLength recorded replay.history
        input := by
  unfold recordedPrefixController
  rw [agreement.historyLength]

private theorem query_success_with_matching_controller
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
    | some entry => simpa only [found] using success
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

private theorem query_success_history_cons_of_final_prefix
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (state nextState finalState : OracleState)
    (input : ShaInput) (output : ShaOutput)
    (success : queryOracle controller limits actor state input =
      .ok (output, nextState))
    (finalPrefix : nextState.history <+: finalState.history) :
    ∃ origin : AnswerOrigin,
      historySince state finalState =
        ({ input := input, output := output, actor := actor,
            origin := origin } : QueryRecord) ::
          historySince nextState finalState := by
  obtain ⟨origin, nextHistory⟩ :=
    query_oracle_success_appends_one_record controller limits actor state
      nextState input output success
  rcases finalPrefix with ⟨suffix, finalHistory⟩
  refine ⟨origin, ?_⟩
  unfold historySince
  rw [← finalHistory, nextHistory]
  simp [List.append_assoc]

/-- One successful recorded-prefix query can be repeated under a different
actor. The histories differ only in actor metadata, while the complete
machine-relevant oracle core remains equal. -/
theorem recorded_prefix_query_actor_change
    (initialHistoryLength : Nat) (recorded : List QueryRecord)
    (limits : OracleLimits) (sourceActor replayActor : QueryActor)
    (source replay nextSource : OracleState)
    (input : ShaInput) (output : ShaOutput)
    (agreement : OracleCoreAgreement source replay)
    (success :
      queryOracle
          (recordedPrefixController initialHistoryLength recorded)
          limits sourceActor source input = .ok (output, nextSource)) :
    ∃ nextReplay,
      queryOracle
          (recordedPrefixController initialHistoryLength recorded)
          limits replayActor replay input = .ok (output, nextReplay) ∧
      OracleCoreAgreement nextSource nextReplay := by
  have controllerEq := recorded_prefix_controller_eq_of_core_agreement
    initialHistoryLength recorded source replay input agreement
  unfold queryOracle at success ⊢
  by_cases totalBlocked : source.totalCalls ≥ limits.totalCalls
  · simp [totalBlocked] at success
  · have replayTotalOpen : ¬ replay.totalCalls ≥ limits.totalCalls := by
      simpa [← agreement.totalCalls] using totalBlocked
    simp only [totalBlocked, replayTotalOpen, if_false] at success ⊢
    have lookupEq : lookupEntry source input = lookupEntry replay input := by
      unfold lookupEntry
      rw [agreement.table]
    cases sourceFound : lookupEntry source input with
    | some entry =>
        have replayFound : lookupEntry replay input = some entry := by
          rw [← lookupEq, sourceFound]
        simp only [sourceFound] at success
        simp only [replayFound]
        simp only [Except.ok.injEq, Prod.mk.injEq] at success
        rcases success with ⟨rfl, rfl⟩
        refine ⟨_, rfl, ?_⟩
        constructor
        · exact agreement.table
        · exact agreement.programmingHistory
        · change source.totalCalls + 1 = replay.totalCalls + 1
          exact congrArg (fun value => value + 1) agreement.totalCalls
        · exact agreement.freshCalls
        · simp [agreement.historyLength]
    | none =>
        have replayFound : lookupEntry replay input = none := by
          rw [← lookupEq, sourceFound]
        simp only [sourceFound] at success
        simp only [replayFound]
        by_cases freshBlocked : source.freshCalls ≥ limits.freshCalls
        · simp [freshBlocked] at success
        · have replayFreshOpen : ¬ replay.freshCalls ≥ limits.freshCalls := by
            simpa [← agreement.freshCalls] using freshBlocked
          simp only [freshBlocked, replayFreshOpen, if_false] at success ⊢
          cases sourceDecision :
              recordedPrefixController initialHistoryLength recorded
                source.history input with
          | refuse => simp [sourceDecision] at success
          | answer answer =>
              have replayDecision :
                  recordedPrefixController initialHistoryLength recorded
                      replay.history input = .answer answer := by
                rw [← controllerEq, sourceDecision]
              simp only [sourceDecision] at success
              simp only [replayDecision]
              simp only [Except.ok.injEq, Prod.mk.injEq] at success
              rcases success with ⟨rfl, rfl⟩
              refine ⟨_, rfl, ?_⟩
              constructor
              · simp [agreement.table]
              · exact agreement.programmingHistory
              · change source.totalCalls + 1 = replay.totalCalls + 1
                exact congrArg (fun value => value + 1) agreement.totalCalls
              · change source.freshCalls + 1 = replay.freshCalls + 1
                exact congrArg (fun value => value + 1) agreement.freshCalls
              · simp [agreement.historyLength]

/-- Strengthened inversion induction. The normally returned source run uses
`sourceActor`; the executable prefix replay may use any `replayActor`. -/
private theorem returned_run_replays_prefix_under_actor_change_aux
    {Result : Type*}
    (controller : AdaptiveController) (limits : OracleLimits)
    (sourceActor replayActor : QueryActor)
    (initialHistoryLength : Nat)
    (recorded consumed remaining : List QueryRecord)
    (sourceState replayState : OracleState)
    (fuel : Nat) (program : OracleMachine Result)
    (result : Result) (chosen : QueryRecord) (after : List QueryRecord)
    (agreement : OracleCoreAgreement sourceState replayState)
    (recordedExact : recorded = consumed ++ remaining)
    (replayLength : replayState.history.length =
      initialHistoryLength + consumed.length)
    (returned :
      (runMachine controller limits sourceActor fuel sourceState program).halt =
        .returned result)
    (decomposition :
      historySince sourceState
          (runMachine controller limits sourceActor fuel sourceState
            program).oracle =
        remaining ++ chosen :: after) :
    let replay := runPrefix
      (recordedPrefixController initialHistoryLength recorded)
      limits replayActor remaining.length replayState program
    ∃ pendingContinuation,
      replay.halt = .paused (.query chosen.input pendingContinuation) ∧
      queryAnswerTrace (historySince replayState replay.oracle) =
        queryAnswerTrace remaining := by
  induction remaining generalizing consumed sourceState replayState fuel program with
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
              cases queried : queryOracle controller limits sourceActor
                  sourceState input with
              | error reason => simp [runMachine, queried] at returned
              | ok pair =>
                  rcases pair with ⟨output, nextSource⟩
                  let tailRun := runMachine controller limits sourceActor fuel
                    nextSource (next output)
                  have outerOracle :
                      (runMachine controller limits sourceActor (fuel + 1)
                        sourceState (.query input next)).oracle =
                          tailRun.oracle := by
                    simp [tailRun, runMachine, queried]
                  have tailPrefix :
                      nextSource.history <+: tailRun.oracle.history :=
                    postfork_run_history_is_preserved controller limits
                      sourceActor fuel nextSource (next output)
                  obtain ⟨origin, firstDelta⟩ :=
                    query_success_history_cons_of_final_prefix controller
                      limits sourceActor sourceState nextSource tailRun.oracle
                      input output queried tailPrefix
                  have exactDecomposition :
                      ({ input := input, output := output,
                          actor := sourceActor, origin := origin } : QueryRecord) ::
                          historySince nextSource tailRun.oracle =
                        chosen :: after := by
                    simpa only [List.nil_append, outerOracle, firstDelta] using
                      decomposition
                  have inputEquality : input = chosen.input :=
                    congrArg QueryRecord.input
                      (List.cons.inj exactDecomposition).1
                  refine ⟨next, ?_, ?_⟩
                  · simp [runPrefix, inputEquality]
                  · simp [runPrefix, historySince, queryAnswerTrace]
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
              cases queried : queryOracle controller limits sourceActor
                  sourceState input with
              | error reason => simp [runMachine, queried] at returned
              | ok pair =>
                  rcases pair with ⟨output, nextSource⟩
                  let tailRun := runMachine controller limits sourceActor fuel
                    nextSource (next output)
                  have tailReturned : tailRun.halt = .returned result := by
                    simpa [tailRun, runMachine, queried] using returned
                  have outerOracle :
                      (runMachine controller limits sourceActor (fuel + 1)
                        sourceState (.query input next)).oracle =
                          tailRun.oracle := by
                    simp [tailRun, runMachine, queried]
                  have tailPrefix :
                      nextSource.history <+: tailRun.oracle.history :=
                    postfork_run_history_is_preserved controller limits
                      sourceActor fuel nextSource (next output)
                  obtain ⟨origin, firstDelta⟩ :=
                    query_success_history_cons_of_final_prefix controller
                      limits sourceActor sourceState nextSource tailRun.oracle
                      input output queried tailPrefix
                  let firstRecord : QueryRecord :=
                    { input := input, output := output,
                      actor := sourceActor, origin := origin }
                  have exactDecomposition :
                      firstRecord :: historySince nextSource tailRun.oracle =
                        head :: (tail ++ chosen :: after) := by
                    simpa only [List.cons_append, outerOracle, firstDelta,
                      firstRecord] using decomposition
                  have firstRecordEquality : firstRecord = head :=
                    (List.cons.inj exactDecomposition).1
                  have tailDecomposition :
                      historySince nextSource tailRun.oracle =
                        tail ++ chosen :: after :=
                    (List.cons.inj exactDecomposition).2
                  have sourceLength : sourceState.history.length =
                      initialHistoryLength + consumed.length := by
                    calc
                      sourceState.history.length = replayState.history.length :=
                        agreement.historyLength
                      _ = initialHistoryLength + consumed.length := replayLength
                  have sourceRecordedAnswer :
                      recordedPrefixController initialHistoryLength recorded
                          sourceState.history input = .answer output := by
                    unfold recordedPrefixController
                    simp [sourceLength, recordedExact, firstRecord,
                      ← firstRecordEquality]
                  have sourceRecordedQuery :
                      queryOracle
                          (recordedPrefixController initialHistoryLength recorded)
                          limits sourceActor sourceState input =
                            .ok (output, nextSource) := by
                    exact query_success_with_matching_controller
                      controller
                      (recordedPrefixController initialHistoryLength recorded)
                      limits sourceActor sourceState nextSource input output
                      queried sourceRecordedAnswer
                  obtain ⟨nextReplay, replayQueried, nextAgreement⟩ :=
                    recorded_prefix_query_actor_change initialHistoryLength
                      recorded limits sourceActor replayActor sourceState
                      replayState nextSource input output agreement
                      sourceRecordedQuery
                  have recursiveRecorded :
                      recorded = (consumed ++ [head]) ++ tail := by
                    simpa only [List.append_assoc, List.singleton_append] using
                      recordedExact
                  have nextReplayLength : nextReplay.history.length =
                      initialHistoryLength + (consumed ++ [head]).length := by
                    obtain ⟨replayRecord, replayHistory, _replayActor⟩ :=
                      query_oracle_success_appends_actor_record
                        (recordedPrefixController initialHistoryLength recorded)
                        limits replayActor replayState nextReplay input output
                        replayQueried
                    rw [replayHistory]
                    simp only [List.length_append, List.length_singleton]
                    rw [replayLength]
                    omega
                  obtain ⟨pendingContinuation, tailPaused, tailTrace⟩ :=
                    inductionHypothesis (consumed ++ [head]) nextSource
                      nextReplay fuel (next output) nextAgreement
                      recursiveRecorded nextReplayLength tailReturned
                      tailDecomposition
                  let replayController :=
                    recordedPrefixController initialHistoryLength recorded
                  let replayTail := runPrefix replayController limits replayActor
                    tail.length nextReplay (next output)
                  have replayTailTrace :
                      queryAnswerTrace
                          (historySince nextReplay replayTail.oracle) =
                        queryAnswerTrace tail := by
                    simpa [replayTail, replayController] using tailTrace
                  have replayTailPrefix :
                      nextReplay.history <+: replayTail.oracle.history :=
                    prefix_run_history_is_preserved replayController limits
                      replayActor tail.length nextReplay (next output)
                  obtain ⟨replayOrigin, replayDelta⟩ :=
                    query_success_history_cons_of_final_prefix
                      replayController limits replayActor replayState nextReplay
                      replayTail.oracle input output
                      (by simpa [replayController] using replayQueried)
                      replayTailPrefix
                  have replayOuterOracle :
                      (runPrefix replayController limits replayActor
                        (head :: tail).length replayState
                        (.query input next)).oracle = replayTail.oracle := by
                    simp [replayController, replayTail, runPrefix,
                      replayQueried]
                  refine ⟨pendingContinuation, ?_, ?_⟩
                  · simpa [replayController, replayTail, runPrefix,
                      replayQueried] using tailPaused
                  · rw [replayOuterOracle, replayDelta]
                    change (input, output) :: queryAnswerTrace
                        (historySince nextReplay replayTail.oracle) =
                      (head.input, head.output) :: queryAnswerTrace tail
                    rw [replayTailTrace]
                    simpa [firstRecord] using congrArg
                      (fun record : QueryRecord =>
                        (record.input, record.output)) firstRecordEquality

theorem returned_run_first_occurrence_replays_as_extractor
    {Result : Type*}
    (controller : AdaptiveController) (limits : OracleLimits)
    (sourceActor : QueryActor) (fuel : Nat) (state : OracleState)
    (program : OracleMachine Result) (result : Result)
    (occurrence : PairOccurrenceSplit)
    (returned :
      (runMachine controller limits sourceActor fuel state program).halt =
        .returned result)
    (decomposition :
      historySince state
          (runMachine controller limits sourceActor fuel state program).oracle =
        occurrence.before ++ occurrence.chosen :: occurrence.after) :
    let replay := runPrefix
      (recordedPrefixController state.history.length occurrence.before)
      limits .extractorReplay occurrence.before.length state program
    ∃ pendingContinuation,
      replay.halt =
        .paused (.query occurrence.chosen.input pendingContinuation) ∧
      queryAnswerTrace (historySince state replay.oracle) =
        queryAnswerTrace occurrence.before := by
  exact returned_run_replays_prefix_under_actor_change_aux controller limits
    sourceActor .extractorReplay state.history.length occurrence.before []
    occurrence.before state state fuel program result occurrence.chosen
    occurrence.after (oracle_core_agreement_refl state) (by simp) (by simp)
    returned decomposition

/-! ## Literal root request closure -/

theorem literal_root_squeeze_request_prepares_ready
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type u}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (runs : RootProjectedTotalizedRuns machine hidden runtime)
    (configuration : ConcreteRestorationConfiguration)
    (limitsExact : configuration.oracleLimits = machine.adversaryLimits)
    (transitionIndex : Nat)
    (transition : FutureFreeTransition)
    (transitionExact : verifierTransitionAt? runtime.node transitionIndex =
      some transition)
    (outputInput advanceInput : ShaInput)
    (pairExact : squeezePairInputsOfTransition transition =
      some (outputInput, advanceInput)) :
    ∃ prepared : PreparedConcreteRestoration Statement Proof Payload,
      prepareConcreteRestorationFromStartProgram
          (machine.blackBox.start hidden machine.observation) configuration
          (initialRestorationAccumulatorFromRoot runtime.node)
          { nodeId := 0, verifierTransitionIndex := transitionIndex } =
        .ready prepared := by
  rcases runs with ⟨adversarySteps, _verifierSteps, adversaryRun,
    _verifierRun⟩
  have returnedRun := run_machine_totalized_ok_reflects
    (rootAdversaryProjectedController runtime) machine.adversaryLimits
    .adversary machine.adversaryFuel emptyOracle
    (machine.blackBox.start hidden machine.observation)
    runtime.adversaryValue runtime.proverFinalOracle adversarySteps adversaryRun
  have returnedHalt :
      (runMachine (rootAdversaryProjectedController runtime)
        machine.adversaryLimits .adversary machine.adversaryFuel emptyOracle
        (machine.blackBox.start hidden machine.observation)).halt =
          .returned runtime.adversaryValue := by
    rw [returnedRun]
  cases occurrenceExact : firstEitherInputOccurrence outputInput advanceInput
      runtime.node.proverHistory with
  | none =>
      let prepared : PreparedConcreteRestoration Statement Proof Payload :=
        { request :=
            { nodeId := 0, verifierTransitionIndex := transitionIndex }
          parentNode := runtime.node
          transition := transition
          restoredState := restoreIndexedTransition transition
          outputInput := outputInput
          advanceInput := advanceInput
          occurrence := none
          prefixRun := none
          programmingBase := runtime.node.proverFinalOracle
          prefixSteps := 0 }
      refine ⟨prepared, ?_⟩
      simp [prepareConcreteRestorationFromStartProgram,
        ConcreteRestorationAccumulator.node?,
        initialRestorationAccumulatorFromRoot, transitionExact, pairExact,
        occurrenceExact, prepared]
  | some occurrence =>
      have occurrenceSpec := first_either_input_occurrence_spec outputInput
        advanceInput runtime.node.proverHistory occurrence occurrenceExact
      have occurrenceDecomposition :
          historySince emptyOracle
              (runMachine (rootAdversaryProjectedController runtime)
                machine.adversaryLimits .adversary machine.adversaryFuel
                emptyOracle
                (machine.blackBox.start hidden machine.observation)).oracle =
            occurrence.before ++ occurrence.chosen :: occurrence.after := by
        rw [returnedRun]
        simpa [SchedulerNativePlainRomRootRuntime.node,
          ConcreteRestorationNode.proverHistory] using occurrenceSpec.1
      have replay := returned_run_first_occurrence_replays_as_extractor
        (rootAdversaryProjectedController runtime) machine.adversaryLimits
        .adversary machine.adversaryFuel emptyOracle
        (machine.blackBox.start hidden machine.observation)
        runtime.adversaryValue occurrence returnedHalt occurrenceDecomposition
      rcases replay with ⟨pendingContinuation, prefixPaused, prefixTrace⟩
      let prefixRun := runPrefix
        (recordedPrefixController emptyOracle.history.length occurrence.before)
        machine.adversaryLimits .extractorReplay occurrence.before.length
        emptyOracle (machine.blackBox.start hidden machine.observation)
      let prepared : PreparedConcreteRestoration Statement Proof Payload :=
        { request :=
            { nodeId := 0, verifierTransitionIndex := transitionIndex }
          parentNode := runtime.node
          transition := transition
          restoredState := restoreIndexedTransition transition
          outputInput := outputInput
          advanceInput := advanceInput
          occurrence := some occurrence
          prefixRun := some prefixRun
          programmingBase := prefixRun.oracle
          prefixSteps := prefixRun.steps }
      have rootEntry : runtime.node.proverEntryOracle = emptyOracle := rfl
      refine ⟨prepared, ?_⟩
      simp only [prepareConcreteRestorationFromStartProgram,
        ConcreteRestorationAccumulator.node?,
        initialRestorationAccumulatorFromRoot, List.getElem?_cons_zero,
        transitionExact, pairExact, occurrenceExact]
      rw [limitsExact]
      simp [rootEntry, prefixRun, prefixPaused, prefixTrace, prepared]

#print axioms recorded_prefix_query_actor_change
#print axioms returned_run_first_occurrence_replays_as_extractor
#print axioms literal_root_squeeze_request_prepares_ready

end

end AspisK1.V7Tag73RootSqueezePreparationClosure
