import AspisFormal.K1.V7Tag73OperationalNodeCertificate
import AspisFormal.K1.V7Tag73SchedulerProjectedTraceSafety
import AspisFormal.K1.V7Tag73CompletedFullRunProjection

/-!
# Concrete-client induction over the actual scheduler trace

This module proves the scheduler-native, partial-run safety theorem needed by
the Tag-73 plain-ROM experiment.  It follows the executable restoration client
itself.  At a successful request it records the actual adjacent pair sampled by
the scheduler, then the actual fresh prover and verifier slices, and constructs
one `ProjectedRestorationNodeExecution` for the node appended by that exact
callback path.

The theorem is intentionally independent of scheduler completion: every child
that is actually emitted is certified.  Completion, restoration-fuel
exhaustion, and global resource failure remain separate terminal facts.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ConcreteRestorationTraceInduction

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73AtomicPairReplay
open AspisK1.V7Tag73AtomicPairFork
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73ProjectedMachinePrefix
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73RawStrictReplacementSuffix
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73SchedulerProjectedTraceSafety
open AspisK1.V7Tag73OperationalNodeCertificate
open AspisK1.V7Tag73CompletedFullRunProjection

noncomputable section

universe u

/-- A ready preparation necessarily selected an existing parent node.  This
small eliminator is sufficient to transport that immutable lookup through the
append-only child insertion. -/
theorem ready_preparation_has_selected_parent
    {Statement Proof Payload : Type u}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (configuration : ConcreteRestorationConfiguration)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (request : ConcreteRestorationRequest)
    (prepared : PreparedConcreteRestoration Statement Proof Payload)
    (ready : prepareConcreteRestorationFromStartProgram startProgram
      configuration accumulator request = .ready prepared) :
    ∃ parent, accumulator.node? request.nodeId = some parent := by
  cases selected : accumulator.node? request.nodeId with
  | none =>
      simp [prepareConcreteRestorationFromStartProgram, selected] at ready
  | some parent => exact ⟨parent, rfl⟩

/-- The request stored in a successful preparation is the literal request
passed to the deterministic preparation program.  This is an inversion fact
about the executable preparer, not an extra well-formedness premise. -/
theorem ready_preparation_request_exact
    {Statement Proof Payload : Type u}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (configuration : ConcreteRestorationConfiguration)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (request : ConcreteRestorationRequest)
    (prepared : PreparedConcreteRestoration Statement Proof Payload)
    (ready : prepareConcreteRestorationFromStartProgram startProgram
      configuration accumulator request = .ready prepared) :
    prepared.request = request := by
  cases selectedNode : accumulator.node? request.nodeId with
  | none =>
      simp [prepareConcreteRestorationFromStartProgram, selectedNode] at ready
  | some parentNode =>
      cases selectedTransition : verifierTransitionAt? parentNode
          request.verifierTransitionIndex with
      | none =>
          simp [prepareConcreteRestorationFromStartProgram, selectedNode,
            selectedTransition] at ready
      | some transition =>
          cases selectedPair : squeezePairInputsOfTransition transition with
          | none =>
              simp [prepareConcreteRestorationFromStartProgram, selectedNode,
                selectedTransition, selectedPair] at ready
          | some pair =>
              rcases pair with ⟨outputInput, advanceInput⟩
              cases selectedOccurrence : firstEitherInputOccurrence outputInput
                  advanceInput parentNode.proverHistory with
              | none =>
                  simp [prepareConcreteRestorationFromStartProgram,
                    selectedNode, selectedTransition, selectedPair,
                    selectedOccurrence] at ready
                  subst prepared
                  rfl
              | some occurrence =>
                  let prefixRun := runPrefix
                    (recordedPrefixController
                      parentNode.proverEntryOracle.history.length
                      occurrence.before)
                    configuration.oracleLimits .extractorReplay
                    occurrence.before.length parentNode.proverEntryOracle
                    startProgram
                  cases halted : prefixRun.halt with
                  | returned result =>
                      simp [prepareConcreteRestorationFromStartProgram,
                        selectedNode, selectedTransition, selectedPair,
                        selectedOccurrence, prefixRun, halted] at ready
                  | oracleAbort reason =>
                      simp [prepareConcreteRestorationFromStartProgram,
                        selectedNode, selectedTransition, selectedPair,
                        selectedOccurrence, prefixRun, halted] at ready
                  | paused residual =>
                      cases residual with
                      | pure result =>
                          simp [prepareConcreteRestorationFromStartProgram,
                            selectedNode, selectedTransition, selectedPair,
                            selectedOccurrence, prefixRun, halted] at ready
                      | abort reason =>
                          simp [prepareConcreteRestorationFromStartProgram,
                            selectedNode, selectedTransition, selectedPair,
                            selectedOccurrence, prefixRun, halted] at ready
                      | query pendingInput next =>
                          by_cases pendingMismatch :
                              pendingInput ≠ occurrence.chosen.input
                          · simp [prepareConcreteRestorationFromStartProgram,
                              selectedNode, selectedTransition, selectedPair,
                              selectedOccurrence, prefixRun, halted,
                              pendingMismatch] at ready
                          · by_cases traceMismatch : queryAnswerTrace
                                (historySince parentNode.proverEntryOracle
                                  prefixRun.oracle) ≠
                                queryAnswerTrace occurrence.before
                            · simp [prepareConcreteRestorationFromStartProgram,
                                selectedNode, selectedTransition, selectedPair,
                                selectedOccurrence, prefixRun, halted,
                                pendingMismatch, traceMismatch] at ready
                            · simp [prepareConcreteRestorationFromStartProgram,
                                selectedNode, selectedTransition, selectedPair,
                                selectedOccurrence, prefixRun, halted,
                                pendingMismatch, traceMismatch] at ready
                              subst prepared
                              rfl

/-- Re-index a normally returned projected prefix by exactly the answers it
consumed.  The scheduler callback also carries an unused future suffix; node
certificates deliberately forget that suffix so they cannot depend on future
tape coordinates. -/
def consumedProjectedMachinePrefix
    {Result : Type u} {limits : OracleLimits} {actor : QueryActor}
    {fuel : Nat} {state : OracleState} {program : OracleMachine Result}
    {available : List Digest256}
    (returned : ProjectedMachinePrefixReturned limits actor fuel state program
      available) :
    ProjectedMachinePrefixReturned limits actor fuel state program
      (returned.freshQueries.map Prod.snd) where
  result := returned.result
  finalState := returned.finalState
  finalCoherent := returned.finalCoherent
  steps := returned.steps
  freshQueries := returned.freshQueries
  remaining := []
  availableExact := by simp
  trace := returned.trace

/-- Static traced safety of all continuations, parameterized by the exact trace
and operational accumulator present at the current recursive client call. -/
def ConcreteClientPreservesEveryNodeOperational
    {Statement Proof Payload Result : Type u}
    {globalOracleCalls : Nat}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (cursor : SchedulerNativeCursor globalOracleCalls
      (ConcreteRestorationClientRun Statement Proof Payload Result)) : Prop :=
  ∀ trace,
    EveryNodeOperational
        (Final := ConcreteRestorationClientRun Statement Proof Payload Result)
        startProgram environment configuration trace accumulator →
      SchedulerNativeCursorAllProjectedTracedReturned
        (fun run suffix =>
          EveryNodeOperational
            (Final := ConcreteRestorationClientRun Statement Proof Payload Result)
            startProgram environment configuration (trace ++ suffix)
              run.accumulator)
        cursor

/-- Failure bookkeeping produces no scheduler exposure and changes no node. -/
theorem failure_continuation_preserves_every_node_operational
    {Statement Proof Payload Result : Type u}
    {globalOracleCalls : Nat}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (resume : ConcreteRestorationReply →
      ConcreteRestorationAccumulator Statement Proof Payload →
        SchedulerNativeCursor globalOracleCalls
          (ConcreteRestorationClientRun Statement Proof Payload Result))
    (continuations : ∀ reply nextAccumulator,
      ConcreteClientPreservesEveryNodeOperational startProgram environment
        configuration nextAccumulator (resume reply nextAccumulator))
    (request : ConcreteRestorationRequest)
    (reason : ConcreteRestorationFailure)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload) :
    ConcreteClientPreservesEveryNodeOperational startProgram environment
      configuration accumulator
      (resume (.failed reason) (accumulator.addFailure request reason)) := by
  intro trace invariant
  exact continuations (.failed reason) (accumulator.addFailure request reason)
    trace (by simpa using
      (every_node_operational_add_failure startProgram environment
        configuration trace [] accumulator request reason invariant))

/-- The actual one-request dispatcher preserves operational certificates over
the exact trace emitted by its scheduler callbacks. -/
theorem dispatch_one_concrete_restoration_preserves_operational_trace
    {Statement Proof Payload Result : Type u}
    {globalOracleCalls : Nat}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (request : ConcreteRestorationRequest)
    (resume : ConcreteRestorationReply →
      ConcreteRestorationAccumulator Statement Proof Payload →
        SchedulerNativeCursor globalOracleCalls
          (ConcreteRestorationClientRun Statement Proof Payload Result))
    (continuations : ∀ reply nextAccumulator,
      ConcreteClientPreservesEveryNodeOperational startProgram environment
        configuration nextAccumulator (resume reply nextAccumulator)) :
    ConcreteClientPreservesEveryNodeOperational startProgram environment
      configuration accumulator
      (dispatchOneConcreteRestoration startProgram environment configuration
        accumulator request resume) := by
  intro trace invariant
  have failureSafe : ∀ failureRequest reason nextAccumulator,
      EveryNodeOperational
        (Final := ConcreteRestorationClientRun Statement Proof Payload Result)
        startProgram environment configuration trace nextAccumulator →
      SchedulerNativeCursorAllProjectedTracedReturned
        (fun run suffix => EveryNodeOperational
          (Final := ConcreteRestorationClientRun Statement Proof Payload Result)
          startProgram environment configuration (trace ++ suffix)
            run.accumulator)
        (resume (.failed reason)
          (nextAccumulator.addFailure failureRequest reason)) := by
    intro failureRequest reason nextAccumulator nextInvariant
    exact continuations (.failed reason)
      (nextAccumulator.addFailure failureRequest reason) trace
      (by simpa using
        (every_node_operational_add_failure startProgram environment configuration
          trace [] nextAccumulator failureRequest reason nextInvariant))
  generalize preparationExact :
    prepareConcreteRestorationFromStartProgram startProgram configuration
      accumulator request = preparation
  cases preparation with
  | failed reason prefixSteps prefixRestarts =>
      simp only [dispatchOneConcreteRestoration, dispatchConcreteRestoration,
        preparationExact]
      apply failureSafe request reason
      simpa using
        (every_node_operational_add_charges startProgram environment
          configuration trace [] accumulator
            [.prefixReplayQueries prefixSteps, .restart prefixRestarts] invariant)
  | ready prepared =>
      have inputExact := prepare_from_start_ready_pair_inputs_exact startProgram
        configuration accumulator request prepared preparationExact
      have inputStateExact := squeeze_pair_inputs_exact_give_input_state
        prepared.transition prepared.outputInput prepared.advanceInput inputExact
      let prefixRestarts := if prepared.prefixRun.isSome then 1 else 0
      let withPrefix := accumulator.addCharges
        [.prefixReplayQueries prepared.prefixSteps, .restart prefixRestarts]
      have withPrefixInvariant : EveryNodeOperational
          (Final := ConcreteRestorationClientRun Statement Proof Payload Result)
          startProgram environment configuration trace withPrefix := by
        simpa [withPrefix] using
          (every_node_operational_add_charges startProgram environment
            configuration trace [] accumulator
              [.prefixReplayQueries prepared.prefixSteps,
                .restart prefixRestarts] invariant)
      simp only [dispatchOneConcreteRestoration, dispatchConcreteRestoration,
        preparationExact]
      unfold dispatchPreparedRestoration
      by_cases prefixCoherent : HistoryTotalCoherent prepared.programmingBase
      next =>
        simp only [prefixCoherent, if_pos]
        by_cases globalLimit :
            configuration.oracleLimits.totalCalls ≤ globalOracleCalls
        next =>
          simp only [globalLimit, if_pos]
          by_cases pairRoom : prepared.programmingBase.history.length + 2 ≤
              globalOracleCalls
          next =>
            simp only [pairRoom, if_pos]
            apply SchedulerNativeCursorAllProjectedTracedReturned.forkPair
            intro scheduled frozenExact outputExact advanceExact templateExact
            have pairRecordsExact :
                [.forkOutput prepared.programmingBase.history
                    prepared.outputInput prepared.advanceInput
                    (canonicalForkTemplate configuration) scheduled.forkOutput,
                  .forkAdvance scheduled] = scheduledPairRecords scheduled := by
              simp [scheduledPairRecords, frozenExact, outputExact,
                advanceExact, templateExact]
            let pairTrace := trace ++ scheduledPairRecords scheduled
            let afterCoordinates := withPrefix.addCharges
              [.forkUniformCoordinates 2]
            cases programmed : programConcretePair configuration.oracleLimits
                configuration.pairProgrammingOrder prepared.programmingBase
                prepared.outputInput prepared.advanceInput
                scheduled.configuration.forkOutput
                scheduled.configuration.forkAdvance with
            | failed reason inserted =>
                simp only [programmed]
                have failedInvariant : EveryNodeOperational
                    (Final := ConcreteRestorationClientRun Statement Proof Payload
                      Result)
                    startProgram environment configuration pairTrace
                      ((afterCoordinates.addCharges
                        [.programmedPoints inserted]).addFailure prepared.request
                          reason) := by
                  have unchanged :
                      (afterCoordinates.addCharges
                        [.programmedPoints inserted]).nodes = accumulator.nodes :=
                    rfl
                  have beforeFailure := every_node_operational_of_nodes_eq
                    startProgram environment configuration trace
                    (scheduledPairRecords scheduled) accumulator
                    (afterCoordinates.addCharges [.programmedPoints inserted])
                    unchanged invariant
                  simpa [pairTrace] using
                    (every_node_operational_add_failure startProgram environment
                      configuration pairTrace []
                        (afterCoordinates.addCharges [.programmedPoints inserted])
                        prepared.request reason (by simpa [pairTrace] using
                          beforeFailure))
                change SchedulerNativeCursorAllProjectedTracedReturned _
                  (resume (.failed reason)
                    ((afterCoordinates.addCharges
                      [.programmedPoints inserted]).addFailure prepared.request
                        reason))
                simpa [pairTrace, pairRecordsExact, List.append_assoc] using
                  (continuations (.failed reason)
                    ((afterCoordinates.addCharges
                      [.programmedPoints inserted]).addFailure prepared.request
                        reason) pairTrace failedInvariant)
            | ready afterBoth =>
                simp only [programmed]
                let afterProgramming := afterCoordinates.addCharges
                  [.programmedPoints 2]
                by_cases afterCoherent : HistoryTotalCoherent afterBoth
                next =>
                  simp only [afterCoherent, if_pos]
                  by_cases proverRoom : StageHasOracleRoom
                      configuration.oracleLimits afterBoth
                      configuration.proverReplayFuel
                  next =>
                    simp only [proverRoom, if_pos]
                    let atProverStart := afterProgramming.addCharges [.restart 1]
                    apply SchedulerNativeCursorAllProjectedTracedReturned.machine
                    intro available proverPrefix
                    let proverRecords := projectedMachineFreshRecords
                      (.extractorReplay) proverPrefix.freshQueries
                    let proverTrace := pairTrace ++ proverRecords
                    cases proverStageExact : proverPrefix.result with
                    | completed proverResult =>
                      simp only [proverStageExact]
                      let proverQueries :=
                        (historySince afterBoth proverPrefix.finalState).length
                      let afterProver := atProverStart.addCharges
                        [.completeFromStartQueries proverQueries]
                      cases proverResult with
                      | error failure =>
                        cases failure with
                        | oracleAbort reason =>
                          have failedInvariant : EveryNodeOperational
                              (Final := ConcreteRestorationClientRun Statement
                                Proof Payload Result)
                              startProgram environment configuration proverTrace
                                (afterProver.addFailure prepared.request
                                  (.proverReplayAbort reason)) := by
                            have unchanged : afterProver.nodes = accumulator.nodes :=
                              rfl
                            have beforeFailure :=
                              every_node_operational_of_nodes_eq startProgram
                                environment configuration trace
                                (scheduledPairRecords scheduled ++ proverRecords)
                                accumulator afterProver unchanged invariant
                            simpa [pairTrace, proverTrace, List.append_assoc] using
                              (every_node_operational_add_failure startProgram
                                environment configuration proverTrace [] afterProver
                                prepared.request (.proverReplayAbort reason) (by
                                  simpa [pairTrace, proverTrace,
                                    List.append_assoc] using beforeFailure))
                          change SchedulerNativeCursorAllProjectedTracedReturned _
                            (resume (.failed (.proverReplayAbort reason))
                              (afterProver.addFailure prepared.request
                                (.proverReplayAbort reason)))
                          simpa [pairTrace, proverTrace, pairRecordsExact,
                            List.append_assoc] using
                            (continuations
                              (.failed (.proverReplayAbort reason))
                              (afterProver.addFailure prepared.request
                                (.proverReplayAbort reason)) proverTrace
                                  failedInvariant)
                        | timeout =>
                          have failedInvariant : EveryNodeOperational
                              (Final := ConcreteRestorationClientRun Statement
                                Proof Payload Result)
                              startProgram environment configuration proverTrace
                                (afterProver.addFailure prepared.request
                                  .proverReplayTimeout) := by
                            have unchanged : afterProver.nodes = accumulator.nodes :=
                              rfl
                            have beforeFailure :=
                              every_node_operational_of_nodes_eq startProgram
                                environment configuration trace
                                (scheduledPairRecords scheduled ++ proverRecords)
                                accumulator afterProver unchanged invariant
                            simpa [pairTrace, proverTrace, List.append_assoc] using
                              (every_node_operational_add_failure startProgram
                                environment configuration proverTrace [] afterProver
                                prepared.request .proverReplayTimeout (by
                                  simpa [pairTrace, proverTrace,
                                    List.append_assoc] using beforeFailure))
                          change SchedulerNativeCursorAllProjectedTracedReturned _
                            (resume (.failed .proverReplayTimeout)
                              (afterProver.addFailure prepared.request
                                .proverReplayTimeout))
                          simpa [pairTrace, proverTrace, pairRecordsExact,
                            List.append_assoc] using
                            (continuations (.failed .proverReplayTimeout)
                              (afterProver.addFailure prepared.request
                                .proverReplayTimeout) proverTrace failedInvariant)
                      | ok adversaryValue =>
                        simp only
                        by_cases bindingMismatch :
                            FixedBindings.ofContext
                                adversaryValue.rawMessages.context ≠
                              prepared.restoredState.current.bindings
                        next =>
                          rw [dif_pos bindingMismatch]
                          have failedInvariant : EveryNodeOperational
                              (Final := ConcreteRestorationClientRun Statement
                                Proof Payload Result)
                              startProgram environment configuration proverTrace
                                (afterProver.addFailure prepared.request
                                  .restoredBindingMismatch) := by
                            have unchanged : afterProver.nodes = accumulator.nodes :=
                              rfl
                            have beforeFailure :=
                              every_node_operational_of_nodes_eq startProgram
                                environment configuration trace
                                (scheduledPairRecords scheduled ++ proverRecords)
                                accumulator afterProver unchanged invariant
                            simpa [pairTrace, proverTrace, List.append_assoc] using
                              (every_node_operational_add_failure startProgram
                                environment configuration proverTrace [] afterProver
                                prepared.request .restoredBindingMismatch (by
                                  simpa [pairTrace, proverTrace,
                                    List.append_assoc] using beforeFailure))
                          change SchedulerNativeCursorAllProjectedTracedReturned _
                            (resume (.failed .restoredBindingMismatch)
                              (afterProver.addFailure prepared.request
                                .restoredBindingMismatch))
                          simpa [pairTrace, proverTrace, pairRecordsExact,
                            List.append_assoc] using
                            (continuations (.failed .restoredBindingMismatch)
                              (afterProver.addFailure prepared.request
                                .restoredBindingMismatch) proverTrace
                                  failedInvariant)
                        next =>
                          rw [dif_neg bindingMismatch]
                          have bindingExact :
                              FixedBindings.ofContext
                                  adversaryValue.rawMessages.context =
                                prepared.restoredState.current.bindings :=
                            Classical.not_not.mp bindingMismatch
                          by_cases verifierRoom : StageHasOracleRoom
                              configuration.oracleLimits proverPrefix.finalState
                              configuration.verifierFuel
                          next =>
                            simp only [verifierRoom, if_pos]
                            apply
                              SchedulerNativeCursorAllProjectedTracedReturned.machine
                            intro verifierAvailable verifierPrefix
                            let verifierRecords := projectedMachineFreshRecords
                              (.verifier) verifierPrefix.freshQueries
                            let verifierTrace := proverTrace ++ verifierRecords
                            cases verifierStageExact : verifierPrefix.result with
                            | completed verifierResult =>
                              simp only [verifierStageExact]
                              let verifierQueries :=
                                (historySince proverPrefix.finalState
                                  verifierPrefix.finalState).length
                              let afterVerifier := afterProver.addCharges
                                [.verifierSuffixQueries verifierQueries]
                              cases verifierResult with
                              | error failure =>
                                cases failure with
                                | oracleAbort reason =>
                                  have failedInvariant : EveryNodeOperational
                                      (Final := ConcreteRestorationClientRun
                                        Statement Proof Payload Result)
                                      startProgram environment configuration
                                        verifierTrace
                                        (afterVerifier.addFailure prepared.request
                                          (.verifierSuffixAbort reason)) := by
                                    have unchanged : afterVerifier.nodes =
                                        accumulator.nodes := rfl
                                    have beforeFailure :=
                                      every_node_operational_of_nodes_eq startProgram
                                        environment configuration trace
                                        (scheduledPairRecords scheduled ++
                                          proverRecords ++ verifierRecords)
                                        accumulator afterVerifier unchanged
                                          invariant
                                    simpa [pairTrace, proverTrace, verifierTrace,
                                      List.append_assoc] using
                                      (every_node_operational_add_failure
                                        startProgram environment configuration
                                        verifierTrace [] afterVerifier
                                        prepared.request
                                        (.verifierSuffixAbort reason) (by
                                          simpa [pairTrace, proverTrace,
                                            verifierTrace, List.append_assoc]
                                            using beforeFailure))
                                  change
                                    SchedulerNativeCursorAllProjectedTracedReturned _
                                      (resume
                                        (.failed (.verifierSuffixAbort reason))
                                        (afterVerifier.addFailure prepared.request
                                          (.verifierSuffixAbort reason)))
                                  simpa [pairTrace, proverTrace, verifierTrace,
                                    pairRecordsExact, List.append_assoc] using
                                    (continuations
                                      (.failed (.verifierSuffixAbort reason))
                                      (afterVerifier.addFailure prepared.request
                                        (.verifierSuffixAbort reason))
                                      verifierTrace failedInvariant)
                                | timeout =>
                                  have failedInvariant : EveryNodeOperational
                                      (Final := ConcreteRestorationClientRun
                                        Statement Proof Payload Result)
                                      startProgram environment configuration
                                        verifierTrace
                                        (afterVerifier.addFailure prepared.request
                                          .verifierSuffixTimeout) := by
                                    have unchanged : afterVerifier.nodes =
                                        accumulator.nodes := rfl
                                    have beforeFailure :=
                                      every_node_operational_of_nodes_eq startProgram
                                        environment configuration trace
                                        (scheduledPairRecords scheduled ++
                                          proverRecords ++ verifierRecords)
                                        accumulator afterVerifier unchanged
                                          invariant
                                    simpa [pairTrace, proverTrace, verifierTrace,
                                      List.append_assoc] using
                                      (every_node_operational_add_failure
                                        startProgram environment configuration
                                        verifierTrace [] afterVerifier
                                        prepared.request .verifierSuffixTimeout (by
                                          simpa [pairTrace, proverTrace,
                                            verifierTrace, List.append_assoc]
                                            using beforeFailure))
                                  change
                                    SchedulerNativeCursorAllProjectedTracedReturned _
                                      (resume (.failed .verifierSuffixTimeout)
                                        (afterVerifier.addFailure prepared.request
                                          .verifierSuffixTimeout))
                                  simpa [pairTrace, proverTrace, verifierTrace,
                                    pairRecordsExact, List.append_assoc] using
                                    (continuations
                                      (.failed .verifierSuffixTimeout)
                                      (afterVerifier.addFailure prepared.request
                                        .verifierSuffixTimeout) verifierTrace
                                          failedInvariant)
                              | ok verifierFinalState =>
                                let transitionCount :=
                                  verifierFinalState.transitions.length
                                let node : ConcreteRestorationNode Statement Proof
                                    Payload :=
                                  { parentRequest := some prepared.request
                                    adversaryValue := adversaryValue
                                    proverEntryOracle := afterBoth
                                    proverFinalOracle := proverPrefix.finalState
                                    verifierEntryOracle := proverPrefix.finalState
                                    verifierFinalOracle := verifierPrefix.finalState
                                    verifierEntryState := prepared.restoredState
                                    verifierFinalState := verifierFinalState }
                                let charged := afterVerifier.addCharges
                                  [.verifierTransitions transitionCount]
                                let added := charged.addNode node
                                have preparedRequestExact :=
                                  ready_preparation_request_exact startProgram
                                    configuration accumulator request prepared
                                      preparationExact
                                have selectedParent :=
                                  (prepare_concrete_restoration_ready_selection_exact
                                    startProgram configuration accumulator request
                                      prepared preparationExact).1
                                have selectedExact : added.2.node?
                                    prepared.request.nodeId =
                                    accumulator.node? prepared.request.nodeId := by
                                  have chargedSelected : charged.node?
                                      prepared.request.nodeId =
                                        some prepared.parentNode := by
                                    change accumulator.node?
                                      prepared.request.nodeId =
                                        some prepared.parentNode
                                    exact selectedParent
                                  calc
                                    added.2.node? prepared.request.nodeId =
                                        some prepared.parentNode :=
                                      node_lookup_preserved_by_add_node charged
                                        node prepared.parentNode
                                          prepared.request.nodeId chargedSelected
                                    _ = accumulator.node?
                                        prepared.request.nodeId :=
                                      selectedParent.symm
                                have preparationAtAdded :
                                    prepareConcreteRestorationFromStartProgram
                                      startProgram configuration added.2
                                        prepared.request = .ready prepared := by
                                  rw [prepare_from_start_eq_of_node_lookup_eq
                                    startProgram configuration added.2 accumulator
                                    prepared.request selectedExact]
                                  simpa [preparedRequestExact] using preparationExact
                                let proverPrefixConsumed :
                                    ProjectedMachinePrefixReturned
                                      configuration.oracleLimits .extractorReplay
                                      configuration.proverReplayFuel afterBoth
                                      (schedulerStageProgram
                                        (ConcreteRestorationClientRun Statement
                                          Proof Payload Result)
                                        (totalizeOracleMachine
                                          configuration.proverReplayFuel
                                          startProgram))
                                      (machineFreshAnswers proverRecords) :=
                                  { result := proverPrefix.result
                                    finalState := proverPrefix.finalState
                                    finalCoherent := proverPrefix.finalCoherent
                                    steps := proverPrefix.steps
                                    freshQueries := proverPrefix.freshQueries
                                    remaining := []
                                    availableExact := by simp [proverRecords]
                                    trace := proverPrefix.trace }
                                let verifierPrefixConsumed :
                                    ProjectedMachinePrefixReturned
                                      configuration.oracleLimits .verifier
                                      configuration.verifierFuel
                                      proverPrefix.finalState
                                      (schedulerStageProgram
                                        (ConcreteRestorationClientRun Statement
                                          Proof Payload Result)
                                        (totalizeOracleMachine
                                          configuration.verifierFuel
                                          (driveRawFutureFree environment
                                            adversaryValue.rawMessages
                                            configuration.driverFuel
                                            prepared.restoredState)))
                                      (machineFreshAnswers verifierRecords) :=
                                  { result := verifierPrefix.result
                                    finalState := verifierPrefix.finalState
                                    finalCoherent := verifierPrefix.finalCoherent
                                    steps := verifierPrefix.steps
                                    freshQueries := verifierPrefix.freshQueries
                                    remaining := []
                                    availableExact := by simp [verifierRecords]
                                    trace := verifierPrefix.trace }
                                have childExecution :
                                    ProjectedRestorationNodeExecution
                                      (Final := ConcreteRestorationClientRun
                                        Statement Proof Payload Result)
                                      startProgram environment configuration
                                        verifierTrace added.2 node := by
                                  refine
                                    { prepared := prepared
                                      preparationExact := preparationAtAdded
                                      parentRequestExact := rfl
                                      restoredEntryExact := rfl
                                      traceBeforePair := trace
                                      proverRecords := proverRecords
                                      verifierRecords := verifierRecords
                                      traceAfterVerifier := []
                                      scheduled := scheduled
                                      scheduledFrozenHistoryExact := frozenExact
                                      scheduledOutputInputExact := outputExact
                                      scheduledAdvanceInputExact := advanceExact
                                      scheduledTemplateExact := templateExact
                                      scheduledInputStateExact := ?_
                                      fullTraceExact := ?_
                                      programmingExact := programmed
                                      proverPrefix := proverPrefixConsumed
                                      proverRecordsOnly := ?_
                                      proverQueriesExact := ?_
                                      proverReturned := by
                                        simpa [proverPrefixConsumed, node]
                                          using proverStageExact
                                      proverFinalExact := by
                                        simp [proverPrefixConsumed, node]
                                      verifierEntryOracleExact := rfl
                                      restoredBindingExact := bindingExact
                                      verifierPrefix := verifierPrefixConsumed
                                      verifierRecordsOnly := ?_
                                      verifierQueriesExact := ?_
                                      verifierReturned := by
                                        simpa [verifierPrefixConsumed, node]
                                          using verifierStageExact
                                      verifierFinalExact := by
                                        simp [verifierPrefixConsumed, node] }
                                  · exact ⟨outputExact.trans inputStateExact.1,
                                      advanceExact.trans inputStateExact.2⟩
                                  · simp [verifierTrace, proverTrace, pairTrace,
                                      proverRecords, verifierRecords,
                                      List.append_assoc]
                                  · exact only_machine_fresh_actor_projected_records
                                      .extractorReplay proverPrefix.freshQueries
                                  · exact
                                      machine_fresh_query_answers_projected_records
                                        .extractorReplay proverPrefix.freshQueries
                                  · exact only_machine_fresh_actor_projected_records
                                      .verifier verifierPrefix.freshQueries
                                  · exact
                                      machine_fresh_query_answers_projected_records
                                        .verifier verifierPrefix.freshQueries
                                have chargedInvariant : EveryNodeOperational
                                    (Final := ConcreteRestorationClientRun
                                      Statement Proof Payload Result)
                                    startProgram environment configuration
                                      verifierTrace charged := by
                                  have unchanged : charged.nodes =
                                      accumulator.nodes := rfl
                                  have transported :=
                                    every_node_operational_of_nodes_eq startProgram
                                      environment configuration trace
                                      (scheduledPairRecords scheduled ++
                                        proverRecords ++ verifierRecords)
                                      accumulator charged unchanged invariant
                                  simpa [pairTrace, proverTrace, verifierTrace,
                                    List.append_assoc] using transported
                                have addedInvariant : EveryNodeOperational
                                    (Final := ConcreteRestorationClientRun
                                      Statement Proof Payload Result)
                                    startProgram environment configuration
                                      verifierTrace added.2 := by
                                  simpa using
                                    (every_node_operational_add_certified_node
                                      startProgram environment configuration
                                      verifierTrace [] charged node chargedInvariant
                                        (by simpa using childExecution))
                                simpa [pairTrace, proverTrace, verifierTrace,
                                  pairRecordsExact, List.append_assoc] using
                                  (continuations (.added added.1) added.2
                                    verifierTrace addedInvariant)
                          next =>
                            simp only [verifierRoom, if_neg]
                            have failedInvariant : EveryNodeOperational
                                (Final := ConcreteRestorationClientRun Statement
                                  Proof Payload Result)
                                startProgram environment configuration proverTrace
                                  (afterProver.addFailure prepared.request
                                    .verifierSuffixRoom) := by
                              have unchanged : afterProver.nodes = accumulator.nodes :=
                                rfl
                              have beforeFailure :=
                                every_node_operational_of_nodes_eq startProgram
                                  environment configuration trace
                                  (scheduledPairRecords scheduled ++ proverRecords)
                                  accumulator afterProver unchanged invariant
                              simpa [pairTrace, proverTrace, List.append_assoc] using
                                (every_node_operational_add_failure startProgram
                                  environment configuration proverTrace [] afterProver
                                  prepared.request .verifierSuffixRoom (by
                                    simpa [pairTrace, proverTrace,
                                      List.append_assoc] using beforeFailure))
                            change SchedulerNativeCursorAllProjectedTracedReturned _
                              (resume (.failed .verifierSuffixRoom)
                                (afterProver.addFailure prepared.request
                                  .verifierSuffixRoom))
                            simpa [pairTrace, proverTrace, pairRecordsExact,
                              List.append_assoc] using
                              (continuations (.failed .verifierSuffixRoom)
                                (afterProver.addFailure prepared.request
                                  .verifierSuffixRoom) proverTrace
                                    failedInvariant)
                  next =>
                    simp only [proverRoom, if_neg]
                    have failedInvariant : EveryNodeOperational
                        (Final := ConcreteRestorationClientRun Statement Proof
                          Payload Result)
                        startProgram environment configuration pairTrace
                          (afterProgramming.addFailure prepared.request
                            .proverReplayRoom) := by
                      have unchanged : afterProgramming.nodes = accumulator.nodes :=
                        rfl
                      have beforeFailure := every_node_operational_of_nodes_eq
                        startProgram environment configuration trace
                          (scheduledPairRecords scheduled) accumulator
                            afterProgramming unchanged invariant
                      simpa [pairTrace] using
                        (every_node_operational_add_failure startProgram environment
                          configuration pairTrace [] afterProgramming
                            prepared.request .proverReplayRoom (by
                              simpa [pairTrace] using beforeFailure))
                    change SchedulerNativeCursorAllProjectedTracedReturned _
                      (resume (.failed .proverReplayRoom)
                        (afterProgramming.addFailure prepared.request
                          .proverReplayRoom))
                    simpa [pairTrace, pairRecordsExact, List.append_assoc] using
                      (continuations (.failed .proverReplayRoom)
                        (afterProgramming.addFailure prepared.request
                          .proverReplayRoom) pairTrace failedInvariant)
                next =>
                  simp only [afterCoherent, if_neg]
                  have failedInvariant : EveryNodeOperational
                      (Final := ConcreteRestorationClientRun Statement Proof Payload
                        Result)
                      startProgram environment configuration pairTrace
                        (afterProgramming.addFailure prepared.request
                          .incoherentProgrammedOracle) := by
                    have unchanged : afterProgramming.nodes = accumulator.nodes :=
                      rfl
                    have beforeFailure := every_node_operational_of_nodes_eq
                      startProgram environment configuration trace
                        (scheduledPairRecords scheduled) accumulator
                          afterProgramming unchanged invariant
                    simpa [pairTrace] using
                      (every_node_operational_add_failure startProgram environment
                        configuration pairTrace [] afterProgramming
                          prepared.request .incoherentProgrammedOracle (by
                            simpa [pairTrace] using beforeFailure))
                  change SchedulerNativeCursorAllProjectedTracedReturned _
                    (resume (.failed .incoherentProgrammedOracle)
                      (afterProgramming.addFailure prepared.request
                        .incoherentProgrammedOracle))
                  simpa [pairTrace, pairRecordsExact, List.append_assoc] using
                    (continuations (.failed .incoherentProgrammedOracle)
                      (afterProgramming.addFailure prepared.request
                        .incoherentProgrammedOracle) pairTrace failedInvariant)
          next =>
            simp only [pairRoom, if_neg]
            apply failureSafe prepared.request .pairExposureLimit
            exact withPrefixInvariant
        next =>
          simp only [globalLimit, if_neg]
          apply failureSafe prepared.request .globalLimitTooSmall
          exact withPrefixInvariant
      next =>
        simp only [prefixCoherent, if_neg]
        apply failureSafe prepared.request .incoherentPrefixOracle
        exact withPrefixInvariant

/-- The finite concrete client certifies every child emitted on every partial
scheduler trace.  No completion premise or resource-success premise is used. -/
theorem concrete_restoration_client_preserves_every_actual_node
    {Statement Proof Payload Result : Type u}
    {globalOracleCalls : Nat}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (root : ConcreteRestorationNode Statement Proof Payload)
    (rootIsRoot : root.parentRequest = none)
    (configuration : ConcreteRestorationConfiguration)
    (restorationFuel : Nat)
    (client : ConcreteRestorationClient Result) :
    ConcreteClientPreservesEveryNodeOperational startProgram environment
      configuration (initialRestorationAccumulatorFromRoot root)
      (startConcreteRestorationClientFromRoot
        (globalOracleCalls := globalOracleCalls) startProgram environment root
          configuration restorationFuel client) := by
  let motive := fun (_fuel : Nat)
      (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
      (_residualClient : ConcreteRestorationClient Result)
      (cursor : SchedulerNativeCursor globalOracleCalls
        (ConcreteRestorationClientRun Statement Proof Payload Result)) =>
      ConcreteClientPreservesEveryNodeOperational startProgram environment
        configuration accumulator cursor
  have induction :=
    start_concrete_restoration_client_from_root_dependent_induction
      (globalOracleCalls := globalOracleCalls) startProgram environment root
      configuration restorationFuel client motive
      (by
        intro fuel accumulator result trace invariant
        apply SchedulerNativeCursorAllProjectedTracedReturned.returned
        intro answers
        exact every_node_operational_of_nodes_eq startProgram environment
          configuration trace (paddingRecords answers) accumulator accumulator rfl
            invariant)
      (by
        intro accumulator request next trace invariant
        apply SchedulerNativeCursorAllProjectedTracedReturned.returned
        intro answers
        exact every_node_operational_add_failure startProgram environment
          configuration trace (paddingRecords answers) accumulator request
            .restorationFuelExhausted invariant)
      (by
        intro fuel accumulator request next resume continuations
        exact dispatch_one_concrete_restoration_preserves_operational_trace
          startProgram environment configuration accumulator request resume
            continuations)
  exact induction

/-- Instantiation from an already accumulated root prefix.  It returns a
trace-indexed certificate for every concrete child in every ordinary terminal;
the caller may later combine it with an actual completed scheduler equality. -/
theorem concrete_restoration_client_traced_safety_from_root_prefix
    {Statement Proof Payload Result : Type u}
    {globalOracleCalls : Nat}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (root : ConcreteRestorationNode Statement Proof Payload)
    (rootIsRoot : root.parentRequest = none)
    (configuration : ConcreteRestorationConfiguration)
    (restorationFuel : Nat)
    (client : ConcreteRestorationClient Result)
    (rootTrace : List UnifiedExposureRecord) :
    SchedulerNativeCursorAllProjectedTracedReturned
      (fun run clientTrace => EveryNodeOperational
        (Final := ConcreteRestorationClientRun Statement Proof Payload Result)
        startProgram environment configuration (rootTrace ++ clientTrace)
          run.accumulator)
      (startConcreteRestorationClientFromRoot
        (globalOracleCalls := globalOracleCalls) startProgram environment root
          configuration restorationFuel client) := by
  exact concrete_restoration_client_preserves_every_actual_node startProgram
    environment root rootIsRoot configuration restorationFuel client rootTrace
      (initial_every_node_operational startProgram environment configuration
        rootTrace root rootIsRoot)

#print axioms ready_preparation_has_selected_parent
#print axioms dispatch_one_concrete_restoration_preserves_operational_trace
#print axioms concrete_restoration_client_preserves_every_actual_node
#print axioms concrete_restoration_client_traced_safety_from_root_prefix

end

end AspisK1.V7Tag73ConcreteRestorationTraceInduction
