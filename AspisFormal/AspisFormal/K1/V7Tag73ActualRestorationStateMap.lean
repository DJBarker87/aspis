import AspisFormal.K1.V7Tag73ActualNodeCausalProvenance

/-!
# Exact restoration-state map for the executable Tag-73 client

This leaf follows the literal one-request dispatcher.  A concrete restoration
certificate is installed at the `.forkAdvance` callback, before programming,
prover replay, verifier replay, or child insertion can fail.  Machine-fresh
suffixes cannot introduce fork coordinates.  A successfully returned child is
added only after the raw future-free path proves its final verifier history is
closed.

There is no abstract restore function and no equality between independently
normalized scheduler cursors in this proof.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ActualRestorationStateMap

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
open AspisK1.V7Tag73SchedulerMachineFactorization
open AspisK1.V7Tag73SchedulerProjectedTraceSafety
open AspisK1.V7Tag73OperationalNodeCertificate
open AspisK1.V7Tag73ConcreteRestorationTraceInduction
open AspisK1.V7Tag73CompletedFullRunProjection
open AspisK1.V7Tag73ActualNodeCausalProvenance
open AspisK1.V7Tag73Q16ControlInvariant

noncomputable section

universe u

/-- One literal request preserves the failure-inclusive map from every emitted
fork pair to the exact complete state selected by the executable preparer. -/
theorem dispatch_one_concrete_restoration_preserves_restoration_state_map
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
      ConcreteClientPreservesRestorationStateMap startProgram configuration
        nextAccumulator (resume reply nextAccumulator)) :
    ConcreteClientPreservesRestorationStateMap startProgram configuration
      accumulator
      (dispatchOneConcreteRestoration startProgram environment configuration
        accumulator request resume) := by
  intro trace invariant
  have unchangedSafe : ∀
      (suffix : List UnifiedExposureRecord)
      (reply : ConcreteRestorationReply)
      (nextAccumulator :
        ConcreteRestorationAccumulator Statement Proof Payload),
      nextAccumulator.nodes = accumulator.nodes →
      EveryEmittedPairHasConcreteRestoration startProgram configuration
        (trace ++ suffix) →
      SchedulerNativeCursorAllProjectedTracedReturned
        (fun run later => ActualRestorationStateMapInvariant startProgram
          configuration (trace ++ suffix ++ later) run.accumulator)
        (resume reply nextAccumulator) := by
    intro suffix reply nextAccumulator nodesExact pairsCovered
    exact unchanged_continuation_preserves_restoration_state_map startProgram
      configuration resume continuations trace suffix accumulator
        nextAccumulator reply nodesExact pairsCovered invariant
  generalize preparationExact :
    prepareConcreteRestorationFromStartProgram startProgram configuration
      accumulator request = preparation
  cases preparation with
  | failed reason prefixSteps prefixRestarts =>
      simp only [dispatchOneConcreteRestoration, dispatchConcreteRestoration,
        preparationExact]
      change SchedulerNativeCursorAllProjectedTracedReturned _
        (resume (.failed reason)
          ((accumulator.addCharges
            [.prefixReplayQueries prefixSteps,
              .restart prefixRestarts]).addFailure request reason))
      simpa using
        (unchangedSafe [] (.failed reason)
          ((accumulator.addCharges
            [.prefixReplayQueries prefixSteps,
              .restart prefixRestarts]).addFailure request reason)
          rfl (by simpa using invariant.everyEmittedPairRestored))
  | ready prepared =>
      have inputExact := prepare_from_start_ready_pair_inputs_exact startProgram
        configuration accumulator request prepared preparationExact
      have inputStateExact := squeeze_pair_inputs_exact_give_input_state
        prepared.transition prepared.outputInput prepared.advanceInput inputExact
      have preparedRequestExact := ready_preparation_request_exact startProgram
        configuration accumulator request prepared preparationExact
      have preparationAtPrepared :
          prepareConcreteRestorationFromStartProgram startProgram configuration
            accumulator prepared.request = .ready prepared := by
        simpa [preparedRequestExact] using preparationExact
      let prefixRestarts := if prepared.prefixRun.isSome then 1 else 0
      let withPrefix := accumulator.addCharges
        [.prefixReplayQueries prepared.prefixSteps, .restart prefixRestarts]
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
            let currentPair := emitted_pair_concrete_restoration_of_ready
              startProgram configuration accumulator prepared
                preparationAtPrepared invariant.everyNodeHistoryClosed trace
                  scheduled frozenExact outputExact advanceExact templateExact
                    ⟨outputExact.trans inputStateExact.1,
                      advanceExact.trans inputStateExact.2⟩
            have pairCovered : EveryEmittedPairHasConcreteRestoration
                startProgram configuration pairTrace := by
              exact every_emitted_pair_append_scheduled_pair startProgram
                configuration trace scheduled invariant.everyEmittedPairRestored
                  currentPair
            let afterCoordinates := withPrefix.addCharges
              [.forkUniformCoordinates 2]
            cases programmed : programConcretePair configuration.oracleLimits
                configuration.pairProgrammingOrder prepared.programmingBase
                prepared.outputInput prepared.advanceInput
                scheduled.configuration.forkOutput
                scheduled.configuration.forkAdvance with
            | failed reason inserted =>
                simp only [programmed]
                change SchedulerNativeCursorAllProjectedTracedReturned _
                  (resume (.failed reason)
                    ((afterCoordinates.addCharges
                      [.programmedPoints inserted]).addFailure prepared.request
                        reason))
                simpa [pairTrace, pairRecordsExact, List.append_assoc] using
                  (unchangedSafe (scheduledPairRecords scheduled)
                    (.failed reason)
                    ((afterCoordinates.addCharges
                      [.programmedPoints inserted]).addFailure prepared.request
                        reason)
                    rfl (by simpa [pairTrace] using pairCovered))
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
                    have proverOnly : OnlyMachineFreshActor .extractorReplay
                        proverRecords := by
                      simpa [proverRecords] using
                        (only_machine_fresh_actor_projected_records
                          .extractorReplay proverPrefix.freshQueries)
                    have proverCovered : EveryEmittedPairHasConcreteRestoration
                        startProgram configuration proverTrace := by
                      exact every_emitted_pair_append_without_fork_advance
                        startProgram configuration pairTrace proverRecords
                          pairCovered
                            (no_fork_advance_of_only_machine_fresh_actor
                              .extractorReplay proverRecords proverOnly)
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
                          change SchedulerNativeCursorAllProjectedTracedReturned _
                            (resume (.failed (.proverReplayAbort reason))
                              (afterProver.addFailure prepared.request
                                (.proverReplayAbort reason)))
                          simpa [pairTrace, proverTrace, pairRecordsExact,
                            List.append_assoc] using
                            (unchangedSafe
                              (scheduledPairRecords scheduled ++ proverRecords)
                              (.failed (.proverReplayAbort reason))
                              (afterProver.addFailure prepared.request
                                (.proverReplayAbort reason))
                              rfl (by simpa [pairTrace, proverTrace,
                                List.append_assoc] using proverCovered))
                        | timeout =>
                          change SchedulerNativeCursorAllProjectedTracedReturned _
                            (resume (.failed .proverReplayTimeout)
                              (afterProver.addFailure prepared.request
                                .proverReplayTimeout))
                          simpa [pairTrace, proverTrace, pairRecordsExact,
                            List.append_assoc] using
                            (unchangedSafe
                              (scheduledPairRecords scheduled ++ proverRecords)
                              (.failed .proverReplayTimeout)
                              (afterProver.addFailure prepared.request
                                .proverReplayTimeout)
                              rfl (by simpa [pairTrace, proverTrace,
                                List.append_assoc] using proverCovered))
                      | ok adversaryValue =>
                        simp only
                        by_cases bindingMismatch :
                            FixedBindings.ofContext
                                adversaryValue.rawMessages.context ≠
                              prepared.restoredState.current.bindings
                        next =>
                          rw [dif_pos bindingMismatch]
                          change SchedulerNativeCursorAllProjectedTracedReturned _
                            (resume (.failed .restoredBindingMismatch)
                              (afterProver.addFailure prepared.request
                                .restoredBindingMismatch))
                          simpa [pairTrace, proverTrace, pairRecordsExact,
                            List.append_assoc] using
                            (unchangedSafe
                              (scheduledPairRecords scheduled ++ proverRecords)
                              (.failed .restoredBindingMismatch)
                              (afterProver.addFailure prepared.request
                                .restoredBindingMismatch)
                              rfl (by simpa [pairTrace, proverTrace,
                                List.append_assoc] using proverCovered))
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
                            have verifierOnly : OnlyMachineFreshActor .verifier
                                verifierRecords := by
                              simpa [verifierRecords] using
                                (only_machine_fresh_actor_projected_records
                                  .verifier verifierPrefix.freshQueries)
                            have verifierCovered :
                                EveryEmittedPairHasConcreteRestoration
                                  startProgram configuration verifierTrace := by
                              exact every_emitted_pair_append_without_fork_advance
                                startProgram configuration proverTrace
                                  verifierRecords proverCovered
                                    (no_fork_advance_of_only_machine_fresh_actor
                                      .verifier verifierRecords verifierOnly)
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
                                  change
                                    SchedulerNativeCursorAllProjectedTracedReturned _
                                      (resume
                                        (.failed (.verifierSuffixAbort reason))
                                        (afterVerifier.addFailure prepared.request
                                          (.verifierSuffixAbort reason)))
                                  simpa [pairTrace, proverTrace, verifierTrace,
                                    pairRecordsExact, List.append_assoc] using
                                    (unchangedSafe
                                      (scheduledPairRecords scheduled ++
                                        proverRecords ++ verifierRecords)
                                      (.failed (.verifierSuffixAbort reason))
                                      (afterVerifier.addFailure prepared.request
                                        (.verifierSuffixAbort reason))
                                      rfl (by simpa [pairTrace, proverTrace,
                                        verifierTrace, List.append_assoc] using
                                          verifierCovered))
                                | timeout =>
                                  change
                                    SchedulerNativeCursorAllProjectedTracedReturned _
                                      (resume (.failed .verifierSuffixTimeout)
                                        (afterVerifier.addFailure prepared.request
                                          .verifierSuffixTimeout))
                                  simpa [pairTrace, proverTrace, verifierTrace,
                                    pairRecordsExact, List.append_assoc] using
                                    (unchangedSafe
                                      (scheduledPairRecords scheduled ++
                                        proverRecords ++ verifierRecords)
                                      (.failed .verifierSuffixTimeout)
                                      (afterVerifier.addFailure prepared.request
                                        .verifierSuffixTimeout)
                                      rfl (by simpa [pairTrace, proverTrace,
                                        verifierTrace, List.append_assoc] using
                                          verifierCovered))
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
                                  exact preparationAtPrepared
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
                                let childExecution :
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
                                have chargedInvariant :
                                    ActualRestorationStateMapInvariant
                                      startProgram configuration verifierTrace
                                        charged := by
                                  have transported :=
                                    restoration_state_map_of_nodes_eq startProgram
                                      configuration trace
                                      (scheduledPairRecords scheduled ++
                                        proverRecords ++ verifierRecords)
                                      accumulator charged rfl
                                      (by simpa [pairTrace, proverTrace,
                                        verifierTrace, List.append_assoc] using
                                          verifierCovered)
                                      invariant
                                  simpa [pairTrace, proverTrace, verifierTrace,
                                    List.append_assoc] using transported
                                have addedInvariant :
                                    ActualRestorationStateMapInvariant
                                      startProgram configuration verifierTrace
                                        added.2 := by
                                  have parentMember :
                                      prepared.parentNode ∈ accumulator.nodes :=
                                    (ready_preparation_parent_is_stored
                                      startProgram configuration accumulator
                                      prepared.request prepared
                                      preparationAtPrepared).2.1
                                  have parentQ16 : FutureFreeQ16SlotInvariant
                                      prepared.parentNode.verifierFinalState :=
                                    invariant.everyNodeQ16SlotInvariant
                                      prepared.parentNode parentMember
                                  have parentClosed : FutureFreeHistoryClosed
                                      prepared.parentNode.verifierFinalState :=
                                    invariant.everyNodeHistoryClosed
                                      prepared.parentNode parentMember
                                  have selection :=
                                    prepare_concrete_restoration_ready_selection_exact
                                      startProgram configuration accumulator
                                      prepared.request prepared
                                      preparationAtPrepared
                                  have beforeSeen : prepared.transition.before ∈
                                      prepared.parentNode.verifierFinalState.seen :=
                                    selected_transition_before_is_previously_seen
                                      prepared.parentNode
                                      prepared.request.verifierTransitionIndex
                                      prepared.transition selection.2.1
                                      parentClosed
                                  have childQ16 : FutureFreeQ16SlotInvariant
                                      node.verifierFinalState := by
                                    apply
                                      projected_restoration_child_q16_slot_invariant
                                        childExecution
                                    · simpa [childExecution] using parentQ16
                                    · simpa [childExecution] using beforeSeen
                                  simpa [added] using
                                    (restoration_state_map_add_child startProgram
                                      configuration verifierTrace [] charged node
                                        (projected_restoration_child_history_closed
                                          childExecution)
                                        childQ16
                                        (by simpa using verifierCovered)
                                        chargedInvariant)
                                change SchedulerNativeCursorAllProjectedTracedReturned _
                                  (resume (.added added.1) added.2)
                                simpa [pairTrace, proverTrace, verifierTrace,
                                  pairRecordsExact, List.append_assoc] using
                                  (continuations (.added added.1) added.2
                                    verifierTrace addedInvariant)
                          next =>
                            simp only [verifierRoom, if_neg]
                            change SchedulerNativeCursorAllProjectedTracedReturned _
                              (resume (.failed .verifierSuffixRoom)
                                (afterProver.addFailure prepared.request
                                  .verifierSuffixRoom))
                            simpa [pairTrace, proverTrace, pairRecordsExact,
                              List.append_assoc] using
                              (unchangedSafe
                                (scheduledPairRecords scheduled ++ proverRecords)
                                (.failed .verifierSuffixRoom)
                                (afterProver.addFailure prepared.request
                                  .verifierSuffixRoom)
                                rfl (by simpa [pairTrace, proverTrace,
                                  List.append_assoc] using proverCovered))
                  next =>
                    simp only [proverRoom, if_neg]
                    change SchedulerNativeCursorAllProjectedTracedReturned _
                      (resume (.failed .proverReplayRoom)
                        (afterProgramming.addFailure prepared.request
                          .proverReplayRoom))
                    simpa [pairTrace, pairRecordsExact, List.append_assoc] using
                      (unchangedSafe (scheduledPairRecords scheduled)
                        (.failed .proverReplayRoom)
                        (afterProgramming.addFailure prepared.request
                          .proverReplayRoom)
                        rfl (by simpa [pairTrace] using pairCovered))
                next =>
                  simp only [afterCoherent, if_neg]
                  change SchedulerNativeCursorAllProjectedTracedReturned _
                    (resume (.failed .incoherentProgrammedOracle)
                      (afterProgramming.addFailure prepared.request
                        .incoherentProgrammedOracle))
                  simpa [pairTrace, pairRecordsExact, List.append_assoc] using
                    (unchangedSafe (scheduledPairRecords scheduled)
                      (.failed .incoherentProgrammedOracle)
                      (afterProgramming.addFailure prepared.request
                        .incoherentProgrammedOracle)
                      rfl (by simpa [pairTrace] using pairCovered))
          next =>
            simp only [pairRoom, if_neg]
            change SchedulerNativeCursorAllProjectedTracedReturned _
              (resume (.failed .pairExposureLimit)
                (withPrefix.addFailure prepared.request .pairExposureLimit))
            simpa using
              (unchangedSafe [] (.failed .pairExposureLimit)
                (withPrefix.addFailure prepared.request .pairExposureLimit)
                rfl (by simpa using invariant.everyEmittedPairRestored))
        next =>
          simp only [globalLimit, if_neg]
          change SchedulerNativeCursorAllProjectedTracedReturned _
            (resume (.failed .globalLimitTooSmall)
              (withPrefix.addFailure prepared.request .globalLimitTooSmall))
          simpa using
            (unchangedSafe [] (.failed .globalLimitTooSmall)
              (withPrefix.addFailure prepared.request .globalLimitTooSmall)
              rfl (by simpa using invariant.everyEmittedPairRestored))
      next =>
        simp only [prefixCoherent, if_neg]
        change SchedulerNativeCursorAllProjectedTracedReturned _
          (resume (.failed .incoherentPrefixOracle)
            (withPrefix.addFailure prepared.request .incoherentPrefixOracle))
        simpa using
          (unchangedSafe [] (.failed .incoherentPrefixOracle)
            (withPrefix.addFailure prepared.request .incoherentPrefixOracle)
          rfl (by simpa using invariant.everyEmittedPairRestored))

/-- The finite adaptive client preserves the restoration-state map on every
ordinary returned branch.  This induction follows the client's actual reply
continuations and does not require replay-base syntax or a chosen restore
function. -/
theorem concrete_restoration_client_preserves_restoration_state_map
    {Statement Proof Payload Result : Type u}
    {globalOracleCalls : Nat}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (root : ConcreteRestorationNode Statement Proof Payload)
    (configuration : ConcreteRestorationConfiguration)
    (restorationFuel : Nat)
    (client : ConcreteRestorationClient Result) :
    ConcreteClientPreservesRestorationStateMap startProgram configuration
      (initialRestorationAccumulatorFromRoot root)
      (startConcreteRestorationClientFromRoot
        (globalOracleCalls := globalOracleCalls) startProgram environment root
          configuration restorationFuel client) := by
  let motive := fun (_fuel : Nat)
      (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
      (_residualClient : ConcreteRestorationClient Result)
      (cursor : SchedulerNativeCursor globalOracleCalls
        (ConcreteRestorationClientRun Statement Proof Payload Result)) =>
      ConcreteClientPreservesRestorationStateMap startProgram configuration
        accumulator cursor
  have induction :=
    start_concrete_restoration_client_from_root_dependent_induction
      (globalOracleCalls := globalOracleCalls) startProgram environment root
      configuration restorationFuel client motive
      (by
        intro fuel accumulator result trace invariant
        apply SchedulerNativeCursorAllProjectedTracedReturned.returned
        intro answers
        exact restoration_state_map_of_nodes_eq startProgram configuration
          trace (paddingRecords answers) accumulator accumulator rfl
            (every_emitted_pair_append_without_fork_advance startProgram
              configuration trace (paddingRecords answers)
                invariant.everyEmittedPairRestored
                  (no_fork_advance_padding_records answers))
            invariant)
      (by
        intro accumulator request next trace invariant
        apply SchedulerNativeCursorAllProjectedTracedReturned.returned
        intro answers
        exact restoration_state_map_of_nodes_eq startProgram configuration
          trace (paddingRecords answers) accumulator
            (accumulator.addFailure request .restorationFuelExhausted) rfl
            (every_emitted_pair_append_without_fork_advance startProgram
              configuration trace (paddingRecords answers)
                invariant.everyEmittedPairRestored
                  (no_fork_advance_padding_records answers))
            invariant)
      (by
        intro fuel accumulator request next resume continuations
        exact
          dispatch_one_concrete_restoration_preserves_restoration_state_map
            startProgram environment configuration accumulator request resume
              continuations)
  exact induction

/-- A literal completed list run exposes the exact state map on its computed
trace.  Positivity of the continuation fuel is derived from successful return,
so the caller cannot hide a normalization-fuel assumption. -/
theorem returned_concrete_restoration_client_has_exact_state_map
    {Statement Proof Payload Result : Type u}
    {globalOracleCalls : Nat}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (currentTransitionFuel : Nat)
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (root : ConcreteRestorationNode Statement Proof Payload)
    (configuration : ConcreteRestorationConfiguration)
    (restorationFuel : Nat)
    (client : ConcreteRestorationClient Result)
    (rootTrace : List UnifiedExposureRecord)
    (rootClosed : FutureFreeHistoryClosed root.verifierFinalState)
    (rootQ16 : FutureFreeQ16SlotInvariant root.verifierFinalState)
    (rootTraceHasNoAdvance : ∀ scheduled,
      (.forkAdvance scheduled : UnifiedExposureRecord) ∉ rootTrace)
    (answers : List Digest256)
    (run : ConcreteRestorationClientRun Statement Proof Payload Result)
    (completed :
      runSchedulerNativeListTerminalFrom transitionFuel currentTransitionFuel
        (startConcreteRestorationClientFromRoot
          (globalOracleCalls := globalOracleCalls) startProgram environment root
          configuration restorationFuel client)
        answers = .returned run) :
    ActualRestorationStateMapInvariant startProgram configuration
      (rootTrace ++
        (runSchedulerNativeListRunFrom transitionFuel currentTransitionFuel
          (startConcreteRestorationClientFromRoot
            (globalOracleCalls := globalOracleCalls) startProgram environment root
            configuration restorationFuel client)
          answers).trace)
      run.accumulator := by
  let cursor := startConcreteRestorationClientFromRoot
    (globalOracleCalls := globalOracleCalls) startProgram environment root
      configuration restorationFuel client
  have currentPositive : 0 < currentTransitionFuel :=
    returned_list_terminal_implies_current_positive transitionFuel positive
      currentTransitionFuel cursor answers run completed
  have safe :=
    concrete_restoration_client_preserves_restoration_state_map
      (globalOracleCalls := globalOracleCalls) startProgram environment root
        configuration restorationFuel client
  have traced := safe rootTrace
    (initial_restoration_state_map startProgram configuration root rootTrace
      rootClosed rootQ16 rootTraceHasNoAdvance)
  apply run_scheduler_native_list_run_respects_projected_traced_returned
    (fun result suffix => ActualRestorationStateMapInvariant startProgram
      configuration (rootTrace ++ suffix) result.accumulator)
    transitionFuel positive cursor traced currentTransitionFuel currentPositive
      answers run
  rw [run_scheduler_native_list_run_terminal]
  exact completed

#print axioms dispatch_one_concrete_restoration_preserves_restoration_state_map
#print axioms concrete_restoration_client_preserves_restoration_state_map
#print axioms returned_concrete_restoration_client_has_exact_state_map

end

end AspisK1.V7Tag73ActualRestorationStateMap
