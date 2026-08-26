import AspisFormal.K1.V7Tag73CompletedRootProjection
import AspisFormal.K1.V7Tag73SchedulerNativeSafety
import AspisFormal.K1.V7Tag73FullResultRootRuns
import AspisFormal.K1.V7Tag73SchedulerResultMapSemantics

/-!
# Project a completed full Tag-73 scheduler run

The initial-only experiment already reconstructs the literal same-tape prover
and future-free verifier runs.  The full experiment continues with the finite
concrete restoration client.  This module proves that any completed full
terminal retains the same operational root and that its returned accumulator
is the actual append-only node store produced by that client.

The proof uses the real private-runner induction exported by
`V7Tag73ConcreteRestorationClient`; it does not accept a client run equation,
an arbitrary terminal accumulator, or a node-store invariant as a premise.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73CompletedFullRunProjection

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73AtomicPairFork
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73RawStrictReplacementSuffix
open AspisK1.V7Tag73UniformRawVerifierExecution
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SchedulerNativeSafety
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ProjectedMachinePrefix
open AspisK1.V7Tag73SchedulerMachineFactorization
open AspisK1.V7Tag73CompletedRootProjection
open AspisK1.V7Tag73TotalizedMachineReflection
open AspisK1.V7Tag73FullResultRootRuns
open AspisK1.V7Tag73SchedulerResultMapSemantics

noncomputable section

universe u

/-! ## Static safety is respected by the executable scheduler -/

/-- The request-level form of `SchedulerNativeCursorAllReturned`.  A fresh
machine request retains the safety of its actual return continuation; a fork
request retains it for every concrete pair of scheduler coordinates. -/
def SchedulerNativeRequestAllReturned
    {globalOracleCalls : Nat} {Result : Type u}
    (P : Result → Prop) : SchedulerNativeRequest globalOracleCalls Result →
      Prop
  | .returned result => P result
  | .failed _reason | .transitionLimit => True
  | .machineFresh _limits _limitBound _actor _state _input _nextProgram
      _remainingFuel _coherent _totalRoom _freshRoom _missing onReturned =>
      ∀ result finalState finalCoherent,
        SchedulerNativeCursorAllReturned P
          (onReturned result finalState finalCoherent)
  | .forkOutput _history _room _outputInput _advanceInput _template next =>
      ∀ configuration,
        SchedulerNativeCursorAllReturned P (next configuration)
  | .forkAdvance _history _room _outputInput _advanceInput _template
      _forkOutput next =>
      ∀ configuration,
        SchedulerNativeCursorAllReturned P (next configuration)

theorem native_request_all_returned
    {globalOracleCalls : Nat} {Result MachineResult : Type u}
    (P : Result → Prop)
    (limits : OracleLimits)
    (limitBound : limits.totalCalls ≤ globalOracleCalls)
    (actor : QueryActor)
    (onReturned : (result : MachineResult) → (state : OracleState) →
      HistoryTotalCoherent state →
        SchedulerNativeCursor globalOracleCalls Result)
    (continueReturned : (result : MachineResult) → (state : OracleState) →
      HistoryTotalCoherent state →
        SchedulerNativeRequest globalOracleCalls Result)
    (onSafe : ∀ result finalState finalCoherent,
      SchedulerNativeCursorAllReturned P
        (onReturned result finalState finalCoherent))
    (continueSafe : ∀ result finalState finalCoherent,
      SchedulerNativeRequestAllReturned P
        (continueReturned result finalState finalCoherent))
    (certified : CoherentSeekResult MachineResult limits) :
    SchedulerNativeRequestAllReturned P
      (nativeRequestOfCoherentSeekResult limits limitBound actor onReturned
        continueReturned certified) := by
  rcases certified with ⟨sought, soughtCoherent⟩
  cases sought with
  | returned result finalState steps =>
      exact continueSafe result finalState soughtCoherent
  | explicitAbort reason finalState steps => trivial
  | resourceAbort reason finalState steps => trivial
  | outOfFuel finalState steps => trivial
  | request requestState input nextProgram remainingFuel steps requestCoherent
      totalRoom freshRoom missing =>
      exact onSafe

/-- Zero-coordinate normalization cannot reach a returned result outside the
static continuation tree of the cursor. -/
theorem seek_scheduler_native_all_returned
    {globalOracleCalls : Nat} {Result : Type u}
    (P : Result → Prop) :
    ∀ (transitionFuel : Nat)
      (cursor : SchedulerNativeCursor globalOracleCalls Result),
      SchedulerNativeCursorAllReturned P cursor →
        SchedulerNativeRequestAllReturned P
          (seekSchedulerNativeExposure transitionFuel cursor) := by
  intro transitionFuel
  induction transitionFuel with
  | zero =>
      intro cursor safe
      trivial
  | succ transitionFuel ih =>
      intro cursor safe
      cases cursor with
      | returned result => exact safe
      | failed reason => trivial
      | forkPair history room outputInput advanceInput template next =>
          exact safe
      | forkAdvance history room outputInput advanceInput template forkOutput
          next =>
          exact safe
      | @machine MachineResult limits limitBound actor state program fuel
          coherent onReturned =>
          apply native_request_all_returned P limits limitBound actor
            onReturned
            (fun result finalState finalCoherent =>
              seekSchedulerNativeExposure transitionFuel
                (onReturned result finalState finalCoherent))
          · exact safe
          · intro result finalState finalCoherent
            exact ih (onReturned result finalState finalCoherent)
              (safe result finalState finalCoherent)

/-- The terminal-only list interpreter can return only a value reachable in
the cursor's actual continuation tree. -/
theorem run_scheduler_native_list_terminal_respects_all_returned
    {globalOracleCalls : Nat} {Result : Type u}
    (P : Result → Prop) (transitionFuel : Nat) :
    ∀ (currentTransitionFuel : Nat)
      (cursor : SchedulerNativeCursor globalOracleCalls Result)
      (answers : List Digest256) (result : Result),
      SchedulerNativeCursorAllReturned P cursor →
      runSchedulerNativeListTerminalFrom transitionFuel currentTransitionFuel
          cursor answers = .returned result →
      P result := by
  intro currentTransitionFuel cursor answers
  induction answers generalizing currentTransitionFuel cursor with
  | nil =>
      intro result safe completed
      have requestSafe := seek_scheduler_native_all_returned P
        currentTransitionFuel cursor safe
      unfold runSchedulerNativeListTerminalFrom at completed
      unfold terminalAtExposureEnd at completed
      generalize requestEq :
        seekSchedulerNativeExposure currentTransitionFuel cursor = request
        at completed requestSafe
      cases request <;> simp_all [SchedulerNativeRequestAllReturned]
  | cons answer rest ih =>
      intro result safe completed
      have requestSafe := seek_scheduler_native_all_returned P
        currentTransitionFuel cursor safe
      unfold runSchedulerNativeListTerminalFrom at completed
      generalize requestEq :
        seekSchedulerNativeExposure currentTransitionFuel cursor = request
        at completed requestSafe
      cases request with
      | returned returnedResult =>
          exact ih transitionFuel (.returned returnedResult) result requestSafe
            completed
      | failed reason =>
          exact ih transitionFuel (.failed reason) result (by trivial)
            completed
      | transitionLimit =>
          exact ih transitionFuel (.failed .transitionLimit) result (by
            trivial) completed
      | @machineFresh MachineResult limits limitBound actor state input
          nextProgram remainingFuel coherent totalRoom freshRoom missing
          onReturned =>
          exact ih transitionFuel
            (.machine limits limitBound actor
              (freshQueryState actor state input answer)
              (nextProgram answer) remainingFuel
              (fresh_query_state_preserves_history_total_coherent actor state
                input answer coherent) onReturned)
            result requestSafe completed
      | forkOutput history room outputInput advanceInput template next =>
          exact ih transitionFuel
            (.forkAdvance history room outputInput advanceInput template answer
              next)
            result requestSafe completed
      | forkAdvance history room outputInput advanceInput template forkOutput
          next =>
          let scheduled : ScheduledForkCoins :=
            { frozenHistory := history
              outputInput := outputInput
              advanceInput := advanceInput
              template := template
              forkOutput := forkOutput
              forkAdvance := answer }
          exact ih transitionFuel (next scheduled.configuration) result
            (requestSafe scheduled.configuration) completed

/-! ## Operational preparation and append-only node stores -/

/-- Everything needed to justify the ancestry of a returned child is computed
by prefix preparation itself. -/
def PreparedSelectionIsExact
    {Statement Proof Payload : Type*}
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (prepared : PreparedConcreteRestoration Statement Proof Payload) : Prop :=
  accumulator.node? prepared.request.nodeId = some prepared.parentNode ∧
    verifierTransitionAt? prepared.parentNode
        prepared.request.verifierTransitionIndex = some prepared.transition ∧
    squeezePairInputsOfTransition prepared.transition ≠ none ∧
    prepared.restoredState = restoreIndexedTransition prepared.transition

/-- A `.ready` value cannot contain an invented parent, transition, or
restored verifier state: all four are projections of the actual validated
request path. -/
theorem prepare_concrete_restoration_ready_selection_exact
    {Statement Proof Payload : Type*}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (configuration : ConcreteRestorationConfiguration)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (request : ConcreteRestorationRequest)
    (prepared : PreparedConcreteRestoration Statement Proof Payload)
    (ready : prepareConcreteRestorationFromStartProgram startProgram
      configuration accumulator request = .ready prepared) :
    PreparedSelectionIsExact accumulator prepared := by
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
                  exact ⟨selectedNode, selectedTransition, by
                    rw [selectedPair]
                    simp, rfl⟩
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
                              exact ⟨selectedNode, selectedTransition, by
                                rw [selectedPair]
                                simp, rfl⟩

theorem node_lookup_preserved_by_append
    {Statement Proof Payload : Type*}
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (child parent : ConcreteRestorationNode Statement Proof Payload)
    (nodeId : Nat)
    (found : accumulator.node? nodeId = some parent) :
    (accumulator.addNode child).2.node? nodeId = some parent := by
  unfold ConcreteRestorationAccumulator.node? at found ⊢
  rw [List.getElem?_eq_some_iff] at found
  rcases found with ⟨within, valueExact⟩
  rw [ConcreteRestorationAccumulator.addNode,
    List.getElem?_append_left within, List.getElem?_eq_some_iff]
  exact ⟨within, valueExact⟩

theorem initial_node_store_invariant
    {TapeIdentity Statement Proof Payload : Type u}
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload) :
    SchedulerNativeNodeStoreInvariant runtime
      (initialRestorationAccumulatorFromRoot runtime.node) := by
  constructor
  · rfl
  · intro child member request parentRequest
    simp [initialRestorationAccumulatorFromRoot] at member
    subst child
    simp [SchedulerNativePlainRomRootRuntime.node] at parentRequest

theorem node_store_invariant_add_charges
    {TapeIdentity Statement Proof Payload : Type u}
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (charges : List ConcreteRestorationCharge)
    (invariant : SchedulerNativeNodeStoreInvariant runtime accumulator) :
    SchedulerNativeNodeStoreInvariant runtime
      (accumulator.addCharges charges) := by
  simpa [SchedulerNativeNodeStoreInvariant,
    ConcreteRestorationAccumulator.addCharges,
    ConcreteRestorationAccumulator.node?] using invariant

theorem node_store_invariant_add_failure
    {TapeIdentity Statement Proof Payload : Type u}
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (request : ConcreteRestorationRequest)
    (reason : ConcreteRestorationFailure)
    (invariant : SchedulerNativeNodeStoreInvariant runtime accumulator) :
    SchedulerNativeNodeStoreInvariant runtime
      (accumulator.addFailure request reason) := by
  simpa [SchedulerNativeNodeStoreInvariant,
    ConcreteRestorationAccumulator.addFailure,
    ConcreteRestorationAccumulator.node?] using invariant

/-- Appending the concrete child produced from a ready preparation preserves
the complete root/ancestry invariant. -/
theorem node_store_invariant_add_prepared_child
    {TapeIdentity Statement Proof Payload : Type u}
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (prepared : PreparedConcreteRestoration Statement Proof Payload)
    (child : ConcreteRestorationNode Statement Proof Payload)
    (invariant : SchedulerNativeNodeStoreInvariant runtime accumulator)
    (selection : PreparedSelectionIsExact accumulator prepared)
    (childRequest : child.parentRequest = some prepared.request)
    (childEntry : child.verifierEntryState = prepared.restoredState) :
    SchedulerNativeNodeStoreInvariant runtime (accumulator.addNode child).2 := by
  rcases selection with ⟨parentFound, transitionFound, squeeze, restored⟩
  constructor
  · exact node_lookup_preserved_by_append accumulator child runtime.node 0
      invariant.1
  · intro candidate member request parentRequest
    have memberCases : candidate ∈ accumulator.nodes ∨ candidate = child := by
      simpa [ConcreteRestorationAccumulator.addNode] using member
    rcases memberCases with oldMember | candidateExact
    · obtain ⟨parent, transition, found, indexed, isSqueeze, entry⟩ :=
        invariant.2 candidate oldMember request parentRequest
      exact ⟨parent, transition,
        node_lookup_preserved_by_append accumulator child parent request.nodeId
          found,
        indexed, isSqueeze, entry⟩
    · subst candidate
      have requestExact : request = prepared.request := by
        exact Option.some.inj (parentRequest.symm.trans childRequest)
      subst request
      exact ⟨prepared.parentNode, prepared.transition,
        node_lookup_preserved_by_append accumulator child prepared.parentNode
          prepared.request.nodeId parentFound,
        transitionFound, squeeze, childEntry.trans restored⟩

/-! ## The real one-request dispatcher preserves the store invariant -/

theorem dispatch_one_concrete_restoration_preserves_node_store
    {TapeIdentity Statement Proof Payload Result : Type u}
    {globalOracleCalls : Nat}
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
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
      SchedulerNativeNodeStoreInvariant runtime nextAccumulator →
        SchedulerNativeCursorAllReturned
          (fun run => SchedulerNativeNodeStoreInvariant runtime run.accumulator)
          (resume reply nextAccumulator))
    (invariant : SchedulerNativeNodeStoreInvariant runtime accumulator) :
    SchedulerNativeCursorAllReturned
      (fun run => SchedulerNativeNodeStoreInvariant runtime run.accumulator)
      (dispatchOneConcreteRestoration startProgram environment configuration
        accumulator request resume) := by
  let P := fun run : ConcreteRestorationClientRun Statement Proof Payload
      Result => SchedulerNativeNodeStoreInvariant runtime run.accumulator
  have failureSafe : ∀ failureRequest reason nextAccumulator,
      SchedulerNativeNodeStoreInvariant runtime nextAccumulator →
      SchedulerNativeCursorAllReturned P
        (resume (.failed reason)
          (nextAccumulator.addFailure failureRequest reason)) := by
    intro failureRequest reason nextAccumulator nextInvariant
    exact continuations (.failed reason)
      (nextAccumulator.addFailure failureRequest reason)
      (node_store_invariant_add_failure runtime nextAccumulator failureRequest
        reason nextInvariant)
  generalize preparationExact :
    prepareConcreteRestorationFromStartProgram startProgram configuration
      accumulator request = preparation
  cases preparation with
  | failed reason prefixSteps prefixRestarts =>
      simp only [dispatchOneConcreteRestoration,
        dispatchConcreteRestoration, preparationExact]
      apply failureSafe request reason
      exact node_store_invariant_add_charges runtime accumulator
        [.prefixReplayQueries prefixSteps, .restart prefixRestarts] invariant
  | ready prepared =>
      have selection := prepare_concrete_restoration_ready_selection_exact
        startProgram configuration accumulator request prepared preparationExact
      let prefixRestarts := if prepared.prefixRun.isSome then 1 else 0
      let withPrefix := accumulator.addCharges
        [.prefixReplayQueries prepared.prefixSteps, .restart prefixRestarts]
      have withPrefixInvariant :
          SchedulerNativeNodeStoreInvariant runtime withPrefix :=
        node_store_invariant_add_charges runtime accumulator _ invariant
      simp only [dispatchOneConcreteRestoration,
        dispatchConcreteRestoration, preparationExact]
      unfold dispatchPreparedRestoration
      by_cases prefixCoherent :
          HistoryTotalCoherent prepared.programmingBase
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
            intro forkConfiguration
            simp only
            let afterCoordinates := withPrefix.addCharges
              [.forkUniformCoordinates 2]
            have afterCoordinatesInvariant :
                SchedulerNativeNodeStoreInvariant runtime afterCoordinates :=
              node_store_invariant_add_charges runtime withPrefix _
                withPrefixInvariant
            cases programmed : programConcretePair configuration.oracleLimits
                configuration.pairProgrammingOrder prepared.programmingBase
                prepared.outputInput prepared.advanceInput
                forkConfiguration.forkOutput forkConfiguration.forkAdvance with
            | failed reason inserted =>
                simp only [programmed]
                apply failureSafe prepared.request reason
                exact node_store_invariant_add_charges runtime afterCoordinates
                  [.programmedPoints inserted] afterCoordinatesInvariant
            | ready afterBoth =>
                simp only [programmed]
                let afterProgramming := afterCoordinates.addCharges
                  [.programmedPoints 2]
                have afterProgrammingInvariant :
                    SchedulerNativeNodeStoreInvariant runtime
                      afterProgramming :=
                  node_store_invariant_add_charges runtime afterCoordinates _
                    afterCoordinatesInvariant
                by_cases afterCoherent : HistoryTotalCoherent afterBoth
                next =>
                  simp only [afterCoherent, if_pos]
                  by_cases proverRoom : StageHasOracleRoom
                      configuration.oracleLimits afterBoth
                      configuration.proverReplayFuel
                  next =>
                    simp only [proverRoom, if_pos]
                    let atProverStart := afterProgramming.addCharges
                      [.restart 1]
                    have atProverStartInvariant :
                        SchedulerNativeNodeStoreInvariant runtime
                          atProverStart :=
                      node_store_invariant_add_charges runtime afterProgramming
                        _ afterProgrammingInvariant
                    intro proverStage proverFinalOracle proverCoherent
                    cases proverStageExact : proverStage with
                    | completed proverResult =>
                        simp only
                        let proverQueries :=
                          (historySince afterBoth proverFinalOracle).length
                        let afterProver := atProverStart.addCharges
                          [.completeFromStartQueries proverQueries]
                        have afterProverInvariant :
                            SchedulerNativeNodeStoreInvariant runtime
                              afterProver :=
                          node_store_invariant_add_charges runtime atProverStart
                            _ atProverStartInvariant
                        cases proverResultExact : proverResult with
                        | error failure =>
                            cases failure with
                            | oracleAbort reason =>
                                exact failureSafe prepared.request
                                  (.proverReplayAbort reason) afterProver
                                  afterProverInvariant
                            | timeout =>
                                exact failureSafe prepared.request
                                  .proverReplayTimeout afterProver
                                  afterProverInvariant
                        | ok adversaryValue =>
                            simp only
                            by_cases bindingMismatch :
                                FixedBindings.ofContext
                                    adversaryValue.rawMessages.context ≠
                                  prepared.restoredState.current.bindings
                            next =>
                              rw [dif_pos bindingMismatch]
                              exact failureSafe prepared.request
                                .restoredBindingMismatch afterProver
                                afterProverInvariant
                            next =>
                              rw [dif_neg bindingMismatch]
                              by_cases verifierRoom : StageHasOracleRoom
                                  configuration.oracleLimits proverFinalOracle
                                  configuration.verifierFuel
                              next =>
                                simp only [verifierRoom, if_pos]
                                intro verifierStage verifierFinalOracle
                                  verifierCoherent
                                cases verifierStageExact : verifierStage with
                                | completed verifierResult =>
                                    simp only
                                    let verifierQueries :=
                                      (historySince proverFinalOracle
                                        verifierFinalOracle).length
                                    let afterVerifier := afterProver.addCharges
                                      [.verifierSuffixQueries verifierQueries]
                                    have afterVerifierInvariant :
                                        SchedulerNativeNodeStoreInvariant
                                          runtime afterVerifier :=
                                      node_store_invariant_add_charges runtime
                                        afterProver _ afterProverInvariant
                                    cases verifierResultExact : verifierResult with
                                    | error failure =>
                                        cases failure with
                                        | oracleAbort reason =>
                                            exact failureSafe prepared.request
                                              (.verifierSuffixAbort reason)
                                              afterVerifier
                                              afterVerifierInvariant
                                        | timeout =>
                                            exact failureSafe prepared.request
                                              .verifierSuffixTimeout
                                              afterVerifier
                                              afterVerifierInvariant
                                    | ok verifierFinalState =>
                                        let transitionCount :=
                                          verifierFinalState.transitions.length
                                        let node : ConcreteRestorationNode
                                            Statement Proof Payload :=
                                          { parentRequest :=
                                              some prepared.request
                                            adversaryValue := adversaryValue
                                            proverEntryOracle := afterBoth
                                            proverFinalOracle :=
                                              proverFinalOracle
                                            verifierEntryOracle :=
                                              proverFinalOracle
                                            verifierFinalOracle :=
                                              verifierFinalOracle
                                            verifierEntryState :=
                                              prepared.restoredState
                                            verifierFinalState :=
                                              verifierFinalState }
                                        let charged := afterVerifier.addCharges
                                          [.verifierTransitions
                                            transitionCount]
                                        have chargedInvariant :
                                            SchedulerNativeNodeStoreInvariant
                                              runtime charged :=
                                          node_store_invariant_add_charges
                                            runtime afterVerifier _
                                            afterVerifierInvariant
                                        let added := charged.addNode node
                                        have addedInvariant :
                                            SchedulerNativeNodeStoreInvariant
                                              runtime added.2 :=
                                          node_store_invariant_add_prepared_child
                                            runtime charged prepared node
                                            chargedInvariant selection rfl rfl
                                        exact continuations (.added added.1)
                                          added.2 addedInvariant
                              next =>
                                simp only [verifierRoom, if_neg]
                                exact failureSafe prepared.request
                                  .verifierSuffixRoom afterProver
                                  afterProverInvariant
                  next =>
                    simp only [proverRoom, if_neg]
                    exact failureSafe prepared.request .proverReplayRoom
                      afterProgramming afterProgrammingInvariant
                next =>
                  simp only [afterCoherent, if_neg]
                  exact failureSafe prepared.request
                    .incoherentProgrammedOracle afterProgramming
                    afterProgrammingInvariant
          next =>
            simp only [pairRoom, if_neg]
            exact failureSafe prepared.request .pairExposureLimit withPrefix
              withPrefixInvariant
        next =>
          simp only [globalLimit, if_neg]
          exact failureSafe prepared.request .globalLimitTooSmall withPrefix
            withPrefixInvariant
      next =>
        simp only [prefixCoherent, if_neg]
        exact failureSafe prepared.request .incoherentPrefixOracle withPrefix
          withPrefixInvariant

/-- The complete concrete client cursor preserves the node-store invariant
from its literal singleton root through every adaptive request/reply branch. -/
theorem concrete_restoration_client_all_returned_node_store
    {TapeIdentity Statement Proof Payload Result : Type u}
    {globalOracleCalls : Nat}
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (restorationFuel : Nat)
    (client : ConcreteRestorationClient Result) :
    SchedulerNativeCursorAllReturned
      (fun run => SchedulerNativeNodeStoreInvariant runtime run.accumulator)
      (startConcreteRestorationClientFromRoot
        (globalOracleCalls := globalOracleCalls) startProgram environment
        runtime.node configuration restorationFuel client) := by
  let motive := fun (_fuel : Nat)
      (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
      (_residualClient : ConcreteRestorationClient Result)
      (cursor : SchedulerNativeCursor globalOracleCalls
        (ConcreteRestorationClientRun Statement Proof Payload Result)) =>
      SchedulerNativeNodeStoreInvariant runtime accumulator →
        SchedulerNativeCursorAllReturned
          (fun run => SchedulerNativeNodeStoreInvariant runtime
            run.accumulator)
          cursor
  have induction :=
    start_concrete_restoration_client_from_root_dependent_induction
      (globalOracleCalls := globalOracleCalls) startProgram environment
      runtime.node configuration restorationFuel client motive
      (by
        intro fuel accumulator result invariant
        exact invariant)
      (by
        intro accumulator request next invariant
        exact node_store_invariant_add_failure runtime accumulator request
          .restorationFuelExhausted invariant)
      (by
        intro fuel accumulator request next resume continuations invariant
        exact dispatch_one_concrete_restoration_preserves_node_store runtime
          startProgram environment configuration accumulator request resume
          (fun reply nextAccumulator nextInvariant =>
            continuations reply nextAccumulator nextInvariant)
          invariant)
  exact induction (initial_node_store_invariant runtime)

/-- Static predicate used after the two initial machine prefixes have fixed a
literal operational root. -/
def CompletedWithExactRootAndStore
    {TapeIdentity Statement Proof Payload Result : Type u}
    (expected : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload) :
    SchedulerNativePlainRomResult TapeIdentity Statement Proof Payload Result →
      Prop
  | .initialFailure _reason => False
  | .completed runtime clientRun =>
      runtime = expected ∧
        SchedulerNativeNodeStoreInvariant expected clientRun.accumulator

/-- Mapping the actual concrete-client cursor into a completed plain-ROM
result fixes the root and retains its real store invariant. -/
theorem mapped_concrete_client_has_exact_root_and_store
    {TapeIdentity Statement Proof Payload Result : Type u}
    {globalOracleCalls : Nat}
    (expected : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (cursor : SchedulerNativeCursor globalOracleCalls
      (ConcreteRestorationClientRun Statement Proof Payload Result))
    (safe : SchedulerNativeCursorAllReturned
      (fun run => SchedulerNativeNodeStoreInvariant expected run.accumulator)
      cursor) :
    SchedulerNativeCursorAllReturned
      (CompletedWithExactRootAndStore expected)
      (mapSchedulerNativeCursorResult
        (fun clientRun => SchedulerNativePlainRomResult.completed expected
          clientRun)
        cursor) := by
  apply all_returned_map
    (fun run => SchedulerNativeNodeStoreInvariant expected run.accumulator)
    (CompletedWithExactRootAndStore expected)
    (fun clientRun => SchedulerNativePlainRomResult.completed expected
      clientRun)
  · intro clientRun invariant
    exact ⟨rfl, invariant⟩
  · exact safe

/-! ## Invert the two initial segments of the actual full cursor -/

/-- The complete full-scheduler factorization.  `prefixes.verifier.remaining`
is not an arbitrary answer list: it is the literal chronological suffix left
after the two root machine prefixes, and `clientTerminalExact` runs the
concrete restoration client on exactly that suffix. -/
structure CompletedSchedulerNativePlainRomProjection
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type u}
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape)
    (restorationConfiguration : ConcreteRestorationConfiguration)
    (restorationFuel : Nat)
    (client : ConcreteRestorationClient Result)
    (answers : List Digest256)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (clientRun : ConcreteRestorationClientRun Statement Proof Payload Result) :
    Type u where
  prefixes : FullResultRootProjectedPrefixes
    (Final := SchedulerNativePlainRomResult TapeIdentity Statement Proof
      Payload Result) machine hidden answers runtime
  nodeStoreInvariant :
    SchedulerNativeNodeStoreInvariant runtime clientRun.accumulator
  clientCurrentTransitionFuel : Nat
  clientTerminalExact :
    runSchedulerNativeListTerminalFrom transitionFuel
        clientCurrentTransitionFuel
        (startConcreteRestorationClientFromRoot
          (globalOracleCalls := globalOracleCalls)
          (machine.blackBox.start hidden machine.observation)
          machine.environment runtime.node restorationConfiguration
          restorationFuel client)
        prefixes.verifier.remaining = .returned clientRun
  sameHiddenTapeIdentity :
    runtime.tapeIdentity = machine.tapeIdentity hidden

theorem completed_scheduler_native_plain_rom_gives_root_runs_and_store_nonempty
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type u}
    {globalOracleCalls : Nat}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape)
    (limitBounds : SchedulerNativeRootLimitBounds machine globalOracleCalls)
    (restorationConfiguration : ConcreteRestorationConfiguration)
    (restorationFuel : Nat)
    (client : ConcreteRestorationClient Result)
    (answers : List Digest256)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (clientRun : ConcreteRestorationClientRun Statement Proof Payload Result)
    (completed :
      runSchedulerNativeListTerminal transitionFuel
          (schedulerNativePlainRomCursor machine hidden limitBounds
            restorationConfiguration restorationFuel client) answers =
        .returned (.completed runtime clientRun)) :
    Nonempty (CompletedSchedulerNativePlainRomProjection
      (globalOracleCalls := globalOracleCalls) transitionFuel machine hidden
      restorationConfiguration restorationFuel client answers runtime
      clientRun) := by
  unfold runSchedulerNativeListTerminal at completed
  unfold schedulerNativePlainRomCursor at completed
  split at completed
  next adversaryRoom =>
    rw [run_scheduler_native_list_machine_factorization_of_positive
      (transitionFuel := transitionFuel)
      (currentTransitionFuel := transitionFuel) (answers := answers)
      (positive := positive)] at completed
    obtain ⟨adversary, adversaryExecution, completed⟩ :=
      terminal_after_projected_machine_prefix_returned_elim
        (positive := positive) (completed := completed)
    cases adversaryStage : adversary.result with
    | completed adversaryTotalized =>
        cases adversaryTotalized with
        | error failure =>
            cases failure with
            | oracleAbort reason =>
                simp only [adversaryStage] at completed
                rw [run_scheduler_native_list_returned_from
                  transitionFuel positive] at completed
                split at completed <;> simp at completed
            | timeout =>
                simp only [adversaryStage] at completed
                rw [run_scheduler_native_list_returned_from
                  transitionFuel positive] at completed
                split at completed <;> simp at completed
        | ok adversaryValue =>
            simp only [adversaryStage] at completed
            split at completed
            next verifierRoom =>
              rw [run_scheduler_native_list_machine_factorization_of_positive
                (transitionFuel := transitionFuel)
                (positive := positive)] at completed
              obtain ⟨verifier, verifierExecution, completed⟩ :=
                terminal_after_projected_machine_prefix_returned_elim
                  (positive := positive) (completed := completed)
              cases verifierStage : verifier.result with
              | completed verifierTotalized =>
                  cases verifierTotalized with
                  | error failure =>
                      cases failure with
                      | oracleAbort reason =>
                          simp only [verifierStage] at completed
                          rw [run_scheduler_native_list_returned_from
                            transitionFuel positive] at completed
                          split at completed <;> simp at completed
                      | timeout =>
                          simp only [verifierStage] at completed
                          rw [run_scheduler_native_list_returned_from
                            transitionFuel positive] at completed
                          split at completed <;> simp at completed
                  | ok verifierFinalState =>
                      simp only [verifierStage] at completed
                      let expected := operationalRootRuntime
                        (machine.tapeIdentity hidden) adversaryValue
                        adversary.finalState verifier.finalState
                        verifierFinalState
                      let clientCursor :=
                        startConcreteRestorationClientFromRoot
                          (globalOracleCalls := globalOracleCalls)
                          (machine.blackBox.start hidden machine.observation)
                          machine.environment expected.node
                          restorationConfiguration restorationFuel client
                      have clientSafe : SchedulerNativeCursorAllReturned
                          (fun run => SchedulerNativeNodeStoreInvariant expected
                            run.accumulator)
                          clientCursor :=
                        concrete_restoration_client_all_returned_node_store
                          expected
                          (machine.blackBox.start hidden machine.observation)
                          machine.environment restorationConfiguration
                          restorationFuel client
                      have mappedSafe :=
                        mapped_concrete_client_has_exact_root_and_store expected
                          clientCursor clientSafe
                      have terminalSafe :=
                        run_scheduler_native_list_terminal_respects_all_returned
                          (CompletedWithExactRootAndStore expected)
                          transitionFuel _ _ verifier.remaining
                          (.completed runtime clientRun) mappedSafe (by
                            simpa [expected, clientCursor] using completed)
                      rcases terminalSafe with ⟨runtimeExact, storeExact⟩
                      let clientCurrentTransitionFuel :=
                        machinePrefixContinuationTransitionFuel transitionFuel
                          (machinePrefixContinuationTransitionFuel
                            transitionFuel (transitionFuel - 1)
                              adversary.freshQueries - 1)
                          verifier.freshQueries
                      have clientTerminal :
                          ∃ currentTransitionFuel,
                            runSchedulerNativeListTerminalFrom transitionFuel
                                currentTransitionFuel clientCursor
                                verifier.remaining = .returned clientRun := by
                        refine ⟨clientCurrentTransitionFuel, ?_⟩
                        apply
                          run_scheduler_native_list_terminal_from_completed_map_reflects
                            expected transitionFuel clientCurrentTransitionFuel
                              clientCursor
                              verifier.remaining clientRun
                        simpa [runtimeExact, expected, clientCursor,
                          clientCurrentTransitionFuel] using completed
                      subst runtime
                      rcases clientTerminal with
                        ⟨clientCurrentTransitionFuel, clientTerminalExact⟩
                      refine ⟨
                        { prefixes := ?_
                          nodeStoreInvariant := storeExact
                          clientCurrentTransitionFuel :=
                            clientCurrentTransitionFuel
                          clientTerminalExact := ?_
                          sameHiddenTapeIdentity := rfl }⟩
                      · exact
                          { adversary := adversary
                            adversaryValue := adversaryValue
                            adversaryResult := adversaryStage
                            verifier := verifier
                            verifierFinalStateValue := verifierFinalState
                            verifierResult := verifierStage
                            runtimeExact := rfl }
                      · simpa [expected, clientCursor] using
                          clientTerminalExact
            next verifierNoRoom =>
              rw [run_scheduler_native_list_returned_from
                transitionFuel positive] at completed
              split at completed <;> simp at completed
  next adversaryNoRoom =>
    rw [run_scheduler_native_list_returned_of_positive transitionFuel positive]
      at completed
    simp at completed

/-- Chosen proof-relevant projection.  Its existence is proved above; the
choice is used only to expose the concrete prefixes and residual client fuel
to later operational compositions. -/
noncomputable def completed_scheduler_native_plain_rom_gives_root_runs_and_store
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type u}
    {globalOracleCalls : Nat}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape)
    (limitBounds : SchedulerNativeRootLimitBounds machine globalOracleCalls)
    (restorationConfiguration : ConcreteRestorationConfiguration)
    (restorationFuel : Nat)
    (client : ConcreteRestorationClient Result)
    (answers : List Digest256)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (clientRun : ConcreteRestorationClientRun Statement Proof Payload Result)
    (completed :
      runSchedulerNativeListTerminal transitionFuel
          (schedulerNativePlainRomCursor machine hidden limitBounds
            restorationConfiguration restorationFuel client) answers =
        .returned (.completed runtime clientRun)) :
    CompletedSchedulerNativePlainRomProjection
      (globalOracleCalls := globalOracleCalls) transitionFuel machine hidden
      restorationConfiguration restorationFuel client answers runtime
      clientRun :=
  Classical.choice
    (completed_scheduler_native_plain_rom_gives_root_runs_and_store_nonempty
      transitionFuel positive machine hidden limitBounds
      restorationConfiguration restorationFuel client answers runtime clientRun
      completed)

/-! ## Principal exact full-run projection -/

/-- Root and append-only ancestry facts recovered from a completed full run.
This structure deliberately does not claim that each child already carries
the stronger replay/suffix trace certificate required for legal restoration;
that separate trace projection is proved in the next layer. -/
structure CompletedExactPlainRomRootAndStoreProjection
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (clientRun : ConcreteRestorationClientRun Statement Proof Payload Result) :
    Type where
  rootPrefixes : FullResultRootProjectedPrefixes
    (Final := SchedulerNativePlainRomResult TapeIdentity Statement Proof
      Payload Result)
    configuration.machine sample.1 (freshAnswerTapeToList sample.2) runtime
  projectedRuns :
    RootProjectedTotalizedRuns configuration.machine sample.1 runtime
  rootInvariant : SchedulerNativePlainRomRootInvariant runtime
  nodeStoreInvariant :
    SchedulerNativeNodeStoreInvariant runtime clientRun.accumulator
  sameHiddenTapeIdentity :
    runtime.tapeIdentity = configuration.machine.tapeIdentity sample.1
  clientCurrentTransitionFuel : Nat
  clientTerminalExact :
    runSchedulerNativeListTerminalFrom
        transitionFuel
        clientCurrentTransitionFuel
        (startConcreteRestorationClientFromRoot
          (globalOracleCalls := globalFull256OracleCallCap parameters)
          (configuration.machine.blackBox.start sample.1
            configuration.machine.observation)
          configuration.machine.environment runtime.node
          configuration.restorationConfiguration
          configuration.restorationFuel configuration.client)
        rootPrefixes.verifier.remaining = .returned clientRun
  clientHaltExact :
    (∃ result, clientRun.halt = .returned result) ∨
      clientRun.halt = .restorationFuelExhausted

/-- Completed full-run bridge for the literal client halt, operational root,
and append-only node ancestry.  Child replay/suffix execution equations are
intentionally outside this theorem. -/
theorem completed_exact_plain_rom_gives_root_and_store_projection_nonempty
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (clientRun : ConcreteRestorationClientRun Statement Proof Payload Result)
    (completed :
      (runExactPlainRom transitionFuel configuration sample).terminal =
        .returned (.completed runtime clientRun)) :
    Nonempty (CompletedExactPlainRomRootAndStoreProjection transitionFuel
      configuration sample runtime clientRun) := by
  have listCompleted :
      runSchedulerNativeListTerminal transitionFuel
          (exactPlainRomCursor configuration sample.1)
          (freshAnswerTapeToList sample.2) =
        .returned (.completed runtime clientRun) := by
    rw [← run_scheduler_native_terminal_eq_list]
    exact completed
  have rootRunsAndStore :=
    completed_scheduler_native_plain_rom_gives_root_runs_and_store
      transitionFuel positive configuration.machine sample.1
      configuration.rootLimitBounds configuration.restorationConfiguration
      configuration.restorationFuel configuration.client
      (freshAnswerTapeToList sample.2) runtime clientRun (by
        simpa [exactPlainRomCursor] using listCompleted)
  have projectedRuns := rootRunsAndStore.prefixes.totalizedRuns
    configuration.machine sample.1 (freshAnswerTapeToList sample.2) runtime
  refine ⟨
    { rootPrefixes := rootRunsAndStore.prefixes
      projectedRuns := projectedRuns
      rootInvariant := projected_root_runs_imply_root_invariant
        configuration.machine sample.1 runtime projectedRuns
      nodeStoreInvariant := rootRunsAndStore.nodeStoreInvariant
      sameHiddenTapeIdentity := rootRunsAndStore.sameHiddenTapeIdentity
      clientCurrentTransitionFuel :=
        rootRunsAndStore.clientCurrentTransitionFuel
      clientTerminalExact := by
        exact rootRunsAndStore.clientTerminalExact
      clientHaltExact := ?_ }⟩
  cases halted : clientRun.halt with
  | returned result => exact Or.inl ⟨result, rfl⟩
  | restorationFuelExhausted => exact Or.inr rfl

/-- Chosen proof-relevant exact-run projection.  All fields come from the
proved nonempty package above; callers supply only the literal completed
terminal equation. -/
noncomputable def completed_exact_plain_rom_gives_root_and_store_projection
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (clientRun : ConcreteRestorationClientRun Statement Proof Payload Result)
    (completed :
      (runExactPlainRom transitionFuel configuration sample).terminal =
        .returned (.completed runtime clientRun)) :
    CompletedExactPlainRomRootAndStoreProjection transitionFuel configuration
      sample runtime clientRun :=
  Classical.choice
    (completed_exact_plain_rom_gives_root_and_store_projection_nonempty
      transitionFuel positive configuration sample runtime clientRun completed)

/-- Root-only source observation and the result-carrying restoration run
return the identical operational root on the same hidden/master-tape sample.
This is derived from their two actual projected prefixes; no alignment premise
is accepted. -/
theorem completed_exact_plain_rom_root_and_full_runtime_eq
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters)
    (rootRuntime fullRuntime : SchedulerNativePlainRomRootRuntime TapeIdentity
      Statement Proof Payload)
    (rootClientRun : ConcreteRestorationClientRun Statement Proof Payload PUnit)
    (fullClientRun : ConcreteRestorationClientRun Statement Proof Payload
      Result)
    (rootCompleted :
      (runExactPlainRomRoot transitionFuel configuration sample).terminal =
        .returned (.completed rootRuntime rootClientRun))
    (fullCompleted :
      (runExactPlainRom transitionFuel configuration sample).terminal =
        .returned (.completed fullRuntime fullClientRun)) :
    rootRuntime = fullRuntime := by
  have rootListCompleted :
      runSchedulerNativeListTerminal transitionFuel
          (exactPlainRomRootCursor configuration sample.1)
          (freshAnswerTapeToList sample.2) =
        .returned (.completed rootRuntime rootClientRun) := by
    rw [← run_scheduler_native_terminal_eq_list]
    exact rootCompleted
  have recovered :=
    completed_scheduler_native_plain_rom_root_recovers_runtime transitionFuel
      positive configuration.machine sample.1 configuration.rootLimitBounds
      configuration.restorationConfiguration
      (freshAnswerTapeToList sample.2) rootRuntime rootClientRun (by
        simpa [exactPlainRomRootCursor] using rootListCompleted)
  have rootPrefixes := recoveredRootRuntimeProjectedPrefixes
    configuration.machine sample.1 (freshAnswerTapeToList sample.2)
      rootRuntime recovered
  have fullProjection :=
    completed_exact_plain_rom_gives_root_and_store_projection transitionFuel
      positive configuration sample fullRuntime fullClientRun fullCompleted
  exact root_and_full_projected_prefixes_runtime_eq configuration.machine
    sample.1 (freshAnswerTapeToList sample.2) rootRuntime fullRuntime
      rootPrefixes fullProjection.rootPrefixes

#print axioms seek_scheduler_native_all_returned
#print axioms run_scheduler_native_list_terminal_respects_all_returned
#print axioms prepare_concrete_restoration_ready_selection_exact
#print axioms node_store_invariant_add_prepared_child
#print axioms dispatch_one_concrete_restoration_preserves_node_store
#print axioms concrete_restoration_client_all_returned_node_store
#print axioms mapped_concrete_client_has_exact_root_and_store
#print axioms completed_scheduler_native_plain_rom_gives_root_runs_and_store
#print axioms completed_exact_plain_rom_gives_root_and_store_projection
#print axioms completed_exact_plain_rom_root_and_full_runtime_eq

end


end AspisK1.V7Tag73CompletedFullRunProjection
