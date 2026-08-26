import AspisFormal.K1.V7Tag73ExactCompilerOperationalCaps
import AspisFormal.K1.V7Tag73CompletedRootProjection

/-!
# Exact resource induction for the concrete Tag-73 restoration client

This module is the operational consumer of the closed resource arithmetic.
It strengthens scheduler continuation safety with the literal projected
machine-run certificates, maintains the `Q` bound for every stored prover
segment, and prepares the dependent induction over the actual private client
interpreter.

No acceptance event, extraction outcome, ROM bad-event cover, or compiler
conclusion is a premise here.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ExactCompilerClientCaps

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AtomicPairFork
open AspisK1.V7Tag73AtomicPairReplay
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73ProjectedMachinePrefix
open AspisK1.V7Tag73SchedulerMachineFactorization
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SequentialOracleRuns
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73RawProverMessages
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73RawStrictReplacementSuffix
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73TotalizedMachineReflection
open AspisK1.V7Tag73ExactCompilerOperationalCaps
open AspisK1.V7Tag73CompletedRootProjection

noncomputable section

universe u v

/-! ## Structural transport of projected scheduler certificates -/

theorem scheduler_native_all_projected_returned_mono
    {globalOracleCalls : Nat} {Result : Type u}
    {P Q : Result → Prop}
    (imp : ∀ result, P result → Q result) :
    ∀ {cursor : SchedulerNativeCursor globalOracleCalls Result},
      SchedulerNativeCursorAllProjectedReturned P cursor →
        SchedulerNativeCursorAllProjectedReturned Q cursor := by
  intro cursor safe
  induction safe with
  | returned result holds =>
      exact .returned result (imp result holds)
  | failed reason =>
      exact .failed reason
  | machine limits limitBound actor state program fuel coherent onReturned
      safe ih =>
      apply SchedulerNativeCursorAllProjectedReturned.machine
        limits limitBound actor state program fuel coherent onReturned
      intro available returned
      exact ih available returned
  | forkPair frozenHistory pairRoom outputInput advanceInput template next safe
      ih =>
      apply SchedulerNativeCursorAllProjectedReturned.forkPair frozenHistory
        pairRoom outputInput advanceInput template next
      intro configuration
      exact ih configuration
  | forkAdvance frozenHistory pairRoom outputInput advanceInput template
      forkOutput next safe ih =>
      apply SchedulerNativeCursorAllProjectedReturned.forkAdvance frozenHistory
        pairRoom outputInput advanceInput template forkOutput next
      intro configuration
      exact ih configuration

/-! ## Every stored prover segment retains its literal `Q` cap -/

def AllStoredProverHistoriesWithin
    {Statement Proof Payload : Type*} (Q : Nat)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload) :
    Prop :=
  ∀ node ∈ accumulator.nodes, node.proverHistory.length ≤ Q

theorem list_getElem?_some_is_member
    {α : Type*} : ∀ (values : List α) (index : Nat) (value : α),
      values[index]? = some value → value ∈ values := by
  intro values
  induction values with
  | nil =>
      intro index value found
      simp at found
  | cons head tail ih =>
      intro index value found
      cases index with
      | zero =>
          simp at found
          subst value
          simp
      | succ index =>
          have tailFound : tail[index]? = some value := by
            simpa using found
          exact List.mem_cons_of_mem head (ih index value tailFound)

theorem all_stored_histories_give_lookup_bound
    {Statement Proof Payload : Type*} (Q : Nat)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (stored : AllStoredProverHistoriesWithin Q accumulator) :
    AccumulatorProverHistoryBound Q accumulator := by
  intro nodeId node found
  apply stored node
  apply list_getElem?_some_is_member accumulator.nodes nodeId node
  simpa [ConcreteRestorationAccumulator.node?] using found

theorem initial_all_stored_prover_histories
    {Statement Proof Payload : Type*} (Q : Nat)
    (root : ConcreteRestorationNode Statement Proof Payload)
    (rootBound : root.proverHistory.length ≤ Q) :
    AllStoredProverHistoriesWithin Q
      (initialRestorationAccumulatorFromRoot root) := by
  intro node member
  have nodeExact : node = root := by
    simpa [initialRestorationAccumulatorFromRoot] using member
  subst node
  exact rootBound

theorem all_stored_prover_histories_add_charges
    {Statement Proof Payload : Type*} (Q : Nat)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (charges : List ConcreteRestorationCharge)
    (stored : AllStoredProverHistoriesWithin Q accumulator) :
    AllStoredProverHistoriesWithin Q (accumulator.addCharges charges) := by
  simpa [AllStoredProverHistoriesWithin,
    ConcreteRestorationAccumulator.addCharges] using stored

theorem all_stored_prover_histories_add_failure
    {Statement Proof Payload : Type*} (Q : Nat)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (request : ConcreteRestorationRequest)
    (reason : ConcreteRestorationFailure)
    (stored : AllStoredProverHistoriesWithin Q accumulator) :
    AllStoredProverHistoriesWithin Q
      (accumulator.addFailure request reason) := by
  simpa [AllStoredProverHistoriesWithin,
    ConcreteRestorationAccumulator.addFailure] using stored

theorem all_stored_prover_histories_add_node
    {Statement Proof Payload : Type*} (Q : Nat)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (node : ConcreteRestorationNode Statement Proof Payload)
    (stored : AllStoredProverHistoriesWithin Q accumulator)
    (nodeBound : node.proverHistory.length ≤ Q) :
    AllStoredProverHistoriesWithin Q (accumulator.addNode node).2 := by
  intro candidate member
  have cases : candidate ∈ accumulator.nodes ∨ candidate = node := by
    simpa [ConcreteRestorationAccumulator.addNode] using member
  rcases cases with oldMember | rfl
  · exact stored candidate oldMember
  · exact nodeBound

/-! ## Resource-delta composition in client order -/

/-- The client induction encounters the one-request delta first and the
remaining `attempts` requests second.  This is the chronological counterpart
of `accumulator_within_restoration_attempts_succ`. -/
theorem one_delta_then_accumulator_within_attempts
    {Statement Proof Payload : Type*}
    (Q driverFuel attempts : Nat)
    (initial middle final :
      ConcreteRestorationAccumulator Statement Proof Payload)
    (delta : OneRestorationAccumulatorDelta Q driverFuel initial middle)
    (tail : AccumulatorWithinRestorationAttempts Q driverFuel attempts middle
      final) :
    AccumulatorWithinRestorationAttempts Q driverFuel (attempts + 1) initial
      final := by
  rcases delta with
    ⟨deltaQueries, deltaForks, deltaProgrammed, deltaRestarts,
      deltaTransitions⟩
  rcases tail with
    ⟨tailQueries, tailForks, tailProgrammed, tailRestarts, tailTransitions⟩
  constructor <;>
    simp only [Nat.add_mul, Nat.one_mul] <;>
    omega

/-- Resource totals depend only on the append-only charge log.  This lemma is
the common arithmetic endpoint for all dispatcher branches, including a
failure record or appended node after the charges were installed. -/
theorem one_restoration_delta_of_charge_log_extension
    {Statement Proof Payload : Type*}
    (Q driverFuel : Nat)
    (before after : ConcreteRestorationAccumulator Statement Proof Payload)
    (extension : List ConcreteRestorationCharge)
    (chargesExact : after.charges = before.charges ++ extension)
    (queryBound :
      (extension.map ConcreteRestorationCharge.oracleQueries).sum ≤
        2 * Q + 1511)
    (forkBound :
      (extension.map
        ConcreteRestorationCharge.uniformForkCoordinates).sum ≤ 2)
    (programmedBound :
      (extension.map
        ConcreteRestorationCharge.successfulProgrammingPoints).sum ≤ 2)
    (restartBound :
      (extension.map ConcreteRestorationCharge.restarts).sum ≤ 2)
    (transitionBound :
      (extension.map
        ConcreteRestorationCharge.protocolTransitions).sum ≤ driverFuel) :
    OneRestorationAccumulatorDelta Q driverFuel before after := by
  constructor
  · unfold ConcreteRestorationAccumulator.oracleQueryTotal
    rw [chargesExact, List.map_append, List.sum_append]
    omega
  · unfold ConcreteRestorationAccumulator.uniformForkCoordinateTotal
    rw [chargesExact, List.map_append, List.sum_append]
    omega
  · unfold ConcreteRestorationAccumulator.programmedPointTotal
    rw [chargesExact, List.map_append, List.sum_append]
    omega
  · unfold ConcreteRestorationAccumulator.restartTotal
    rw [chargesExact, List.map_append, List.sum_append]
    omega
  · unfold ConcreteRestorationAccumulator.verifierTransitionTotal
    rw [chargesExact, List.map_append, List.sum_append]
    omega

/-! ## Exact projected verifier-stage reflection -/

/-- A prepared `.ready` result carries the literal restored state computed by
the validated transition lookup; callers cannot install another snapshot in
this theorem. -/
theorem prepared_ready_restored_state_exact
    {Statement Proof Payload : Type*}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (configuration : ConcreteRestorationConfiguration)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (request : ConcreteRestorationRequest)
    (prepared : PreparedConcreteRestoration Statement Proof Payload)
    (ready : prepareConcreteRestorationFromStartProgram startProgram
      configuration accumulator request = .ready prepared) :
    prepared.restoredState = restoreIndexedTransition prepared.transition := by
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

/-- Remove the result-only scheduler wrapper from an actual projected
machine return.  The controller and answer tape are reconstructed from the
certificate itself. -/
theorem projected_scheduler_stage_completed_reflects
    {Final : Type u} {Payload : Type v}
    (limits : OracleLimits) (actor : QueryActor) (fuel : Nat)
    (entry : OracleState) (program : OracleMachine Payload)
    (available : List Digest256)
    (returned : ProjectedMachinePrefixReturned limits actor fuel entry
      (schedulerStageProgram Final program) available)
    (result : Payload)
    (resultExact : returned.result = .completed result) :
    let controller := controllerFromProjectedFreshAnswers entry.history
      (returned.freshQueries.map Prod.snd)
    runMachine controller limits actor fuel entry program =
      { halt := .returned result
        oracle := returned.finalState
        steps := returned.steps } := by
  let controller := controllerFromProjectedFreshAnswers entry.history
    (returned.freshQueries.map Prod.snd)
  have entryCoherent : HistoryTotalCoherent entry :=
    projected_returned_trace_entry_coherent limits actor fuel entry
      (schedulerStageProgram Final program) returned.freshQueries
      returned.result returned.finalState returned.steps returned.trace
  have wrapped := projected_machine_prefix_returned_run_exact limits actor fuel
    entry (schedulerStageProgram Final program) available returned entryCoherent
  rw [resultExact] at wrapped
  exact run_machine_scheduler_stage_completed_reflects (Final := Final)
    controller limits actor fuel entry program result returned.finalState
      returned.steps wrapped

/-- Consequently, an actual projected successful restored-verifier stage has
at most the raw driver's supplied transition fuel. -/
theorem projected_totalized_restored_driver_transition_count_le
    {Final : Type u}
    (limits : OracleLimits) (fuel : Nat)
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (driverFuel : Nat) (transition : FutureFreeTransition)
    (restoredState : FutureFreeVerifierState)
    (restoredExact : restoredState = restoreIndexedTransition transition)
    (entry : OracleState) (available : List Digest256)
    (returned : ProjectedMachinePrefixReturned limits .verifier fuel entry
      (schedulerStageProgram Final
        (totalizeOracleMachine fuel
          (driveRawFutureFree environment raw driverFuel
            restoredState))) available)
    (result : FutureFreeVerifierState)
    (resultExact : returned.result = .completed (.ok result)) :
    result.transitions.length ≤ driverFuel := by
  subst restoredState
  let controller := controllerFromProjectedFreshAnswers entry.history
    (returned.freshQueries.map Prod.snd)
  have reflected := projected_scheduler_stage_completed_reflects
    (Final := Final)
    (Payload := Except TotalizedMachineFailure FutureFreeVerifierState) limits
    .verifier fuel entry
    (totalizeOracleMachine fuel
      (driveRawFutureFree environment raw driverFuel
        (restoreIndexedTransition transition)))
    available returned (.ok result) resultExact
  exact totalized_restored_driver_transition_count_le controller limits
    environment raw fuel driverFuel transition entry returned.finalState result
      returned.steps reflected

/-! ## Pair programming has a literal two-point cap -/

/-- A failed pair-programming attempt has inserted either zero or one point;
success is charged separately as exactly two. -/
theorem program_concrete_pair_failure_inserted_le_one
    (limits : OracleLimits) (order : PairProgrammingOrder)
    (state : OracleState) (outputInput advanceInput : ShaInput)
    (forkOutput forkAdvance : Digest256)
    (reason : ConcreteRestorationFailure) (inserted : Nat)
    (failed : programConcretePair limits order state outputInput advanceInput
      forkOutput forkAdvance = .failed reason inserted) :
    inserted ≤ 1 := by
  unfold programConcretePair at failed
  split at failed
  · cases failed
    omega
  split at failed
  · cases failed
    omega
  split at failed
  · cases failed
    omega
  cases order with
  | outputThenAdvance =>
      dsimp only at failed
      cases first : programConcreteHalf limits state outputInput forkOutput with
      | error firstReason =>
          simp [first] at failed
          omega
      | ok afterFirst =>
          simp only [first] at failed
          cases second : programConcreteHalf limits afterFirst advanceInput
              forkAdvance with
          | error secondReason =>
              simp [second] at failed
              omega
          | ok afterBoth =>
              simp [second] at failed
  | advanceThenOutput =>
      dsimp only at failed
      cases first : programConcreteHalf limits state advanceInput forkAdvance with
      | error firstReason =>
          simp [first] at failed
          omega
      | ok afterFirst =>
          simp only [first] at failed
          cases second : programConcreteHalf limits afterFirst outputInput
              forkOutput with
          | error secondReason =>
              simp [second] at failed
              omega
          | ok afterBoth =>
              simp [second] at failed

/-! ## One actual dispatcher layer preserves the resource envelope -/

/-- Every normally returned continuation of the literal one-request
dispatcher is reached through an accumulator satisfying the exact one-request
delta.  Projected machine certificates, rather than arbitrary callback
states, bound the complete replay and verifier suffix query counts. -/
theorem dispatch_one_concrete_restoration_preserves_projected_resources
    {Statement Proof Payload Result : Type u}
    {globalOracleCalls : Nat}
    (Q : Nat)
    (P : ConcreteRestorationClientRun Statement Proof Payload Result → Prop)
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
    (proverFuelBound : configuration.proverReplayFuel ≤ Q)
    (verifierFuelBound : configuration.verifierFuel ≤ 1511)
    (stored : AllStoredProverHistoriesWithin Q accumulator)
    (continuations : ∀ reply nextAccumulator,
      OneRestorationAccumulatorDelta Q configuration.driverFuel accumulator
          nextAccumulator →
      AllStoredProverHistoriesWithin Q nextAccumulator →
      SchedulerNativeCursorAllProjectedReturned P
        (resume reply nextAccumulator)) :
    SchedulerNativeCursorAllProjectedReturned P
      (dispatchOneConcreteRestoration startProgram environment configuration
        accumulator request resume) := by
  have continueSafe : ∀ reply
      (nextAccumulator :
        ConcreteRestorationAccumulator Statement Proof Payload)
      (extension : List ConcreteRestorationCharge),
      nextAccumulator.charges = accumulator.charges ++ extension →
      (extension.map ConcreteRestorationCharge.oracleQueries).sum ≤
        2 * Q + 1511 →
      (extension.map
        ConcreteRestorationCharge.uniformForkCoordinates).sum ≤ 2 →
      (extension.map
        ConcreteRestorationCharge.successfulProgrammingPoints).sum ≤ 2 →
      (extension.map ConcreteRestorationCharge.restarts).sum ≤ 2 →
      (extension.map
        ConcreteRestorationCharge.protocolTransitions).sum ≤
          configuration.driverFuel →
      AllStoredProverHistoriesWithin Q nextAccumulator →
      SchedulerNativeCursorAllProjectedReturned P
        (resume reply nextAccumulator) := by
    intro reply nextAccumulator extension chargesExact queryBound forkBound
      programmedBound restartBound transitionBound nextStored
    apply continuations reply nextAccumulator
    · exact one_restoration_delta_of_charge_log_extension Q
        configuration.driverFuel accumulator nextAccumulator extension
        chargesExact queryBound forkBound programmedBound restartBound
        transitionBound
    · exact nextStored
  have nodeBound : AccumulatorProverHistoryBound Q accumulator :=
    all_stored_histories_give_lookup_bound Q accumulator stored
  generalize preparationExact :
    prepareConcreteRestorationFromStartProgram startProgram configuration
      accumulator request = preparation
  have preparationBounds := prepare_concrete_restoration_prefix_use_le Q
    startProgram configuration accumulator request nodeBound
  rw [preparationExact] at preparationBounds
  cases preparation with
  | failed reason prefixSteps prefixRestarts =>
      have prefixStepsBound : prefixSteps ≤ Q := by
        exact preparationBounds.1
      have prefixRestartsBound : prefixRestarts ≤ 1 := by
        exact preparationBounds.2
      let charged := accumulator.addCharges
        [.prefixReplayQueries prefixSteps, .restart prefixRestarts]
      let failedAccumulator := charged.addFailure request reason
      simp only [dispatchOneConcreteRestoration,
        dispatchConcreteRestoration, preparationExact]
      apply continueSafe (.failed reason) failedAccumulator
        [.prefixReplayQueries prefixSteps, .restart prefixRestarts]
      · simp [failedAccumulator, charged,
          ConcreteRestorationAccumulator.addCharges,
          ConcreteRestorationAccumulator.addFailure]
      · simp [ConcreteRestorationCharge.oracleQueries]
        omega
      · simp [ConcreteRestorationCharge.uniformForkCoordinates]
      · simp [ConcreteRestorationCharge.successfulProgrammingPoints]
      · simp [ConcreteRestorationCharge.restarts]
        omega
      · simp [ConcreteRestorationCharge.protocolTransitions]
      · exact all_stored_prover_histories_add_failure Q charged request reason
          (all_stored_prover_histories_add_charges Q accumulator _ stored)
  | ready prepared =>
      have prefixStepsBound : prepared.prefixSteps ≤ Q := preparationBounds.1
      have restoredStateExact := prepared_ready_restored_state_exact
        startProgram configuration accumulator request prepared
          preparationExact
      let prefixRestarts := if prepared.prefixRun.isSome then 1 else 0
      have prefixRestartsBound : prefixRestarts ≤ 1 := preparationBounds.2
      let withPrefix := accumulator.addCharges
        [.prefixReplayQueries prepared.prefixSteps, .restart prefixRestarts]
      have withPrefixStored : AllStoredProverHistoriesWithin Q withPrefix :=
        all_stored_prover_histories_add_charges Q accumulator _ stored
      simp only [dispatchOneConcreteRestoration,
        dispatchConcreteRestoration, preparationExact]
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
            apply SchedulerNativeCursorAllProjectedReturned.forkPair
            intro forkConfiguration
            let afterCoordinates := withPrefix.addCharges
              [.forkUniformCoordinates 2]
            have afterCoordinatesStored :
                AllStoredProverHistoriesWithin Q afterCoordinates :=
              all_stored_prover_histories_add_charges Q withPrefix _
                withPrefixStored
            cases programmed : programConcretePair configuration.oracleLimits
                configuration.pairProgrammingOrder prepared.programmingBase
                prepared.outputInput prepared.advanceInput
                forkConfiguration.forkOutput forkConfiguration.forkAdvance with
            | failed programmingReason inserted =>
                simp only [programmed]
                have insertedBound :=
                  program_concrete_pair_failure_inserted_le_one
                    configuration.oracleLimits
                    configuration.pairProgrammingOrder
                    prepared.programmingBase prepared.outputInput
                    prepared.advanceInput forkConfiguration.forkOutput
                    forkConfiguration.forkAdvance programmingReason inserted
                    programmed
                let afterProgramming := afterCoordinates.addCharges
                  [.programmedPoints inserted]
                let failedAccumulator := afterProgramming.addFailure
                  prepared.request programmingReason
                apply continueSafe (.failed programmingReason)
                  failedAccumulator
                  [.prefixReplayQueries prepared.prefixSteps,
                    .restart prefixRestarts, .forkUniformCoordinates 2,
                    .programmedPoints inserted]
                · simp [failedAccumulator, afterProgramming, afterCoordinates,
                    withPrefix, ConcreteRestorationAccumulator.addCharges,
                    ConcreteRestorationAccumulator.addFailure,
                    List.append_assoc]
                · simp [ConcreteRestorationCharge.oracleQueries]
                  omega
                · simp [ConcreteRestorationCharge.uniformForkCoordinates]
                · simp [ConcreteRestorationCharge.successfulProgrammingPoints]
                  omega
                · simp [ConcreteRestorationCharge.restarts]
                  omega
                · simp [ConcreteRestorationCharge.protocolTransitions]
                · exact all_stored_prover_histories_add_failure Q
                    afterProgramming prepared.request programmingReason
                    (all_stored_prover_histories_add_charges Q afterCoordinates
                      _ afterCoordinatesStored)
            | ready afterBoth =>
                simp only [programmed]
                let afterProgramming := afterCoordinates.addCharges
                  [.programmedPoints 2]
                have afterProgrammingStored :
                    AllStoredProverHistoriesWithin Q afterProgramming :=
                  all_stored_prover_histories_add_charges Q afterCoordinates _
                    afterCoordinatesStored
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
                    have atProverStartStored :
                        AllStoredProverHistoriesWithin Q atProverStart :=
                      all_stored_prover_histories_add_charges Q afterProgramming
                        _ afterProgrammingStored
                    apply SchedulerNativeCursorAllProjectedReturned.machine
                    intro available proverReturned
                    have proverQueriesBound :=
                      (projected_returned_history_length_le_fuel
                        configuration.oracleLimits .extractorReplay
                        configuration.proverReplayFuel afterBoth
                        (schedulerStageProgram
                          (ConcreteRestorationClientRun Statement Proof Payload
                            Result)
                          (totalizeOracleMachine
                            configuration.proverReplayFuel startProgram))
                        available proverReturned).trans proverFuelBound
                    cases proverResultExact : proverReturned.result with
                    | completed proverResult =>
                      simp only [proverResultExact]
                      let proverQueries :=
                        (historySince afterBoth
                          proverReturned.finalState).length
                      let afterProver := atProverStart.addCharges
                        [.completeFromStartQueries proverQueries]
                      have afterProverStored :
                          AllStoredProverHistoriesWithin Q afterProver :=
                        all_stored_prover_histories_add_charges Q atProverStart
                          _ atProverStartStored
                      cases proverResult with
                      | error failure =>
                          cases failure with
                          | oracleAbort abortReason =>
                              let failedAccumulator := afterProver.addFailure
                                prepared.request
                                  (.proverReplayAbort abortReason)
                              apply continueSafe
                                (.failed (.proverReplayAbort abortReason))
                                failedAccumulator
                                [.prefixReplayQueries prepared.prefixSteps,
                                  .restart prefixRestarts,
                                  .forkUniformCoordinates 2,
                                  .programmedPoints 2, .restart 1,
                                  .completeFromStartQueries proverQueries]
                              · simp [failedAccumulator, afterProver,
                                  atProverStart, afterProgramming,
                                  afterCoordinates, withPrefix,
                                  ConcreteRestorationAccumulator.addCharges,
                                  ConcreteRestorationAccumulator.addFailure,
                                  List.append_assoc]
                              · simp [ConcreteRestorationCharge.oracleQueries]
                                omega
                              · simp [ConcreteRestorationCharge.uniformForkCoordinates]
                              · simp [ConcreteRestorationCharge.successfulProgrammingPoints]
                              · simp [ConcreteRestorationCharge.restarts]
                                omega
                              · simp [ConcreteRestorationCharge.protocolTransitions]
                              · exact all_stored_prover_histories_add_failure Q
                                  afterProver prepared.request
                                  (.proverReplayAbort abortReason)
                                  afterProverStored
                          | timeout =>
                              let failedAccumulator := afterProver.addFailure
                                prepared.request .proverReplayTimeout
                              apply continueSafe (.failed .proverReplayTimeout)
                                failedAccumulator
                                [.prefixReplayQueries prepared.prefixSteps,
                                  .restart prefixRestarts,
                                  .forkUniformCoordinates 2,
                                  .programmedPoints 2, .restart 1,
                                  .completeFromStartQueries proverQueries]
                              · simp [failedAccumulator, afterProver,
                                  atProverStart, afterProgramming,
                                  afterCoordinates, withPrefix,
                                  ConcreteRestorationAccumulator.addCharges,
                                  ConcreteRestorationAccumulator.addFailure,
                                  List.append_assoc]
                              · simp [ConcreteRestorationCharge.oracleQueries]
                                omega
                              · simp [ConcreteRestorationCharge.uniformForkCoordinates]
                              · simp [ConcreteRestorationCharge.successfulProgrammingPoints]
                              · simp [ConcreteRestorationCharge.restarts]
                                omega
                              · simp [ConcreteRestorationCharge.protocolTransitions]
                              · exact all_stored_prover_histories_add_failure Q
                                  afterProver prepared.request
                                  .proverReplayTimeout afterProverStored
                      | ok adversaryValue =>
                          simp only
                          by_cases bindingMismatch :
                              FixedBindings.ofContext
                                  adversaryValue.rawMessages.context ≠
                                prepared.restoredState.current.bindings
                          next =>
                            rw [dif_pos bindingMismatch]
                            let failedAccumulator := afterProver.addFailure
                              prepared.request .restoredBindingMismatch
                            apply continueSafe
                              (.failed .restoredBindingMismatch)
                              failedAccumulator
                              [.prefixReplayQueries prepared.prefixSteps,
                                .restart prefixRestarts,
                                .forkUniformCoordinates 2,
                                .programmedPoints 2, .restart 1,
                                .completeFromStartQueries proverQueries]
                            · simp [failedAccumulator, afterProver,
                                atProverStart, afterProgramming,
                                afterCoordinates, withPrefix,
                                ConcreteRestorationAccumulator.addCharges,
                                ConcreteRestorationAccumulator.addFailure,
                                List.append_assoc]
                            · simp [ConcreteRestorationCharge.oracleQueries]
                              omega
                            · simp [ConcreteRestorationCharge.uniformForkCoordinates]
                            · simp [ConcreteRestorationCharge.successfulProgrammingPoints]
                            · simp [ConcreteRestorationCharge.restarts]
                              omega
                            · simp [ConcreteRestorationCharge.protocolTransitions]
                            · exact all_stored_prover_histories_add_failure Q
                                afterProver prepared.request
                                .restoredBindingMismatch afterProverStored
                          next =>
                            rw [dif_neg bindingMismatch]
                            by_cases verifierRoom : StageHasOracleRoom
                                configuration.oracleLimits
                                proverReturned.finalState
                                configuration.verifierFuel
                            next =>
                              simp only [verifierRoom, if_pos]
                              apply SchedulerNativeCursorAllProjectedReturned.machine
                              intro verifierAvailable verifierReturned
                              have verifierQueriesBound :=
                                (projected_returned_history_length_le_fuel
                                  configuration.oracleLimits .verifier
                                  configuration.verifierFuel
                                  proverReturned.finalState
                                  (schedulerStageProgram
                                    (ConcreteRestorationClientRun Statement Proof
                                      Payload Result)
                                    (totalizeOracleMachine
                                      configuration.verifierFuel
                                      (driveRawFutureFree environment
                                        adversaryValue.rawMessages
                                        configuration.driverFuel
                                        prepared.restoredState)))
                                  verifierAvailable verifierReturned).trans
                                    verifierFuelBound
                              cases verifierResultExact :
                                  verifierReturned.result with
                              | completed verifierResult =>
                                simp only [verifierResultExact]
                                let verifierQueries :=
                                  (historySince proverReturned.finalState
                                    verifierReturned.finalState).length
                                let afterVerifier := afterProver.addCharges
                                  [.verifierSuffixQueries verifierQueries]
                                have afterVerifierStored :
                                    AllStoredProverHistoriesWithin Q
                                      afterVerifier :=
                                  all_stored_prover_histories_add_charges Q
                                    afterProver _ afterProverStored
                                cases verifierResult with
                                | error failure =>
                                    cases failure with
                                    | oracleAbort abortReason =>
                                        let failedAccumulator :=
                                          afterVerifier.addFailure
                                            prepared.request
                                            (.verifierSuffixAbort abortReason)
                                        apply continueSafe
                                          (.failed
                                            (.verifierSuffixAbort abortReason))
                                          failedAccumulator
                                          [.prefixReplayQueries
                                              prepared.prefixSteps,
                                            .restart prefixRestarts,
                                            .forkUniformCoordinates 2,
                                            .programmedPoints 2, .restart 1,
                                            .completeFromStartQueries
                                              proverQueries,
                                            .verifierSuffixQueries
                                              verifierQueries]
                                        · simp [failedAccumulator,
                                            afterVerifier, afterProver,
                                            atProverStart, afterProgramming,
                                            afterCoordinates, withPrefix,
                                            ConcreteRestorationAccumulator.addCharges,
                                            ConcreteRestorationAccumulator.addFailure,
                                            List.append_assoc]
                                        · simp [ConcreteRestorationCharge.oracleQueries]
                                          omega
                                        · simp [ConcreteRestorationCharge.uniformForkCoordinates]
                                        · simp [ConcreteRestorationCharge.successfulProgrammingPoints]
                                        · simp [ConcreteRestorationCharge.restarts]
                                          omega
                                        · simp [ConcreteRestorationCharge.protocolTransitions]
                                        · exact all_stored_prover_histories_add_failure
                                            Q afterVerifier prepared.request
                                            (.verifierSuffixAbort abortReason)
                                            afterVerifierStored
                                    | timeout =>
                                        let failedAccumulator :=
                                          afterVerifier.addFailure
                                            prepared.request
                                            .verifierSuffixTimeout
                                        apply continueSafe
                                          (.failed .verifierSuffixTimeout)
                                          failedAccumulator
                                          [.prefixReplayQueries
                                              prepared.prefixSteps,
                                            .restart prefixRestarts,
                                            .forkUniformCoordinates 2,
                                            .programmedPoints 2, .restart 1,
                                            .completeFromStartQueries
                                              proverQueries,
                                            .verifierSuffixQueries
                                              verifierQueries]
                                        · simp [failedAccumulator,
                                            afterVerifier, afterProver,
                                            atProverStart, afterProgramming,
                                            afterCoordinates, withPrefix,
                                            ConcreteRestorationAccumulator.addCharges,
                                            ConcreteRestorationAccumulator.addFailure,
                                            List.append_assoc]
                                        · simp [ConcreteRestorationCharge.oracleQueries]
                                          omega
                                        · simp [ConcreteRestorationCharge.uniformForkCoordinates]
                                        · simp [ConcreteRestorationCharge.successfulProgrammingPoints]
                                        · simp [ConcreteRestorationCharge.restarts]
                                          omega
                                        · simp [ConcreteRestorationCharge.protocolTransitions]
                                        · exact all_stored_prover_histories_add_failure
                                            Q afterVerifier prepared.request
                                            .verifierSuffixTimeout
                                            afterVerifierStored
                                | ok verifierFinalState =>
                                    have transitionBound :=
                                      projected_totalized_restored_driver_transition_count_le
                                        (Final := ConcreteRestorationClientRun
                                          Statement Proof Payload Result)
                                        configuration.oracleLimits
                                        configuration.verifierFuel environment
                                        adversaryValue.rawMessages
                                        configuration.driverFuel
                                        prepared.transition
                                        prepared.restoredState
                                        restoredStateExact
                                        proverReturned.finalState
                                        verifierAvailable verifierReturned
                                        verifierFinalState
                                        verifierResultExact
                                    let transitionCount :=
                                      verifierFinalState.transitions.length
                                    let node : ConcreteRestorationNode Statement
                                        Proof Payload :=
                                      { parentRequest := some prepared.request
                                        adversaryValue := adversaryValue
                                        proverEntryOracle := afterBoth
                                        proverFinalOracle :=
                                          proverReturned.finalState
                                        verifierEntryOracle :=
                                          proverReturned.finalState
                                        verifierFinalOracle :=
                                          verifierReturned.finalState
                                        verifierEntryState :=
                                          prepared.restoredState
                                        verifierFinalState :=
                                          verifierFinalState }
                                    let charged := afterVerifier.addCharges
                                      [.verifierTransitions transitionCount]
                                    let added := charged.addNode node
                                    have nodeHistoryBound :
                                        node.proverHistory.length ≤ Q := by
                                      simpa [node, ConcreteRestorationNode.proverHistory,
                                        proverQueries] using proverQueriesBound
                                    have addedStored :
                                        AllStoredProverHistoriesWithin Q
                                          added.2 :=
                                      all_stored_prover_histories_add_node Q
                                        charged node
                                        (all_stored_prover_histories_add_charges
                                          Q afterVerifier _
                                          afterVerifierStored)
                                        nodeHistoryBound
                                    apply continueSafe (.added added.1) added.2
                                      [.prefixReplayQueries
                                          prepared.prefixSteps,
                                        .restart prefixRestarts,
                                        .forkUniformCoordinates 2,
                                        .programmedPoints 2, .restart 1,
                                        .completeFromStartQueries proverQueries,
                                        .verifierSuffixQueries verifierQueries,
                                        .verifierTransitions transitionCount]
                                    · simp [added, charged, node, afterVerifier,
                                        afterProver, atProverStart,
                                        afterProgramming, afterCoordinates,
                                        withPrefix,
                                        ConcreteRestorationAccumulator.addCharges,
                                        ConcreteRestorationAccumulator.addNode,
                                        List.append_assoc]
                                    · simp [ConcreteRestorationCharge.oracleQueries]
                                      omega
                                    · simp [ConcreteRestorationCharge.uniformForkCoordinates]
                                    · simp [ConcreteRestorationCharge.successfulProgrammingPoints]
                                    · simp [ConcreteRestorationCharge.restarts]
                                      omega
                                    · simp [ConcreteRestorationCharge.protocolTransitions]
                                      exact transitionBound
                                    · exact addedStored
                            next =>
                              simp only [verifierRoom, if_neg]
                              let failedAccumulator := afterProver.addFailure
                                prepared.request .verifierSuffixRoom
                              apply continueSafe (.failed .verifierSuffixRoom)
                                failedAccumulator
                                [.prefixReplayQueries prepared.prefixSteps,
                                  .restart prefixRestarts,
                                  .forkUniformCoordinates 2,
                                  .programmedPoints 2, .restart 1,
                                  .completeFromStartQueries proverQueries]
                              · simp [failedAccumulator, afterProver,
                                  atProverStart, afterProgramming,
                                  afterCoordinates, withPrefix,
                                  ConcreteRestorationAccumulator.addCharges,
                                  ConcreteRestorationAccumulator.addFailure,
                                  List.append_assoc]
                              · simp [ConcreteRestorationCharge.oracleQueries]
                                omega
                              · simp [ConcreteRestorationCharge.uniformForkCoordinates]
                              · simp [ConcreteRestorationCharge.successfulProgrammingPoints]
                              · simp [ConcreteRestorationCharge.restarts]
                                omega
                              · simp [ConcreteRestorationCharge.protocolTransitions]
                              · exact all_stored_prover_histories_add_failure Q
                                  afterProver prepared.request
                                  .verifierSuffixRoom afterProverStored
                  next =>
                    simp only [proverRoom, if_neg]
                    let failedAccumulator := afterProgramming.addFailure
                      prepared.request .proverReplayRoom
                    apply continueSafe (.failed .proverReplayRoom)
                      failedAccumulator
                      [.prefixReplayQueries prepared.prefixSteps,
                        .restart prefixRestarts, .forkUniformCoordinates 2,
                        .programmedPoints 2]
                    · simp [failedAccumulator, afterProgramming,
                        afterCoordinates, withPrefix,
                        ConcreteRestorationAccumulator.addCharges,
                        ConcreteRestorationAccumulator.addFailure,
                        List.append_assoc]
                    · simp [ConcreteRestorationCharge.oracleQueries]
                      omega
                    · simp [ConcreteRestorationCharge.uniformForkCoordinates]
                    · simp [ConcreteRestorationCharge.successfulProgrammingPoints]
                    · simp [ConcreteRestorationCharge.restarts]
                      omega
                    · simp [ConcreteRestorationCharge.protocolTransitions]
                    · exact all_stored_prover_histories_add_failure Q
                        afterProgramming prepared.request .proverReplayRoom
                        afterProgrammingStored
                next =>
                  simp only [afterCoherent, if_neg]
                  let failedAccumulator := afterProgramming.addFailure
                    prepared.request .incoherentProgrammedOracle
                  apply continueSafe (.failed .incoherentProgrammedOracle)
                    failedAccumulator
                    [.prefixReplayQueries prepared.prefixSteps,
                      .restart prefixRestarts, .forkUniformCoordinates 2,
                      .programmedPoints 2]
                  · simp [failedAccumulator, afterProgramming,
                      afterCoordinates, withPrefix,
                      ConcreteRestorationAccumulator.addCharges,
                      ConcreteRestorationAccumulator.addFailure,
                      List.append_assoc]
                  · simp [ConcreteRestorationCharge.oracleQueries]
                    omega
                  · simp [ConcreteRestorationCharge.uniformForkCoordinates]
                  · simp [ConcreteRestorationCharge.successfulProgrammingPoints]
                  · simp [ConcreteRestorationCharge.restarts]
                    omega
                  · simp [ConcreteRestorationCharge.protocolTransitions]
                  · exact all_stored_prover_histories_add_failure Q
                      afterProgramming prepared.request
                      .incoherentProgrammedOracle afterProgrammingStored
          next =>
            simp only [pairRoom, if_neg]
            let failedAccumulator := withPrefix.addFailure prepared.request
              .pairExposureLimit
            apply continueSafe (.failed .pairExposureLimit) failedAccumulator
              [.prefixReplayQueries prepared.prefixSteps,
                .restart prefixRestarts]
            · simp [failedAccumulator, withPrefix,
                ConcreteRestorationAccumulator.addCharges,
                ConcreteRestorationAccumulator.addFailure]
            · simp [ConcreteRestorationCharge.oracleQueries]
              omega
            · simp [ConcreteRestorationCharge.uniformForkCoordinates]
            · simp [ConcreteRestorationCharge.successfulProgrammingPoints]
            · simp [ConcreteRestorationCharge.restarts]
              omega
            · simp [ConcreteRestorationCharge.protocolTransitions]
            · exact all_stored_prover_histories_add_failure Q withPrefix
                prepared.request .pairExposureLimit withPrefixStored
        next =>
          simp only [globalLimit, if_neg]
          let failedAccumulator := withPrefix.addFailure prepared.request
            .globalLimitTooSmall
          apply continueSafe (.failed .globalLimitTooSmall) failedAccumulator
            [.prefixReplayQueries prepared.prefixSteps,
              .restart prefixRestarts]
          · simp [failedAccumulator, withPrefix,
              ConcreteRestorationAccumulator.addCharges,
              ConcreteRestorationAccumulator.addFailure]
          · simp [ConcreteRestorationCharge.oracleQueries]
            omega
          · simp [ConcreteRestorationCharge.uniformForkCoordinates]
          · simp [ConcreteRestorationCharge.successfulProgrammingPoints]
          · simp [ConcreteRestorationCharge.restarts]
            omega
          · simp [ConcreteRestorationCharge.protocolTransitions]
          · exact all_stored_prover_histories_add_failure Q withPrefix
              prepared.request .globalLimitTooSmall withPrefixStored
      next =>
        simp only [prefixCoherent, if_neg]
        let failedAccumulator := withPrefix.addFailure prepared.request
          .incoherentPrefixOracle
        apply continueSafe (.failed .incoherentPrefixOracle) failedAccumulator
          [.prefixReplayQueries prepared.prefixSteps, .restart prefixRestarts]
        · simp [failedAccumulator, withPrefix,
            ConcreteRestorationAccumulator.addCharges,
            ConcreteRestorationAccumulator.addFailure]
        · simp [ConcreteRestorationCharge.oracleQueries]
          omega
        · simp [ConcreteRestorationCharge.uniformForkCoordinates]
        · simp [ConcreteRestorationCharge.successfulProgrammingPoints]
        · simp [ConcreteRestorationCharge.restarts]
          omega
        · simp [ConcreteRestorationCharge.protocolTransitions]
        · exact all_stored_prover_histories_add_failure Q withPrefix
            prepared.request .incoherentPrefixOracle withPrefixStored

/-! ## Dependent induction over every actual client request -/

/-- The literal fuel-bounded client cursor carries the exact resource
envelope relative to the accumulator at every recursive call.  Synchronous
preparation failures are included because the dependent interpreter induction
visits the actual dispatcher before decreasing restoration fuel. -/
theorem concrete_restoration_client_projected_resource_induction
    {Statement Proof Payload Result : Type u}
    {globalOracleCalls : Nat}
    (Q : Nat)
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (root : ConcreteRestorationNode Statement Proof Payload)
    (configuration : ConcreteRestorationConfiguration)
    (restorationFuel : Nat)
    (client : ConcreteRestorationClient Result)
    (rootBound : root.proverHistory.length ≤ Q)
    (proverFuelBound : configuration.proverReplayFuel ≤ Q)
    (verifierFuelBound : configuration.verifierFuel ≤ 1511) :
    SchedulerNativeCursorAllProjectedReturned
      (fun run =>
        AccumulatorWithinRestorationAttempts Q configuration.driverFuel
          restorationFuel (initialRestorationAccumulatorFromRoot root)
          run.accumulator ∧
        AllStoredProverHistoriesWithin Q run.accumulator)
      (startConcreteRestorationClientFromRoot
        (globalOracleCalls := globalOracleCalls) startProgram environment root
        configuration restorationFuel client) := by
  let motive := fun (fuel : Nat)
      (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
      (_residualClient : ConcreteRestorationClient Result)
      (cursor : SchedulerNativeCursor globalOracleCalls
        (ConcreteRestorationClientRun Statement Proof Payload Result)) =>
      AllStoredProverHistoriesWithin Q accumulator →
      SchedulerNativeCursorAllProjectedReturned
        (fun run =>
          AccumulatorWithinRestorationAttempts Q configuration.driverFuel fuel
            accumulator run.accumulator ∧
          AllStoredProverHistoriesWithin Q run.accumulator)
        cursor
  have inducted :=
    start_concrete_restoration_client_from_root_dependent_induction
      (globalOracleCalls := globalOracleCalls) startProgram environment root
      configuration restorationFuel client motive
      (fun fuel accumulator result => by
        intro stored
        apply SchedulerNativeCursorAllProjectedReturned.returned
        change AccumulatorWithinRestorationAttempts Q
            configuration.driverFuel fuel accumulator accumulator ∧
          AllStoredProverHistoriesWithin Q accumulator
        refine ⟨?_, stored⟩
        constructor <;> simp)
      (fun accumulator request next => by
        intro stored
        apply SchedulerNativeCursorAllProjectedReturned.returned
        constructor
        · constructor <;>
            simp [ConcreteRestorationAccumulator.addFailure,
              ConcreteRestorationAccumulator.oracleQueryTotal,
              ConcreteRestorationAccumulator.uniformForkCoordinateTotal,
              ConcreteRestorationAccumulator.programmedPointTotal,
              ConcreteRestorationAccumulator.restartTotal,
              ConcreteRestorationAccumulator.verifierTransitionTotal]
        · exact all_stored_prover_histories_add_failure Q accumulator request
            .restorationFuelExhausted stored)
      (fun fuel accumulator request next resume ih => by
        intro stored
        apply dispatch_one_concrete_restoration_preserves_projected_resources
          Q
          (fun run =>
            AccumulatorWithinRestorationAttempts Q configuration.driverFuel
              (fuel + 1) accumulator run.accumulator ∧
            AllStoredProverHistoriesWithin Q run.accumulator)
          startProgram environment configuration accumulator request resume
          proverFuelBound verifierFuelBound stored
        intro reply nextAccumulator delta nextStored
        have tailSafe := ih reply nextAccumulator nextStored
        apply scheduler_native_all_projected_returned_mono
          (P := fun run =>
            AccumulatorWithinRestorationAttempts Q configuration.driverFuel fuel
              nextAccumulator run.accumulator ∧
            AllStoredProverHistoriesWithin Q run.accumulator)
        · intro run tailHolds
          exact ⟨one_delta_then_accumulator_within_attempts Q
            configuration.driverFuel fuel accumulator nextAccumulator
            run.accumulator delta tailHolds.1, tailHolds.2⟩
        · exact tailSafe)
  exact inducted (initial_all_stored_prover_histories Q root rootBound)

/-- A completed list-scheduler client run therefore has the exact closed
`R`-attempt accumulator bounds.  This theorem does not assert that the client
completes; scheduler resource/timeout failures remain ordinary non-returned
terminals. -/
theorem completed_concrete_client_has_exact_accumulator_caps
    {Statement Proof Payload Result : Type u}
    {globalOracleCalls : Nat}
    (Q : Nat)
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (root : ConcreteRestorationNode Statement Proof Payload)
    (configuration : ConcreteRestorationConfiguration)
    (R transitionFuel currentTransitionFuel : Nat)
    (transitionFuelPositive : 0 < transitionFuel)
    (client : ConcreteRestorationClient Result)
    (rootBound : root.proverHistory.length ≤ Q)
    (proverFuelBound : configuration.proverReplayFuel ≤ Q)
    (verifierFuelBound : configuration.verifierFuel ≤ 1511)
    (answers : List Digest256)
    (run : ConcreteRestorationClientRun Statement Proof Payload Result)
    (completed : runSchedulerNativeListTerminalFrom transitionFuel
      currentTransitionFuel
      (startConcreteRestorationClientFromRoot
        (globalOracleCalls := globalOracleCalls) startProgram environment root
        configuration R client) answers = .returned run) :
    run.accumulator.oracleQueryTotal ≤ R * (2 * Q + 1511) ∧
      run.accumulator.uniformForkCoordinateTotal ≤ 2 * R ∧
      run.accumulator.programmedPointTotal ≤ 2 * R ∧
      run.accumulator.restartTotal ≤ 2 * R ∧
      run.accumulator.verifierTransitionTotal ≤
        R * configuration.driverFuel ∧
      AllStoredProverHistoriesWithin Q run.accumulator := by
  have safe := concrete_restoration_client_projected_resource_induction
    (globalOracleCalls := globalOracleCalls) Q startProgram environment root
      configuration R client rootBound proverFuelBound verifierFuelBound
  have reached := run_scheduler_native_list_respects_all_projected_returned
    (fun returnedRun =>
      AccumulatorWithinRestorationAttempts Q configuration.driverFuel R
        (initialRestorationAccumulatorFromRoot root) returnedRun.accumulator ∧
      AllStoredProverHistoriesWithin Q returnedRun.accumulator)
    transitionFuel transitionFuelPositive _ safe currentTransitionFuel answers
      run completed
  have caps := zero_initial_accumulator_attempt_caps Q
    configuration.driverFuel R root run.accumulator reached.1
  exact ⟨caps.1, caps.2.1, caps.2.2.1, caps.2.2.2.1,
    caps.2.2.2.2, reached.2⟩

#print axioms scheduler_native_all_projected_returned_mono
#print axioms list_getElem?_some_is_member
#print axioms all_stored_histories_give_lookup_bound
#print axioms initial_all_stored_prover_histories
#print axioms all_stored_prover_histories_add_charges
#print axioms all_stored_prover_histories_add_failure
#print axioms all_stored_prover_histories_add_node
#print axioms one_delta_then_accumulator_within_attempts
#print axioms one_restoration_delta_of_charge_log_extension
#print axioms prepared_ready_restored_state_exact
#print axioms projected_scheduler_stage_completed_reflects
#print axioms projected_totalized_restored_driver_transition_count_le
#print axioms program_concrete_pair_failure_inserted_le_one
#print axioms dispatch_one_concrete_restoration_preserves_projected_resources
#print axioms concrete_restoration_client_projected_resource_induction
#print axioms completed_concrete_client_has_exact_accumulator_caps

end

end AspisK1.V7Tag73ExactCompilerClientCaps
