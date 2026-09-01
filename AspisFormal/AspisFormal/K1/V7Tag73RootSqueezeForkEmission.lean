import AspisFormal.K1.V7Tag73RootSqueezePreparationClosure
import AspisFormal.K1.V7Tag73PreparedRestorationRoles

/-!
# Root squeeze preparation reaches the real fork cursor

The root-sweep client already requests every deployed transition.  The prior
module proves that a literal paired squeeze always prepares successfully,
including adversary-first prequeries.  This module discharges the remaining
deterministic dispatcher guard that is semantic rather than a resource bound:
the prepared prefix is history/total-call coherent.  With the two explicit
global resource inequalities, the real dispatcher therefore emits its
literal pair-fork cursor.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73RootSqueezeForkEmission

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73AtomicPairFork
open AspisK1.V7Tag73CompletedFullRunProjection
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73PreparedRestorationRoles
open AspisK1.V7Tag73RawStrictReplacementSuffix
open AspisK1.V7Tag73RootSqueezePreparationClosure
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SequentialOracleRuns
open AspisK1.V7Tag73TotalizedMachineReflection
open AspisK1.V7Tag73UniformRawVerifierExecution

noncomputable section

universe u

theorem successful_query_preserves_history_total_coherent
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (state nextState : OracleState)
    (input : ShaInput) (output : ShaOutput)
    (coherent : HistoryTotalCoherent state)
    (success : queryOracle controller limits actor state input =
      .ok (output, nextState)) :
    HistoryTotalCoherent nextState := by
  obtain ⟨record, historyExact, _actorExact⟩ :=
    query_oracle_success_appends_actor_record controller limits actor state
      nextState input output success
  have counterExact :=
    (query_oracle_success_counter_step controller limits actor state nextState
      input output success).1
  unfold HistoryTotalCoherent at coherent ⊢
  rw [historyExact, counterExact]
  simp only [List.length_append, List.length_singleton]
  omega

theorem run_prefix_preserves_history_total_coherent
    {Result : Type*}
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (program : OracleMachine Result)
    (coherent : HistoryTotalCoherent state) :
    HistoryTotalCoherent
      (runPrefix controller limits actor fuel state program).oracle := by
  induction fuel generalizing state program with
  | zero => simpa [runPrefix] using coherent
  | succ fuel inductionHypothesis =>
      cases program with
      | pure result => simpa [runPrefix] using coherent
      | abort reason => simpa [runPrefix] using coherent
      | query input next =>
          cases queried : queryOracle controller limits actor state input with
          | error reason => simpa [runPrefix, queried] using coherent
          | ok pair =>
              rcases pair with ⟨output, nextState⟩
              have nextCoherent :=
                successful_query_preserves_history_total_coherent controller
                  limits actor state nextState input output coherent queried
              simpa [runPrefix, queried] using
                inductionHypothesis nextState (next output) nextCoherent

theorem run_machine_preserves_history_total_coherent
    {Result : Type*}
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (program : OracleMachine Result)
    (coherent : HistoryTotalCoherent state) :
    HistoryTotalCoherent
      (runMachine controller limits actor fuel state program).oracle := by
  induction fuel generalizing state program with
  | zero =>
      cases program <;> simpa [runMachine] using coherent
  | succ fuel inductionHypothesis =>
      cases program with
      | pure result => simpa [runMachine] using coherent
      | abort reason => simpa [runMachine] using coherent
      | query input next =>
          cases queried : queryOracle controller limits actor state input with
          | error reason => simpa [runMachine, queried] using coherent
          | ok pair =>
              rcases pair with ⟨output, nextState⟩
              have nextCoherent :=
                successful_query_preserves_history_total_coherent controller
                  limits actor state nextState input output coherent queried
              simpa [runMachine, queried] using
                inductionHypothesis nextState (next output) nextCoherent

/-- A literal root squeeze prepares successfully in every live accumulator
that still stores the completed root at index zero.  Its programming base is
coherent: either the completed root oracle itself or a literal prefix replay
from `emptyOracle`. -/
theorem literal_root_squeeze_request_prepares_ready_coherent
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
      some (outputInput, advanceInput))
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (rootStored : accumulator.node? 0 = some runtime.node) :
    ∃ prepared : PreparedConcreteRestoration Statement Proof Payload,
      prepareConcreteRestorationFromStartProgram
          (machine.blackBox.start hidden machine.observation) configuration
          accumulator
          { nodeId := 0, verifierTransitionIndex := transitionIndex } =
        .ready prepared ∧
      HistoryTotalCoherent prepared.programmingBase := by
  rcases runs with ⟨adversarySteps, _verifierSteps, adversaryRun,
    _verifierRun⟩
  have returnedRun := run_machine_totalized_ok_reflects
    (rootAdversaryProjectedController runtime) machine.adversaryLimits
    .adversary machine.adversaryFuel emptyOracle
    (machine.blackBox.start hidden machine.observation)
    runtime.adversaryValue runtime.proverFinalOracle adversarySteps adversaryRun
  have rootFinalCoherent : HistoryTotalCoherent runtime.proverFinalOracle := by
    have returnedOracle :
        (runMachine (rootAdversaryProjectedController runtime)
          machine.adversaryLimits .adversary machine.adversaryFuel emptyOracle
          (machine.blackBox.start hidden machine.observation)).oracle =
            runtime.proverFinalOracle :=
      congrArg MachineRun.oracle returnedRun
    rw [← returnedOracle]
    exact run_machine_preserves_history_total_coherent
      (rootAdversaryProjectedController runtime) machine.adversaryLimits
      .adversary machine.adversaryFuel emptyOracle
      (machine.blackBox.start hidden machine.observation)
      empty_oracle_history_total_coherent
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
        { request := { nodeId := 0, verifierTransitionIndex := transitionIndex }
          parentNode := runtime.node
          transition := transition
          restoredState := restoreIndexedTransition transition
          outputInput := outputInput
          advanceInput := advanceInput
          occurrence := none
          prefixRun := none
          programmingBase := runtime.node.proverFinalOracle
          prefixSteps := 0 }
      refine ⟨prepared, ?_, ?_⟩
      · simp [prepareConcreteRestorationFromStartProgram, rootStored,
          transitionExact, pairExact, occurrenceExact, prepared]
      · exact rootFinalCoherent
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
        { request := { nodeId := 0, verifierTransitionIndex := transitionIndex }
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
      refine ⟨prepared, ?_, ?_⟩
      · simp only [prepareConcreteRestorationFromStartProgram, rootStored,
          transitionExact, pairExact, occurrenceExact]
        rw [limitsExact]
        simp [rootEntry, prefixRun, prefixPaused, prefixTrace, prepared]
      · exact run_prefix_preserves_history_total_coherent
          (recordedPrefixController emptyOracle.history.length
            occurrence.before)
          machine.adversaryLimits .extractorReplay occurrence.before.length
          emptyOracle (machine.blackBox.start hidden machine.observation)
          empty_oracle_history_total_coherent

/-- Complete deterministic root-squeeze dispatcher cut.  Preparation and
coherence are proved internally.  The only remaining hypotheses are the two
literal global resource guards; under them the actual dispatcher exposes the
exact pair-fork header. -/
theorem literal_root_squeeze_dispatch_emits_fork
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type u}
    {globalOracleCalls : Nat}
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
      some (outputInput, advanceInput))
    (environment : FutureFreeEnvironment)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (rootStored : accumulator.node? 0 = some runtime.node)
    (resume : ConcreteRestorationReply →
      ConcreteRestorationAccumulator Statement Proof Payload →
        SchedulerNativeCursor globalOracleCalls
          (ConcreteRestorationClientRun Statement Proof Payload Result)) :
    ∃ prepared : PreparedConcreteRestoration Statement Proof Payload,
      prepareConcreteRestorationFromStartProgram
          (machine.blackBox.start hidden machine.observation) configuration
          accumulator
          { nodeId := 0, verifierTransitionIndex := transitionIndex } =
        .ready prepared ∧
      HistoryTotalCoherent prepared.programmingBase ∧
      (configuration.oracleLimits.totalCalls ≤ globalOracleCalls →
        prepared.programmingBase.history.length + 2 ≤ globalOracleCalls →
        schedulerNativeForkHeader?
            (dispatchOneConcreteRestoration
              (machine.blackBox.start hidden machine.observation) environment
              configuration accumulator
              { nodeId := 0, verifierTransitionIndex := transitionIndex }
              resume) =
          some (preparedForkHeader configuration prepared)) := by
  obtain ⟨prepared, ready, coherent⟩ :=
    literal_root_squeeze_request_prepares_ready_coherent
    machine hidden runtime runs configuration limitsExact transitionIndex
    transition transitionExact outputInput advanceInput pairExact accumulator
    rootStored
  refine ⟨prepared, ready, coherent, ?_⟩
  intro globalLimit pairRoom
  unfold dispatchOneConcreteRestoration dispatchConcreteRestoration
  rw [ready]
  exact dispatch_prepared_restoration_emits_role_erased_fork
    (machine.blackBox.start hidden machine.observation) environment
    configuration prepared accumulator resume coherent globalLimit pairRoom

#print axioms successful_query_preserves_history_total_coherent
#print axioms run_prefix_preserves_history_total_coherent
#print axioms run_machine_preserves_history_total_coherent
#print axioms literal_root_squeeze_request_prepares_ready_coherent
#print axioms literal_root_squeeze_dispatch_emits_fork

end

end AspisK1.V7Tag73RootSqueezeForkEmission
