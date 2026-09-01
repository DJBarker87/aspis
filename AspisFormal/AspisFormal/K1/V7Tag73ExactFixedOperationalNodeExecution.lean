import AspisFormal.K1.V7Tag73ExactFixedOperationalStateMap
import AspisFormal.K1.V7Tag73ConcreteRestorationTraceInduction

/-!
# Exact completed-package operational node executions

The executable restoration-client induction already constructs a literal
`ProjectedRestorationNodeExecution` for every non-root child.  This leaf
exports that stronger source object at the same completed exact-compiler
boundary used by the restoration-state map.

Unlike the state-map invariant, the resulting certificate retains the
scheduled fork pair, the two programmed values, both replayed machine
segments, and the exact child insertion.  It is therefore the appropriate
starting point for restored gamma/alpha/q16 source alignment.  No root-query
origin, transcript-role classifier, or probability statement is added here.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73ExactFixedOperationalNodeExecution

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ActualRestorationStateMap
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73ConcreteRestorationTraceInduction
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73OperationalNodeCertificate
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73SchedulerMachineFactorization
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerProjectedTraceSafety
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

universe u

/-- A successful concrete list run exposes the already-proved operational
certificate for every non-root child in its literal returned accumulator. -/
theorem returned_concrete_restoration_client_has_every_node_operational
    {Statement Proof Payload Result : Type u}
    {globalOracleCalls : Nat}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (currentTransitionFuel : Nat)
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (root : ConcreteRestorationNode Statement Proof Payload)
    (rootIsRoot : root.parentRequest = none)
    (configuration : ConcreteRestorationConfiguration)
    (restorationFuel : Nat)
    (client : ConcreteRestorationClient Result)
    (rootTrace : List UnifiedExposureRecord)
    (answers : List Digest256)
    (run : ConcreteRestorationClientRun Statement Proof Payload Result)
    (completed :
      runSchedulerNativeListTerminalFrom transitionFuel currentTransitionFuel
        (startConcreteRestorationClientFromRoot
          (globalOracleCalls := globalOracleCalls) startProgram environment root
          configuration restorationFuel client)
        answers = .returned run) :
    EveryNodeOperational
      (Final := ConcreteRestorationClientRun Statement Proof Payload Result)
      startProgram environment configuration
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
  have traced := concrete_restoration_client_traced_safety_from_root_prefix
    (globalOracleCalls := globalOracleCalls) startProgram environment root
      rootIsRoot configuration restorationFuel client rootTrace
  apply run_scheduler_native_list_run_respects_projected_traced_returned
    (fun result suffix => EveryNodeOperational
      (Final := ConcreteRestorationClientRun Statement Proof Payload Result)
      startProgram environment configuration (rootTrace ++ suffix)
        result.accumulator)
    transitionFuel positive cursor traced currentTransitionFuel currentPositive
      answers run
  rw [run_scheduler_native_list_run_terminal]
  exact completed

/-- The exact fixed completed package retains a literal source execution for
every non-root restoration node on the complete compiler trace. -/
theorem exact_fixed_completed_package_has_every_node_operational
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (projection : AcceptedTapeProjection Statement Proof Payload)
    (fixedInstance : PublicInstance Statement)
    (sample : ExactCompilerSample HiddenTape parameters)
    (package : ExactFixedCleanFullRunFactorizationPackage transitionFuel
      configuration projection fixedInstance sample) :
    EveryNodeOperational
      (Final := ConcreteRestorationClientRun Statement Proof Payload Result)
      (configuration.machine.blackBox.start sample.1
        configuration.machine.observation)
      configuration.machine.environment
      configuration.restorationConfiguration
      (runExactPlainRom transitionFuel configuration sample).trace
      package.root.full.clientRun.accumulator := by
  have operational :=
    returned_concrete_restoration_client_has_every_node_operational
      transitionFuel positive
      (exactFixedClientContinuationFuel transitionFuel package.root)
      (configuration.machine.blackBox.start sample.1
        configuration.machine.observation)
      configuration.machine.environment package.root.fixedRoot.base.runtime.node
      rfl configuration.restorationConfiguration configuration.restorationFuel
      configuration.client (exactFixedRootRecords package.root)
      package.root.full.projection.rootPrefixes.verifier.remaining
      package.root.full.clientRun
      package.factorization.computedClientListTerminalExact
  rw [exact_fixed_operational_state_map_trace_is_full_trace transitionFuel
    configuration projection fixedInstance sample package]
  exact operational

/-- Package-facing form used by the K1.2--K1.5 operational input.  The
certificate is reconstructed from its retained completed package, so the
existing state-map record need not be widened or duplicated. -/
theorem exact_operational_input_has_every_node_operational
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Proof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (positive : 0 < transitionFuel)
    (input : ExactFixedOperationalStateRestorationInput transitionFuel
      configuration projection fixedInstance sample) :
    EveryNodeOperational
      (Final := ConcreteRestorationClientRun Statement Proof Payload Result)
      (configuration.machine.blackBox.start sample.1
        configuration.machine.observation)
      configuration.machine.environment
      configuration.restorationConfiguration
      (runExactPlainRom transitionFuel configuration sample).trace
      input.package.root.full.clientRun.accumulator :=
  exact_fixed_completed_package_has_every_node_operational transitionFuel
    positive configuration projection fixedInstance sample input.package

/-- Every literal non-root node named by an operational extraction input has
the exact scheduled-pair/programming/replay execution that inserted it. -/
theorem exact_operational_nonroot_node_has_projected_execution
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Proof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (positive : 0 < transitionFuel)
    (input : ExactFixedOperationalStateRestorationInput transitionFuel
      configuration projection fixedInstance sample)
    (node : ConcreteRestorationNode Statement Proof Payload)
    (member : node ∈ input.package.root.full.clientRun.accumulator.nodes)
    (nonroot : node.parentRequest ≠ none) :
    Nonempty (ProjectedRestorationNodeExecution
      (Final := ConcreteRestorationClientRun Statement Proof Payload Result)
      (configuration.machine.blackBox.start sample.1
        configuration.machine.observation)
      configuration.machine.environment
      configuration.restorationConfiguration
      (runExactPlainRom transitionFuel configuration sample).trace
      input.package.root.full.clientRun.accumulator node) := by
  exact (exact_operational_input_has_every_node_operational positive input)
    node member nonroot

#print axioms returned_concrete_restoration_client_has_every_node_operational
#print axioms exact_fixed_completed_package_has_every_node_operational
#print axioms exact_operational_input_has_every_node_operational
#print axioms exact_operational_nonroot_node_has_projected_execution

end

end AspisK1.V7Tag73ExactFixedOperationalNodeExecution
