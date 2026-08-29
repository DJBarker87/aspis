import AspisFormal.K1.V7Tag73ExactFixedFullRunFactorization
import AspisFormal.K1.V7Tag73ActualRestorationStateMap
import AspisFormal.K1.V7Tag73ExactOperationalResourceCertificate

/-!
# Fixed-instance operational restoration map for Tag-73

This leaf instantiates the dispatcher induction on the exact completed client
tail recovered from a member of the fixed clean source event.  Consequently,
every fork pair in the actual full scheduler trace has a proof-relevant map to
the complete, nonempty, previously seen verifier state selected by the real
preparer.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ExactFixedOperationalStateMap

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73SchedulerMachineFactorization
open AspisK1.V7Tag73SchedulerProjectedTraceSafety
open AspisK1.V7Tag73OperationalNodeCertificate
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedInstanceEvent
open AspisK1.V7Tag73ExactFixedOperationalRootPackage
open AspisK1.V7Tag73FullCursorClientLineageLift
open AspisK1.V7Tag73FullResultRootRuns
open AspisK1.V7Tag73UniformRawVerifierExecution
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73CanonicalFutureFreeFuel
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73RawVerifierExecution
open AspisK1.V7Tag73ActualNodeCausalProvenance
open AspisK1.V7Tag73ActualRestorationStateMap
open AspisK1.V7Tag73ExactOperationalResourceCertificate
open AspisK1.V7Tag73Q16ControlInvariant
open AspisK1.V7Tag73Q16LedgerCertificate
open AspisK1.V7Tag73Q16LedgerControlInvariant

noncomputable section

/-- The two projected root machine segments contain only machine-fresh
records, hence cannot contain a restoration fork coordinate. -/
theorem full_projected_root_records_have_no_fork_advance
    {HiddenTape TapeIdentity Observation Statement Proof Payload Final : Type}
    {machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    {hidden : HiddenTape} {available : List Digest256}
    {runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload}
    (prefixes : FullResultRootProjectedPrefixes (Final := Final) machine hidden
      available runtime) :
    ∀ scheduled,
      (.forkAdvance scheduled : UnifiedExposureRecord) ∉
        fullProjectedRootRecords prefixes := by
  intro scheduled member
  rw [fullProjectedRootRecords, List.mem_append] at member
  rcases member with adversaryMember | verifierMember
  · exact (no_fork_advance_of_only_machine_fresh_actor .adversary
      (projectedMachineFreshRecords .adversary
        prefixes.adversary.freshQueries)
      (only_machine_fresh_actor_projected_records .adversary
        prefixes.adversary.freshQueries)) scheduled adversaryMember
  · exact (no_fork_advance_of_only_machine_fresh_actor .verifier
      (projectedMachineFreshRecords .verifier
        prefixes.verifier.freshQueries)
      (only_machine_fresh_actor_projected_records .verifier
        prefixes.verifier.freshQueries)) scheduled verifierMember

/-- The returned root verifier state is closed because it is the endpoint of
the exact initial future-free machine path starting at the dummy singleton. -/
theorem exact_fixed_package_root_history_closed
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Proof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (package : ExactFixedCleanFullRunFactorizationPackage transitionFuel
      configuration projection fixedInstance sample) :
    FutureFreeHistoryClosed
      package.root.fixedRoot.base.runtime.node.verifierFinalState := by
  let projected := package.root.fixedRoot.base.projected
  obtain ⟨pairs, path, _history, _actors, _answers⟩ :=
    raw_verifier_execution_has_exact_query_path projected.execution
  have closed := initial_raw_future_free_return_has_closed_nonempty_seen_history
    projected.execution.environment
    projected.execution.adversaryValue.rawMessages
    projected.execution.driverFuel pairs projected.execution.finalState path
  change FutureFreeHistoryClosed
    package.root.fixedRoot.base.runtime.verifierFinalState
  rw [← projected.finalStateExact]
  exact closed

/-- The same literal root trace preserves the executable q16 block cap for
the live state and every complete restoration snapshot. -/
theorem exact_fixed_package_root_q16_slot_invariant
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Proof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (package : ExactFixedCleanFullRunFactorizationPackage transitionFuel
      configuration projection fixedInstance sample) :
    FutureFreeQ16SlotInvariant
      package.root.fixedRoot.base.runtime.node.verifierFinalState := by
  let projected := package.root.fixedRoot.base.projected
  obtain ⟨pairs, _history, operational⟩ :=
    raw_verifier_execution_has_operational_trace projected.execution
  have invariant :=
    future_free_operational_trace_preserves_q16_slot_invariant
      projected.execution.environment
      projected.execution.adversaryValue.rawMessages operational
      (initial_future_free_q16_slot_invariant
        (FixedBindings.ofContext
          projected.execution.adversaryValue.rawMessages.context))
  change FutureFreeQ16SlotInvariant
    package.root.fixedRoot.base.runtime.verifierFinalState
  rw [← projected.finalStateExact]
  exact invariant

/-- The same literal root execution establishes the stronger ledger-phase
invariant at every retained restoration snapshot. -/
theorem exact_fixed_package_root_q16_ledger_invariant
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Proof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (package : ExactFixedCleanFullRunFactorizationPackage transitionFuel
      configuration projection fixedInstance sample) :
    FutureFreeQ16LedgerInvariant configuration.machine.environment
      package.root.fixedRoot.base.runtime.node.verifierFinalState := by
  let projected := package.root.fixedRoot.base.projected
  obtain ⟨pairs, _history, operational⟩ :=
    raw_verifier_execution_has_operational_trace projected.execution
  have invariant :=
    future_free_operational_trace_preserves_q16_ledger_invariant
      projected.execution.environment
      projected.execution.adversaryValue.rawMessages _ _ pairs operational
      (initial_future_free_q16_ledger_invariant
        projected.execution.environment
        (FixedBindings.ofContext
          projected.execution.adversaryValue.rawMessages.context))
  rw [projected.environmentExact] at invariant
  change FutureFreeQ16LedgerInvariant configuration.machine.environment
    package.root.fixedRoot.base.runtime.verifierFinalState
  rw [← projected.finalStateExact]
  exact invariant

/-- The fixed operational package retains the stronger selected-ledger
certificate constructed by the strict source replay, not merely the local
q16 sampler block-cap invariant. -/
def exact_fixed_package_root_selected_q16_ledger
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Proof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (package : ExactFixedCleanFullRunFactorizationPackage transitionFuel
      configuration projection fixedInstance sample) :
    SelectedQ16LedgerCertificate configuration.machine.environment
      package.root.fixedRoot.base.runtime.node.verifierFinalState.current := by
  exact package.root.fixedRoot.base.selectedQ16Ledger

/-- Canonical chronological trace used by the operational state map. -/
def exactFixedOperationalStateMapTrace
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    {projection : AcceptedTapeProjection Statement Proof Payload}
    {fixedInstance : PublicInstance Statement}
    (sample : ExactCompilerSample HiddenTape parameters)
    (package : ExactFixedCleanFullRunFactorizationPackage transitionFuel
      configuration projection fixedInstance sample) :
    List UnifiedExposureRecord :=
  exactFixedRootRecords package.root ++
    (exactFixedComputedClientTailRun transitionFuel configuration sample
      package.root).trace

/-- The exact fixed full scheduler trace is the root prefix followed by the
literal computed client tail. -/
theorem exact_fixed_operational_state_map_trace_is_full_trace
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (projection : AcceptedTapeProjection Statement Proof Payload)
    (fixedInstance : PublicInstance Statement)
    (sample : ExactCompilerSample HiddenTape parameters)
    (package : ExactFixedCleanFullRunFactorizationPackage transitionFuel
      configuration projection fixedInstance sample) :
    (runExactPlainRom transitionFuel configuration sample).trace =
      exactFixedOperationalStateMapTrace transitionFuel configuration sample
        package := by
  unfold runExactPlainRom
  rw [run_scheduler_native_eq_list_run]
  unfold runSchedulerNativeListRun
  rw [package.factorization.fullRunExact]
  rfl

/-- Concrete replacement for the former abstract query-DAG-to-state-map
placeholder.  It is proved on the actual fixed full trace and actual returned
accumulator. -/
theorem exact_fixed_completed_package_has_operational_state_map
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
    ActualRestorationStateMapInvariant
      (configuration.machine.blackBox.start sample.1
        configuration.machine.observation)
      configuration.machine.environment
      configuration.restorationConfiguration
      (runExactPlainRom transitionFuel configuration sample).trace
      package.root.full.clientRun.accumulator := by
  have mapped := returned_concrete_restoration_client_has_exact_state_map
    transitionFuel positive
    (exactFixedClientContinuationFuel transitionFuel package.root)
    (configuration.machine.blackBox.start sample.1
      configuration.machine.observation)
    configuration.machine.environment package.root.fixedRoot.base.runtime.node
    configuration.restorationConfiguration configuration.restorationFuel
    configuration.client (exactFixedRootRecords package.root)
    (exact_fixed_package_root_history_closed package)
    (exact_fixed_package_root_q16_slot_invariant package)
    (exact_fixed_package_root_q16_ledger_invariant package)
    (full_projected_root_records_have_no_fork_advance
      package.root.full.projection.rootPrefixes)
    package.root.full.projection.rootPrefixes.verifier.remaining
    package.root.full.clientRun
    package.factorization.computedClientListTerminalExact
  rw [exact_fixed_operational_state_map_trace_is_full_trace transitionFuel
    configuration projection fixedInstance sample package]
  change ActualRestorationStateMapInvariant
    (configuration.machine.blackBox.start sample.1
      configuration.machine.observation)
    configuration.machine.environment
    configuration.restorationConfiguration
    (exactFixedOperationalStateMapTrace transitionFuel configuration sample
      package)
    package.root.full.clientRun.accumulator at mapped
  exact mapped

/-- Every accepting node in the literal returned accumulator—not just the
root—retains an exact first-cap-203 q16 ledger certificate. -/
theorem exact_fixed_completed_stored_done_node_has_selected_q16_ledger
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (projection : AcceptedTapeProjection Statement Proof Payload)
    (fixedInstance : PublicInstance Statement)
    (sample : ExactCompilerSample HiddenTape parameters)
    (package : ExactFixedCleanFullRunFactorizationPackage transitionFuel
      configuration projection fixedInstance sample)
    (node : ConcreteRestorationNode Statement Proof Payload)
    (member : node ∈ package.root.full.clientRun.accumulator.nodes)
    (done : node.verifierFinalState.current.control = .done) :
    Nonempty (SelectedQ16LedgerCertificate configuration.machine.environment
      node.verifierFinalState.current) := by
  have stateMap := exact_fixed_completed_package_has_operational_state_map
    transitionFuel positive configuration projection fixedInstance sample
      package
  have invariant := stateMap.everyNodeQ16LedgerInvariant node member
  exact done_state_has_selected_q16_ledger configuration.machine.environment
    node.verifierFinalState invariant done

/-- Proof-relevant operational input constructed from the fixed clean event.
It contains the completed-root/full-run factorization and the proved state map;
neither field mentions a witness or an extraction conclusion. -/
structure ExactFixedOperationalStateRestorationInput
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (projection : AcceptedTapeProjection Statement Proof Payload)
    (fixedInstance : PublicInstance Statement)
    (sample : ExactCompilerSample HiddenTape parameters) : Type where
  package : ExactFixedCleanFullRunFactorizationPackage transitionFuel
    configuration projection fixedInstance sample
  stateMap : ActualRestorationStateMapInvariant
    (configuration.machine.blackBox.start sample.1
      configuration.machine.observation)
    configuration.machine.environment
    configuration.restorationConfiguration
    (runExactPlainRom transitionFuel configuration sample).trace
    package.root.full.clientRun.accumulator
  resources : ExactOperationalResourceCertificate transitionFuel configuration
    sample package.root.fixedRoot.base.runtime package.root.full

/-- A literal fixed clean-event member constructs the operational state-map
input.  The only hypotheses are the static scheduler and driver fuel reserves
already needed to obtain the completed root. -/
theorem fixed_legal_member_has_operational_state_restoration_input
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (projection : AcceptedTapeProjection Statement Proof Payload)
    (fixedInstance : PublicInstance Statement)
    (transitionRoom : 3 ≤ transitionFuel)
    (driverCoversProtocol :
      tag73CanonicalDriverFuelCap ≤ configuration.machine.driverFuel)
    (runtimeReserves : ExactOperationalRuntimeReserves parameters)
    (cutoffBeyondCap :
      totalCompilerRuntimeCap parameters < parameters.timeoutCutoff)
    (sample : ExactCompilerSample HiddenTape parameters)
    (member : sample ∈ exactFixedPlainRomLegalSameTapeEvent transitionFuel
      configuration projection fixedInstance) :
    Nonempty (ExactFixedOperationalStateRestorationInput transitionFuel
      configuration projection fixedInstance sample) := by
  let package := fixed_legal_member_full_run_factorization_package
    transitionFuel configuration projection fixedInstance transitionRoom
      driverCoversProtocol sample member
  exact ⟨
    { package := package
      stateMap := exact_fixed_completed_package_has_operational_state_map
        transitionFuel (by omega) configuration projection fixedInstance sample
          package
      resources := completed_full_run_has_exact_operational_resource_certificate
        transitionFuel configuration sample
          package.root.fixedRoot.base.runtime package.root.full transitionRoom
            runtimeReserves cutoffBeyondCap }⟩

#print axioms full_projected_root_records_have_no_fork_advance
#print axioms exact_fixed_package_root_history_closed
#print axioms exact_fixed_package_root_q16_slot_invariant
#print axioms exact_fixed_package_root_q16_ledger_invariant
#print axioms exact_fixed_package_root_selected_q16_ledger
#print axioms exact_fixed_operational_state_map_trace_is_full_trace
#print axioms exact_fixed_completed_package_has_operational_state_map
#print axioms exact_fixed_completed_stored_done_node_has_selected_q16_ledger
#print axioms fixed_legal_member_has_operational_state_restoration_input

end

end AspisK1.V7Tag73ExactFixedOperationalStateMap
