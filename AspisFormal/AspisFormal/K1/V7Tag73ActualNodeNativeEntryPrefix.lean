import AspisFormal.K1.V7Tag73OperationalNodeCertificate
import AspisFormal.K1.V7Tag73SchedulerCausalStateAlignment

/-!
# Actual native entry-history provenance for restored Tag-73 nodes

This is the operational conjunct constructed by the concrete dispatcher
induction.  For every fresh prover/verifier record of a child, it retains the
literal global scheduler prefix and proves that the native request at that
coordinate contains a pre-query oracle history extending the child's concrete
machine-entry history.

No target-clean certificate occurs here.  The separate native/erased cursor
alignment later identifies this native request state with the state in the
dependent probability certificate.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ActualNodeNativeEntryPrefix

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73OperationalNodeCertificate
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73SchedulerNativePrefixTraversal
open AspisK1.V7Tag73SchedulerCausalStateAlignment

noncomputable section

universe u

/-- Exact native machine request at one chronological global prefix, together
with the cumulative-history fact needed downstream. -/
def NativeMachineRecordHasEntryPrefix
    {globalOracleCalls : Nat} {Final : Type u}
    (transitionFuel : Nat)
    (rootCursor : SchedulerNativeCursor globalOracleCalls Final)
    (entryState : OracleState) (actor : QueryActor)
    (globalPrior : List UnifiedExposureRecord)
    (input : ShaInput) : Prop :=
  ∃ requestState : OracleState,
    entryState.history <+: requestState.history ∧
      IsExactSchedulerNativeMachineFreshRequest actor requestState input
        (seekSchedulerNativeExposure transitionFuel
          (schedulerNativePrefixCursor transitionFuel rootCursor
            (globalPrior.map UnifiedExposureRecord.answer)))

/-- The actual root traversal and a local callback cursor expose the same next
native request at this chronological prefix.  The dispatcher induction proves
this equality; it is never accepted by the final compiler theorem. -/
def NativeRequestAlignedAtGlobalPrefix
    {globalOracleCalls : Nat} {Final : Type u}
    (transitionFuel : Nat)
    (rootCursor localCursor : SchedulerNativeCursor globalOracleCalls Final)
    (globalPrior : List UnifiedExposureRecord) : Prop :=
  seekSchedulerNativeExposure transitionFuel
      (schedulerNativePrefixCursor transitionFuel rootCursor
        (globalPrior.map UnifiedExposureRecord.answer)) =
    seekSchedulerNativeExposure transitionFuel localCursor

/-- Local projected-machine state plus actual dispatcher alignment constructs
the frozen global-prefix certificate. -/
theorem native_machine_record_has_entry_prefix_of_local_alignment
    {globalOracleCalls : Nat} {Final : Type u}
    (transitionFuel : Nat)
    (rootCursor localCursor : SchedulerNativeCursor globalOracleCalls Final)
    (entryState requestState : OracleState) (actor : QueryActor)
    (globalPrior : List UnifiedExposureRecord) (input : ShaInput)
    (historyPrefix : entryState.history <+: requestState.history)
    (localExact : IsExactSchedulerNativeMachineFreshRequest actor requestState
      input (seekSchedulerNativeExposure transitionFuel localCursor))
    (aligned : NativeRequestAlignedAtGlobalPrefix transitionFuel rootCursor
      localCursor globalPrior) :
    NativeMachineRecordHasEntryPrefix transitionFuel rootCursor entryState actor
      globalPrior input := by
  refine ⟨requestState, historyPrefix, ?_⟩
  rw [aligned]
  exact localExact

/-- One child with exact native request-state provenance for both of its
actual machine slices.  `globalPrior` is assembled internally from the
certificate's literal chronological decomposition; a caller cannot supply a
snapshot or reached cursor. -/
structure NativeEntryAlignedRestorationNodeExecution
    {Statement Proof Payload Final : Type u} {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (rootCursor : SchedulerNativeCursor globalOracleCalls Final)
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (fullTrace : List UnifiedExposureRecord)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (child : ConcreteRestorationNode Statement Proof Payload) : Type u where
  base : ProjectedRestorationNodeExecution (Final := Final) startProgram
    environment configuration fullTrace accumulator child
  proverRequestsExtendEntry :
    ∀ localPrior input answer localLater,
      base.proverRecords = localPrior ++
          .machineFresh .extractorReplay input answer :: localLater →
        NativeMachineRecordHasEntryPrefix transitionFuel rootCursor
          child.proverEntryOracle .extractorReplay
          (base.traceBeforePair ++ scheduledPairRecords base.scheduled ++
            localPrior)
          input
  verifierRequestsExtendEntry :
    ∀ localPrior input answer localLater,
      base.verifierRecords = localPrior ++
          .machineFresh .verifier input answer :: localLater →
        NativeMachineRecordHasEntryPrefix transitionFuel rootCursor
          child.verifierEntryOracle .verifier
          (base.traceBeforePair ++ scheduledPairRecords base.scheduled ++
            base.proverRecords ++ localPrior)
          input

/-- Frozen constructor surface consumed by the concrete dispatcher induction.
The two functional arguments must be proved from the actual callback machine
prefixes; they are not premises of the final compiler theorem. -/
def native_entry_aligned_child_of_exact_machine_prefixes
    {Statement Proof Payload Final : Type u} {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (rootCursor : SchedulerNativeCursor globalOracleCalls Final)
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (fullTrace : List UnifiedExposureRecord)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (child : ConcreteRestorationNode Statement Proof Payload)
    (base : ProjectedRestorationNodeExecution (Final := Final) startProgram
      environment configuration fullTrace accumulator child)
    (proverRequests :
      ∀ localPrior input answer localLater,
        base.proverRecords = localPrior ++
            .machineFresh .extractorReplay input answer :: localLater →
          NativeMachineRecordHasEntryPrefix transitionFuel rootCursor
            child.proverEntryOracle .extractorReplay
            (base.traceBeforePair ++ scheduledPairRecords base.scheduled ++
              localPrior)
            input)
    (verifierRequests :
      ∀ localPrior input answer localLater,
        base.verifierRecords = localPrior ++
            .machineFresh .verifier input answer :: localLater →
          NativeMachineRecordHasEntryPrefix transitionFuel rootCursor
            child.verifierEntryOracle .verifier
            (base.traceBeforePair ++ scheduledPairRecords base.scheduled ++
              base.proverRecords ++ localPrior)
            input) :
    NativeEntryAlignedRestorationNodeExecution transitionFuel rootCursor
      startProgram environment configuration fullTrace accumulator child :=
  { base := base
    proverRequestsExtendEntry := proverRequests
    verifierRequestsExtendEntry := verifierRequests }

def EveryNodeOperationalWithNativeEntryPrefix
    {Statement Proof Payload Final : Type u} {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (rootCursor : SchedulerNativeCursor globalOracleCalls Final)
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (fullTrace : List UnifiedExposureRecord)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload) :
    Prop :=
  ∀ child ∈ accumulator.nodes,
    child.parentRequest ≠ none →
      Nonempty (NativeEntryAlignedRestorationNodeExecution transitionFuel
        rootCursor startProgram environment configuration fullTrace accumulator
          child)

/-- Append-only transport changes neither a child's local machine slices nor
the global prefixes preceding those slices. -/
def transport_native_entry_aligned_restoration_node_execution
    {Statement Proof Payload Final : Type u} {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (rootCursor : SchedulerNativeCursor globalOracleCalls Final)
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (oldTrace newTrace suffix : List UnifiedExposureRecord)
    (oldAccumulator newAccumulator :
      ConcreteRestorationAccumulator Statement Proof Payload)
    (child : ConcreteRestorationNode Statement Proof Payload)
    (execution : NativeEntryAlignedRestorationNodeExecution transitionFuel
      rootCursor startProgram environment configuration oldTrace oldAccumulator
        child)
    (traceExact : newTrace = oldTrace ++ suffix)
    (selectedExact :
      newAccumulator.node? execution.base.prepared.request.nodeId =
        oldAccumulator.node? execution.base.prepared.request.nodeId) :
    NativeEntryAlignedRestorationNodeExecution transitionFuel rootCursor
      startProgram environment configuration newTrace newAccumulator child :=
  { base := transport_projected_restoration_node_execution startProgram
      environment configuration oldTrace newTrace suffix oldAccumulator
        newAccumulator child execution.base traceExact selectedExact
    proverRequestsExtendEntry := execution.proverRequestsExtendEntry
    verifierRequestsExtendEntry := execution.verifierRequestsExtendEntry }

/-- Node-store-preserving bookkeeping transports the invariant through an
exact scheduler trace suffix. -/
theorem every_node_native_entry_prefix_of_nodes_eq
    {Statement Proof Payload Final : Type u} {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (rootCursor : SchedulerNativeCursor globalOracleCalls Final)
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (trace suffix : List UnifiedExposureRecord)
    (oldAccumulator newAccumulator :
      ConcreteRestorationAccumulator Statement Proof Payload)
    (nodesExact : newAccumulator.nodes = oldAccumulator.nodes)
    (invariant : EveryNodeOperationalWithNativeEntryPrefix transitionFuel
      rootCursor startProgram environment configuration trace oldAccumulator) :
    EveryNodeOperationalWithNativeEntryPrefix transitionFuel rootCursor
      startProgram environment configuration (trace ++ suffix)
        newAccumulator := by
  intro child member parentRequest
  have oldMember : child ∈ oldAccumulator.nodes := by
    rw [← nodesExact]
    exact member
  obtain ⟨execution⟩ := invariant child oldMember parentRequest
  have selectedSome : ∃ parent,
      oldAccumulator.node? execution.base.prepared.request.nodeId =
        some parent := by
    cases selected : oldAccumulator.node?
        execution.base.prepared.request.nodeId with
    | none =>
        have impossible := execution.base.preparationExact
        simp [prepareConcreteRestorationFromStartProgram, selected] at impossible
    | some parent => exact ⟨parent, rfl⟩
  refine ⟨transport_native_entry_aligned_restoration_node_execution
    transitionFuel rootCursor startProgram environment configuration trace
      (trace ++ suffix) suffix oldAccumulator newAccumulator child execution rfl
        ?_⟩
  rcases selectedSome with ⟨parent, selected⟩
  have newSelected : newAccumulator.node?
      execution.base.prepared.request.nodeId = some parent := by
    unfold ConcreteRestorationAccumulator.node? at selected ⊢
    rw [nodesExact]
    exact selected
  rw [newSelected, selected]

theorem every_node_native_entry_prefix_add_charges
    {Statement Proof Payload Final : Type u} {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (rootCursor : SchedulerNativeCursor globalOracleCalls Final)
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (trace suffix : List UnifiedExposureRecord)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (charges : List ConcreteRestorationCharge)
    (invariant : EveryNodeOperationalWithNativeEntryPrefix transitionFuel
      rootCursor startProgram environment configuration trace accumulator) :
    EveryNodeOperationalWithNativeEntryPrefix transitionFuel rootCursor
      startProgram environment configuration (trace ++ suffix)
        (accumulator.addCharges charges) := by
  exact every_node_native_entry_prefix_of_nodes_eq transitionFuel rootCursor
    startProgram environment configuration trace suffix accumulator
      (accumulator.addCharges charges) rfl invariant

theorem every_node_native_entry_prefix_add_failure
    {Statement Proof Payload Final : Type u} {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (rootCursor : SchedulerNativeCursor globalOracleCalls Final)
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (trace suffix : List UnifiedExposureRecord)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (request : ConcreteRestorationRequest)
    (reason : ConcreteRestorationFailure)
    (invariant : EveryNodeOperationalWithNativeEntryPrefix transitionFuel
      rootCursor startProgram environment configuration trace accumulator) :
    EveryNodeOperationalWithNativeEntryPrefix transitionFuel rootCursor
      startProgram environment configuration (trace ++ suffix)
        (accumulator.addFailure request reason) := by
  exact every_node_native_entry_prefix_of_nodes_eq transitionFuel rootCursor
    startProgram environment configuration trace suffix accumulator
      (accumulator.addFailure request reason) rfl invariant

/-- Add one newly constructed child and transport all older certificates. -/
theorem every_node_native_entry_prefix_add_certified_node
    {Statement Proof Payload Final : Type u} {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (rootCursor : SchedulerNativeCursor globalOracleCalls Final)
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (trace suffix : List UnifiedExposureRecord)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (child : ConcreteRestorationNode Statement Proof Payload)
    (invariant : EveryNodeOperationalWithNativeEntryPrefix transitionFuel
      rootCursor startProgram environment configuration trace accumulator)
    (childExecution : NativeEntryAlignedRestorationNodeExecution transitionFuel
      rootCursor startProgram environment configuration (trace ++ suffix)
        (accumulator.addNode child).2 child) :
    EveryNodeOperationalWithNativeEntryPrefix transitionFuel rootCursor
      startProgram environment configuration (trace ++ suffix)
        (accumulator.addNode child).2 := by
  intro candidate member parentRequest
  have memberCases : candidate ∈ accumulator.nodes ∨ candidate = child := by
    simpa [ConcreteRestorationAccumulator.addNode] using member
  rcases memberCases with oldMember | candidateExact
  · obtain ⟨execution⟩ := invariant candidate oldMember parentRequest
    have selectedSome : ∃ parent,
        accumulator.node? execution.base.prepared.request.nodeId = some parent := by
      cases selected : accumulator.node?
          execution.base.prepared.request.nodeId with
      | none =>
          have impossible := execution.base.preparationExact
          simp [prepareConcreteRestorationFromStartProgram, selected] at impossible
      | some parent => exact ⟨parent, rfl⟩
    refine ⟨transport_native_entry_aligned_restoration_node_execution
      transitionFuel rootCursor startProgram environment configuration trace
        (trace ++ suffix) suffix accumulator (accumulator.addNode child).2
          candidate execution rfl ?_⟩
    rcases selectedSome with ⟨parent, selected⟩
    rw [selected]
    exact node_lookup_preserved_by_add_node accumulator child parent
      execution.base.prepared.request.nodeId selected
  · subst candidate
    exact ⟨childExecution⟩

/-- The singleton root contains no child requiring native-entry provenance. -/
theorem initial_every_node_native_entry_prefix
    {Statement Proof Payload Final : Type u} {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (rootCursor : SchedulerNativeCursor globalOracleCalls Final)
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (trace : List UnifiedExposureRecord)
    (root : ConcreteRestorationNode Statement Proof Payload)
    (rootIsRoot : root.parentRequest = none) :
    EveryNodeOperationalWithNativeEntryPrefix transitionFuel rootCursor
      startProgram environment configuration trace
        (initialRestorationAccumulatorFromRoot root) := by
  intro child member parentRequest
  have childExact : child = root := by
    simpa [initialRestorationAccumulatorFromRoot] using member
  subst child
  exact (parentRequest rootIsRoot).elim

#print axioms native_entry_aligned_child_of_exact_machine_prefixes
#print axioms native_machine_record_has_entry_prefix_of_local_alignment
#print axioms transport_native_entry_aligned_restoration_node_execution
#print axioms every_node_native_entry_prefix_of_nodes_eq
#print axioms every_node_native_entry_prefix_add_certified_node
#print axioms initial_every_node_native_entry_prefix

end

end AspisK1.V7Tag73ActualNodeNativeEntryPrefix
