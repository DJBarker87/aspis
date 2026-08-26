import AspisFormal.K1.V7Tag73ActualNodeNativeEntryPrefix
import AspisFormal.K1.V7Tag73CausalProgrammingFreshness

/-!
# Compose actual native node prefixes with target-clean query states

The concrete dispatcher constructs `NativeEntryAlignedRestorationNodeExecution`.
The probability experiment constructs one dependent
`UnifiedOperationalTargetCleanCertificate` for the erasure of the same root
cursor and the same master tape.  This leaf composes those two constructed
objects pointwise.  Exact native-request indexing proves that their pre-query
`OracleState`s are equal; no flat-record lookup or caller-supplied state
alignment is used.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ActualNodeCleanStateComposition

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73OperationalNodeCertificate
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73SchedulerNativePrefixTraversal
open AspisK1.V7Tag73SchedulerCausalStateAlignment
open AspisK1.V7Tag73ActualNodeNativeEntryPrefix
open AspisK1.V7Tag73ExactProbabilityCoverageAudit
open AspisK1.V7Tag73CausalProgrammingFreshness

noncomputable section

universe u

/-- The verifier machine starts after the normally returned prover replay, so
its entry history extends the child's literal prover-entry history. -/
theorem projected_node_prover_entry_history_prefix_verifier_entry
    {Statement Proof Payload Final : Type u}
    {startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload)}
    {environment : FutureFreeEnvironment}
    {configuration : ConcreteRestorationConfiguration}
    {fullTrace : List UnifiedExposureRecord}
    {accumulator : ConcreteRestorationAccumulator Statement Proof Payload}
    {child : ConcreteRestorationNode Statement Proof Payload}
    (execution : ProjectedRestorationNodeExecution (Final := Final) startProgram
      environment configuration fullTrace accumulator child) :
    child.proverEntryOracle.history <+:
      child.verifierEntryOracle.history := by
  rw [execution.verifierEntryOracleExact, ← execution.proverFinalExact]
  exact projected_fresh_returned_trace_history_prefix
    configuration.oracleLimits .extractorReplay
      configuration.proverReplayFuel child.proverEntryOracle
      (schedulerStageProgram Final
        (totalizeOracleMachine configuration.proverReplayFuel startProgram))
      execution.proverPrefix.freshQueries execution.proverPrefix.result
      execution.proverPrefix.finalState execution.proverPrefix.steps
      execution.proverPrefix.trace

/-- Every actual native machine record of one restored child is paired with
the exact target-clean pre-query state, which necessarily extends the child's
prover-entry history. -/
theorem native_entry_aligned_node_has_causal_states
    {Statement Proof Payload Final : Type u} {globalOracleCalls : Nat}
    {transitionFuel step remaining : Nat}
    {seen : Finset Digest256} {seenBound : seen.card ≤ step}
    {rootCursor : SchedulerNativeCursor globalOracleCalls Final}
    {tape : FreshAnswerTape Digest256 remaining}
    {certificate : UnifiedOperationalTargetCleanCertificate transitionFuel
      step remaining seen seenBound rootCursor.erase tape}
    {startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload)}
    {environment : FutureFreeEnvironment}
    {configuration : ConcreteRestorationConfiguration}
    {fullTrace : List UnifiedExposureRecord}
    {accumulator : ConcreteRestorationAccumulator Statement Proof Payload}
    {child : ConcreteRestorationNode Statement Proof Payload}
    (execution : NativeEntryAlignedRestorationNodeExecution transitionFuel
      rootCursor startProgram environment configuration fullTrace accumulator
        child)
    (traceExact :
      runUnifiedExposureTrace transitionFuel remaining rootCursor.erase tape =
        fullTrace) :
    NodeMachineRecordHasCausalState execution.base := by
  intro actor input answer member
  rcases List.mem_append.mp member with proverMember | verifierMember
  · obtain ⟨recordInput, recordAnswer, recordExact⟩ :=
      execution.base.proverRecordsOnly (.machineFresh actor input answer)
        proverMember
    simp only [UnifiedExposureRecord.machineFresh.injEq] at recordExact
    rcases recordExact with ⟨actorExact, inputExact, answerExact⟩
    subst actor
    subst recordInput
    subst recordAnswer
    obtain ⟨localPrior, localLater, localExact⟩ :=
      (List.mem_iff_append).mp proverMember
    let globalPrior := execution.base.traceBeforePair ++
      scheduledPairRecords execution.base.scheduled ++ localPrior
    let globalLater := localLater ++ execution.base.verifierRecords ++
      execution.base.traceAfterVerifier
    have fullDecomposition :
        fullTrace = globalPrior ++
          .machineFresh .extractorReplay input answer :: globalLater := by
      calc
        fullTrace = execution.base.traceBeforePair ++
            scheduledPairRecords execution.base.scheduled ++
            execution.base.proverRecords ++ execution.base.verifierRecords ++
            execution.base.traceAfterVerifier :=
          execution.base.fullTraceExact
        _ = globalPrior ++
            .machineFresh .extractorReplay input answer :: globalLater := by
          simp [globalPrior, globalLater, localExact, List.append_assoc]
    obtain ⟨cleanState, cleanAtPrefix⟩ :=
      certified_operational_machine_at_prefix_of_trace_decomposition
        certificate globalPrior globalLater .extractorReplay input answer
          (traceExact.trans fullDecomposition)
    have cleanNative :=
      certified_machine_exposure_has_exact_native_request
        (nativeCursor := rootCursor) rfl cleanAtPrefix
    obtain ⟨nativeState, entryPrefix, nativeExact⟩ :=
      execution.proverRequestsExtendEntry localPrior input answer localLater
        localExact
    have stateExact : nativeState = cleanState :=
      exact_native_machine_request_state_unique nativeExact cleanNative
    rcases cleanAtPrefix with ⟨snapshotSeen, avoids, priorSnapshots,
      laterSnapshots, snapshotTrace, requestCursor, reached, exactRequest,
      priorErase, laterErase⟩
    refine ⟨cleanState, snapshotSeen, ?_, avoids⟩
    simpa [stateExact] using entryPrefix
  · obtain ⟨recordInput, recordAnswer, recordExact⟩ :=
      execution.base.verifierRecordsOnly (.machineFresh actor input answer)
        verifierMember
    simp only [UnifiedExposureRecord.machineFresh.injEq] at recordExact
    rcases recordExact with ⟨actorExact, inputExact, answerExact⟩
    subst actor
    subst recordInput
    subst recordAnswer
    obtain ⟨localPrior, localLater, localExact⟩ :=
      (List.mem_iff_append).mp verifierMember
    let globalPrior := execution.base.traceBeforePair ++
      scheduledPairRecords execution.base.scheduled ++
        execution.base.proverRecords ++ localPrior
    let globalLater := localLater ++ execution.base.traceAfterVerifier
    have fullDecomposition :
        fullTrace = globalPrior ++
          .machineFresh .verifier input answer :: globalLater := by
      calc
        fullTrace = execution.base.traceBeforePair ++
            scheduledPairRecords execution.base.scheduled ++
            execution.base.proverRecords ++ execution.base.verifierRecords ++
            execution.base.traceAfterVerifier :=
          execution.base.fullTraceExact
        _ = globalPrior ++ .machineFresh .verifier input answer ::
            globalLater := by
          simp [globalPrior, globalLater, localExact, List.append_assoc]
    obtain ⟨cleanState, cleanAtPrefix⟩ :=
      certified_operational_machine_at_prefix_of_trace_decomposition
        certificate globalPrior globalLater .verifier input answer
          (traceExact.trans fullDecomposition)
    have cleanNative :=
      certified_machine_exposure_has_exact_native_request
        (nativeCursor := rootCursor) rfl cleanAtPrefix
    obtain ⟨nativeState, verifierEntryPrefix, nativeExact⟩ :=
      execution.verifierRequestsExtendEntry localPrior input answer localLater
        localExact
    have stateExact : nativeState = cleanState :=
      exact_native_machine_request_state_unique nativeExact cleanNative
    have proverToVerifier :=
      projected_node_prover_entry_history_prefix_verifier_entry execution.base
    rcases cleanAtPrefix with ⟨snapshotSeen, avoids, priorSnapshots,
      laterSnapshots, snapshotTrace, requestCursor, reached, exactRequest,
      priorErase, laterErase⟩
    refine ⟨cleanState, snapshotSeen, ?_, avoids⟩
    have combined := proverToVerifier.trans verifierEntryPrefix
    simpa [stateExact] using combined

#print axioms projected_node_prover_entry_history_prefix_verifier_entry
#print axioms native_entry_aligned_node_has_causal_states

end

end AspisK1.V7Tag73ActualNodeCleanStateComposition
