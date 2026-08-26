import AspisFormal.K1.V7Tag73SchedulerNativePrefixTraversal
import AspisFormal.K1.V7Tag73ExactProbabilityCoverageAudit

/-!
# Native/dependent scheduler cursor alignment for Tag-73

The probability certificate and the executable result-carrying scheduler walk
the same fixed master tape.  This leaf identifies their live cursors after an
exact chronological prefix.  In particular, a pre-query `OracleState` kept by
the dependent target-clean certificate can later be identified with the
literal state exposed by the native machine callback; flat record equality is
never used as a substitute for that state equality.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73SchedulerCausalStateAlignment

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73ExactProbabilityCoverageAudit
open AspisK1.V7Tag73SchedulerNativePrefixTraversal

noncomputable section

universe u

/-- Master-tape answers consumed by a proof-rich certified prefix. -/
def certifiedOperationalExposureAnswers
    (certifiedPrefix : List CertifiedOperationalExposure) : List Digest256 :=
  (certifiedPrefix.map CertifiedOperationalExposure.erase).map
    UnifiedExposureRecord.answer

/-- Proof-rich native counterpart of `IsExactMachineFreshRequest`.  The
pre-query state is an index, so a witness proves state equality rather than
merely equality of the erased actor/input/answer record. -/
inductive IsExactSchedulerNativeMachineFreshRequest
    {globalOracleCalls : Nat} {Result : Type u}
    (actor : QueryActor) (state : OracleState) (input : ShaInput) :
    SchedulerNativeRequest globalOracleCalls Result → Prop where
  | witness
      {MachineResult : Type u}
      (limits : OracleLimits)
      (limitBound : limits.totalCalls ≤ globalOracleCalls)
      (nextProgram : ShaOutput → OracleMachine MachineResult)
      (remainingFuel : Nat) (coherent : HistoryTotalCoherent state)
      (totalRoom : state.totalCalls < limits.totalCalls)
      (freshRoom : state.freshCalls < limits.freshCalls)
      (missing : lookupEntry state input = none)
      (onReturned : (result : MachineResult) → (state : OracleState) →
        HistoryTotalCoherent state →
          SchedulerNativeCursor globalOracleCalls Result) :
      IsExactSchedulerNativeMachineFreshRequest actor state input
        (.machineFresh limits limitBound actor state input nextProgram
          remainingFuel coherent totalRoom freshRoom missing onReturned)

/-- An erased exact machine request can only have come from the literal native
machine request with the same actor, input, and full pre-query oracle state. -/
theorem exact_native_machine_request_of_erased_request
    {globalOracleCalls : Nat} {Result : Type u}
    (actor : QueryActor) (state : OracleState) (input : ShaInput)
    (request : SchedulerNativeRequest globalOracleCalls Result)
    (exact : IsExactMachineFreshRequest actor state input request.erase) :
    IsExactSchedulerNativeMachineFreshRequest actor state input request := by
  cases request with
  | returned result => cases exact
  | failed reason => cases exact
  | transitionLimit => cases exact
  | @machineFresh MachineResult limits limitBound requestActor requestState
      requestInput nextProgram remainingFuel coherent totalRoom freshRoom
      missing onReturned =>
      cases exact
      exact .witness limits limitBound nextProgram remainingFuel coherent
        totalRoom freshRoom missing onReturned
  | forkOutput frozenHistory pairRoom outputInput advanceInput template next =>
      cases exact
  | forkAdvance frozenHistory pairRoom outputInput advanceInput template
      forkOutput next =>
      cases exact

/-- One literal native request cannot expose two different indexed pre-query
states. -/
theorem exact_native_machine_request_state_unique
    {globalOracleCalls : Nat} {Result : Type u}
    {actor : QueryActor} {firstState secondState : OracleState}
    {input : ShaInput}
    {request : SchedulerNativeRequest globalOracleCalls Result}
    (first : IsExactSchedulerNativeMachineFreshRequest actor firstState input
      request)
    (second : IsExactSchedulerNativeMachineFreshRequest actor secondState input
      request) :
    firstState = secondState := by
  cases first
  cases second
  rfl

/-- The cursor stored by a dependent certified prefix is exactly the
result-free scheduler cursor computed from the same root and answer prefix. -/
theorem certified_operational_prefix_cursor_exact
    {globalOracleCalls transitionFuel step remaining : Nat}
    {seen : Finset Digest256} {seenBound : seen.card ≤ step}
    {cursor : UnifiedExposureCursor globalOracleCalls}
    {tape : FreshAnswerTape Digest256 remaining}
    {certificate : UnifiedOperationalTargetCleanCertificate transitionFuel
      step remaining seen seenBound cursor tape}
    {snapshots certifiedPrefix : List CertifiedOperationalExposure}
    {trace : CertifiedOperationalExposureTrace certificate snapshots}
    {requestCursor : UnifiedExposureCursor globalOracleCalls}
    (reached : CertifiedOperationalTracePrefixCursor trace certifiedPrefix
      requestCursor) :
    unifiedPrefixCursor transitionFuel cursor
        (certifiedOperationalExposureAnswers certifiedPrefix) = requestCursor := by
  induction reached with
  | here => rfl
  | halted reached ih =>
      simp only [certifiedOperationalExposureAnswers, List.map_cons,
        CertifiedOperationalExposure.erase, UnifiedExposureRecord.answer,
        unifiedPrefixCursor]
      simp_all [unifiedRequestNext]
      simpa only [certifiedOperationalExposureAnswers, List.map_map] using ih
  | transitionLimit reached ih =>
      simp only [certifiedOperationalExposureAnswers, List.map_cons,
        CertifiedOperationalExposure.erase, UnifiedExposureRecord.answer,
        unifiedPrefixCursor]
      simp_all [unifiedRequestNext]
      simpa only [certifiedOperationalExposureAnswers, List.map_map] using ih
  | machineFresh reached ih =>
      simp only [certifiedOperationalExposureAnswers, List.map_cons,
        CertifiedOperationalExposure.erase, UnifiedExposureRecord.answer,
        unifiedPrefixCursor]
      simp_all [unifiedRequestNext]
      simpa only [certifiedOperationalExposureAnswers, List.map_map] using ih
  | forkOutput reached ih =>
      simp only [certifiedOperationalExposureAnswers, List.map_cons,
        CertifiedOperationalExposure.erase, UnifiedExposureRecord.answer,
        unifiedPrefixCursor]
      simp_all [unifiedRequestNext]
      simpa only [certifiedOperationalExposureAnswers, List.map_map] using ih
  | forkAdvance reached ih =>
      simp only [certifiedOperationalExposureAnswers, List.map_cons,
        CertifiedOperationalExposure.erase, UnifiedExposureRecord.answer,
        unifiedPrefixCursor]
      simp_all [unifiedRequestNext]
      simpa only [certifiedOperationalExposureAnswers, List.map_map] using ih

/-- Starting from a native cursor whose erasure is the certificate root, the
native cursor reached by that prefix erases to the exact certified cursor. -/
theorem native_prefix_cursor_erases_to_certified_cursor
    {globalOracleCalls transitionFuel step remaining : Nat}
    {Result : Type u}
    {seen : Finset Digest256} {seenBound : seen.card ≤ step}
    {cursor : UnifiedExposureCursor globalOracleCalls}
    {nativeCursor : SchedulerNativeCursor globalOracleCalls Result}
    {tape : FreshAnswerTape Digest256 remaining}
    {certificate : UnifiedOperationalTargetCleanCertificate transitionFuel
      step remaining seen seenBound cursor tape}
    {snapshots certifiedPrefix : List CertifiedOperationalExposure}
    {trace : CertifiedOperationalExposureTrace certificate snapshots}
    {requestCursor : UnifiedExposureCursor globalOracleCalls}
    (rootExact : nativeCursor.erase = cursor)
    (reached : CertifiedOperationalTracePrefixCursor trace certifiedPrefix
      requestCursor) :
    (schedulerNativePrefixCursor transitionFuel nativeCursor
        (certifiedOperationalExposureAnswers certifiedPrefix)).erase = requestCursor := by
  rw [erase_scheduler_native_prefix_cursor, rootExact]
  exact certified_operational_prefix_cursor_exact reached

/-- Flat-prefix form used by the node execution certificate.  The answer list
is obtained from an exact erasure of the proof-rich prefix, rather than chosen
independently. -/
theorem native_flat_prefix_cursor_erases_to_certified_cursor
    {globalOracleCalls transitionFuel step remaining : Nat}
    {Result : Type u}
    {seen : Finset Digest256} {seenBound : seen.card ≤ step}
    {cursor : UnifiedExposureCursor globalOracleCalls}
    {nativeCursor : SchedulerNativeCursor globalOracleCalls Result}
    {tape : FreshAnswerTape Digest256 remaining}
    {certificate : UnifiedOperationalTargetCleanCertificate transitionFuel
      step remaining seen seenBound cursor tape}
    {snapshots certifiedPrefix : List CertifiedOperationalExposure}
    {trace : CertifiedOperationalExposureTrace certificate snapshots}
    {requestCursor : UnifiedExposureCursor globalOracleCalls}
    (priorRecords : List UnifiedExposureRecord)
    (rootExact : nativeCursor.erase = cursor)
    (prefixErases : certifiedPrefix.map CertifiedOperationalExposure.erase =
      priorRecords)
    (reached : CertifiedOperationalTracePrefixCursor trace certifiedPrefix
      requestCursor) :
    (schedulerNativePrefixCursor transitionFuel nativeCursor
        (priorRecords.map UnifiedExposureRecord.answer)).erase =
      requestCursor := by
  have answersExact :
      certifiedOperationalExposureAnswers certifiedPrefix =
        priorRecords.map UnifiedExposureRecord.answer := by
    unfold certifiedOperationalExposureAnswers
    rw [prefixErases]
  rw [← answersExact]
  exact native_prefix_cursor_erases_to_certified_cursor rootExact reached

/-- At an exact flat prefix, the native scheduler exposes the very same
proof-rich machine request (including its full `OracleState`) as the dependent
target-clean certificate. -/
theorem certified_machine_exposure_has_exact_native_request
    {globalOracleCalls transitionFuel step remaining : Nat}
    {Result : Type u}
    {seen : Finset Digest256} {seenBound : seen.card ≤ step}
    {cursor : UnifiedExposureCursor globalOracleCalls}
    {nativeCursor : SchedulerNativeCursor globalOracleCalls Result}
    {tape : FreshAnswerTape Digest256 remaining}
    {certificate : UnifiedOperationalTargetCleanCertificate transitionFuel
      step remaining seen seenBound cursor tape}
    {priorRecords laterRecords : List UnifiedExposureRecord}
    {actor : QueryActor} {state : OracleState} {input : ShaInput}
    {answer : Digest256}
    (rootExact : nativeCursor.erase = cursor)
    (atPrefix : CertifiedMachineExposureAtPrefix certificate priorRecords
      laterRecords actor state input answer) :
    IsExactSchedulerNativeMachineFreshRequest actor state input
      (seekSchedulerNativeExposure transitionFuel
        (schedulerNativePrefixCursor transitionFuel nativeCursor
          (priorRecords.map UnifiedExposureRecord.answer))) := by
  rcases certified_machine_exposure_at_prefix_has_exact_traversal atPrefix with
    ⟨snapshotSeen, avoids, priorSnapshots, laterSnapshots, snapshotTrace,
      requestCursor, reached, exactRequest, priorExact, laterExact⟩
  have reachedExact :=
    native_flat_prefix_cursor_erases_to_certified_cursor priorRecords rootExact
      priorExact reached
  let nativeReached := schedulerNativePrefixCursor transitionFuel nativeCursor
    (priorRecords.map UnifiedExposureRecord.answer)
  have requestErase :
      (seekSchedulerNativeExposure transitionFuel nativeReached).erase =
        seekUnifiedExposure transitionFuel requestCursor := by
    rw [erase_seek_scheduler_native_exposure, reachedExact]
  apply exact_native_machine_request_of_erased_request actor state input
  rw [requestErase]
  exact exactRequest

#print axioms certified_operational_prefix_cursor_exact
#print axioms native_prefix_cursor_erases_to_certified_cursor
#print axioms native_flat_prefix_cursor_erases_to_certified_cursor
#print axioms exact_native_machine_request_of_erased_request
#print axioms exact_native_machine_request_state_unique
#print axioms certified_machine_exposure_has_exact_native_request

end

end AspisK1.V7Tag73SchedulerCausalStateAlignment
