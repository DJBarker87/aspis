import AspisFormal.K1.V7Tag73ExactPlainRomOperationalCompletion
import AspisFormal.K1.V7Tag73OperationalNodeCertificate
import AspisFormal.K1.V7Tag73SchedulerProjectedTraceSafety
import AspisFormal.K1.V7Tag73UniformRawVerifierExecution

/-!
# Trace-derived full-256 resource caps for the exact Tag-73 compiler

The completion theorem bounds the total master-tape length `F`; final
`ResourceUse` accounting also has to distinguish genuinely machine-fresh
lazy-oracle answers from the two uniform coordinates allocated by every
atomic fork.  This module counts those two record classes in the literal
result-carrying scheduler trace.

Padding is counted as neither class.  Cached prefix replay is deliberately
absent from the machine-fresh count: it is executed synchronously against the
frozen table and remains charged in the concrete accumulator's ordinary oracle
query and restart totals.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ExactPlainRomTraceResourceCaps

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73AtomicPairReplay
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73ProjectedMachinePrefix
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73SchedulerProjectedTraceSafety
open AspisK1.V7Tag73SequentialOracleRuns
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73OperationalNodeCertificate
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73RawProverMessages
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73UniformRawVerifierExecution
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactPlainRomOperationalCompletion
open AspisK1.V7Tag73SchedulerCompletionCore

noncomputable section

universe u

/-! ## Literal trace counters -/

def machineFreshCoordinateCount : List UnifiedExposureRecord → Nat
  | [] => 0
  | .machineFresh _actor _input _answer :: rest =>
      machineFreshCoordinateCount rest + 1
  | _record :: rest => machineFreshCoordinateCount rest

def forkCoordinateCount : List UnifiedExposureRecord → Nat
  | [] => 0
  | .forkOutput _history _outputInput _advanceInput _template _answer :: rest =>
      forkCoordinateCount rest + 1
  | .forkAdvance _scheduled :: rest => forkCoordinateCount rest + 1
  | _record :: rest => forkCoordinateCount rest

def paddingCoordinateCount : List UnifiedExposureRecord → Nat
  | [] => 0
  | .padding _answer :: rest => paddingCoordinateCount rest + 1
  | _record :: rest => paddingCoordinateCount rest

@[simp] theorem machine_fresh_coordinate_count_append
    (first second : List UnifiedExposureRecord) :
    machineFreshCoordinateCount (first ++ second) =
      machineFreshCoordinateCount first + machineFreshCoordinateCount second := by
  induction first with
  | nil => simp [machineFreshCoordinateCount]
  | cons record rest ih =>
      cases record <;> simp [machineFreshCoordinateCount, ih, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm]

@[simp] theorem fork_coordinate_count_append
    (first second : List UnifiedExposureRecord) :
    forkCoordinateCount (first ++ second) =
      forkCoordinateCount first + forkCoordinateCount second := by
  induction first with
  | nil => simp [forkCoordinateCount]
  | cons record rest ih =>
      cases record <;> simp [forkCoordinateCount, ih, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm]

@[simp] theorem padding_coordinate_count_append
    (first second : List UnifiedExposureRecord) :
    paddingCoordinateCount (first ++ second) =
      paddingCoordinateCount first + paddingCoordinateCount second := by
  induction first with
  | nil => simp [paddingCoordinateCount]
  | cons record rest ih =>
      cases record <;> simp [paddingCoordinateCount, ih, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm]

theorem trace_coordinate_partition (records : List UnifiedExposureRecord) :
    machineFreshCoordinateCount records + forkCoordinateCount records +
        paddingCoordinateCount records = records.length := by
  induction records with
  | nil => rfl
  | cons record rest ih =>
      cases record <;>
        simp [machineFreshCoordinateCount, forkCoordinateCount,
          paddingCoordinateCount, ih] <;> omega

/-- Every successful query, cached or fresh, appends exactly one history
record.  Hence the actual chronological history slice of a returned projected
machine segment is bounded by that segment's query fuel. -/
theorem projected_machine_prefix_history_since_length_le_fuel
    {MachineResult : Type u}
    (limits : OracleLimits) (actor : QueryActor)
    (fuel : Nat) (state : OracleState) (program : OracleMachine MachineResult)
    (available : List Digest256)
    (returned : ProjectedMachinePrefixReturned limits actor fuel state program
      available) :
    (historySince state returned.finalState).length ≤ fuel := by
  have entryCoherent : HistoryTotalCoherent state :=
    projected_trace_entry_coherent limits actor fuel state program
      returned.freshQueries returned.result returned.finalState returned.steps
      returned.trace
  have runExact := projected_machine_prefix_returned_run_exact limits actor fuel
    state program available returned entryCoherent
  have totalLe := run_machine_total_calls_le_initial_add_fuel
    (controllerFromProjectedFreshAnswers state.history
      (returned.freshQueries.map Prod.snd)) limits actor fuel state program
  rw [runExact] at totalLe
  change returned.finalState.totalCalls ≤ state.totalCalls + fuel at totalLe
  have suffix := projected_fresh_returned_trace_preserves_suffix limits actor
    state.history [] fuel state program returned.freshQueries returned.result
      returned.finalState returned.steps (projected_fresh_suffix_initial state)
        returned.trace
  rcases suffix with ⟨appended, historyExact, _answersExact⟩
  have finalCoherent := returned.finalCoherent
  unfold HistoryTotalCoherent at entryCoherent finalCoherent
  rw [historyExact] at finalCoherent
  simp only [List.length_append] at finalCoherent
  have appendedLe : appended.length ≤ fuel := by omega
  unfold historySince
  rw [historyExact]
  simpa using appendedLe

@[simp] theorem machine_fresh_coordinate_count_padding_records
    (answers : List Digest256) :
    machineFreshCoordinateCount (paddingRecords answers) = 0 := by
  unfold paddingRecords
  induction answers with
  | nil => rfl
  | cons answer rest ih =>
      simp [machineFreshCoordinateCount, ih]

@[simp] theorem fork_coordinate_count_padding_records
    (answers : List Digest256) :
    forkCoordinateCount (paddingRecords answers) = 0 := by
  unfold paddingRecords
  induction answers with
  | nil => rfl
  | cons answer rest ih =>
      simp [forkCoordinateCount, ih]

@[simp] theorem machine_fresh_coordinate_count_projected_records
    (actor : QueryActor) (queries : List (ShaInput × Digest256)) :
    machineFreshCoordinateCount (projectedMachineFreshRecords actor queries) =
      queries.length := by
  induction queries with
  | nil => rfl
  | cons query rest ih =>
      rcases query with ⟨input, answer⟩
      simp [projectedMachineFreshRecords, machineFreshCoordinateCount, ih]

@[simp] theorem fork_coordinate_count_projected_records
    (actor : QueryActor) (queries : List (ShaInput × Digest256)) :
    forkCoordinateCount (projectedMachineFreshRecords actor queries) = 0 := by
  induction queries with
  | nil => rfl
  | cons query rest ih =>
      rcases query with ⟨input, answer⟩
      simp [projectedMachineFreshRecords, forkCoordinateCount, ih]

@[simp] theorem scheduled_pair_machine_fresh_count
    (scheduled : ScheduledForkCoins) :
    machineFreshCoordinateCount (scheduledPairRecords scheduled) = 0 := by
  rfl

@[simp] theorem scheduled_pair_fork_coordinate_count
    (scheduled : ScheduledForkCoins) :
    forkCoordinateCount (scheduledPairRecords scheduled) = 2 := by
  rfl

/-! ## Static trace-cap property -/

def TraceCoordinateCaps (machineFresh fork : Nat)
    (records : List UnifiedExposureRecord) : Prop :=
  machineFreshCoordinateCount records ≤ machineFresh ∧
    forkCoordinateCount records ≤ fork

theorem trace_coordinate_caps_mono
    {oldMachine newMachine oldFork newFork : Nat}
    {records : List UnifiedExposureRecord}
    (caps : TraceCoordinateCaps oldMachine oldFork records)
    (machineLe : oldMachine ≤ newMachine) (forkLe : oldFork ≤ newFork) :
    TraceCoordinateCaps newMachine newFork records :=
  ⟨caps.1.trans machineLe, caps.2.trans forkLe⟩

theorem trace_coordinate_caps_append
    {firstMachine secondMachine firstFork secondFork : Nat}
    {first second : List UnifiedExposureRecord}
    (firstCaps : TraceCoordinateCaps firstMachine firstFork first)
    (secondCaps : TraceCoordinateCaps secondMachine secondFork second) :
    TraceCoordinateCaps (firstMachine + secondMachine)
      (firstFork + secondFork) (first ++ second) := by
  constructor
  · rw [machine_fresh_coordinate_count_append]
    exact Nat.add_le_add firstCaps.1 secondCaps.1
  · rw [fork_coordinate_count_append]
    exact Nat.add_le_add firstCaps.2 secondCaps.2

/-! The next section constructs this property over the actual native cursor.
It does not assume completion; failed terminals are harmless, while every
ordinary returned terminal carries its literal trace bound. -/

def SchedulerNativeCursorHasTraceCaps
    {globalOracleCalls : Nat} {Result : Type u}
    (machineFresh fork : Nat)
    (cursor : SchedulerNativeCursor globalOracleCalls Result) : Prop :=
  SchedulerNativeCursorAllProjectedTracedReturned
    (fun _result trace => TraceCoordinateCaps machineFresh fork trace) cursor

theorem returned_cursor_has_zero_trace_caps
    {globalOracleCalls : Nat} {Result : Type u}
    (result : Result) :
    SchedulerNativeCursorHasTraceCaps 0 0
      (.returned result : SchedulerNativeCursor globalOracleCalls Result) := by
  apply SchedulerNativeCursorAllProjectedTracedReturned.returned
  intro answers
  simp [TraceCoordinateCaps]

theorem failed_cursor_has_trace_caps
    {globalOracleCalls : Nat} {Result : Type u}
    (machineFresh fork : Nat) (reason : SchedulerNativeFailure) :
    SchedulerNativeCursorHasTraceCaps machineFresh fork
      (.failed reason : SchedulerNativeCursor globalOracleCalls Result) := by
  exact .failed reason

theorem scheduler_native_all_projected_traced_returned_mono
    {globalOracleCalls : Nat} {Result : Type u}
    {P Q : Result → List UnifiedExposureRecord → Prop}
    (imp : ∀ result trace, P result trace → Q result trace) :
    ∀ {cursor : SchedulerNativeCursor globalOracleCalls Result},
      SchedulerNativeCursorAllProjectedTracedReturned P cursor →
        SchedulerNativeCursorAllProjectedTracedReturned Q cursor := by
  intro cursor safe
  induction safe generalizing Q with
  | returned result holds =>
      apply SchedulerNativeCursorAllProjectedTracedReturned.returned
      intro answers
      exact imp result (paddingRecords answers) (holds answers)
  | failed reason =>
      exact .failed reason
  | machine limits limitBound actor state program fuel coherent onReturned
      safe ih =>
      apply SchedulerNativeCursorAllProjectedTracedReturned.machine
        limits limitBound actor state program fuel coherent onReturned
      intro available returned
      apply ih available returned
      intro result trace holds
      exact imp result
        (projectedMachineFreshRecords actor returned.freshQueries ++ trace)
        holds
  | forkPair frozenHistory pairRoom outputInput advanceInput template next safe
      ih =>
      apply SchedulerNativeCursorAllProjectedTracedReturned.forkPair
        frozenHistory pairRoom outputInput advanceInput template next
      intro scheduled frozenExact outputExact advanceExact templateExact
      apply ih scheduled frozenExact outputExact advanceExact templateExact
      intro result trace holds
      exact imp result
        ([.forkOutput frozenHistory outputInput advanceInput template
              scheduled.forkOutput,
            .forkAdvance scheduled] ++ trace)
        holds
  | forkAdvance frozenHistory pairRoom outputInput advanceInput template
      forkOutput next safe ih =>
      apply SchedulerNativeCursorAllProjectedTracedReturned.forkAdvance
        frozenHistory pairRoom outputInput advanceInput template forkOutput next
      intro scheduled frozenExact outputExact advanceExact templateExact
        forkOutputExact
      apply ih scheduled frozenExact outputExact advanceExact templateExact
        forkOutputExact
      intro result trace holds
      exact imp result (.forkAdvance scheduled :: trace) holds

theorem machine_cursor_has_trace_caps
    {globalOracleCalls : Nat} {Result MachineResult : Type u}
    (nextMachine nextFork : Nat)
    (limits : OracleLimits) (limitBound : limits.totalCalls ≤ globalOracleCalls)
    (actor : QueryActor) (state : OracleState)
    (program : OracleMachine MachineResult) (fuel : Nat)
    (coherent : HistoryTotalCoherent state)
    (onReturned : (result : MachineResult) → (state : OracleState) →
      HistoryTotalCoherent state → SchedulerNativeCursor globalOracleCalls Result)
    (continuations : ∀ available
      (returned : ProjectedMachinePrefixReturned limits actor fuel state program
        available),
      SchedulerNativeCursorHasTraceCaps nextMachine nextFork
        (onReturned returned.result returned.finalState returned.finalCoherent)) :
    SchedulerNativeCursorHasTraceCaps (fuel + nextMachine) nextFork
      (.machine limits limitBound actor state program fuel coherent onReturned) := by
  apply SchedulerNativeCursorAllProjectedTracedReturned.machine
  intro available returned
  apply scheduler_native_all_projected_traced_returned_mono
    (P := fun _result trace => TraceCoordinateCaps nextMachine nextFork trace)
    (Q := fun _result trace =>
      TraceCoordinateCaps (fuel + nextMachine) nextFork
        (projectedMachineFreshRecords actor returned.freshQueries ++ trace))
  · intro result trace tailCaps
    have headCaps : TraceCoordinateCaps fuel 0
        (projectedMachineFreshRecords actor returned.freshQueries) := by
      constructor
      · simpa using projected_machine_prefix_fresh_length_le_fuel limits
          actor fuel state program available returned
      · simp
    simpa using trace_coordinate_caps_append headCaps tailCaps
  · exact continuations available returned

theorem fork_pair_cursor_has_trace_caps
    {globalOracleCalls : Nat} {Result : Type u}
    (nextMachine nextFork : Nat)
    (frozenHistory : List QueryRecord)
    (pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls)
    (outputInput advanceInput : ShaInput)
    (template : AtomicPairReplayConfiguration)
    (next : AtomicPairReplayConfiguration →
      SchedulerNativeCursor globalOracleCalls Result)
    (continuations : ∀ scheduled : ScheduledForkCoins,
      scheduled.frozenHistory = frozenHistory →
      scheduled.outputInput = outputInput →
      scheduled.advanceInput = advanceInput →
      scheduled.template = template →
      SchedulerNativeCursorHasTraceCaps nextMachine nextFork
        (next scheduled.configuration)) :
    SchedulerNativeCursorHasTraceCaps nextMachine (2 + nextFork)
      (.forkPair frozenHistory pairRoom outputInput advanceInput template next) := by
  apply SchedulerNativeCursorAllProjectedTracedReturned.forkPair
  intro scheduled frozenExact outputExact advanceExact templateExact
  apply scheduler_native_all_projected_traced_returned_mono
    (globalOracleCalls := globalOracleCalls) (Result := Result)
    (P := fun _result trace => TraceCoordinateCaps nextMachine nextFork trace)
    (Q := fun _result trace =>
      TraceCoordinateCaps nextMachine (2 + nextFork)
        ([UnifiedExposureRecord.forkOutput frozenHistory outputInput
              advanceInput template scheduled.forkOutput,
            UnifiedExposureRecord.forkAdvance scheduled] ++ trace))
  · intro result trace tailCaps
    have headCaps : TraceCoordinateCaps 0 2
        [UnifiedExposureRecord.forkOutput frozenHistory outputInput advanceInput
            template scheduled.forkOutput,
          UnifiedExposureRecord.forkAdvance scheduled] := by
      constructor <;> simp [machineFreshCoordinateCount, forkCoordinateCount]
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      trace_coordinate_caps_append headCaps tailCaps
  · exact continuations scheduled frozenExact outputExact advanceExact
      templateExact

theorem fork_advance_cursor_has_trace_caps
    {globalOracleCalls : Nat} {Result : Type u}
    (nextMachine nextFork : Nat)
    (frozenHistory : List QueryRecord)
    (pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls)
    (outputInput advanceInput : ShaInput)
    (template : AtomicPairReplayConfiguration)
    (forkOutput : Digest256)
    (next : AtomicPairReplayConfiguration →
      SchedulerNativeCursor globalOracleCalls Result)
    (continuations : ∀ scheduled : ScheduledForkCoins,
      scheduled.frozenHistory = frozenHistory →
      scheduled.outputInput = outputInput →
      scheduled.advanceInput = advanceInput →
      scheduled.template = template →
      scheduled.forkOutput = forkOutput →
      SchedulerNativeCursorHasTraceCaps nextMachine nextFork
        (next scheduled.configuration)) :
    SchedulerNativeCursorHasTraceCaps nextMachine (1 + nextFork)
      (.forkAdvance frozenHistory pairRoom outputInput advanceInput template
        forkOutput next) := by
  apply SchedulerNativeCursorAllProjectedTracedReturned.forkAdvance
  intro scheduled frozenExact outputExact advanceExact templateExact
    forkOutputExact
  apply scheduler_native_all_projected_traced_returned_mono
    (P := fun _result trace => TraceCoordinateCaps nextMachine nextFork trace)
    (Q := fun _result trace =>
      TraceCoordinateCaps nextMachine (1 + nextFork)
        (.forkAdvance scheduled :: trace))
  · intro result trace tailCaps
    have headCaps : TraceCoordinateCaps 0 1 [.forkAdvance scheduled] := by
      constructor <;> simp [machineFreshCoordinateCount, forkCoordinateCount]
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      trace_coordinate_caps_append headCaps tailCaps
  · exact continuations scheduled frozenExact outputExact advanceExact
      templateExact forkOutputExact

theorem scheduler_native_trace_caps_mono
    {globalOracleCalls : Nat} {Result : Type u}
    {oldMachine newMachine oldFork newFork : Nat}
    {cursor : SchedulerNativeCursor globalOracleCalls Result}
    (safe : SchedulerNativeCursorHasTraceCaps oldMachine oldFork cursor)
    (machineLe : oldMachine ≤ newMachine) (forkLe : oldFork ≤ newFork) :
    SchedulerNativeCursorHasTraceCaps newMachine newFork cursor := by
  apply scheduler_native_all_projected_traced_returned_mono
    (P := fun _result trace => TraceCoordinateCaps oldMachine oldFork trace)
    (Q := fun _result trace => TraceCoordinateCaps newMachine newFork trace)
  · intro result trace caps
    exact trace_coordinate_caps_mono caps machineLe forkLe
  · exact safe

/-- Result mapping changes no operational record.  The existential predicate
retains the original returned value only long enough to transport an arbitrary
trace property through the result map. -/
def ResultMapTracePredicate {Input Output : Type u}
    (map : Input → Output)
    (P : Input → List UnifiedExposureRecord → Prop) :
    Output → List UnifiedExposureRecord → Prop :=
  fun output trace => ∃ input, map input = output ∧ P input trace

theorem scheduler_native_all_projected_traced_returned_map
    {globalOracleCalls : Nat} {Input Output : Type u}
    (map : Input → Output) :
    ∀ {P : Input → List UnifiedExposureRecord → Prop}
      {cursor : SchedulerNativeCursor globalOracleCalls Input},
      SchedulerNativeCursorAllProjectedTracedReturned P cursor →
        SchedulerNativeCursorAllProjectedTracedReturned
          (ResultMapTracePredicate map P)
          (mapSchedulerNativeCursorResult map cursor) := by
  intro P cursor safe
  induction safe with
  | returned result holds =>
      apply SchedulerNativeCursorAllProjectedTracedReturned.returned
      intro answers
      exact ⟨result, rfl, holds answers⟩
  | failed reason =>
      exact .failed reason
  | machine limits limitBound actor state program fuel coherent onReturned
      safe ih =>
      apply SchedulerNativeCursorAllProjectedTracedReturned.machine
      intro available returned
      have tail := ih available returned
      unfold ResultMapTracePredicate at tail
      simpa only [ResultMapTracePredicate] using tail
  | forkPair frozenHistory pairRoom outputInput advanceInput template next safe
      ih =>
      apply SchedulerNativeCursorAllProjectedTracedReturned.forkPair
      intro scheduled frozenExact outputExact advanceExact templateExact
      have tail :=
        ih scheduled frozenExact outputExact advanceExact templateExact
      unfold ResultMapTracePredicate at tail
      simpa only [ResultMapTracePredicate] using tail
  | forkAdvance frozenHistory pairRoom outputInput advanceInput template
      forkOutput next safe ih =>
      apply SchedulerNativeCursorAllProjectedTracedReturned.forkAdvance
      intro scheduled frozenExact outputExact advanceExact templateExact
        forkOutputExact
      have tail := ih scheduled frozenExact outputExact advanceExact
        templateExact forkOutputExact
      unfold ResultMapTracePredicate at tail
      simpa only [ResultMapTracePredicate] using tail

theorem scheduler_native_trace_caps_map
    {globalOracleCalls : Nat} {Input Output : Type u}
    (map : Input → Output) (machineFresh fork : Nat)
    {cursor : SchedulerNativeCursor globalOracleCalls Input}
    (safe : SchedulerNativeCursorHasTraceCaps machineFresh fork cursor) :
    SchedulerNativeCursorHasTraceCaps machineFresh fork
      (mapSchedulerNativeCursorResult map cursor) := by
  unfold SchedulerNativeCursorHasTraceCaps at safe ⊢
  apply scheduler_native_all_projected_traced_returned_mono
    (P := ResultMapTracePredicate map
      (fun _result trace => TraceCoordinateCaps machineFresh fork trace))
    (Q := fun _result trace => TraceCoordinateCaps machineFresh fork trace)
  · intro result trace mapped
    rcases mapped with ⟨input, _mappedResult, caps⟩
    exact caps
  · exact scheduler_native_all_projected_traced_returned_map map safe

/-! ## The literal concrete dispatcher -/

/-- One actual restoration request emits at most two fork coordinates and at
most one complete prover plus one verifier machine-fresh block.  Prefix replay
is synchronous and therefore contributes no master-tape coordinate here. -/
theorem dispatch_concrete_restoration_has_trace_caps
    {Statement Proof Payload Result : Type u}
    {globalOracleCalls : Nat}
    (Q verifierCalls tailMachine tailFork : Nat)
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
    (verifierFuelBound : configuration.verifierFuel ≤ verifierCalls)
    (continuations : ∀ reply nextAccumulator,
      SchedulerNativeCursorHasTraceCaps tailMachine tailFork
        (resume reply nextAccumulator)) :
    SchedulerNativeCursorHasTraceCaps (Q + verifierCalls + tailMachine)
      (2 + tailFork)
      (dispatchOneConcreteRestoration startProgram environment configuration
        accumulator request resume) := by
  classical
  have tailFull : ∀ reply nextAccumulator,
      SchedulerNativeCursorHasTraceCaps (Q + verifierCalls + tailMachine)
        tailFork (resume reply nextAccumulator) := by
    intro reply nextAccumulator
    exact scheduler_native_trace_caps_mono
      (continuations reply nextAccumulator) (by omega) (Nat.le_refl _)
  have tailAfterProver : ∀ reply nextAccumulator,
      SchedulerNativeCursorHasTraceCaps (verifierCalls + tailMachine)
        tailFork (resume reply nextAccumulator) := by
    intro reply nextAccumulator
    exact scheduler_native_trace_caps_mono
      (continuations reply nextAccumulator) (by omega) (Nat.le_refl _)
  generalize preparationExact :
    prepareConcreteRestorationFromStartProgram startProgram configuration
      accumulator request = preparation
  cases preparation with
  | failed reason prefixSteps prefixRestarts =>
      simp only [dispatchOneConcreteRestoration, dispatchConcreteRestoration,
        preparationExact]
      apply scheduler_native_trace_caps_mono
        (continuations (.failed reason)
          ((accumulator.addCharges
            [.prefixReplayQueries prefixSteps, .restart prefixRestarts]).addFailure
              request reason))
      · omega
      · omega
  | ready prepared =>
      let prefixRestarts := if prepared.prefixRun.isSome then 1 else 0
      let withPrefix := accumulator.addCharges
        [.prefixReplayQueries prepared.prefixSteps, .restart prefixRestarts]
      simp only [dispatchOneConcreteRestoration, dispatchConcreteRestoration,
        preparationExact]
      unfold dispatchPreparedRestoration
      by_cases prefixCoherent : HistoryTotalCoherent prepared.programmingBase
      next =>
        rw [dif_pos prefixCoherent]
        by_cases globalLimit :
            configuration.oracleLimits.totalCalls ≤ globalOracleCalls
        next =>
          rw [dif_pos globalLimit]
          by_cases pairRoom : prepared.programmingBase.history.length + 2 ≤
              globalOracleCalls
          next =>
            rw [dif_pos pairRoom]
            apply fork_pair_cursor_has_trace_caps
              (Q + verifierCalls + tailMachine) tailFork
            intro scheduled frozenExact outputExact advanceExact templateExact
            let forkConfiguration := scheduled.configuration
            let afterCoordinates := withPrefix.addCharges
              [.forkUniformCoordinates 2]
            cases programmed : programConcretePair configuration.oracleLimits
                configuration.pairProgrammingOrder prepared.programmingBase
                prepared.outputInput prepared.advanceInput
                forkConfiguration.forkOutput forkConfiguration.forkAdvance with
            | failed programmingReason inserted =>
                simp only [forkConfiguration, programmed]
                exact tailFull (.failed programmingReason)
                  ((afterCoordinates.addCharges
                    [.programmedPoints inserted]).addFailure prepared.request
                      programmingReason)
            | ready afterBoth =>
                simp only [forkConfiguration, programmed]
                let afterProgramming := afterCoordinates.addCharges
                  [.programmedPoints 2]
                by_cases afterCoherent : HistoryTotalCoherent afterBoth
                next =>
                  rw [dif_pos afterCoherent]
                  by_cases proverRoom : StageHasOracleRoom
                      configuration.oracleLimits afterBoth
                        configuration.proverReplayFuel
                  next =>
                    rw [dif_pos proverRoom]
                    let atProverStart := afterProgramming.addCharges [.restart 1]
                    apply scheduler_native_trace_caps_mono
                      (machine_cursor_has_trace_caps
                        (verifierCalls + tailMachine) tailFork
                        configuration.oracleLimits globalLimit .extractorReplay
                        afterBoth
                        (schedulerStageProgram
                          (ConcreteRestorationClientRun Statement Proof Payload
                            Result)
                          (totalizeOracleMachine configuration.proverReplayFuel
                            startProgram))
                        configuration.proverReplayFuel afterCoherent
                        (fun proverStage proverFinalOracle proverCoherent =>
                          match proverStage with
                          | .completed proverResult =>
                              let proverQueries :=
                                (historySince afterBoth proverFinalOracle).length
                              let afterProver := atProverStart.addCharges
                                [.completeFromStartQueries proverQueries]
                              match proverResult with
                              | .error (.oracleAbort reason) =>
                                  resume (.failed (.proverReplayAbort reason))
                                    (afterProver.addFailure prepared.request
                                      (.proverReplayAbort reason))
                              | .error .timeout =>
                                  resume (.failed .proverReplayTimeout)
                                    (afterProver.addFailure prepared.request
                                      .proverReplayTimeout)
                              | .ok adversaryValue =>
                                  let rawMessages :=
                                    CheckedRawTag73AdversaryReturnedValue.rawMessages
                                      adversaryValue
                                  if bindingMismatch :
                                      FixedBindings.ofContext rawMessages.context ≠
                                        prepared.restoredState.current.bindings
                                  then
                                    resume (.failed .restoredBindingMismatch)
                                      (afterProver.addFailure prepared.request
                                        .restoredBindingMismatch)
                                  else if verifierRoom : StageHasOracleRoom
                                      configuration.oracleLimits proverFinalOracle
                                        configuration.verifierFuel then
                                    .machine configuration.oracleLimits globalLimit
                                      .verifier proverFinalOracle
                                      (schedulerStageProgram
                                        (ConcreteRestorationClientRun Statement
                                          Proof Payload Result)
                                        (totalizeOracleMachine
                                          configuration.verifierFuel
                                          (driveRawFutureFree environment
                                            rawMessages configuration.driverFuel
                                              prepared.restoredState)))
                                      configuration.verifierFuel proverCoherent
                                      (fun verifierStage verifierFinalOracle
                                          _verifierCoherent =>
                                        match verifierStage with
                                        | .completed verifierResult =>
                                            let verifierQueries :=
                                              (historySince proverFinalOracle
                                                verifierFinalOracle).length
                                            let afterVerifier :=
                                              afterProver.addCharges
                                                [.verifierSuffixQueries
                                                  verifierQueries]
                                            match verifierResult with
                                            | .error (.oracleAbort reason) =>
                                                resume
                                                  (.failed
                                                    (.verifierSuffixAbort reason))
                                                  (afterVerifier.addFailure
                                                    prepared.request
                                                    (.verifierSuffixAbort reason))
                                            | .error .timeout =>
                                                resume
                                                  (.failed .verifierSuffixTimeout)
                                                  (afterVerifier.addFailure
                                                    prepared.request
                                                    .verifierSuffixTimeout)
                                            | .ok verifierFinalState =>
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
                                                let charged :=
                                                  afterVerifier.addCharges
                                                    [.verifierTransitions
                                                      transitionCount]
                                                let added := charged.addNode node
                                                resume (.added added.1) added.2)
                                  else
                                    resume (.failed .verifierSuffixRoom)
                                      (afterProver.addFailure prepared.request
                                        .verifierSuffixRoom))
                        (by
                          intro available returned
                          cases returned.result with
                          | completed proverResult =>
                              let proverQueries :=
                                (historySince afterBoth returned.finalState).length
                              let afterProver := atProverStart.addCharges
                                [.completeFromStartQueries proverQueries]
                              cases proverResult with
                              | error failure =>
                                  cases failure with
                                  | oracleAbort reason =>
                                      exact tailAfterProver
                                        (.failed (.proverReplayAbort reason))
                                        (afterProver.addFailure prepared.request
                                          (.proverReplayAbort reason))
                                  | timeout =>
                                      exact tailAfterProver
                                        (.failed .proverReplayTimeout)
                                        (afterProver.addFailure prepared.request
                                          .proverReplayTimeout)
                              | ok adversaryValue =>
                                  simp only
                                  let rawMessages :=
                                    CheckedRawTag73AdversaryReturnedValue.rawMessages
                                      adversaryValue
                                  by_cases bindingMismatch :
                                      FixedBindings.ofContext rawMessages.context ≠
                                        prepared.restoredState.current.bindings
                                  next =>
                                    rw [dif_pos bindingMismatch]
                                    exact tailAfterProver
                                      (.failed .restoredBindingMismatch)
                                      (afterProver.addFailure prepared.request
                                        .restoredBindingMismatch)
                                  next =>
                                    rw [dif_neg bindingMismatch]
                                    by_cases verifierRoom : StageHasOracleRoom
                                        configuration.oracleLimits
                                        returned.finalState
                                        configuration.verifierFuel
                                    next =>
                                      rw [dif_pos verifierRoom]
                                      apply scheduler_native_trace_caps_mono
                                        (machine_cursor_has_trace_caps tailMachine
                                          tailFork configuration.oracleLimits
                                          globalLimit .verifier returned.finalState
                                          (schedulerStageProgram
                                            (ConcreteRestorationClientRun
                                              Statement Proof Payload Result)
                                            (totalizeOracleMachine
                                              configuration.verifierFuel
                                              (driveRawFutureFree environment
                                                rawMessages
                                                configuration.driverFuel
                                                prepared.restoredState)))
                                          configuration.verifierFuel
                                          returned.finalCoherent
                                          (fun verifierStage verifierFinalOracle
                                              _verifierCoherent =>
                                            match verifierStage with
                                            | .completed verifierResult =>
                                                let verifierQueries :=
                                                  (historySince
                                                    returned.finalState
                                                    verifierFinalOracle).length
                                                let afterVerifier :=
                                                  afterProver.addCharges
                                                    [.verifierSuffixQueries
                                                      verifierQueries]
                                                match verifierResult with
                                                | .error (.oracleAbort reason) =>
                                                    resume
                                                      (.failed
                                                        (.verifierSuffixAbort
                                                          reason))
                                                      (afterVerifier.addFailure
                                                        prepared.request
                                                        (.verifierSuffixAbort
                                                          reason))
                                                | .error .timeout =>
                                                    resume
                                                      (.failed
                                                        .verifierSuffixTimeout)
                                                      (afterVerifier.addFailure
                                                        prepared.request
                                                        .verifierSuffixTimeout)
                                                | .ok verifierFinalState =>
                                                    let transitionCount :=
                                                      verifierFinalState.transitions.length
                                                    let node :
                                                        ConcreteRestorationNode
                                                          Statement Proof Payload :=
                                                      { parentRequest :=
                                                          some prepared.request
                                                        adversaryValue :=
                                                          adversaryValue
                                                        proverEntryOracle :=
                                                          afterBoth
                                                        proverFinalOracle :=
                                                          returned.finalState
                                                        verifierEntryOracle :=
                                                          returned.finalState
                                                        verifierFinalOracle :=
                                                          verifierFinalOracle
                                                        verifierEntryState :=
                                                          prepared.restoredState
                                                        verifierFinalState :=
                                                          verifierFinalState }
                                                    let charged :=
                                                      afterVerifier.addCharges
                                                        [.verifierTransitions
                                                          transitionCount]
                                                    let added :=
                                                      charged.addNode node
                                                    resume (.added added.1)
                                                      added.2)
                                          (by
                                            intro verifierAvailable
                                              verifierReturned
                                            cases verifierReturned.result with
                                            | completed verifierResult =>
                                                let verifierQueries :=
                                                  (historySince
                                                    returned.finalState
                                                    verifierReturned.finalState).length
                                                let afterVerifier :=
                                                  afterProver.addCharges
                                                    [.verifierSuffixQueries
                                                      verifierQueries]
                                                cases verifierResult with
                                                | error failure =>
                                                    cases failure with
                                                    | oracleAbort reason =>
                                                        exact continuations
                                                          (.failed
                                                            (.verifierSuffixAbort
                                                              reason))
                                                          (afterVerifier.addFailure
                                                            prepared.request
                                                            (.verifierSuffixAbort
                                                              reason))
                                                    | timeout =>
                                                        exact continuations
                                                          (.failed
                                                            .verifierSuffixTimeout)
                                                          (afterVerifier.addFailure
                                                            prepared.request
                                                            .verifierSuffixTimeout)
                                                | ok verifierFinalState =>
                                                    let transitionCount :=
                                                      verifierFinalState.transitions.length
                                                    let node :
                                                        ConcreteRestorationNode
                                                          Statement Proof Payload :=
                                                      { parentRequest :=
                                                          some prepared.request
                                                        adversaryValue :=
                                                          adversaryValue
                                                        proverEntryOracle :=
                                                          afterBoth
                                                        proverFinalOracle :=
                                                          returned.finalState
                                                        verifierEntryOracle :=
                                                          returned.finalState
                                                        verifierFinalOracle :=
                                                          verifierReturned.finalState
                                                        verifierEntryState :=
                                                          prepared.restoredState
                                                        verifierFinalState :=
                                                          verifierFinalState }
                                                    let charged :=
                                                      afterVerifier.addCharges
                                                        [.verifierTransitions
                                                          transitionCount]
                                                    let added :=
                                                      charged.addNode node
                                                    exact continuations
                                                      (.added added.1) added.2))
                                      · omega
                                      · exact Nat.le_refl _
                                    next =>
                                      rw [dif_neg verifierRoom]
                                      exact tailAfterProver
                                        (.failed .verifierSuffixRoom)
                                        (afterProver.addFailure prepared.request
                                          .verifierSuffixRoom)))
                    · omega
                    · exact Nat.le_refl _
                  next =>
                    rw [dif_neg proverRoom]
                    exact tailFull (.failed .proverReplayRoom)
                      (afterProgramming.addFailure prepared.request
                        .proverReplayRoom)
                next =>
                  rw [dif_neg afterCoherent]
                  exact tailFull (.failed .incoherentProgrammedOracle)
                    (afterProgramming.addFailure prepared.request
                      .incoherentProgrammedOracle)
          next =>
            rw [dif_neg pairRoom]
            apply scheduler_native_trace_caps_mono
              (continuations (.failed .pairExposureLimit)
                (withPrefix.addFailure prepared.request .pairExposureLimit))
            · omega
            · omega
        next =>
          rw [dif_neg globalLimit]
          apply scheduler_native_trace_caps_mono
            (continuations (.failed .globalLimitTooSmall)
              (withPrefix.addFailure prepared.request .globalLimitTooSmall))
          · omega
          · omega
      next =>
        rw [dif_neg prefixCoherent]
        apply scheduler_native_trace_caps_mono
          (continuations (.failed .incoherentPrefixOracle)
            (withPrefix.addFailure prepared.request .incoherentPrefixOracle))
        · omega
        · omega

/-- Fuel induction over the actual private client interpreter. -/
theorem concrete_restoration_client_has_trace_caps
    {Statement Proof Payload Result : Type u}
    {globalOracleCalls : Nat}
    (Q verifierCalls : Nat)
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (root : ConcreteRestorationNode Statement Proof Payload)
    (configuration : ConcreteRestorationConfiguration)
    (restorationFuel : Nat)
    (client : ConcreteRestorationClient Result)
    (proverFuelBound : configuration.proverReplayFuel ≤ Q)
    (verifierFuelBound : configuration.verifierFuel ≤ verifierCalls) :
    SchedulerNativeCursorHasTraceCaps
      (restorationFuel * (Q + verifierCalls)) (2 * restorationFuel)
      (startConcreteRestorationClientFromRoot
        (globalOracleCalls := globalOracleCalls) startProgram environment root
        configuration restorationFuel client) := by
  let motive := fun (fuel : Nat)
      (_accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
      (_residualClient : ConcreteRestorationClient Result)
      (cursor : SchedulerNativeCursor globalOracleCalls
        (ConcreteRestorationClientRun Statement Proof Payload Result)) =>
      SchedulerNativeCursorHasTraceCaps (fuel * (Q + verifierCalls))
        (2 * fuel) cursor
  exact start_concrete_restoration_client_from_root_dependent_induction
    (globalOracleCalls := globalOracleCalls) startProgram environment root
    configuration restorationFuel client motive
    (by
      intro fuel accumulator result
      change SchedulerNativeCursorHasTraceCaps (fuel * (Q + verifierCalls))
        (2 * fuel)
        (.returned
          ({ halt := .returned result, accumulator := accumulator } :
            ConcreteRestorationClientRun Statement Proof Payload Result))
      apply scheduler_native_trace_caps_mono
        (returned_cursor_has_zero_trace_caps
          (globalOracleCalls := globalOracleCalls)
          ({ halt := .returned result, accumulator := accumulator } :
            ConcreteRestorationClientRun Statement Proof Payload Result))
      · omega
      · omega)
    (by
      intro accumulator request next
      change SchedulerNativeCursorHasTraceCaps (0 * (Q + verifierCalls))
        (2 * 0)
        (.returned
          ({ halt := .restorationFuelExhausted
             accumulator := accumulator.addFailure request
               .restorationFuelExhausted } :
            ConcreteRestorationClientRun Statement Proof Payload Result))
      simpa only [Nat.zero_mul, Nat.mul_zero] using
        (returned_cursor_has_zero_trace_caps
          (globalOracleCalls := globalOracleCalls)
          ({ halt := .restorationFuelExhausted
             accumulator := accumulator.addFailure request
               .restorationFuelExhausted } :
            ConcreteRestorationClientRun Statement Proof Payload Result)))
    (by
      intro fuel accumulator request next resume continuations
      apply scheduler_native_trace_caps_mono
        (dispatch_concrete_restoration_has_trace_caps Q verifierCalls
          (fuel * (Q + verifierCalls)) (2 * fuel) startProgram environment
          configuration accumulator request resume proverFuelBound
          verifierFuelBound continuations)
      · ring_nf
        exact Nat.le_refl _
      · ring_nf
        exact Nat.le_refl _)

/-! ## Root composition and exact `M,2R` bounds -/

/-- The literal root prover/verifier followed by the actual finite client has
the closed machine-fresh and fork-coordinate caps. -/
theorem scheduler_native_plain_rom_cursor_has_trace_caps
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type u}
    {globalOracleCalls : Nat}
    (Q verifierCalls R : Nat)
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape)
    (limitBounds : SchedulerNativeRootLimitBounds machine globalOracleCalls)
    (restorationConfiguration : ConcreteRestorationConfiguration)
    (restorationFuel : Nat)
    (client : ConcreteRestorationClient Result)
    (rootAdversaryFuelBound : machine.adversaryFuel ≤ Q)
    (rootVerifierFuelBound : machine.verifierFuel ≤ verifierCalls)
    (replayAdversaryFuelBound :
      restorationConfiguration.proverReplayFuel ≤ Q)
    (replayVerifierFuelBound :
      restorationConfiguration.verifierFuel ≤ verifierCalls)
    (restorationRequestBound : restorationFuel ≤ R) :
    SchedulerNativeCursorHasTraceCaps
      (Q + verifierCalls + R * (Q + verifierCalls)) (2 * R)
      (schedulerNativePlainRomCursor machine hidden limitBounds
        restorationConfiguration restorationFuel client) := by
  classical
  let Final := SchedulerNativePlainRomResult TapeIdentity Statement Proof
    Payload Result
  let startProgram := machine.blackBox.start hidden machine.observation
  unfold schedulerNativePlainRomCursor
  dsimp only
  by_cases adversaryRoom : StageHasOracleRoom machine.adversaryLimits
      emptyOracle machine.adversaryFuel
  next =>
    rw [dif_pos adversaryRoom]
    apply scheduler_native_trace_caps_mono
      (machine_cursor_has_trace_caps
        (verifierCalls + R * (Q + verifierCalls)) (2 * R)
        machine.adversaryLimits limitBounds.adversary .adversary emptyOracle
        (schedulerStageProgram Final
          (totalizeOracleMachine machine.adversaryFuel startProgram))
        machine.adversaryFuel empty_oracle_history_total_coherent
        (fun adversaryStage proverFinalOracle proverCoherent =>
          match adversaryStage with
          | .completed adversaryResult =>
              match adversaryResult with
              | .error (.oracleAbort reason) =>
                  .returned (SchedulerNativePlainRomResult.initialFailure
                    (.adversaryOracleAbort reason))
              | .error .timeout =>
                  .returned (SchedulerNativePlainRomResult.initialFailure
                    .adversaryTimeout)
              | .ok adversaryValue =>
                  if verifierRoom : StageHasOracleRoom machine.verifierLimits
                      proverFinalOracle machine.verifierFuel then
                    .machine machine.verifierLimits limitBounds.verifier
                      .verifier proverFinalOracle
                      (schedulerStageProgram Final
                        (totalizeOracleMachine machine.verifierFuel
                          (initialRawFutureFreeProgram machine.environment
                            adversaryValue.rawMessages machine.driverFuel)))
                      machine.verifierFuel proverCoherent
                      (fun verifierStage verifierFinalOracle
                          _verifierCoherent =>
                        match verifierStage with
                        | .completed verifierResult =>
                            match verifierResult with
                            | .error (.oracleAbort reason) =>
                                .returned
                                  (SchedulerNativePlainRomResult.initialFailure
                                    (.verifierOracleAbort reason))
                            | .error .timeout =>
                                .returned
                                  (SchedulerNativePlainRomResult.initialFailure
                                    .verifierTimeout)
                            | .ok verifierFinalState =>
                                let rootRuntime := operationalRootRuntime
                                  (machine.tapeIdentity hidden) adversaryValue
                                  proverFinalOracle verifierFinalOracle
                                  verifierFinalState
                                mapSchedulerNativeCursorResult
                                  (fun clientRun =>
                                    SchedulerNativePlainRomResult.completed
                                      rootRuntime clientRun)
                                  (startConcreteRestorationClientFromRoot
                                    (globalOracleCalls := globalOracleCalls)
                                    startProgram machine.environment
                                    rootRuntime.node restorationConfiguration
                                    restorationFuel client))
                  else
                    .returned
                      (SchedulerNativePlainRomResult.initialFailure
                        .verifierRoom))
        (by
          intro available adversaryReturned
          cases adversaryReturned.result with
          | completed adversaryResult =>
              cases adversaryResult with
              | error failure =>
                  cases failure with
                  | oracleAbort reason =>
                      apply scheduler_native_trace_caps_mono
                        (returned_cursor_has_zero_trace_caps
                          (SchedulerNativePlainRomResult.initialFailure
                            (.adversaryOracleAbort reason)))
                      · omega
                      · omega
                  | timeout =>
                      apply scheduler_native_trace_caps_mono
                        (returned_cursor_has_zero_trace_caps
                          (SchedulerNativePlainRomResult.initialFailure
                            .adversaryTimeout))
                      · omega
                      · omega
              | ok adversaryValue =>
                  simp only
                  by_cases verifierRoom : StageHasOracleRoom
                      machine.verifierLimits adversaryReturned.finalState
                        machine.verifierFuel
                  next =>
                    rw [dif_pos verifierRoom]
                    apply scheduler_native_trace_caps_mono
                      (machine_cursor_has_trace_caps
                        (R * (Q + verifierCalls)) (2 * R)
                        machine.verifierLimits limitBounds.verifier .verifier
                        adversaryReturned.finalState
                        (schedulerStageProgram Final
                          (totalizeOracleMachine machine.verifierFuel
                            (initialRawFutureFreeProgram machine.environment
                              adversaryValue.rawMessages machine.driverFuel)))
                        machine.verifierFuel adversaryReturned.finalCoherent
                        (fun verifierStage verifierFinalOracle
                            _verifierCoherent =>
                          match verifierStage with
                          | .completed verifierResult =>
                              match verifierResult with
                              | .error (.oracleAbort reason) =>
                                  .returned
                                    (SchedulerNativePlainRomResult.initialFailure
                                      (.verifierOracleAbort reason))
                              | .error .timeout =>
                                  .returned
                                    (SchedulerNativePlainRomResult.initialFailure
                                      .verifierTimeout)
                              | .ok verifierFinalState =>
                                  let rootRuntime := operationalRootRuntime
                                    (machine.tapeIdentity hidden) adversaryValue
                                    adversaryReturned.finalState
                                    verifierFinalOracle verifierFinalState
                                  mapSchedulerNativeCursorResult
                                    (fun clientRun =>
                                      SchedulerNativePlainRomResult.completed
                                        rootRuntime clientRun)
                                    (startConcreteRestorationClientFromRoot
                                      (globalOracleCalls := globalOracleCalls)
                                      startProgram machine.environment
                                      rootRuntime.node restorationConfiguration
                                      restorationFuel client))
                        (by
                          intro verifierAvailable verifierReturned
                          cases verifierReturned.result with
                          | completed verifierResult =>
                              cases verifierResult with
                              | error failure =>
                                  cases failure with
                                  | oracleAbort reason =>
                                      apply scheduler_native_trace_caps_mono
                                        (returned_cursor_has_zero_trace_caps
                                          (SchedulerNativePlainRomResult.initialFailure
                                            (.verifierOracleAbort reason)))
                                      · omega
                                      · omega
                                  | timeout =>
                                      apply scheduler_native_trace_caps_mono
                                        (returned_cursor_has_zero_trace_caps
                                          (SchedulerNativePlainRomResult.initialFailure
                                            .verifierTimeout))
                                      · omega
                                      · omega
                              | ok verifierFinalState =>
                                  let rootRuntime := operationalRootRuntime
                                    (machine.tapeIdentity hidden) adversaryValue
                                    adversaryReturned.finalState
                                    verifierReturned.finalState
                                    verifierFinalState
                                  have clientSafe :=
                                    concrete_restoration_client_has_trace_caps
                                      (globalOracleCalls := globalOracleCalls)
                                      Q verifierCalls startProgram
                                      machine.environment rootRuntime.node
                                      restorationConfiguration restorationFuel
                                      client replayAdversaryFuelBound
                                      replayVerifierFuelBound
                                  have clientMachineLe :
                                      restorationFuel * (Q + verifierCalls) ≤
                                        R * (Q + verifierCalls) :=
                                    Nat.mul_le_mul_right _ restorationRequestBound
                                  have clientForkLe : 2 * restorationFuel ≤
                                      2 * R :=
                                    Nat.mul_le_mul_left 2 restorationRequestBound
                                  exact scheduler_native_trace_caps_map
                                    (fun clientRun =>
                                      SchedulerNativePlainRomResult.completed
                                        rootRuntime clientRun)
                                    (R * (Q + verifierCalls)) (2 * R)
                                    (scheduler_native_trace_caps_mono clientSafe
                                      clientMachineLe clientForkLe)))
                    · omega
                    · exact Nat.le_refl _
                  next =>
                    rw [dif_neg verifierRoom]
                    apply scheduler_native_trace_caps_mono
                      (returned_cursor_has_zero_trace_caps
                        (SchedulerNativePlainRomResult.initialFailure
                          .verifierRoom))
                    · omega
                    · omega))
    · omega
    · exact Nat.le_refl _
  next =>
    rw [dif_neg adversaryRoom]
    apply scheduler_native_trace_caps_mono
      (returned_cursor_has_zero_trace_caps
        (SchedulerNativePlainRomResult.initialFailure .adversaryRoom))
    · omega
    · omega

theorem exact_plain_rom_cursor_has_M_and_2R_trace_caps
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type}
    {parameters : ExactCompilerResourceParameters}
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (hidden : HiddenTape) :
    SchedulerNativeCursorHasTraceCaps
      (full256MachineFreshCap parameters) (sameTapeStartCap parameters)
      (exactPlainRomCursor configuration hidden) := by
  simpa [exactPlainRomCursor, full256MachineFreshCap, sameTapeStartCap,
    deployedFull256VerifierCallCap, Nat.add_assoc] using
    (scheduler_native_plain_rom_cursor_has_trace_caps
      parameters.q1ShaCallCap deployedFull256VerifierCallCap
      parameters.forkRequestCap configuration.machine hidden
      configuration.rootLimitBounds configuration.restorationConfiguration
      configuration.restorationFuel configuration.client
      configuration.bounds.rootAdversaryFuel
      configuration.bounds.rootVerifierFuel
      configuration.bounds.replayAdversaryFuel
      configuration.bounds.replayVerifierFuel
      configuration.bounds.restorationRequests)

/-- Experiment-facing actual trace bound.  Unlike the total `F`-length fact,
this theorem identifies the two resource classes used by `ResourceUse`:
machine-fresh answers are bounded by `M` and fork coordinates by `2R`. -/
theorem run_exact_plain_rom_trace_has_M_and_2R_caps
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters)
    (transitionRoom : 3 ≤ transitionFuel) :
    TraceCoordinateCaps (full256MachineFreshCap parameters)
      (sameTapeStartCap parameters)
      (runExactPlainRom transitionFuel configuration sample).trace := by
  obtain ⟨result, completed⟩ :=
    run_exact_plain_rom_terminal_is_returned transitionFuel configuration sample
      transitionRoom
  have safe := exact_plain_rom_cursor_has_M_and_2R_trace_caps configuration
    sample.1
  exact run_scheduler_native_respects_projected_traced_returned
    (fun _result trace => TraceCoordinateCaps
      (full256MachineFreshCap parameters) (sameTapeStartCap parameters) trace)
    transitionFuel (by omega) (exactPlainRomCursor configuration sample.1) safe
      sample.2 result (by simpa [runExactPlainRom] using completed)

#print axioms trace_coordinate_partition
#print axioms machine_cursor_has_trace_caps
#print axioms fork_pair_cursor_has_trace_caps
#print axioms scheduler_native_trace_caps_map
#print axioms dispatch_concrete_restoration_has_trace_caps
#print axioms concrete_restoration_client_has_trace_caps
#print axioms exact_plain_rom_cursor_has_M_and_2R_trace_caps
#print axioms run_exact_plain_rom_trace_has_M_and_2R_caps

end

end AspisK1.V7Tag73ExactPlainRomTraceResourceCaps
