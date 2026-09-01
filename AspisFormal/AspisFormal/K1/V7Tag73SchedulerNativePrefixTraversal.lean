import AspisFormal.K1.V7Tag73SchedulerTraceFactorization

/-!
# Exact prefix traversal for the result-carrying Tag-73 scheduler

The fixed scheduler's existing run semantics retains the final terminal and
flat exposure trace, but not the live cursor reached after a strict prefix of
that trace.  Causal-state alignment needs that cursor: its erasure is the
proof-rich cursor indexed by the lazy-oracle target-clean certificate.

This leaf defines the one-coordinate transition directly from
`seekSchedulerNativeExposure` and an inductive finite prefix traversal.  No
cursor, controller, trace decomposition, or restoration state is supplied by
the caller: every step contains the literal scheduler request equation.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73SchedulerNativePrefixTraversal

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73AtomicPairReplay
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerTraceFactorization

noncomputable section

universe u

/-- The live native cursor after supplying one answer to the literal exposed
request.  Terminal requests consume padding and remain terminal, exactly as
`runSchedulerNative` does. -/
def schedulerNativeRequestNext
    {globalOracleCalls : Nat} {Result : Type u} :
    SchedulerNativeRequest globalOracleCalls Result → Digest256 →
      SchedulerNativeCursor globalOracleCalls Result
  | .returned result, _answer => .returned result
  | .failed reason, _answer => .failed reason
  | .transitionLimit, _answer => .failed .transitionLimit
  | .machineFresh limits limitBound actor state input nextProgram
      remainingFuel coherent _totalRoom _freshRoom _missing onReturned,
      answer =>
      .machine limits limitBound actor
        (freshQueryState actor state input answer) (nextProgram answer)
        remainingFuel
        (fresh_query_state_preserves_history_total_coherent actor state input
          answer coherent)
        onReturned
  | .forkOutput frozenHistory pairRoom outputInput advanceInput template next,
      answer =>
      .forkAdvance frozenHistory pairRoom outputInput advanceInput template
        answer next
  | .forkAdvance _frozenHistory _pairRoom _outputInput _advanceInput template
      forkOutput next, answer =>
      next (scheduledForkConfiguration template forkOutput answer)

/-- Result-free successor used by the dependent target-clean traversal. -/
def unifiedRequestNext
    {globalOracleCalls : Nat} :
    UnifiedExposureRequest globalOracleCalls → Digest256 →
      UnifiedExposureCursor globalOracleCalls
  | .halted, _answer => .halted
  | .transitionLimit, _answer => .halted
  | .machineFresh limits limitBound actor state input nextProgram
      remainingFuel coherent _totalRoom _freshRoom _missing onReturned,
      answer =>
      .machine limits limitBound actor
        (freshQueryState actor state input answer) (nextProgram answer)
        remainingFuel
        (fresh_query_state_preserves_history_total_coherent actor state input
          answer coherent)
        onReturned
  | .forkOutput frozenHistory pairRoom outputInput advanceInput template next,
      answer =>
      .forkAdvance frozenHistory pairRoom outputInput advanceInput template
        answer next
  | .forkAdvance _frozenHistory _pairRoom _outputInput _advanceInput template
      forkOutput next, answer =>
      next (scheduledForkConfiguration template forkOutput answer)

/-- Erasure commutes with one literal answer step. -/
theorem erase_scheduler_native_request_next
    {globalOracleCalls : Nat} {Result : Type u}
    (request : SchedulerNativeRequest globalOracleCalls Result)
    (answer : Digest256) :
    (schedulerNativeRequestNext request answer).erase =
      unifiedRequestNext request.erase answer := by
  cases request <;> rfl

/-- The exact flat record emitted by one request/answer coordinate. -/
def schedulerNativeRequestRecord
    {globalOracleCalls : Nat} {Result : Type u} :
    SchedulerNativeRequest globalOracleCalls Result → Digest256 →
      UnifiedExposureRecord
  | .returned _result, answer => .padding answer
  | .failed _reason, answer => .padding answer
  | .transitionLimit, answer => .padding answer
  | .machineFresh _limits _limitBound actor _state input _nextProgram
      _remainingFuel _coherent _totalRoom _freshRoom _missing _onReturned,
      answer =>
      .machineFresh actor input answer
  | .forkOutput frozenHistory _pairRoom outputInput advanceInput template _next,
      answer =>
      .forkOutput frozenHistory outputInput advanceInput template answer
  | .forkAdvance frozenHistory _pairRoom outputInput advanceInput template
      forkOutput _next, answer =>
      .forkAdvance
        { frozenHistory := frozenHistory
          outputInput := outputInput
          advanceInput := advanceInput
          template := template
          forkOutput := forkOutput
          forkAdvance := answer }

/-- Deterministic cursor reached after a finite answer prefix. -/
def schedulerNativePrefixCursor
    {globalOracleCalls : Nat} {Result : Type u} (transitionFuel : Nat) :
    SchedulerNativeCursor globalOracleCalls Result → List Digest256 →
      SchedulerNativeCursor globalOracleCalls Result
  | cursor, [] => cursor
  | cursor, answer :: rest =>
      schedulerNativePrefixCursor transitionFuel
        (schedulerNativeRequestNext
          (seekSchedulerNativeExposure transitionFuel cursor) answer)
        rest

/-- Result-free cursor reached by the same answer prefix. -/
def unifiedPrefixCursor
    {globalOracleCalls : Nat} (transitionFuel : Nat) :
    UnifiedExposureCursor globalOracleCalls → List Digest256 →
      UnifiedExposureCursor globalOracleCalls
  | cursor, [] => cursor
  | cursor, answer :: rest =>
      unifiedPrefixCursor transitionFuel
        (unifiedRequestNext (seekUnifiedExposure transitionFuel cursor) answer)
        rest

/-- Erasing terminal data commutes with every finite prefix, not only with one
normalized request. -/
theorem erase_scheduler_native_prefix_cursor
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat)
    (cursor : SchedulerNativeCursor globalOracleCalls Result)
    (answers : List Digest256) :
    (schedulerNativePrefixCursor transitionFuel cursor answers).erase =
      unifiedPrefixCursor transitionFuel cursor.erase answers := by
  induction answers generalizing cursor with
  | nil => rfl
  | cons answer rest ih =>
      simp only [schedulerNativePrefixCursor, unifiedPrefixCursor]
      rw [← erase_seek_scheduler_native_exposure transitionFuel cursor]
      rw [← erase_scheduler_native_request_next]
      exact ih _

/-- Deterministic chronological records emitted by the same finite prefix. -/
def schedulerNativePrefixRecords
    {globalOracleCalls : Nat} {Result : Type u} (transitionFuel : Nat) :
    SchedulerNativeCursor globalOracleCalls Result → List Digest256 →
      List UnifiedExposureRecord
  | _cursor, [] => []
  | cursor, answer :: rest =>
      let request := seekSchedulerNativeExposure transitionFuel cursor
      schedulerNativeRequestRecord request answer ::
        schedulerNativePrefixRecords transitionFuel
          (schedulerNativeRequestNext request answer) rest

@[simp] theorem scheduler_native_prefix_cursor_append
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat)
    (cursor : SchedulerNativeCursor globalOracleCalls Result)
    (first second : List Digest256) :
    schedulerNativePrefixCursor transitionFuel cursor (first ++ second) =
      schedulerNativePrefixCursor transitionFuel
        (schedulerNativePrefixCursor transitionFuel cursor first) second := by
  induction first generalizing cursor with
  | nil => rfl
  | cons answer rest ih =>
      simp only [List.cons_append, schedulerNativePrefixCursor]
      exact ih _

@[simp] theorem scheduler_native_prefix_records_append
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat)
    (cursor : SchedulerNativeCursor globalOracleCalls Result)
    (first second : List Digest256) :
    schedulerNativePrefixRecords transitionFuel cursor (first ++ second) =
      schedulerNativePrefixRecords transitionFuel cursor first ++
        schedulerNativePrefixRecords transitionFuel
          (schedulerNativePrefixCursor transitionFuel cursor first) second := by
  induction first generalizing cursor with
  | nil => rfl
  | cons answer rest ih =>
      simp only [List.cons_append, schedulerNativePrefixRecords,
        schedulerNativePrefixCursor, List.cons_append]
      rw [ih]

@[simp] theorem scheduler_native_request_record_answer
    {globalOracleCalls : Nat} {Result : Type u}
    (request : SchedulerNativeRequest globalOracleCalls Result)
    (answer : Digest256) :
    (schedulerNativeRequestRecord request answer).answer = answer := by
  cases request <;> rfl

/-- A finite prefix of the executable scheduler.  The request equation at
each constructor prevents an arbitrary successor cursor from being chosen. -/
inductive SchedulerNativePrefixTraversal
    {globalOracleCalls : Nat} {Result : Type u} (transitionFuel : Nat) :
    SchedulerNativeCursor globalOracleCalls Result →
      List Digest256 → List UnifiedExposureRecord →
      SchedulerNativeCursor globalOracleCalls Result → Prop where
  | nil (cursor : SchedulerNativeCursor globalOracleCalls Result) :
      SchedulerNativePrefixTraversal transitionFuel cursor [] [] cursor
  | cons
      (cursor : SchedulerNativeCursor globalOracleCalls Result)
      (answer : Digest256)
      (request : SchedulerNativeRequest globalOracleCalls Result)
      (answers : List Digest256) (records : List UnifiedExposureRecord)
      (finalCursor : SchedulerNativeCursor globalOracleCalls Result)
      (requestExact : seekSchedulerNativeExposure transitionFuel cursor =
        request)
      (tail : SchedulerNativePrefixTraversal transitionFuel
        (schedulerNativeRequestNext request answer) answers records
          finalCursor) :
      SchedulerNativePrefixTraversal transitionFuel cursor (answer :: answers)
        (schedulerNativeRequestRecord request answer :: records) finalCursor

/-- Every concrete answer prefix has a unique operational traversal witness;
the records and reached cursor are computed by the scheduler itself. -/
theorem scheduler_native_prefix_traversal_exists
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat)
    (cursor : SchedulerNativeCursor globalOracleCalls Result)
    (answers : List Digest256) :
    ∃ records finalCursor,
      SchedulerNativePrefixTraversal transitionFuel cursor answers records
        finalCursor := by
  induction answers generalizing cursor with
  | nil => exact ⟨[], cursor, .nil cursor⟩
  | cons answer rest ih =>
      let request := seekSchedulerNativeExposure transitionFuel cursor
      obtain ⟨records, finalCursor, tail⟩ :=
        ih (schedulerNativeRequestNext request answer)
      exact ⟨schedulerNativeRequestRecord request answer :: records,
        finalCursor, .cons cursor answer request rest records finalCursor rfl
          tail⟩

/-- The relational traversal cannot hide a convenient record list: it is the
literal deterministic scheduler prefix. -/
theorem scheduler_native_prefix_traversal_records_exact
    {globalOracleCalls : Nat} {Result : Type u} {transitionFuel : Nat}
    {cursor finalCursor : SchedulerNativeCursor globalOracleCalls Result}
    {answers : List Digest256} {records : List UnifiedExposureRecord}
    (traversal : SchedulerNativePrefixTraversal transitionFuel cursor answers
      records finalCursor) :
    schedulerNativePrefixRecords transitionFuel cursor answers = records := by
  induction traversal with
  | nil => rfl
  | cons cursor answer request answers records finalCursor requestExact tail ih =>
      simp only [schedulerNativePrefixRecords, requestExact]
      exact congrArg (List.cons (schedulerNativeRequestRecord request answer)) ih

/-- Likewise the reached native cursor is computed, not selected by the
certificate witness. -/
theorem scheduler_native_prefix_traversal_cursor_exact
    {globalOracleCalls : Nat} {Result : Type u} {transitionFuel : Nat}
    {cursor finalCursor : SchedulerNativeCursor globalOracleCalls Result}
    {answers : List Digest256} {records : List UnifiedExposureRecord}
    (traversal : SchedulerNativePrefixTraversal transitionFuel cursor answers
      records finalCursor) :
    schedulerNativePrefixCursor transitionFuel cursor answers = finalCursor := by
  induction traversal with
  | nil => rfl
  | cons cursor answer request answers records finalCursor requestExact tail ih =>
      simp only [schedulerNativePrefixCursor, requestExact]
      exact ih

/-- The flat answers in a native prefix are exactly the supplied coordinates. -/
theorem scheduler_native_prefix_traversal_answers_exact
    {globalOracleCalls : Nat} {Result : Type u} {transitionFuel : Nat}
    {cursor finalCursor : SchedulerNativeCursor globalOracleCalls Result}
    {answers : List Digest256} {records : List UnifiedExposureRecord}
    (traversal : SchedulerNativePrefixTraversal transitionFuel cursor answers
      records finalCursor) :
    records.map UnifiedExposureRecord.answer = answers := by
  induction traversal with
  | nil => rfl
  | cons cursor answer request answers records finalCursor requestExact tail ih =>
      simp only [List.map_cons, scheduler_native_request_record_answer, ih]

/-- One exposed coordinate contributes its literal record and continues from
the literal native successor.  Keeping this as a separate lemma prevents the
prefix induction from depending on constructor-specific reduction details. -/
theorem run_scheduler_native_list_run_from_cons_trace
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat)
    (cursor : SchedulerNativeCursor globalOracleCalls Result)
    (answer : Digest256) (rest : List Digest256)
    (request : SchedulerNativeRequest globalOracleCalls Result)
    (requestExact : seekSchedulerNativeExposure transitionFuel cursor =
      request) :
    (runSchedulerNativeListRunFrom transitionFuel transitionFuel cursor
        (answer :: rest)).trace =
      schedulerNativeRequestRecord request answer ::
        (runSchedulerNativeListRunFrom transitionFuel transitionFuel
          (schedulerNativeRequestNext request answer) rest).trace := by
  simp only [runSchedulerNativeListRunFrom, requestExact]
  cases request <;> rfl

/-- Terminal data follows the same literal one-coordinate successor. -/
theorem run_scheduler_native_list_run_from_cons_terminal
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat)
    (cursor : SchedulerNativeCursor globalOracleCalls Result)
    (answer : Digest256) (rest : List Digest256)
    (request : SchedulerNativeRequest globalOracleCalls Result)
    (requestExact : seekSchedulerNativeExposure transitionFuel cursor =
      request) :
    (runSchedulerNativeListRunFrom transitionFuel transitionFuel cursor
        (answer :: rest)).terminal =
      (runSchedulerNativeListRunFrom transitionFuel transitionFuel
        (schedulerNativeRequestNext request answer) rest).terminal := by
  simp only [runSchedulerNativeListRunFrom, requestExact]
  cases request <;> rfl

/-- The trace produced on a prefixed answer list factors through the literal
cursor reached by the prefix traversal. -/
theorem scheduler_native_prefix_traversal_trace_factorization
    {globalOracleCalls : Nat} {Result : Type u} {transitionFuel : Nat}
    {cursor finalCursor : SchedulerNativeCursor globalOracleCalls Result}
    {answers : List Digest256} {records : List UnifiedExposureRecord}
    (traversal : SchedulerNativePrefixTraversal transitionFuel cursor answers
      records finalCursor) (suffix : List Digest256) :
    (runSchedulerNativeListRunFrom transitionFuel transitionFuel cursor
        (answers ++ suffix)).trace =
      records ++
        (runSchedulerNativeListRunFrom transitionFuel transitionFuel finalCursor
          suffix).trace := by
  induction traversal with
  | nil => rfl
  | cons cursor answer request answers records finalCursor requestExact tail ih =>
      rw [List.cons_append]
      rw [run_scheduler_native_list_run_from_cons_trace transitionFuel cursor
        answer (answers ++ suffix) request requestExact]
      rw [ih]
      rfl

/-- Terminal data factors through the same reached cursor as the trace. -/
theorem scheduler_native_prefix_traversal_terminal_factorization
    {globalOracleCalls : Nat} {Result : Type u} {transitionFuel : Nat}
    {cursor finalCursor : SchedulerNativeCursor globalOracleCalls Result}
    {answers : List Digest256} {records : List UnifiedExposureRecord}
    (traversal : SchedulerNativePrefixTraversal transitionFuel cursor answers
      records finalCursor) (suffix : List Digest256) :
    (runSchedulerNativeListRunFrom transitionFuel transitionFuel cursor
        (answers ++ suffix)).terminal =
      (runSchedulerNativeListRunFrom transitionFuel transitionFuel finalCursor
        suffix).terminal := by
  induction traversal with
  | nil => rfl
  | cons cursor answer request answers records finalCursor requestExact tail ih =>
      rw [List.cons_append]
      rw [run_scheduler_native_list_run_from_cons_terminal transitionFuel cursor
        answer (answers ++ suffix) request requestExact]
      exact ih

/-! ## Recovering the deterministic prefix from a concrete run -/

/-- The list interpreter emits exactly the supplied flat answer list.  This is
the list-level companion of `run_scheduler_native_answers_are_exact_tape` and
lets prefix arguments avoid manufacturing a length-indexed tape. -/
theorem run_scheduler_native_list_run_from_answers_exact
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) : ∀ (currentTransitionFuel : Nat)
      (cursor : SchedulerNativeCursor globalOracleCalls Result)
      (answers : List Digest256),
      (runSchedulerNativeListRunFrom transitionFuel currentTransitionFuel
        cursor answers).trace.map UnifiedExposureRecord.answer = answers := by
  intro currentTransitionFuel cursor answers
  induction answers generalizing currentTransitionFuel cursor with
  | nil => rfl
  | cons answer rest ih =>
      simp only [runSchedulerNativeListRunFrom]
      cases request : seekSchedulerNativeExposure currentTransitionFuel cursor
        <;> simp only [List.map_cons]
      all_goals simp only [UnifiedExposureRecord.answer]
      all_goals rw [ih]

/-- A prefix observed in a concrete scheduler trace is not merely compatible
with the supplied answers: it is the literal deterministic native prefix
computed from them.  This is the uniqueness direction needed when one run
exports a chronological prefix and a second run shares the same answer
prefix. -/
theorem scheduler_native_prefix_records_eq_of_run_trace_prefix
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat)
    (cursor : SchedulerNativeCursor globalOracleCalls Result)
    (answers : List Digest256)
    (preRecords postRecords : List UnifiedExposureRecord)
    (traceExact :
      (runSchedulerNativeListRun transitionFuel cursor answers).trace =
        preRecords ++ postRecords) :
    schedulerNativePrefixRecords transitionFuel cursor
        (preRecords.map UnifiedExposureRecord.answer) = preRecords := by
  have answersExact : answers =
      preRecords.map UnifiedExposureRecord.answer ++
        postRecords.map UnifiedExposureRecord.answer := by
    calc
      answers =
          (runSchedulerNativeListRun transitionFuel cursor answers).trace.map
            UnifiedExposureRecord.answer :=
        (run_scheduler_native_list_run_from_answers_exact transitionFuel
          transitionFuel cursor answers).symm
      _ = (preRecords ++ postRecords).map UnifiedExposureRecord.answer := by
        rw [traceExact]
      _ = preRecords.map UnifiedExposureRecord.answer ++
          postRecords.map UnifiedExposureRecord.answer := List.map_append
  obtain ⟨records, finalCursor, traversal⟩ :=
    scheduler_native_prefix_traversal_exists transitionFuel cursor
      (preRecords.map UnifiedExposureRecord.answer)
  have recordsExact :=
    scheduler_native_prefix_traversal_records_exact traversal
  have recordsAnswers :=
    scheduler_native_prefix_traversal_answers_exact traversal
  have traceFactor :=
    scheduler_native_prefix_traversal_trace_factorization traversal
      (postRecords.map UnifiedExposureRecord.answer)
  rw [← answersExact] at traceFactor
  have splitExact : preRecords ++ postRecords = records ++
      (runSchedulerNativeListRunFrom transitionFuel transitionFuel finalCursor
        (postRecords.map UnifiedExposureRecord.answer)).trace :=
    traceExact.symm.trans traceFactor
  have recordsLength : records.length = preRecords.length := by
    have := congrArg List.length recordsAnswers
    simpa using this
  have taken := congrArg (List.take preRecords.length) splitExact
  have recordsEq : preRecords = records := by
    simpa [recordsLength] using taken
  rw [recordsExact, recordsEq]

#print axioms scheduler_native_prefix_traversal_exists
#print axioms erase_scheduler_native_request_next
#print axioms erase_scheduler_native_prefix_cursor
#print axioms scheduler_native_prefix_cursor_append
#print axioms scheduler_native_prefix_records_append
#print axioms scheduler_native_prefix_traversal_records_exact
#print axioms scheduler_native_prefix_traversal_cursor_exact
#print axioms scheduler_native_prefix_traversal_answers_exact
#print axioms scheduler_native_prefix_traversal_trace_factorization
#print axioms run_scheduler_native_list_run_from_answers_exact
#print axioms scheduler_native_prefix_records_eq_of_run_trace_prefix
#print axioms scheduler_native_prefix_traversal_terminal_factorization

end

end AspisK1.V7Tag73SchedulerNativePrefixTraversal
