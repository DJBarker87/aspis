import V7Tag73GeneratedReaderBridge

/-!
# Literal generated compact-relation fixed-field loop bridge

This file traces the translated inner six-element mutable-slice loop used by
`decode_compact_relation_fields`.  Every continuing edge is tied to one
literal successful production `next_qm31` call, and the exact iterator measure
is preserved without a source-agreement premise.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

set_option autoImplicit false
set_option maxRecDepth 20000

namespace AspisV7Tag73GeneratedRelationFieldsBridge

open V7Tag73FixedFieldGenericNamespaceR1Generated
open AspisV7Tag73AeneasExactLoopTrace
open AspisV7Tag73GeneratedReaderBridge

theorem SuccessfulFixedReaderTrace.append
    {first middle final : v6_onefold.V6FixedFieldReader}
    {left right : List field.QM31}
    (leftTrace : SuccessfulFixedReaderTrace first left middle)
    (rightTrace : SuccessfulFixedReaderTrace middle right final) :
    SuccessfulFixedReaderTrace first (left ++ right) final := by
  induction leftTrace with
  | nil => simpa using rightTrace
  | cons read rest inductionHypothesis =>
    simpa using SuccessfulFixedReaderTrace.cons read
      (inductionHypothesis rightTrace)

abbrev RelationInnerState :=
  core.slice.iter.IterMut field.QM31 ×
    (core.slice.iter.IterMut field.QM31 →
      core.slice.iter.IterMut field.QM31) ×
    v6_onefold.V6FixedFieldReader

abbrev RelationFieldsOutput :=
  v6_onefold.V6FixedFieldReader ×
    Option (core.result.Result
      (Array (Array field.QM31 6#usize) 4#usize)
      v6_transcript.V6TranscriptError) ×
    core.slice.iter.IterMut field.QM31

def relationInnerBody (state : RelationInnerState) :
    Result (ControlFlow RelationInnerState RelationFieldsOutput) :=
  v6_transcript.decode_compact_relation_fields_loop0_loop0.body
    v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
    state.1 state.2.1 state.2.2

def relationInnerMeasure (state : RelationInnerState) : Nat :=
  state.1.slice.val.length - state.1.i

private theorem iterMutNextSomeExact
    (before after : core.slice.iter.IterMut field.QM31)
    (value : field.QM31)
    (back : core.slice.iter.IterMut field.QM31 → Option field.QM31 →
      core.slice.iter.IterMut field.QM31)
    (run : core.slice.iter.IteratorIterMut.next before =
      .ok (some value, after, back)) :
    before.i < before.slice.val.length ∧
      after.i = before.i + 1 ∧ after.slice = before.slice := by
  unfold core.slice.iter.IteratorIterMut.next at run
  split at run
  · rename_i available
    simp at run
    rcases run with ⟨_, afterExact, _⟩
    rw [← afterExact]
    exact ⟨by simpa [Slice.len_val] using available, rfl, rfl⟩
  · simp at run

private theorem iterMutNextNoneExhausted
    (before after : core.slice.iter.IterMut field.QM31)
    (back : core.slice.iter.IterMut field.QM31 → Option field.QM31 →
      core.slice.iter.IterMut field.QM31)
    (run : core.slice.iter.IteratorIterMut.next before =
      .ok (none, after, back)) :
    before.slice.val.length ≤ before.i := by
  unfold core.slice.iter.IteratorIterMut.next at run
  split at run
  · simp at run
  · rename_i exhausted
    simpa [Slice.len_val] using Nat.le_of_not_gt exhausted

theorem relation_inner_body_cont_measure_exact
    (state next : RelationInnerState)
    (run : relationInnerBody state = .ok (.cont next)) :
    relationInnerMeasure next + 1 = relationInnerMeasure state := by
  unfold relationInnerBody at run
  unfold v6_transcript.decode_compact_relation_fields_loop0_loop0.body at run
  generalize iteratorRun :
      core.slice.iter.IteratorIterMut.next state.1 = iteratorResult at run
  cases iteratorResult with
  | fail error => simp at run
  | div => simp at run
  | ok iteratorOutput =>
    rcases iteratorOutput with ⟨item, iterAfter, nextBack⟩
    cases item with
    | none => simp at run
    | some slot =>
      have iteratorExact :=
        iterMutNextSomeExact state.1 iterAfter slot nextBack iteratorRun
      simp only [bind_tc_ok] at run
      generalize readRun :
          v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream.next_qm31
            state.2.2 = readResult at run
      cases readResult with
      | fail error => simp at run
      | div => simp at run
      | ok readOutput =>
        rcases readOutput with ⟨fixedResult, readerAfter⟩
        cases fixedResult with
        | Err error =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            v6_transcript.V6TranscriptError.Insts.CoreConvertFromV6WireError.from]
            at run
        | Ok value =>
          simp [core.result.Result.Insts.CoreOpsTry.branch] at run
          subst next
          unfold relationInnerMeasure
          rw [iteratorExact.2.2, iteratorExact.2.1]
          omega

theorem relation_inner_body_cont_has_successful_read
    (state next : RelationInnerState)
    (run : relationInnerBody state = .ok (.cont next)) :
    ∃ value,
      v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream.next_qm31
          state.2.2 = .ok (.Ok value, next.2.2) := by
  unfold relationInnerBody at run
  unfold v6_transcript.decode_compact_relation_fields_loop0_loop0.body at run
  generalize iteratorRun :
      core.slice.iter.IteratorIterMut.next state.1 = iteratorResult at run
  cases iteratorResult with
  | fail error => simp at run
  | div => simp at run
  | ok iteratorOutput =>
    rcases iteratorOutput with ⟨item, iterAfter, nextBack⟩
    cases item with
    | none => simp at run
    | some slot =>
      simp only [bind_tc_ok] at run
      generalize readRun :
          v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream.next_qm31
            state.2.2 = readResult at run
      cases readResult with
      | fail error => simp at run
      | div => simp at run
      | ok readOutput =>
        rcases readOutput with ⟨fixedResult, readerAfter⟩
        cases fixedResult with
        | Err error =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            v6_transcript.V6TranscriptError.Insts.CoreConvertFromV6WireError.from]
            at run
        | Ok value =>
          simp [core.result.Result.Insts.CoreOpsTry.branch] at run
          subst next
          exact ⟨value, by simpa using readRun⟩

theorem relation_inner_body_done_classification
    (state : RelationInnerState)
    (output : RelationFieldsOutput)
    (run : relationInnerBody state = .ok (.done output)) :
    (output.2.1 = none ∧ output.1 = state.2.2 ∧
      relationInnerMeasure state = 0) ∨
    ∃ error : v6_transcript.V6TranscriptError,
      output.2.1 = some (.Err error) := by
  unfold relationInnerBody at run
  unfold v6_transcript.decode_compact_relation_fields_loop0_loop0.body at run
  generalize iteratorRun :
      core.slice.iter.IteratorIterMut.next state.1 = iteratorResult at run
  cases iteratorResult with
  | fail error => simp at run
  | div => simp at run
  | ok iteratorOutput =>
    rcases iteratorOutput with ⟨item, iterAfter, nextBack⟩
    cases item with
    | none =>
      have exhausted :=
        iterMutNextNoneExhausted state.1 iterAfter nextBack iteratorRun
      simp at run
      subst output
      left
      refine ⟨rfl, rfl, ?_⟩
      unfold relationInnerMeasure
      omega
    | some slot =>
      simp only [bind_tc_ok] at run
      generalize readRun :
          v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream.next_qm31
            state.2.2 = readResult at run
      cases readResult with
      | fail error => simp at run
      | div => simp at run
      | ok readOutput =>
        rcases readOutput with ⟨fixedResult, readerAfter⟩
        cases fixedResult with
        | Err error =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            v6_transcript.V6TranscriptError.Insts.CoreConvertFromV6WireError.from]
            at run
          subst output
          right
          exact ⟨_, rfl⟩
        | Ok value =>
          simp [core.result.Result.Insts.CoreOpsTry.branch] at run

theorem relation_inner_body_cont_decreases
    (state next : RelationInnerState)
    (run : relationInnerBody state = .ok (.cont next)) :
    relationInnerMeasure next < relationInnerMeasure state := by
  have exactStep := relation_inner_body_cont_measure_exact state next run
  omega

theorem relation_inner_body_done_without_pending_exact
    (state : RelationInnerState)
    (output : RelationFieldsOutput)
    (run : relationInnerBody state = .ok (.done output))
    (noPending : output.2.1 = none) :
    output.1 = state.2.2 ∧ relationInnerMeasure state = 0 := by
  rcases relation_inner_body_done_classification state output run with
    normal | ⟨error, pendingError⟩
  · exact ⟨normal.2.1, normal.2.2⟩
  · rw [noPending] at pendingError
    simp at pendingError

theorem relation_inner_loop_success_has_exact_trace
    (state : RelationInnerState)
    (output : RelationFieldsOutput)
    (run :
      v6_transcript.decode_compact_relation_fields_loop0_loop0
        v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
        state.1 state.2.1 state.2.2 = .ok output) :
    Nonempty (ExactLoopTrace relationInnerBody state output) := by
  apply loop_success_has_exact_trace relationInnerBody relationInnerMeasure
    relation_inner_body_cont_decreases state output
  exact run

theorem relation_inner_trace_without_pending_has_successful_reads
    {state : RelationInnerState} {output : RelationFieldsOutput}
    (trace : ExactLoopTrace relationInnerBody state output)
    (noPending : output.2.1 = none) :
    ∃ values,
      SuccessfulReadTrace
        v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream.next_qm31
        state.2.2 values output.1 ∧
      values.length = trace.contCount := by
  induction trace with
  | done equation =>
    have doneExact := relation_inner_body_done_without_pending_exact
      _ _ equation noPending
    rw [doneExact.1]
    exact ⟨[], .nil _, rfl⟩
  | cont equation tail inductionHypothesis =>
    obtain ⟨value, read⟩ :=
      relation_inner_body_cont_has_successful_read _ _ equation
    obtain ⟨values, rest, lengthExact⟩ := inductionHypothesis noPending
    refine ⟨value :: values, .cons read rest, ?_⟩
    change values.length + 1 = tail.contCount + 1
    omega

theorem relation_inner_trace_without_pending_cont_count
    {state : RelationInnerState} {output : RelationFieldsOutput}
    (trace : ExactLoopTrace relationInnerBody state output)
    (noPending : output.2.1 = none) :
    trace.contCount = relationInnerMeasure state := by
  induction trace with
  | done equation =>
    have doneExact := relation_inner_body_done_without_pending_exact
      _ _ equation noPending
    simp [ExactLoopTrace.contCount, doneExact.2]
  | cont equation tail inductionHypothesis =>
    have stepExact := relation_inner_body_cont_measure_exact _ _ equation
    simp only [ExactLoopTrace.contCount]
    rw [inductionHypothesis noPending]
    omega

theorem relation_inner_trace_never_returns_pending_success
    {state : RelationInnerState} {output : RelationFieldsOutput}
    (trace : ExactLoopTrace relationInnerBody state output) :
    ∀ values : Array (Array field.QM31 6#usize) 4#usize,
      output.2.1 ≠ some (.Ok values) := by
  induction trace with
  | done equation =>
    rcases relation_inner_body_done_classification _ _ equation with
      normal | ⟨error, pendingError⟩
    · intro values pendingSuccess
      rw [normal.1] at pendingSuccess
      simp at pendingSuccess
    · intro values pendingSuccess
      rw [pendingError] at pendingSuccess
      simp at pendingSuccess
  | cont equation tail inductionHypothesis => exact inductionHypothesis

theorem relation_inner_loop_success_without_pending_has_reads
    (state : RelationInnerState) (output : RelationFieldsOutput)
    (run :
      v6_transcript.decode_compact_relation_fields_loop0_loop0
        v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
        state.1 state.2.1 state.2.2 = .ok output)
    (noPending : output.2.1 = none) :
    ∃ values,
      SuccessfulReadTrace
        v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream.next_qm31
        state.2.2 values output.1 ∧
      values.length = relationInnerMeasure state := by
  obtain ⟨trace⟩ := relation_inner_loop_success_has_exact_trace state output run
  obtain ⟨values, reads, lengthExact⟩ :=
    relation_inner_trace_without_pending_has_successful_reads trace noPending
  refine ⟨values, reads, ?_⟩
  rw [lengthExact, relation_inner_trace_without_pending_cont_count trace noPending]

abbrev RelationOuterState :=
  core.slice.iter.IterMut (Array field.QM31 6#usize) ×
    (core.slice.iter.IterMut (Array field.QM31 6#usize) →
      core.slice.iter.IterMut (Array field.QM31 6#usize)) ×
    v6_onefold.V6FixedFieldReader

abbrev RelationOuterOutput :=
  v6_onefold.V6FixedFieldReader ×
    Option (core.result.Result
      (Array (Array field.QM31 6#usize) 4#usize)
      v6_transcript.V6TranscriptError) ×
    core.slice.iter.IterMut (Array field.QM31 6#usize)

def relationOuterBody (state : RelationOuterState) :
    Result (ControlFlow RelationOuterState RelationOuterOutput) :=
  v6_transcript.decode_compact_relation_fields_loop0.body
    v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
    state.1 state.2.1 state.2.2

def relationOuterMeasure (state : RelationOuterState) : Nat :=
  state.1.slice.val.length - state.1.i

private theorem outerIterMutNextSomeExact
    (before after : core.slice.iter.IterMut (Array field.QM31 6#usize))
    (value : Array field.QM31 6#usize)
    (back : core.slice.iter.IterMut (Array field.QM31 6#usize) →
      Option (Array field.QM31 6#usize) →
      core.slice.iter.IterMut (Array field.QM31 6#usize))
    (run : core.slice.iter.IteratorIterMut.next before =
      .ok (some value, after, back)) :
    before.i < before.slice.val.length ∧
      after.i = before.i + 1 ∧ after.slice = before.slice := by
  unfold core.slice.iter.IteratorIterMut.next at run
  split at run
  · rename_i available
    simp at run
    rcases run with ⟨_, afterExact, _⟩
    rw [← afterExact]
    exact ⟨by simpa [Slice.len_val] using available, rfl, rfl⟩
  · simp at run

private theorem outerIterMutNextNoneExhausted
    (before after : core.slice.iter.IterMut (Array field.QM31 6#usize))
    (back : core.slice.iter.IterMut (Array field.QM31 6#usize) →
      Option (Array field.QM31 6#usize) →
      core.slice.iter.IterMut (Array field.QM31 6#usize))
    (run : core.slice.iter.IteratorIterMut.next before =
      .ok (none, after, back)) :
    before.slice.val.length ≤ before.i := by
  unfold core.slice.iter.IteratorIterMut.next at run
  split at run
  · simp at run
  · rename_i exhausted
    simpa [Slice.len_val] using Nat.le_of_not_gt exhausted

theorem relation_outer_body_cont_measure_exact
    (state next : RelationOuterState)
    (run : relationOuterBody state = .ok (.cont next)) :
    relationOuterMeasure next + 1 = relationOuterMeasure state := by
  unfold relationOuterBody at run
  unfold v6_transcript.decode_compact_relation_fields_loop0.body at run
  generalize iteratorRun :
      core.slice.iter.IteratorIterMut.next state.1 = iteratorResult at run
  cases iteratorResult with
  | fail error => simp at run
  | div => simp at run
  | ok iteratorOutput =>
    rcases iteratorOutput with ⟨item, iterAfter, nextBack⟩
    cases item with
    | none => simp at run
    | some round =>
      have iteratorExact :=
        outerIterMutNextSomeExact state.1 iterAfter round nextBack iteratorRun
      simp only [bind_tc_ok] at run
      generalize intoRun :
          MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter
            round = intoResult at run
      cases intoResult with
      | fail error => simp at run
      | div => simp at run
      | ok intoOutput =>
        rcases intoOutput with ⟨innerIter, innerBack⟩
        simp only [bind_tc_ok] at run
        generalize innerRun :
            v6_transcript.decode_compact_relation_fields_loop0_loop0
              v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
              innerIter (fun iterator => iterator) state.2.2 =
                innerResult at run
        cases innerResult with
        | fail error => simp at run
        | div => simp at run
        | ok innerOutput =>
          rcases innerOutput with ⟨readerAfter, pending, innerFinal⟩
          cases pending with
          | none =>
            simp at run
            subst next
            unfold relationOuterMeasure
            rw [iteratorExact.2.2, iteratorExact.2.1]
            omega
          | some pendingResult => simp at run

theorem relation_outer_body_cont_has_six_reads
    (state next : RelationOuterState)
    (run : relationOuterBody state = .ok (.cont next)) :
    ∃ values,
      SuccessfulFixedReaderTrace state.2.2 values next.2.2 ∧
      values.length = 6 := by
  unfold relationOuterBody at run
  unfold v6_transcript.decode_compact_relation_fields_loop0.body at run
  generalize iteratorRun :
      core.slice.iter.IteratorIterMut.next state.1 = iteratorResult at run
  cases iteratorResult with
  | fail error => simp at run
  | div => simp at run
  | ok iteratorOutput =>
    rcases iteratorOutput with ⟨item, iterAfter, nextBack⟩
    cases item with
    | none => simp at run
    | some round =>
      simp only [bind_tc_ok] at run
      generalize intoRun :
          MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter
            round = intoResult at run
      cases intoResult with
      | fail error => simp at run
      | div => simp at run
      | ok intoOutput =>
        rcases intoOutput with ⟨innerIter, innerBack⟩
        simp only [bind_tc_ok] at run
        generalize innerRun :
            v6_transcript.decode_compact_relation_fields_loop0_loop0
              v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
              innerIter (fun iterator => iterator) state.2.2 =
                innerResult at run
        cases innerResult with
        | fail error => simp at run
        | div => simp at run
        | ok innerOutput =>
          rcases innerOutput with ⟨readerAfter, pending, innerFinal⟩
          cases pending with
          | some pendingResult => simp at run
          | none =>
            have innerReads :=
              relation_inner_loop_success_without_pending_has_reads
                (innerIter, (fun iterator => iterator), state.2.2)
                (readerAfter, none, innerFinal) innerRun rfl
            simp at run
            subst next
            obtain ⟨values, reads, lengthExact⟩ := innerReads
            have fixedReads :=
              successful_generated_read_trace_is_fixed_reader_trace reads
            refine ⟨values, fixedReads, ?_⟩
            rw [lengthExact]
            unfold relationInnerMeasure
            unfold
              MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter
              at intoRun
            simp at intoRun
            rcases intoRun with ⟨rfl, rfl⟩
            simpa [Slice.len_val] using round.property

theorem relation_outer_body_done_classification
    (state : RelationOuterState) (output : RelationOuterOutput)
    (run : relationOuterBody state = .ok (.done output)) :
    (output.2.1 = none ∧ output.1 = state.2.2 ∧
      relationOuterMeasure state = 0) ∨
    ∃ error : v6_transcript.V6TranscriptError,
      output.2.1 = some (.Err error) := by
  unfold relationOuterBody at run
  unfold v6_transcript.decode_compact_relation_fields_loop0.body at run
  generalize iteratorRun :
      core.slice.iter.IteratorIterMut.next state.1 = iteratorResult at run
  cases iteratorResult with
  | fail error => simp at run
  | div => simp at run
  | ok iteratorOutput =>
    rcases iteratorOutput with ⟨item, iterAfter, nextBack⟩
    cases item with
    | none =>
      have exhausted :=
        outerIterMutNextNoneExhausted state.1 iterAfter nextBack iteratorRun
      simp at run
      subst output
      left
      refine ⟨rfl, rfl, ?_⟩
      unfold relationOuterMeasure
      omega
    | some round =>
      simp only [bind_tc_ok] at run
      generalize intoRun :
          MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter
            round = intoResult at run
      cases intoResult with
      | fail error => simp at run
      | div => simp at run
      | ok intoOutput =>
        rcases intoOutput with ⟨innerIter, innerBack⟩
        simp only [bind_tc_ok] at run
        generalize innerRun :
            v6_transcript.decode_compact_relation_fields_loop0_loop0
              v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
              innerIter (fun iterator => iterator) state.2.2 =
                innerResult at run
        cases innerResult with
        | fail error => simp at run
        | div => simp at run
        | ok innerOutput =>
          rcases innerOutput with ⟨readerAfter, pending, innerFinal⟩
          cases pending with
          | none => simp at run
          | some pendingResult =>
            cases pendingResult with
            | Err error =>
              simp at run
              subst output
              right
              exact ⟨error, rfl⟩
            | Ok values =>
              obtain ⟨trace⟩ := relation_inner_loop_success_has_exact_trace
                (innerIter, (fun iterator => iterator), state.2.2)
                (readerAfter, some (.Ok values), innerFinal) innerRun
              exact False.elim
                (relation_inner_trace_never_returns_pending_success
                  trace values rfl)

theorem relation_outer_body_cont_decreases
    (state next : RelationOuterState)
    (run : relationOuterBody state = .ok (.cont next)) :
    relationOuterMeasure next < relationOuterMeasure state := by
  have exactStep := relation_outer_body_cont_measure_exact state next run
  omega

theorem relation_outer_body_done_without_pending_exact
    (state : RelationOuterState) (output : RelationOuterOutput)
    (run : relationOuterBody state = .ok (.done output))
    (noPending : output.2.1 = none) :
    output.1 = state.2.2 ∧ relationOuterMeasure state = 0 := by
  rcases relation_outer_body_done_classification state output run with
    normal | ⟨error, pendingError⟩
  · exact ⟨normal.2.1, normal.2.2⟩
  · rw [noPending] at pendingError
    simp at pendingError

theorem relation_outer_loop_success_has_exact_trace
    (state : RelationOuterState) (output : RelationOuterOutput)
    (run :
      v6_transcript.decode_compact_relation_fields_loop0
        v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
        state.1 state.2.1 state.2.2 = .ok output) :
    Nonempty (ExactLoopTrace relationOuterBody state output) := by
  apply loop_success_has_exact_trace relationOuterBody relationOuterMeasure
    relation_outer_body_cont_decreases state output
  exact run

theorem relation_outer_trace_without_pending_has_successful_reads
    {state : RelationOuterState} {output : RelationOuterOutput}
    (trace : ExactLoopTrace relationOuterBody state output)
    (noPending : output.2.1 = none) :
    ∃ values,
      SuccessfulFixedReaderTrace state.2.2 values output.1 ∧
      values.length = 6 * trace.contCount := by
  induction trace with
  | done equation =>
    have doneExact := relation_outer_body_done_without_pending_exact
      _ _ equation noPending
    rw [doneExact.1]
    exact ⟨[], .nil _, by simp [ExactLoopTrace.contCount]⟩
  | cont equation tail inductionHypothesis =>
    obtain ⟨headValues, headReads, headLength⟩ :=
      relation_outer_body_cont_has_six_reads _ _ equation
    obtain ⟨tailValues, tailReads, tailLength⟩ :=
      inductionHypothesis noPending
    refine ⟨headValues ++ tailValues,
      SuccessfulFixedReaderTrace.append headReads tailReads, ?_⟩
    rw [List.length_append, headLength, tailLength]
    change 6 + 6 * tail.contCount = 6 * (tail.contCount + 1)
    omega

theorem relation_outer_trace_without_pending_cont_count
    {state : RelationOuterState} {output : RelationOuterOutput}
    (trace : ExactLoopTrace relationOuterBody state output)
    (noPending : output.2.1 = none) :
    trace.contCount = relationOuterMeasure state := by
  induction trace with
  | done equation =>
    have doneExact := relation_outer_body_done_without_pending_exact
      _ _ equation noPending
    simp [ExactLoopTrace.contCount, doneExact.2]
  | cont equation tail inductionHypothesis =>
    have stepExact := relation_outer_body_cont_measure_exact _ _ equation
    simp only [ExactLoopTrace.contCount]
    rw [inductionHypothesis noPending]
    omega

theorem relation_outer_trace_never_returns_pending_success
    {state : RelationOuterState} {output : RelationOuterOutput}
    (trace : ExactLoopTrace relationOuterBody state output) :
    ∀ values : Array (Array field.QM31 6#usize) 4#usize,
      output.2.1 ≠ some (.Ok values) := by
  induction trace with
  | done equation =>
    rcases relation_outer_body_done_classification _ _ equation with
      normal | ⟨error, pendingError⟩
    · intro values pendingSuccess
      rw [normal.1] at pendingSuccess
      simp at pendingSuccess
    · intro values pendingSuccess
      rw [pendingError] at pendingSuccess
      simp at pendingSuccess
  | cont equation tail inductionHypothesis => exact inductionHypothesis

theorem relation_outer_loop_success_without_pending_has_reads
    (state : RelationOuterState) (output : RelationOuterOutput)
    (run :
      v6_transcript.decode_compact_relation_fields_loop0
        v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
        state.1 state.2.1 state.2.2 = .ok output)
    (noPending : output.2.1 = none) :
    ∃ values,
      SuccessfulFixedReaderTrace state.2.2 values output.1 ∧
      values.length = 6 * relationOuterMeasure state := by
  obtain ⟨trace⟩ := relation_outer_loop_success_has_exact_trace state output run
  obtain ⟨values, reads, lengthExact⟩ :=
    relation_outer_trace_without_pending_has_successful_reads trace noPending
  refine ⟨values, reads, ?_⟩
  rw [lengthExact, relation_outer_trace_without_pending_cont_count trace noPending]

theorem generated_decode_compact_relation_fields_success_reads_exactly_24
    (reader readerAfter : v6_onefold.V6FixedFieldReader)
    (decoded : Array (Array field.QM31 6#usize) 4#usize)
    (run :
      v6_transcript.decode_compact_relation_fields
        v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
        reader = .ok (.Ok decoded, readerAfter)) :
    ∃ values,
      SuccessfulFixedReaderTrace reader values readerAfter ∧
      values.length = 24 ∧
      ∀ value ∈ values, CanonicalGeneratedQM31 value := by
  unfold v6_transcript.decode_compact_relation_fields at run
  simp only [Aeneas.Std.lift, bind_tc_ok] at run
  let outerIter : core.slice.iter.IterMut (Array field.QM31 6#usize) :=
    { slice := Array.to_slice (Array.repeat 4#usize
        (Array.repeat 6#usize field.QM31.ZERO)) }
  change
    (do
      let loopOutput ←
        v6_transcript.decode_compact_relation_fields_loop0
          v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
          outerIter (fun iterator => iterator) reader
      match loopOutput.2.1 with
      | none =>
        ok (.Ok ((fun iterator => Array.from_slice
          (Array.repeat 4#usize (Array.repeat 6#usize field.QM31.ZERO))
          iterator.slice) loopOutput.2.2), loopOutput.1)
      | some result => ok (result, loopOutput.1)) =
        ok (.Ok decoded, readerAfter) at run
  generalize loopRun :
      v6_transcript.decode_compact_relation_fields_loop0
        v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
        outerIter (fun iterator => iterator) reader = loopResult at run
  cases loopResult with
  | fail error => simp at run
  | div => simp at run
  | ok loopOutput =>
    rcases loopOutput with ⟨reader1, pending, outerFinal⟩
    cases pending with
    | none =>
      have reads := relation_outer_loop_success_without_pending_has_reads
        (outerIter, (fun iterator => iterator), reader)
        (reader1, none, outerFinal) loopRun rfl
      simp at run
      rw [← run.2]
      obtain ⟨values, fixedReads, lengthExact⟩ := reads
      refine ⟨values, fixedReads, ?_,
        successful_trace_values_canonical fixedReads⟩
      rw [lengthExact]
      unfold relationOuterMeasure outerIter
      norm_num [Array.to_slice, Slice.len_val]
    | some pendingResult =>
      cases pendingResult with
      | Err error => simp at run
      | Ok pendingValues =>
        obtain ⟨trace⟩ := relation_outer_loop_success_has_exact_trace
          (outerIter, (fun iterator => iterator), reader)
          (reader1, some (.Ok pendingValues), outerFinal) loopRun
        exact False.elim
          (relation_outer_trace_never_returns_pending_success
            trace pendingValues rfl)

#print axioms iterMutNextSomeExact
#print axioms iterMutNextNoneExhausted
#print axioms relation_inner_body_cont_measure_exact
#print axioms relation_inner_body_cont_has_successful_read
#print axioms relation_inner_body_done_classification
#print axioms relation_inner_body_cont_decreases
#print axioms relation_inner_body_done_without_pending_exact
#print axioms relation_inner_loop_success_has_exact_trace
#print axioms relation_inner_trace_without_pending_has_successful_reads
#print axioms relation_inner_trace_without_pending_cont_count
#print axioms relation_inner_trace_never_returns_pending_success
#print axioms relation_inner_loop_success_without_pending_has_reads
#print axioms outerIterMutNextSomeExact
#print axioms relation_outer_body_cont_measure_exact
#print axioms relation_outer_body_cont_has_six_reads
#print axioms relation_outer_body_done_classification
#print axioms relation_outer_loop_success_has_exact_trace
#print axioms relation_outer_trace_without_pending_has_successful_reads
#print axioms relation_outer_trace_without_pending_cont_count
#print axioms relation_outer_trace_never_returns_pending_success
#print axioms relation_outer_loop_success_without_pending_has_reads
#print axioms generated_decode_compact_relation_fields_success_reads_exactly_24

end AspisV7Tag73GeneratedRelationFieldsBridge
