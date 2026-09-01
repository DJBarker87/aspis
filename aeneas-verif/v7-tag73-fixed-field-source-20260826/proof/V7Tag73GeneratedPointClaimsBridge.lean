import V7Tag73GeneratedReaderBridge

/-!
# Literal generated point-claim fixed-field bridge

This file starts the source closure for the production 3 x 29 point-claim
decoder.  The inner generated range loop is related directly to one successful
production `next_qm31` call per continuing edge.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

set_option autoImplicit false
set_option maxRecDepth 30000

namespace AspisV7Tag73GeneratedPointClaimsBridge

open V7Tag73FixedFieldGenericNamespaceR1Generated
open AspisV7Tag73AeneasExactLoopTrace
open AspisV7Tag73GeneratedReaderBridge

private theorem fixedReaderTraceAppend
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

abbrev PointClaims := Array (Array field.QM31 29#usize) 3#usize

abbrev PointInnerState :=
  core.ops.range.Range Std.Usize × v6_onefold.V6FixedFieldReader ×
    PointClaims × alloc.vec.Vec Std.U8

abbrev PointLoopOutput :=
  v6_onefold.V6FixedFieldReader × PointClaims × alloc.vec.Vec Std.U8 ×
    Option (core.result.Result PointClaims v6_transcript.V6TranscriptError)

def pointInnerBody (columns row : Std.Usize) (state : PointInnerState) :
    Result (ControlFlow PointInnerState PointLoopOutput) :=
  v6_transcript.decode_and_absorb_point_claims_loop0_loop0.body
    v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
    columns row state.1 state.2.1 state.2.2.1 state.2.2.2

def pointInnerMeasure (state : PointInnerState) : Nat :=
  state.1.end.val - state.1.start.val

theorem point_inner_body_cont_exact
    (columns row : Std.Usize) (state next : PointInnerState)
    (run : pointInnerBody columns row state = .ok (.cont next)) :
    pointInnerMeasure next + 1 = pointInnerMeasure state ∧
    ∃ value,
      v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream.next_qm31
          state.2.1 = .ok (.Ok value, next.2.1) := by
  unfold pointInnerBody at run
  unfold v6_transcript.decode_and_absorb_point_claims_loop0_loop0.body at run
  generalize rangeRun :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize state.1 =
        rangeResult at run
  cases rangeResult with
  | fail error => simp at run
  | div => simp at run
  | ok rangeOutput =>
    rcases rangeOutput with ⟨item, rangeAfter⟩
    cases item with
    | none => simp at run
    | some column =>
      have rangeSpec :=
        core.iter.range.IteratorRange.next_UScalar_spec
          (ty := .Usize) (cloneInst := core.clone.CloneUsize)
          (partialOrdInst := core.cmp.PartialOrdUsize)
          (by intro value; rfl)
          (by intro left right; rfl) state.1
      rw [rangeRun] at rangeSpec
      simp only [WP.spec_ok] at rangeSpec
      rcases rangeSpec with ⟨conditional, endExact⟩
      have startsBeforeEnd : state.1.start.val < state.1.end.val := by
        by_contra notBefore
        simp [notBefore] at conditional
      simp [startsBeforeEnd] at conditional
      rcases conditional with ⟨_, startExact⟩
      simp only [bind_tc_ok] at run
      generalize rowOffsetRun : row * columns = rowOffsetResult at run
      cases rowOffsetResult with
      | fail error => simp at run
      | div => simp at run
      | ok rowOffset =>
        simp only [bind_tc_ok] at run
        generalize ordinalRun : rowOffset + column = ordinalResult at run
        cases ordinalResult with
        | fail error => simp at run
        | div => simp at run
        | ok ordinal =>
          simp only [bind_tc_ok] at run
          generalize readRun :
              v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream.next_qm31
                state.2.1 = readResult at run
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
              simp only [core.result.Result.Insts.CoreOpsTry.branch,
                bind_tc_ok] at run
              generalize claimRowRun :
                  Array.index_mut_usize state.2.2.1 row = claimRowResult at run
              cases claimRowResult with
              | fail error => simp at run
              | div => simp at run
              | ok claimRowOutput =>
                rcases claimRowOutput with ⟨claimRow, claimRowBack⟩
                simp only [bind_tc_ok] at run
                generalize updateRun :
                    Array.update claimRow column value = updateResult at run
                cases updateResult with
                | fail error => simp at run
                | div => simp at run
                | ok claimRowAfter =>
                  simp only [bind_tc_ok] at run
                  generalize byteOffsetRun :
                      ordinal * 16#usize = byteOffsetResult at run
                  cases byteOffsetResult with
                  | fail error => simp at run
                  | div => simp at run
                  | ok byteOffset =>
                    simp only [bind_tc_ok] at run
                    generalize outerSliceRun :
                        alloc.vec.Vec.index_mut
                          (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8)
                          state.2.2.2 { start := byteOffset } =
                            outerSliceResult at run
                    cases outerSliceResult with
                    | fail error => simp at run
                    | div => simp at run
                    | ok outerSliceOutput =>
                      rcases outerSliceOutput with ⟨outerSlice, outerBack⟩
                      simp only [bind_tc_ok] at run
                      generalize innerSliceRun :
                          core.slice.index.Slice.index_mut
                            (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)
                            outerSlice { «end» := 16#usize } =
                              innerSliceResult at run
                      cases innerSliceResult with
                      | fail error => simp at run
                      | div => simp at run
                      | ok innerSliceOutput =>
                        rcases innerSliceOutput with ⟨innerSlice, innerBack⟩
                        simp only [bind_tc_ok] at run
                        generalize writeRun :
                            field.QM31.write_le_bytes value innerSlice =
                              writeResult at run
                        cases writeResult with
                        | fail error => simp at run
                        | div => simp at run
                        | ok written =>
                          simp at run
                          subst next
                          constructor
                          · unfold pointInnerMeasure
                            rw [endExact, startExact]
                            omega
                          · exact ⟨value, by simpa using readRun⟩

theorem point_inner_body_done_classification
    (columns row : Std.Usize) (state : PointInnerState)
    (output : PointLoopOutput)
    (run : pointInnerBody columns row state = .ok (.done output)) :
    (output.2.2.2 = none ∧ output.1 = state.2.1 ∧
      pointInnerMeasure state = 0) ∨
    ∃ error : v6_transcript.V6TranscriptError,
      output.2.2.2 = some (.Err error) := by
  unfold pointInnerBody at run
  unfold v6_transcript.decode_and_absorb_point_claims_loop0_loop0.body at run
  generalize rangeRun :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize state.1 =
        rangeResult at run
  cases rangeResult with
  | fail error => simp at run
  | div => simp at run
  | ok rangeOutput =>
    rcases rangeOutput with ⟨item, rangeAfter⟩
    cases item with
    | none =>
      have rangeSpec :=
        core.iter.range.IteratorRange.next_UScalar_spec
          (ty := .Usize) (cloneInst := core.clone.CloneUsize)
          (partialOrdInst := core.cmp.PartialOrdUsize)
          (by intro value; rfl)
          (by intro left right; rfl) state.1
      rw [rangeRun] at rangeSpec
      simp only [WP.spec_ok] at rangeSpec
      rcases rangeSpec with ⟨conditional, endExact⟩
      have notBefore : ¬ state.1.start.val < state.1.end.val := by
        intro startsBefore
        simp [startsBefore] at conditional
      simp at run
      subst output
      left
      refine ⟨rfl, rfl, ?_⟩
      unfold pointInnerMeasure
      omega
    | some column =>
      simp only [bind_tc_ok] at run
      generalize rowOffsetRun : row * columns = rowOffsetResult at run
      cases rowOffsetResult with
      | fail error => simp at run
      | div => simp at run
      | ok rowOffset =>
        simp only [bind_tc_ok] at run
        generalize ordinalRun : rowOffset + column = ordinalResult at run
        cases ordinalResult with
        | fail error => simp at run
        | div => simp at run
        | ok ordinal =>
          simp only [bind_tc_ok] at run
          generalize readRun :
              v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream.next_qm31
                state.2.1 = readResult at run
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
              simp only [core.result.Result.Insts.CoreOpsTry.branch,
                bind_tc_ok] at run
              generalize claimRowRun :
                  Array.index_mut_usize state.2.2.1 row = claimRowResult at run
              cases claimRowResult with
              | fail error => simp at run
              | div => simp at run
              | ok claimRowOutput =>
                rcases claimRowOutput with ⟨claimRow, claimRowBack⟩
                simp only [bind_tc_ok] at run
                generalize updateRun :
                    Array.update claimRow column value = updateResult at run
                cases updateResult with
                | fail error => simp at run
                | div => simp at run
                | ok claimRowAfter =>
                  simp only [bind_tc_ok] at run
                  generalize byteOffsetRun :
                      ordinal * 16#usize = byteOffsetResult at run
                  cases byteOffsetResult with
                  | fail error => simp at run
                  | div => simp at run
                  | ok byteOffset =>
                    simp only [bind_tc_ok] at run
                    generalize outerSliceRun :
                        alloc.vec.Vec.index_mut
                          (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8)
                          state.2.2.2 { start := byteOffset } =
                            outerSliceResult at run
                    cases outerSliceResult with
                    | fail error => simp at run
                    | div => simp at run
                    | ok outerSliceOutput =>
                      rcases outerSliceOutput with ⟨outerSlice, outerBack⟩
                      simp only [bind_tc_ok] at run
                      generalize innerSliceRun :
                          core.slice.index.Slice.index_mut
                            (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)
                            outerSlice { «end» := 16#usize } =
                              innerSliceResult at run
                      cases innerSliceResult with
                      | fail error => simp at run
                      | div => simp at run
                      | ok innerSliceOutput =>
                        rcases innerSliceOutput with ⟨innerSlice, innerBack⟩
                        simp only [bind_tc_ok] at run
                        generalize writeRun :
                            field.QM31.write_le_bytes value innerSlice =
                              writeResult at run
                        cases writeResult with
                        | fail error => simp at run
                        | div => simp at run
                        | ok written => simp at run

theorem point_inner_body_cont_decreases
    (columns row : Std.Usize) (state next : PointInnerState)
    (run : pointInnerBody columns row state = .ok (.cont next)) :
    pointInnerMeasure next < pointInnerMeasure state := by
  have exactStep := (point_inner_body_cont_exact columns row state next run).1
  omega

theorem point_inner_body_done_without_pending_exact
    (columns row : Std.Usize) (state : PointInnerState)
    (output : PointLoopOutput)
    (run : pointInnerBody columns row state = .ok (.done output))
    (noPending : output.2.2.2 = none) :
    output.1 = state.2.1 ∧ pointInnerMeasure state = 0 := by
  rcases point_inner_body_done_classification columns row state output run with
    normal | ⟨error, pendingError⟩
  · exact ⟨normal.2.1, normal.2.2⟩
  · rw [noPending] at pendingError
    simp at pendingError

theorem point_inner_loop_success_has_exact_trace
    (columns row : Std.Usize) (state : PointInnerState)
    (output : PointLoopOutput)
    (run :
      v6_transcript.decode_and_absorb_point_claims_loop0_loop0
        v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
        columns state.1 state.2.1 state.2.2.1 state.2.2.2 row =
          .ok output) :
    Nonempty (ExactLoopTrace (pointInnerBody columns row) state output) := by
  apply loop_success_has_exact_trace (pointInnerBody columns row)
    pointInnerMeasure (point_inner_body_cont_decreases columns row) state output
  exact run

theorem point_inner_trace_without_pending_has_reads
    (columns row : Std.Usize) {state : PointInnerState}
    {output : PointLoopOutput}
    (trace : ExactLoopTrace (pointInnerBody columns row) state output)
    (noPending : output.2.2.2 = none) :
    ∃ values,
      SuccessfulReadTrace
        v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream.next_qm31
        state.2.1 values output.1 ∧
      values.length = trace.contCount := by
  induction trace with
  | done equation =>
    have doneExact := point_inner_body_done_without_pending_exact
      columns row _ _ equation noPending
    rw [doneExact.1]
    exact ⟨[], .nil _, rfl⟩
  | cont equation tail inductionHypothesis =>
    obtain ⟨value, read⟩ :=
      (point_inner_body_cont_exact columns row _ _ equation).2
    obtain ⟨values, rest, lengthExact⟩ := inductionHypothesis noPending
    refine ⟨value :: values, .cons read rest, ?_⟩
    change values.length + 1 = tail.contCount + 1
    omega

theorem point_inner_trace_without_pending_cont_count
    (columns row : Std.Usize) {state : PointInnerState}
    {output : PointLoopOutput}
    (trace : ExactLoopTrace (pointInnerBody columns row) state output)
    (noPending : output.2.2.2 = none) :
    trace.contCount = pointInnerMeasure state := by
  induction trace with
  | done equation =>
    have doneExact := point_inner_body_done_without_pending_exact
      columns row _ _ equation noPending
    simp [ExactLoopTrace.contCount, doneExact.2]
  | cont equation tail inductionHypothesis =>
    have stepExact :=
      (point_inner_body_cont_exact columns row _ _ equation).1
    simp only [ExactLoopTrace.contCount]
    rw [inductionHypothesis noPending]
    omega

theorem point_inner_trace_never_returns_pending_success
    (columns row : Std.Usize) {state : PointInnerState}
    {output : PointLoopOutput}
    (trace : ExactLoopTrace (pointInnerBody columns row) state output) :
    ∀ values : PointClaims, output.2.2.2 ≠ some (.Ok values) := by
  induction trace with
  | done equation =>
    rcases point_inner_body_done_classification columns row _ _ equation with
      normal | ⟨error, pendingError⟩
    · intro values pendingSuccess
      rw [normal.1] at pendingSuccess
      simp at pendingSuccess
    · intro values pendingSuccess
      rw [pendingError] at pendingSuccess
      simp at pendingSuccess
  | cont equation tail inductionHypothesis => exact inductionHypothesis

theorem generated_point_inner_29_success_reads_exactly_29
    (row : Std.Usize) (reader readerAfter : v6_onefold.V6FixedFieldReader)
    (claims claimsAfter : PointClaims)
    (encoded encodedAfter : alloc.vec.Vec Std.U8)
    (run :
      v6_transcript.decode_and_absorb_point_claims_loop0_loop0
        v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
        29#usize { start := 0#usize, «end» := 29#usize }
        reader claims encoded row =
          .ok (readerAfter, claimsAfter, encodedAfter, none)) :
    ∃ values,
      SuccessfulFixedReaderTrace reader values readerAfter ∧
      values.length = 29 ∧
      ∀ value ∈ values, CanonicalGeneratedQM31 value := by
  let state : PointInnerState :=
    ({ start := 0#usize, «end» := 29#usize }, reader, claims, encoded)
  obtain ⟨trace⟩ := point_inner_loop_success_has_exact_trace
    29#usize row state (readerAfter, claimsAfter, encodedAfter, none) run
  obtain ⟨values, reads, lengthExact⟩ :=
    point_inner_trace_without_pending_has_reads 29#usize row trace rfl
  have fixedReads := successful_generated_read_trace_is_fixed_reader_trace reads
  refine ⟨values, fixedReads, ?_, successful_trace_values_canonical fixedReads⟩
  rw [lengthExact,
    point_inner_trace_without_pending_cont_count 29#usize row trace rfl]
  norm_num [state, pointInnerMeasure]

def pointOuterBody (state : PointInnerState) :
    Result (ControlFlow PointInnerState PointLoopOutput) :=
  v6_transcript.decode_and_absorb_point_claims_loop0.body
    v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
    29#usize state.1 state.2.1 state.2.2.1 state.2.2.2

theorem point_outer_body_cont_exact
    (state next : PointInnerState)
    (run : pointOuterBody state = .ok (.cont next)) :
    pointInnerMeasure next + 1 = pointInnerMeasure state ∧
    ∃ values,
      SuccessfulFixedReaderTrace state.2.1 values next.2.1 ∧
      values.length = 29 := by
  unfold pointOuterBody at run
  unfold v6_transcript.decode_and_absorb_point_claims_loop0.body at run
  generalize rangeRun :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize state.1 =
        rangeResult at run
  cases rangeResult with
  | fail error => simp at run
  | div => simp at run
  | ok rangeOutput =>
    rcases rangeOutput with ⟨item, rangeAfter⟩
    cases item with
    | none => simp at run
    | some row =>
      have rangeSpec :=
        core.iter.range.IteratorRange.next_UScalar_spec
          (ty := .Usize) (cloneInst := core.clone.CloneUsize)
          (partialOrdInst := core.cmp.PartialOrdUsize)
          (by intro value; rfl)
          (by intro left right; rfl) state.1
      rw [rangeRun] at rangeSpec
      simp only [WP.spec_ok] at rangeSpec
      rcases rangeSpec with ⟨conditional, endExact⟩
      have startsBeforeEnd : state.1.start.val < state.1.end.val := by
        by_contra notBefore
        simp [notBefore] at conditional
      simp [startsBeforeEnd] at conditional
      rcases conditional with ⟨_, startExact⟩
      simp only [bind_tc_ok] at run
      generalize innerRun :
          v6_transcript.decode_and_absorb_point_claims_loop0_loop0
            v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
            29#usize { start := 0#usize, «end» := 29#usize }
            state.2.1 state.2.2.1 state.2.2.2 row = innerResult at run
      cases innerResult with
      | fail error => simp at run
      | div => simp at run
      | ok innerOutput =>
        rcases innerOutput with ⟨readerAfter, claimsAfter, encodedAfter, pending⟩
        cases pending with
        | some pendingResult => simp at run
        | none =>
          have reads := generated_point_inner_29_success_reads_exactly_29
            row state.2.1 readerAfter state.2.2.1 claimsAfter
            state.2.2.2 encodedAfter innerRun
          simp at run
          subst next
          constructor
          · unfold pointInnerMeasure
            rw [endExact, startExact]
            omega
          · obtain ⟨values, fixedReads, lengthExact, canonical⟩ := reads
            exact ⟨values, fixedReads, lengthExact⟩

theorem point_outer_body_done_classification
    (state : PointInnerState) (output : PointLoopOutput)
    (run : pointOuterBody state = .ok (.done output)) :
    (output.2.2.2 = none ∧ output.1 = state.2.1 ∧
      pointInnerMeasure state = 0) ∨
    ∃ error : v6_transcript.V6TranscriptError,
      output.2.2.2 = some (.Err error) := by
  unfold pointOuterBody at run
  unfold v6_transcript.decode_and_absorb_point_claims_loop0.body at run
  generalize rangeRun :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize state.1 =
        rangeResult at run
  cases rangeResult with
  | fail error => simp at run
  | div => simp at run
  | ok rangeOutput =>
    rcases rangeOutput with ⟨item, rangeAfter⟩
    cases item with
    | none =>
      have rangeSpec :=
        core.iter.range.IteratorRange.next_UScalar_spec
          (ty := .Usize) (cloneInst := core.clone.CloneUsize)
          (partialOrdInst := core.cmp.PartialOrdUsize)
          (by intro value; rfl)
          (by intro left right; rfl) state.1
      rw [rangeRun] at rangeSpec
      simp only [WP.spec_ok] at rangeSpec
      rcases rangeSpec with ⟨conditional, endExact⟩
      have notBefore : ¬ state.1.start.val < state.1.end.val := by
        intro startsBefore
        simp [startsBefore] at conditional
      simp at run
      subst output
      left
      refine ⟨rfl, rfl, ?_⟩
      unfold pointInnerMeasure
      omega
    | some row =>
      simp only [bind_tc_ok] at run
      generalize innerRun :
          v6_transcript.decode_and_absorb_point_claims_loop0_loop0
            v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
            29#usize { start := 0#usize, «end» := 29#usize }
            state.2.1 state.2.2.1 state.2.2.2 row = innerResult at run
      cases innerResult with
      | fail error => simp at run
      | div => simp at run
      | ok innerOutput =>
        rcases innerOutput with ⟨readerAfter, claimsAfter, encodedAfter, pending⟩
        cases pending with
        | none => simp at run
        | some pendingResult =>
          cases pendingResult with
          | Err error =>
            simp at run
            subst output
            right
            exact ⟨error, rfl⟩
          | Ok pendingClaims =>
            obtain ⟨trace⟩ := point_inner_loop_success_has_exact_trace
              29#usize row
              ({ start := 0#usize, «end» := 29#usize }, state.2.1,
                state.2.2.1, state.2.2.2)
              (readerAfter, claimsAfter, encodedAfter, some (.Ok pendingClaims))
              innerRun
            exact False.elim
              (point_inner_trace_never_returns_pending_success
                29#usize row trace pendingClaims rfl)

theorem point_outer_body_cont_decreases
    (state next : PointInnerState)
    (run : pointOuterBody state = .ok (.cont next)) :
    pointInnerMeasure next < pointInnerMeasure state := by
  have exactStep := (point_outer_body_cont_exact state next run).1
  omega

theorem point_outer_body_done_without_pending_exact
    (state : PointInnerState) (output : PointLoopOutput)
    (run : pointOuterBody state = .ok (.done output))
    (noPending : output.2.2.2 = none) :
    output.1 = state.2.1 ∧ pointInnerMeasure state = 0 := by
  rcases point_outer_body_done_classification state output run with
    normal | ⟨error, pendingError⟩
  · exact ⟨normal.2.1, normal.2.2⟩
  · rw [noPending] at pendingError
    simp at pendingError

theorem point_outer_loop_success_has_exact_trace
    (state : PointInnerState) (output : PointLoopOutput)
    (run :
      v6_transcript.decode_and_absorb_point_claims_loop0
        v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
        29#usize state.1 state.2.1 state.2.2.1 state.2.2.2 = .ok output) :
    Nonempty (ExactLoopTrace pointOuterBody state output) := by
  apply loop_success_has_exact_trace pointOuterBody pointInnerMeasure
    point_outer_body_cont_decreases state output
  exact run

theorem point_outer_trace_without_pending_has_reads
    {state : PointInnerState} {output : PointLoopOutput}
    (trace : ExactLoopTrace pointOuterBody state output)
    (noPending : output.2.2.2 = none) :
    ∃ values,
      SuccessfulFixedReaderTrace state.2.1 values output.1 ∧
      values.length = 29 * trace.contCount := by
  induction trace with
  | done equation =>
    have doneExact := point_outer_body_done_without_pending_exact
      _ _ equation noPending
    rw [doneExact.1]
    exact ⟨[], .nil _, by simp [ExactLoopTrace.contCount]⟩
  | cont equation tail inductionHypothesis =>
    obtain ⟨headValues, headReads, headLength⟩ :=
      (point_outer_body_cont_exact _ _ equation).2
    obtain ⟨tailValues, tailReads, tailLength⟩ :=
      inductionHypothesis noPending
    refine ⟨headValues ++ tailValues,
      fixedReaderTraceAppend headReads tailReads, ?_⟩
    rw [List.length_append, headLength, tailLength]
    change 29 + 29 * tail.contCount = 29 * (tail.contCount + 1)
    omega

theorem point_outer_trace_without_pending_cont_count
    {state : PointInnerState} {output : PointLoopOutput}
    (trace : ExactLoopTrace pointOuterBody state output)
    (noPending : output.2.2.2 = none) :
    trace.contCount = pointInnerMeasure state := by
  induction trace with
  | done equation =>
    have doneExact := point_outer_body_done_without_pending_exact
      _ _ equation noPending
    simp [ExactLoopTrace.contCount, doneExact.2]
  | cont equation tail inductionHypothesis =>
    have stepExact := (point_outer_body_cont_exact _ _ equation).1
    simp only [ExactLoopTrace.contCount]
    rw [inductionHypothesis noPending]
    omega

theorem point_outer_trace_never_returns_pending_success
    {state : PointInnerState} {output : PointLoopOutput}
    (trace : ExactLoopTrace pointOuterBody state output) :
    ∀ values : PointClaims, output.2.2.2 ≠ some (.Ok values) := by
  induction trace with
  | done equation =>
    rcases point_outer_body_done_classification _ _ equation with
      normal | ⟨error, pendingError⟩
    · intro values pendingSuccess
      rw [normal.1] at pendingSuccess
      simp at pendingSuccess
    · intro values pendingSuccess
      rw [pendingError] at pendingSuccess
      simp at pendingSuccess
  | cont equation tail inductionHypothesis => exact inductionHypothesis

theorem generated_point_outer_success_reads_exactly_87
    (reader readerAfter : v6_onefold.V6FixedFieldReader)
    (claims claimsAfter : PointClaims)
    (encoded encodedAfter : alloc.vec.Vec Std.U8)
    (run :
      v6_transcript.decode_and_absorb_point_claims_loop0
        v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
        29#usize { start := 0#usize, «end» := 3#usize }
        reader claims encoded =
          .ok (readerAfter, claimsAfter, encodedAfter, none)) :
    ∃ values,
      SuccessfulFixedReaderTrace reader values readerAfter ∧
      values.length = 87 ∧
      ∀ value ∈ values, CanonicalGeneratedQM31 value := by
  let state : PointInnerState :=
    ({ start := 0#usize, «end» := 3#usize }, reader, claims, encoded)
  obtain ⟨trace⟩ := point_outer_loop_success_has_exact_trace
    state (readerAfter, claimsAfter, encodedAfter, none) run
  obtain ⟨values, reads, lengthExact⟩ :=
    point_outer_trace_without_pending_has_reads trace rfl
  refine ⟨values, reads, ?_, successful_trace_values_canonical reads⟩
  rw [lengthExact, point_outer_trace_without_pending_cont_count trace rfl]
  norm_num [state, pointInnerMeasure]

private theorem usizeAddExact (x y z : Std.Usize)
    (hbound : x.val + y.val ≤ Std.Usize.max)
    (hval : z.val = x.val + y.val) :
    x + y = ok z := by
  have specification := Std.Usize.add_spec (x := x) (y := y) hbound
  obtain ⟨computed, computedRun, computedVal⟩ :=
    WP.spec_imp_exists specification
  have computedExact : computed = z := by
    apply UScalar.eq_of_val_eq
    omega
  rw [computedRun, computedExact]

private theorem totalColumnsExact :
    v6_onefold.V6_TOTAL_COLUMNS = .ok 29#usize := by
  unfold v6_onefold.V6_TOTAL_COLUMNS v6_onefold.V6_C1_COLUMNS
    v6_onefold.V6_C2_COLUMNS
  apply usizeAddExact <;> scalar_tac

theorem generated_decode_and_absorb_point_claims_success_reads_exactly_87
    (transcriptBefore transcriptAfter : transcript.Transcript)
    (reader readerAfter : v6_onefold.V6FixedFieldReader)
    (claims : PointClaims)
    (run :
      v6_transcript.decode_and_absorb_point_claims
        v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
        transcriptBefore reader = .ok (.Ok claims, transcriptAfter, readerAfter)) :
    ∃ values,
      SuccessfulFixedReaderTrace reader values readerAfter ∧
      values.length = 87 ∧
      ∀ value ∈ values, CanonicalGeneratedQM31 value := by
  unfold v6_transcript.decode_and_absorb_point_claims at run
  rw [totalColumnsExact] at run
  simp only [bind_tc_ok] at run
  generalize claimsSizeRun :
      v6_onefold.V6_POINT_CLAIM_ROWS * 29#usize = claimsSizeResult at run
  cases claimsSizeResult with
  | fail error => simp at run
  | div => simp at run
  | ok claimsSize =>
    simp only [bind_tc_ok] at run
    generalize encodedSizeRun : claimsSize * 16#usize = encodedSizeResult at run
    cases encodedSizeResult with
    | fail error => simp at run
    | div => simp at run
    | ok encodedSize =>
      simp only [bind_tc_ok] at run
      generalize encodedRun :
          alloc.vec.from_elem core.clone.CloneU8 0#u8 encodedSize =
            encodedResult at run
      cases encodedResult with
      | fail error => simp at run
      | div => simp at run
      | ok encoded =>
        simp only [bind_tc_ok] at run
        generalize loopRun :
            v6_transcript.decode_and_absorb_point_claims_loop0
              v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
              29#usize
              { start := 0#usize,
                «end» := v6_onefold.V6_POINT_CLAIM_ROWS }
              reader
              (Array.repeat 3#usize (Array.repeat 29#usize field.QM31.ZERO))
              encoded = loopResult at run
        cases loopResult with
        | fail error => simp at run
        | div => simp at run
        | ok loopOutput =>
          rcases loopOutput with
            ⟨reader1, claims1, encoded1, pending⟩
          cases pending with
          | none =>
            have loopRunExact :
                v6_transcript.decode_and_absorb_point_claims_loop0
                  v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
                  29#usize { start := 0#usize, «end» := 3#usize }
                  reader
                  (Array.repeat 3#usize
                    (Array.repeat 29#usize field.QM31.ZERO)) encoded =
                    .ok (reader1, claims1, encoded1, none) := by
              simpa [v6_onefold.V6_POINT_CLAIM_ROWS] using loopRun
            have reads := generated_point_outer_success_reads_exactly_87
              reader reader1
              (Array.repeat 3#usize
                (Array.repeat 29#usize field.QM31.ZERO)) claims1
              encoded encoded1 loopRunExact
            simp only [bind_tc_ok] at run
            generalize absorbRun :
                transcript.Transcript.absorb transcriptBefore
                  transcript.label.V6_POINT_CLAIMS
                  (alloc.vec.Vec.deref encoded1) = absorbResult at run
            cases absorbResult with
            | fail error => simp at run
            | div => simp at run
            | ok transcript1 =>
              simp at run
              rw [← run.2.2]
              exact reads
          | some pendingResult =>
            cases pendingResult with
            | Err error => simp at run
            | Ok pendingClaims =>
              have loopRunExact :
                  v6_transcript.decode_and_absorb_point_claims_loop0
                    v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
                    29#usize { start := 0#usize, «end» := 3#usize }
                    reader
                    (Array.repeat 3#usize
                      (Array.repeat 29#usize field.QM31.ZERO)) encoded =
                      .ok (reader1, claims1, encoded1,
                        some (.Ok pendingClaims)) := by
                simpa [v6_onefold.V6_POINT_CLAIM_ROWS] using loopRun
              obtain ⟨trace⟩ := point_outer_loop_success_has_exact_trace
                ({ start := 0#usize, «end» := 3#usize }, reader,
                  Array.repeat 3#usize
                    (Array.repeat 29#usize field.QM31.ZERO), encoded)
                (reader1, claims1, encoded1, some (.Ok pendingClaims))
                loopRunExact
              exact False.elim
                (point_outer_trace_never_returns_pending_success
                  trace pendingClaims rfl)

#print axioms point_inner_body_cont_exact
#print axioms point_inner_body_done_classification
#print axioms point_inner_body_cont_decreases
#print axioms point_inner_loop_success_has_exact_trace
#print axioms point_inner_trace_without_pending_has_reads
#print axioms point_inner_trace_without_pending_cont_count
#print axioms point_inner_trace_never_returns_pending_success
#print axioms generated_point_inner_29_success_reads_exactly_29
#print axioms point_outer_body_cont_exact
#print axioms point_outer_body_done_classification
#print axioms point_outer_body_cont_decreases
#print axioms point_outer_loop_success_has_exact_trace
#print axioms point_outer_trace_without_pending_has_reads
#print axioms point_outer_trace_without_pending_cont_count
#print axioms point_outer_trace_never_returns_pending_success
#print axioms generated_point_outer_success_reads_exactly_87
#print axioms totalColumnsExact
#print axioms generated_decode_and_absorb_point_claims_success_reads_exactly_87

end AspisV7Tag73GeneratedPointClaimsBridge
