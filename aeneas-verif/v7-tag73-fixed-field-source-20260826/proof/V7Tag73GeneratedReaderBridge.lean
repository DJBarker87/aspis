import V7Tag73FixedFieldGenericNamespaceR1.Funs
import AeneasExactLoopTrace

/-!
# Literal generated fixed-field reader bridge

These lemmas invert the translated production `V6FixedFieldReader` operations.
They do not replace the reader with a model and take no source-agreement
premise.  The first reusable step records exactly what one successful
`next_qm31` call establishes: a nonempty input reader, a one-element remaining
count decrement, and all four returned M31 limbs strictly below the production
modulus.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

set_option autoImplicit false
set_option maxRecDepth 20000

namespace AspisV7Tag73GeneratedReaderBridge

open V7Tag73FixedFieldGenericNamespaceR1Generated
open AspisV7Tag73AeneasExactLoopTrace

private theorem usizeMulExact (x y z : Std.Usize)
    (hbound : x.val * y.val ≤ Std.Usize.max)
    (hval : z.val = x.val * y.val) :
    x * y = ok z := by
  have specification := Std.Usize.mul_spec (x := x) (y := y) hbound
  obtain ⟨computed, computedRun, computedVal⟩ :=
    WP.spec_imp_exists specification
  have computedExact : computed = z := by
    apply UScalar.eq_of_val_eq
    omega
  rw [computedRun, computedExact]

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

private theorem usizeDivExact (x y z : Std.Usize)
    (nonzero : y.val ≠ 0)
    (hval : z.val = x.val / y.val) :
    x / y = ok z := by
  obtain ⟨computed, computedRun, computedVal⟩ :=
    UScalar.div_spec x nonzero
  have computedExact : computed = z := by
    apply UScalar.eq_of_val_eq
    omega
  rw [computedRun, computedExact]

theorem next_qm31_success_remaining_and_canonical
    (before after : v6_onefold.V6FixedFieldReader)
    (value : field.QM31)
    (run : v6_onefold.V6FixedFieldReader.next_qm31 before =
      .ok (.Ok value, after)) :
    before.remaining.val > 0 ∧
      after.remaining.val + 1 = before.remaining.val ∧
      value.c0.a.val < field.P.val ∧
      value.c0.b.val < field.P.val ∧
      value.c1.a.val < field.P.val ∧
  value.c1.b.val < field.P.val := by
  unfold v6_onefold.V6FixedFieldReader.next_qm31 at run
  split at run
  · simp at run
  · generalize packedRun :
        v6_onefold.PackedM31Reader.qm31 before.packed = packedResult at run
    cases packedResult with
    | fail error => simp at run
    | div => simp at run
    | ok pair =>
      rcases pair with ⟨decoded, packedAfter⟩
      generalize subRun : before.remaining - 1#usize = subResult at run
      have subFacts := UScalar.sub_equiv before.remaining 1#usize
      rw [subRun] at subFacts
      cases subResult with
      | fail error => simp at run
      | div => simp at run
      | ok remainingAfter =>
        simp only [bind_tc_ok] at run
        split at run <;> try simp_all
        split at run <;> try simp_all
        split at run <;> try simp_all
        split at run <;> try simp_all
        rcases run with ⟨rfl, rfl⟩
        simp_all

theorem fixed_qm31_values_exact :
    v6_onefold.V6_FIXED_QM31_VALUES = ok 641#usize := by
  have mul4_6 : 4#usize * 6#usize = ok 24#usize := by
    apply usizeMulExact <;> scalar_tac
  have add26_3 : 26#usize + 3#usize = ok 29#usize := by
    apply usizeAddExact <;> scalar_tac
  have mul3_29 : 3#usize * 29#usize = ok 87#usize := by
    apply usizeMulExact <;> scalar_tac
  have mul10_27 : 10#usize * 27#usize = ok 270#usize := by
    apply usizeMulExact <;> scalar_tac
  have add0_1 : 0#usize + 1#usize = ok 1#usize := by
    apply usizeAddExact <;> scalar_tac
  have add1_270 : 1#usize + 270#usize = ok 271#usize := by
    apply usizeAddExact <;> scalar_tac
  have add271_87 : 271#usize + 87#usize = ok 358#usize := by
    apply usizeAddExact <;> scalar_tac
  have add358_1 : 358#usize + 1#usize = ok 359#usize := by
    apply usizeAddExact <;> scalar_tac
  have add359_2 : 359#usize + 2#usize = ok 361#usize := by
    apply usizeAddExact <;> scalar_tac
  have add361_24 : 361#usize + 24#usize = ok 385#usize := by
    apply usizeAddExact <;> scalar_tac
  have add385_256 : 385#usize + 256#usize = ok 641#usize := by
    apply usizeAddExact <;> scalar_tac
  simp only [v6_onefold.V6_FIXED_QM31_VALUES,
    v6_onefold.V6_FINAL_QM31_OFFSET,
    v6_onefold.V6_RELATION_QM31_OFFSET,
    v6_onefold.V6_OOD_QM31_OFFSET,
    v6_onefold.V6_INACTIVE_CLAIM_QM31_OFFSET,
    v6_onefold.V6_POINT_CLAIMS_QM31_OFFSET,
    v6_onefold.V6_SEMANTIC_QM31_OFFSET,
    v6_onefold.V6_INITIAL_CLAIM_OFFSET,
    v6_onefold.V6_SEMANTIC_ROUNDS,
    v6_onefold.V6_SEMANTIC_SENT_VALUES,
    v6_onefold.V6_POINT_CLAIM_ROWS,
    v6_onefold.V6_C1_COLUMNS,
    v6_onefold.V6_C2_COLUMNS,
    v6_onefold.V6_TOTAL_COLUMNS,
    v6_onefold.V6_RELATION_ROUNDS,
    v6_onefold.V6_RELATION_SENT_VALUES,
    v6_onefold.V6_FINAL_QM31_VALUES, mul4_6, add26_3, mul3_29,
    mul10_27, add0_1, add1_270, add271_87, add358_1, add359_2,
    add361_24, add385_256, bind_tc_ok]

theorem fixed_m31_limbs_exact :
    v6_onefold.V6_FIXED_M31_LIMBS = ok 2564#usize := by
  have mul4_641 : 4#usize * 641#usize = ok 2564#usize := by
    apply usizeMulExact <;> scalar_tac
  simp only [v6_onefold.V6_FIXED_M31_LIMBS, fixed_qm31_values_exact,
    bind_tc_ok, mul4_641]

theorem packed_bytes_2564_exact :
    v6_onefold.packed_bytes 2564#usize = ok 9936#usize := by
  have mul2564_31 : 2564#usize * 31#usize = ok 79484#usize := by
    apply usizeMulExact <;> scalar_tac
  have add79484_7 : 79484#usize + 7#usize = ok 79491#usize := by
    apply usizeAddExact <;> scalar_tac
  have div79491_8 : 79491#usize / 8#usize = ok 9936#usize := by
    apply usizeDivExact <;> scalar_tac
  unfold v6_onefold.packed_bytes
  simp only [mul2564_31, add79484_7, div79491_8, bind_tc_ok]

theorem packed_padding_success_has_exact_length
    (bytes : Slice Std.U8)
    (run : v6_onefold.validate_packed_padding bytes 2564#usize =
      .ok (.Ok ())) :
    bytes.val.length = 9936 := by
  unfold v6_onefold.validate_packed_padding at run
  rw [packed_bytes_2564_exact] at run
  by_cases exactLength : bytes.val.length = 9936
  · exact exactLength
  · simp [exactLength] at run

theorem new_success_exact_length_and_count
    (bytes : Slice Std.U8) (reader : v6_onefold.V6FixedFieldReader)
    (run : v6_onefold.V6FixedFieldReader.new bytes = .ok (.Ok reader)) :
    bytes.val.length = 9936 ∧
      reader.remaining.val = 641 ∧
      reader.packed.bytes = bytes ∧
      reader.packed.byte_index.val = 0 ∧
      reader.packed.buffer.val = 0 ∧
      reader.packed.buffered_bits.val = 0 := by
  unfold v6_onefold.V6FixedFieldReader.new at run
  simp only [fixed_m31_limbs_exact, bind_tc_ok] at run
  generalize validationRun :
      v6_onefold.validate_packed_padding bytes 2564#usize = validation at run
  cases validation with
  | fail error => simp at run
  | div => simp at run
  | ok validationResult =>
    cases validationResult with
    | Err error =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from] at run
    | Ok unit =>
      cases unit
      simp only [fixed_qm31_values_exact, bind_tc_ok] at run
      simp [v6_onefold.PackedM31Reader.new] at run
      injection run with readerExact
      injection readerExact with readerValueExact
      subst reader
      exact ⟨packed_padding_success_has_exact_length bytes validationRun,
        by norm_num, rfl, by norm_num, by norm_num, by norm_num⟩

theorem finish_success_remaining_zero
    (reader : v6_onefold.V6FixedFieldReader)
    (run : v6_onefold.V6FixedFieldReader.finish reader = .ok (.Ok ())) :
    reader.remaining.val = 0 := by
  unfold v6_onefold.V6FixedFieldReader.finish at run
  by_cases empty : reader.remaining = 0#usize
  · simpa using congrArg UScalar.val empty
  · simp [empty] at run

def CanonicalGeneratedQM31 (value : field.QM31) : Prop :=
  value.c0.a.val < field.P.val ∧
    value.c0.b.val < field.P.val ∧
    value.c1.a.val < field.P.val ∧
    value.c1.b.val < field.P.val

inductive SuccessfulFixedReaderTrace :
    v6_onefold.V6FixedFieldReader → List field.QM31 →
      v6_onefold.V6FixedFieldReader → Prop
  | nil (reader) : SuccessfulFixedReaderTrace reader [] reader
  | cons {before after final value tail}
      (read : v6_onefold.V6FixedFieldReader.next_qm31 before =
        .ok (.Ok value, after))
      (rest : SuccessfulFixedReaderTrace after tail final) :
      SuccessfulFixedReaderTrace before (value :: tail) final

theorem successful_trace_length_measure
    {first final values}
    (trace : SuccessfulFixedReaderTrace first values final) :
    final.remaining.val + values.length = first.remaining.val := by
  induction trace with
  | nil => simp
  | cons read rest inductionHypothesis =>
    obtain ⟨_, step, _⟩ :=
      next_qm31_success_remaining_and_canonical _ _ _ read
    simp only [List.length_cons]
    omega

theorem successful_trace_values_canonical
    {first final values}
    (trace : SuccessfulFixedReaderTrace first values final) :
    ∀ value ∈ values, CanonicalGeneratedQM31 value := by
  induction trace with
  | nil => simp
  | cons read rest inductionHypothesis =>
    obtain ⟨_, _, h0, h1, h2, h3⟩ :=
      next_qm31_success_remaining_and_canonical _ _ _ read
    intro candidate membership
    simp only [List.mem_cons] at membership
    rcases membership with rfl | inTail
    · exact ⟨h0, h1, h2, h3⟩
    · exact inductionHypothesis candidate inTail

theorem complete_successful_trace_has_exact_641_canonical_values
    (bytes : Slice Std.U8)
    (initial final : v6_onefold.V6FixedFieldReader)
    (values : List field.QM31)
    (newRun : v6_onefold.V6FixedFieldReader.new bytes = .ok (.Ok initial))
    (trace : SuccessfulFixedReaderTrace initial values final)
    (finishRun : v6_onefold.V6FixedFieldReader.finish final = .ok (.Ok ())) :
    bytes.val.length = 9936 ∧ values.length = 641 ∧
      (∀ value ∈ values, CanonicalGeneratedQM31 value) := by
  have initialFacts := new_success_exact_length_and_count bytes initial newRun
  have finalCount := finish_success_remaining_zero final finishRun
  have traceCount := successful_trace_length_measure trace
  exact ⟨initialFacts.1, by omega,
    successful_trace_values_canonical trace⟩

theorem successful_generated_read_trace_is_fixed_reader_trace
    {first final : v6_onefold.V6FixedFieldReader}
    {values : List field.QM31}
    (trace : SuccessfulReadTrace
      v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream.next_qm31
      first values final) :
    SuccessfulFixedReaderTrace first values final := by
  induction trace with
  | nil => exact .nil _
  | cons read rest inductionHypothesis =>
    apply SuccessfulFixedReaderTrace.cons
    · simpa [
        v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream.next_qm31]
        using read
    · exact inductionHypothesis

theorem production_root_success_exposes_exact_fixed_reader
    {TerminalCheck QueryFold : Type}
    (terminalCheckInst : core.ops.function.FnOnce TerminalCheck
      v6_transcript.V6SemanticView Bool)
    (queryFoldInst : core.ops.function.FnOnce QueryFold
      v6_transcript.V6QueryBatchView
      (core.result.Result v6_query_batch.V6AuthenticatedQueryBatch
        v6_onefold.V6WireError))
    (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
    (wire : v7_onefold.V7CompactOneFoldWire)
    (context : v6_transcript.V6TranscriptContext)
    (hidingContext : state_only_hiding.StateOnlyHidingContext)
    (inactiveRowGroups : Array Std.U8 64#usize)
    (inactiveGroupMasks : Slice Std.U16)
    (checkPow : Bool) (terminalCheck : TerminalCheck)
    (queryFold : QueryFold)
    (output : v6_transcript.V6VerifiedTranscript)
    (run :
      v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context
        terminalCheckInst queryFoldInst hash wire context hidingContext
        inactiveRowGroups inactiveGroupMasks checkPow terminalCheck queryFold =
          .ok (.Ok output)) :
    ∃ initial : v6_onefold.V6FixedFieldReader,
      v6_onefold.V6FixedFieldReader.new wire.fixed_fields_packed =
        .ok (.Ok initial) ∧
      wire.fixed_fields_packed.val.length = 9936 ∧
      initial.remaining.val = 641 := by
  unfold
    v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context
    at run
  generalize readerRun :
      v6_onefold.V6FixedFieldReader.new wire.fixed_fields_packed =
        readerResult at run
  cases readerResult with
  | fail error => simp at run
  | div => simp at run
  | ok fixedResult =>
    cases fixedResult with
    | Err error =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from,
        v6_transcript.V6TranscriptError.Insts.CoreConvertFromV6WireError.from]
        at run
    | Ok initial =>
      have initialFacts := new_success_exact_length_and_count
        wire.fixed_fields_packed initial readerRun
      exact ⟨initial, rfl, initialFacts.1, initialFacts.2.1⟩

abbrev Final256DecodeState :=
  core.ops.range.Range Std.Usize × v6_onefold.V6FixedFieldReader ×
    alloc.vec.Vec field.QM31 × alloc.vec.Vec Std.U8

def final256DecodeBody (state : Final256DecodeState) :
    Result (ControlFlow Final256DecodeState
      (v6_onefold.V6FixedFieldReader × alloc.vec.Vec field.QM31 ×
        alloc.vec.Vec Std.U8 ×
        Option (core.result.Result (Array field.QM31 256#usize)
          v6_transcript.V6TranscriptError))) :=
  v6_transcript.decode_and_absorb_final256_loop.body
    v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
    state.1 state.2.1 state.2.2.1 state.2.2.2

def final256DecodeMeasure (state : Final256DecodeState) : Nat :=
  state.1.end.val - state.1.start.val

theorem final256_decode_body_cont_measure_exact
    (state next : Final256DecodeState)
    (run : final256DecodeBody state = .ok (.cont next)) :
    final256DecodeMeasure next + 1 = final256DecodeMeasure state := by
  unfold final256DecodeBody at run
  unfold v6_transcript.decode_and_absorb_final256_loop.body at run
  generalize rangeRun :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize state.1 =
        rangeResult at run
  cases rangeResult with
  | fail error => simp at run
  | div => simp at run
  | ok rangePair =>
    rcases rangePair with ⟨item, rangeAfter⟩
    cases item with
    | none => simp at run
    | some index =>
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
      generalize readRun :
          v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream.next_qm31
            state.2.1 = readResult at run
      cases readResult with
      | fail error => simp at run
      | div => simp at run
      | ok readPair =>
        rcases readPair with ⟨fixedResult, readerAfter⟩
        cases fixedResult with
        | Err error =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            v6_transcript.V6TranscriptError.Insts.CoreConvertFromV6WireError.from]
            at run
        | Ok value =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at run
          generalize pushRun : state.2.2.1.push value = pushResult at run
          cases pushResult with
          | fail error => simp at run
          | div => simp at run
          | ok decodedAfter =>
            simp only [bind_tc_ok] at run
            generalize offsetRun : index * 16#usize = offsetResult at run
            cases offsetResult with
            | fail error => simp at run
            | div => simp at run
            | ok offset =>
              simp only [bind_tc_ok] at run
              generalize outerIndexRun :
                  alloc.vec.Vec.index_mut
                    (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8)
                    state.2.2.2 { start := offset } = outerIndexResult at run
              cases outerIndexResult with
              | fail error => simp at run
              | div => simp at run
              | ok outerPair =>
                rcases outerPair with ⟨outerSlice, outerBack⟩
                simp only [bind_tc_ok] at run
                generalize innerIndexRun :
                    core.slice.index.Slice.index_mut
                      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)
                      outerSlice { «end» := 16#usize } =
                        innerIndexResult at run
                cases innerIndexResult with
                | fail error => simp at run
                | div => simp at run
                | ok innerPair =>
                  rcases innerPair with ⟨innerSlice, innerBack⟩
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
                    unfold final256DecodeMeasure
                    rw [endExact, startExact]
                    omega

theorem final256_decode_body_cont_decreases
    (state next : Final256DecodeState)
    (run : final256DecodeBody state = .ok (.cont next)) :
    final256DecodeMeasure next < final256DecodeMeasure state := by
  have exactStep := final256_decode_body_cont_measure_exact state next run
  omega

theorem final256_loop_success_has_exact_trace
    (state : Final256DecodeState)
    (output : v6_onefold.V6FixedFieldReader × alloc.vec.Vec field.QM31 ×
      alloc.vec.Vec Std.U8 ×
      Option (core.result.Result (Array field.QM31 256#usize)
        v6_transcript.V6TranscriptError))
    (run :
      v6_transcript.decode_and_absorb_final256_loop
        v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
        state.1 state.2.1 state.2.2.1 state.2.2.2 = .ok output) :
    Nonempty (ExactLoopTrace final256DecodeBody state output) := by
  apply loop_success_has_exact_trace final256DecodeBody final256DecodeMeasure
    final256_decode_body_cont_decreases state output
  exact run

theorem final256_decode_body_cont_has_successful_read
    (state next : Final256DecodeState)
    (run : final256DecodeBody state = .ok (.cont next)) :
    ∃ value,
      v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream.next_qm31
          state.2.1 = .ok (.Ok value, next.2.1) := by
  unfold final256DecodeBody at run
  unfold v6_transcript.decode_and_absorb_final256_loop.body at run
  generalize rangeRun :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize state.1 =
        rangeResult at run
  cases rangeResult with
  | fail error => simp at run
  | div => simp at run
  | ok rangePair =>
    rcases rangePair with ⟨item, rangeAfter⟩
    cases item with
    | none => simp at run
    | some index =>
      simp only [bind_tc_ok] at run
      generalize readRun :
          v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream.next_qm31
            state.2.1 = readResult at run
      cases readResult with
      | fail error => simp at run
      | div => simp at run
      | ok readPair =>
        rcases readPair with ⟨fixedResult, readerAfter⟩
        cases fixedResult with
        | Err error =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            v6_transcript.V6TranscriptError.Insts.CoreConvertFromV6WireError.from]
            at run
        | Ok value =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at run
          generalize pushRun : state.2.2.1.push value = pushResult at run
          cases pushResult with
          | fail error => simp at run
          | div => simp at run
          | ok decodedAfter =>
            simp only [bind_tc_ok] at run
            generalize offsetRun : index * 16#usize = offsetResult at run
            cases offsetResult with
            | fail error => simp at run
            | div => simp at run
            | ok offset =>
              simp only [bind_tc_ok] at run
              generalize outerIndexRun :
                  alloc.vec.Vec.index_mut
                    (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8)
                    state.2.2.2 { start := offset } = outerIndexResult at run
              cases outerIndexResult with
              | fail error => simp at run
              | div => simp at run
              | ok outerPair =>
                rcases outerPair with ⟨outerSlice, outerBack⟩
                simp only [bind_tc_ok] at run
                generalize innerIndexRun :
                    core.slice.index.Slice.index_mut
                      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)
                      outerSlice { «end» := 16#usize } =
                        innerIndexResult at run
                cases innerIndexResult with
                | fail error => simp at run
                | div => simp at run
                | ok innerPair =>
                  rcases innerPair with ⟨innerSlice, innerBack⟩
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
                    exact ⟨value, by simpa using readRun⟩

theorem final256_decode_body_done_without_pending_exact
    (state : Final256DecodeState)
    (output : v6_onefold.V6FixedFieldReader × alloc.vec.Vec field.QM31 ×
      alloc.vec.Vec Std.U8 ×
      Option (core.result.Result (Array field.QM31 256#usize)
        v6_transcript.V6TranscriptError))
    (run : final256DecodeBody state = .ok (.done output))
    (noPending : output.2.2.2 = none) :
    output.1 = state.2.1 ∧ final256DecodeMeasure state = 0 := by
  unfold final256DecodeBody at run
  unfold v6_transcript.decode_and_absorb_final256_loop.body at run
  generalize rangeRun :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize state.1 =
        rangeResult at run
  cases rangeResult with
  | fail error => simp at run
  | div => simp at run
  | ok rangePair =>
    rcases rangePair with ⟨item, rangeAfter⟩
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
      constructor
      · rfl
      · unfold final256DecodeMeasure
        omega
    | some index =>
      simp only [bind_tc_ok] at run
      generalize readRun :
          v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream.next_qm31
            state.2.1 = readResult at run
      cases readResult with
      | fail error => simp at run
      | div => simp at run
      | ok readPair =>
        rcases readPair with ⟨fixedResult, readerAfter⟩
        cases fixedResult with
        | Err error =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            v6_transcript.V6TranscriptError.Insts.CoreConvertFromV6WireError.from]
            at run
          subst output
          simp at noPending
        | Ok value =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at run
          generalize pushRun : state.2.2.1.push value = pushResult at run
          cases pushResult with
          | fail error => simp at run
          | div => simp at run
          | ok decodedAfter =>
            simp only [bind_tc_ok] at run
            generalize offsetRun : index * 16#usize = offsetResult at run
            cases offsetResult with
            | fail error => simp at run
            | div => simp at run
            | ok offset =>
              simp only [bind_tc_ok] at run
              generalize outerIndexRun :
                  alloc.vec.Vec.index_mut
                    (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8)
                    state.2.2.2 { start := offset } = outerIndexResult at run
              cases outerIndexResult with
              | fail error => simp at run
              | div => simp at run
              | ok outerPair =>
                rcases outerPair with ⟨outerSlice, outerBack⟩
                simp only [bind_tc_ok] at run
                generalize innerIndexRun :
                    core.slice.index.Slice.index_mut
                      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)
                      outerSlice { «end» := 16#usize } =
                        innerIndexResult at run
                cases innerIndexResult with
                | fail error => simp at run
                | div => simp at run
                | ok innerPair =>
                  rcases innerPair with ⟨innerSlice, innerBack⟩
                  simp only [bind_tc_ok] at run
                  generalize writeRun :
                      field.QM31.write_le_bytes value innerSlice =
                        writeResult at run
                  cases writeResult with
                  | fail error => simp at run
                  | div => simp at run
                  | ok written => simp at run

theorem final256_exact_loop_trace_without_pending_has_successful_reads
    {state : Final256DecodeState}
    {output : v6_onefold.V6FixedFieldReader × alloc.vec.Vec field.QM31 ×
      alloc.vec.Vec Std.U8 ×
      Option (core.result.Result (Array field.QM31 256#usize)
        v6_transcript.V6TranscriptError)}
    (trace : ExactLoopTrace final256DecodeBody state output)
    (noPending : output.2.2.2 = none) :
    ∃ values,
      SuccessfulReadTrace
        v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream.next_qm31
        state.2.1 values output.1 ∧
      values.length = trace.contCount := by
  induction trace with
  | done equation =>
    have doneExact :=
      final256_decode_body_done_without_pending_exact
        _ _ equation noPending
    rw [doneExact.1]
    exact ⟨[], .nil _, rfl⟩
  | cont equation tail inductionHypothesis =>
    obtain ⟨value, read⟩ :=
      final256_decode_body_cont_has_successful_read _ _ equation
    obtain ⟨values, rest, lengthExact⟩ := inductionHypothesis noPending
    refine ⟨value :: values, .cons read rest, ?_⟩
    change values.length + 1 = tail.contCount + 1
    omega

theorem final256_exact_loop_trace_without_pending_cont_count
    {state : Final256DecodeState}
    {output : v6_onefold.V6FixedFieldReader × alloc.vec.Vec field.QM31 ×
      alloc.vec.Vec Std.U8 ×
      Option (core.result.Result (Array field.QM31 256#usize)
        v6_transcript.V6TranscriptError)}
    (trace : ExactLoopTrace final256DecodeBody state output)
    (noPending : output.2.2.2 = none) :
    trace.contCount = final256DecodeMeasure state := by
  induction trace with
  | done equation =>
    have doneExact :=
      final256_decode_body_done_without_pending_exact
        _ _ equation noPending
    simp [ExactLoopTrace.contCount, doneExact.2]
  | cont equation tail inductionHypothesis =>
    have stepExact :=
      final256_decode_body_cont_measure_exact _ _ equation
    simp only [ExactLoopTrace.contCount]
    rw [inductionHypothesis noPending]
    omega

theorem final256_loop_success_without_pending_has_successful_reads
    (state : Final256DecodeState)
    (output : v6_onefold.V6FixedFieldReader × alloc.vec.Vec field.QM31 ×
      alloc.vec.Vec Std.U8 ×
      Option (core.result.Result (Array field.QM31 256#usize)
        v6_transcript.V6TranscriptError))
    (run :
      v6_transcript.decode_and_absorb_final256_loop
        v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
        state.1 state.2.1 state.2.2.1 state.2.2.2 = .ok output)
    (noPending : output.2.2.2 = none) :
    ∃ values,
      SuccessfulReadTrace
        v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream.next_qm31
        state.2.1 values output.1 ∧
      values.length = final256DecodeMeasure state := by
  obtain ⟨trace⟩ := final256_loop_success_has_exact_trace state output run
  obtain ⟨values, reads, lengthExact⟩ :=
    final256_exact_loop_trace_without_pending_has_successful_reads
      trace noPending
  refine ⟨values, reads, ?_⟩
  rw [lengthExact,
    final256_exact_loop_trace_without_pending_cont_count trace noPending]

theorem generated_final256_success_reads_exactly_256_canonical_values
    (reader : v6_onefold.V6FixedFieldReader)
    (decoded : alloc.vec.Vec field.QM31)
    (encoded : alloc.vec.Vec Std.U8)
    (output : v6_onefold.V6FixedFieldReader × alloc.vec.Vec field.QM31 ×
      alloc.vec.Vec Std.U8 ×
      Option (core.result.Result (Array field.QM31 256#usize)
        v6_transcript.V6TranscriptError))
    (run :
      v6_transcript.decode_and_absorb_final256_loop
        v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
        { start := 0#usize, «end» := v6_onefold.V6_FINAL_QM31_VALUES }
        reader decoded encoded = .ok output)
    (noPending : output.2.2.2 = none) :
    ∃ values,
      SuccessfulFixedReaderTrace reader values output.1 ∧
      values.length = 256 ∧
      ∀ value ∈ values, CanonicalGeneratedQM31 value := by
  let state : Final256DecodeState :=
    ({ start := 0#usize, «end» := v6_onefold.V6_FINAL_QM31_VALUES },
      reader, decoded, encoded)
  obtain ⟨values, reads, lengthExact⟩ :=
    final256_loop_success_without_pending_has_successful_reads
      state output run noPending
  have fixedReads := successful_generated_read_trace_is_fixed_reader_trace reads
  refine ⟨values, fixedReads, ?_, successful_trace_values_canonical fixedReads⟩
  simpa [state, final256DecodeMeasure, v6_onefold.V6_FINAL_QM31_VALUES]
    using lengthExact

#print axioms next_qm31_success_remaining_and_canonical
#print axioms fixed_qm31_values_exact
#print axioms fixed_m31_limbs_exact
#print axioms packed_bytes_2564_exact
#print axioms packed_padding_success_has_exact_length
#print axioms new_success_exact_length_and_count
#print axioms finish_success_remaining_zero
#print axioms successful_trace_length_measure
#print axioms successful_trace_values_canonical
#print axioms complete_successful_trace_has_exact_641_canonical_values
#print axioms successful_generated_read_trace_is_fixed_reader_trace
#print axioms production_root_success_exposes_exact_fixed_reader
#print axioms final256_decode_body_cont_measure_exact
#print axioms final256_decode_body_cont_decreases
#print axioms final256_loop_success_has_exact_trace
#print axioms final256_decode_body_cont_has_successful_read
#print axioms final256_decode_body_done_without_pending_exact
#print axioms final256_exact_loop_trace_without_pending_has_successful_reads
#print axioms final256_exact_loop_trace_without_pending_cont_count
#print axioms final256_loop_success_without_pending_has_successful_reads
#print axioms generated_final256_success_reads_exactly_256_canonical_values
#print axioms final256_decode_body_cont_decreases

end AspisV7Tag73GeneratedReaderBridge
