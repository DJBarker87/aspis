import V7Tag73GeneratedProductionRootBridge
import V7Tag73FixedFieldLayoutModel

/-!
# Generated packed-reader bit bridge

This file connects the generated reader's source slice to the pure frozen
9,936-byte packed-section model.  It first exposes the literal parser-padding
success hidden inside `V6FixedFieldReader.new`, then proves the exact last-byte
high-nibble condition.  The subsequent reader-state invariant connects every
generated low-31-bit read to `packedLimbNat`.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

set_option autoImplicit false
set_option maxRecDepth 20000

namespace AspisV7Tag73GeneratedPackedReaderBridge

open V7Tag73FixedFieldGenericNamespaceR1Generated
open AspisV7Tag73GeneratedReaderBridge
open AspisV7Tag73GeneratedProductionRootBridge
open AspisV7Tag73FixedFieldLayoutModel
open AspisV5ComponentCRejectionSampler

private theorem usizeMulExact (x y z : Std.Usize)
    (hbound : x.val * y.val ≤ Std.Usize.max)
    (hval : z.val = x.val * y.val) :
    x * y = Aeneas.Std.Result.ok z := by
  have specification := Std.Usize.mul_spec (x := x) (y := y) hbound
  obtain ⟨computed, computedRun, computedVal⟩ :=
    WP.spec_imp_exists specification
  have computedExact : computed = z := by
    apply UScalar.eq_of_val_eq
    omega
  rw [computedRun, computedExact]

private theorem usizeRemExact (x y z : Std.Usize)
    (nonzero : y.val ≠ 0) (hval : z.val = x.val % y.val) :
    x % y = Aeneas.Std.Result.ok z := by
  obtain ⟨computed, computedRun, computedVal⟩ :=
    WP.spec_imp_exists (UScalar.rem_spec x nonzero)
  have computedExact : computed = z := by
    apply UScalar.eq_of_val_eq
    omega
  rw [computedRun, computedExact]

def packedSectionOfSlice (bytes : Slice Std.U8)
    (lengthExact : bytes.val.length = 9936) : PackedFixedSection :=
  fun index =>
    ⟨(bytes.val[index.val]'(by simpa [lengthExact] using index.isLt)).val,
      by scalar_tac⟩

@[simp] theorem packedSectionOfSlice_val
    (bytes : Slice Std.U8) (lengthExact : bytes.val.length = 9936)
    (index : Fin 9936) :
    ((packedSectionOfSlice bytes lengthExact index : Fin 256) : Nat) =
      (bytes.val[index.val]'(by simpa [lengthExact] using index.isLt)).val := by
  rfl

theorem new_success_exposes_padding_validation
    (bytes : Slice Std.U8) (reader : v6_onefold.V6FixedFieldReader)
    (run : v6_onefold.V6FixedFieldReader.new bytes = .ok (.Ok reader)) :
    v6_onefold.validate_packed_padding bytes 2564#usize = .ok (.Ok ()) := by
  unfold v6_onefold.V6FixedFieldReader.new at run
  simp only [fixed_m31_limbs_exact, bind_tc_ok] at run
  generalize validationRun :
      v6_onefold.validate_packed_padding bytes 2564#usize = validation at run
  cases validation with
  | fail error => simp at run
  | div => simp at run
  | ok validationOutcome =>
    cases validationOutcome with
    | Err wireError =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from] at run
    | Ok unit =>
      cases unit
      rfl

private theorem bitvec8_high_nibble_zero_implies_lt_16 :
    ∀ candidate : BitVec 8,
      candidate &&& (240 : BitVec 8) = 0 → candidate.toNat < 16 := by
  intro candidate highZero
  have bound : candidate.toNat < 256 := by
    simpa using candidate.isLt
  have reconstruct : candidate = BitVec.ofNat 8 candidate.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp
  rw [reconstruct] at highZero
  interval_cases h : candidate.toNat
  all_goals first | omega | (exfalso; revert highZero; bv_decide)

private theorem u8_high_nibble_zero_implies_lt_16
    (value : Std.U8) (highZero : (value &&& 240#u8).val = 0) :
    value.val < 16 := by
  have highZeroBits : value.bv &&& (240#u8).bv = 0 := by
    apply BitVec.eq_of_toNat_eq
    simpa using highZero
  simpa using bitvec8_high_nibble_zero_implies_lt_16 value.bv highZeroBits

theorem padding_validation_success_last_byte_lt_16
    (bytes : Slice Std.U8)
    (run : v6_onefold.validate_packed_padding bytes 2564#usize =
      .ok (.Ok ())) :
    ∃ lengthExact : bytes.val.length = 9936,
      (packedSectionOfSlice bytes lengthExact
        ⟨9935, by norm_num⟩ : Nat) < 16 := by
  have lengthExact := packed_padding_success_has_exact_length bytes run
  unfold v6_onefold.validate_packed_padding at run
  rw [packed_bytes_2564_exact] at run
  have mulExact : 2564#usize * 31#usize =
      Aeneas.Std.Result.ok 79484#usize := by
    apply usizeMulExact <;> scalar_tac
  have modExact : 79484#usize % 8#usize =
      Aeneas.Std.Result.ok 4#usize := by
    apply usizeRemExact <;> scalar_tac
  have lastExact : core.slice.Slice.last bytes =
      .ok (some (bytes.val[9935]'(by omega))) := by
    unfold core.slice.Slice.last
    rw [List.getLast?_eq_getElem?]
    simp [lengthExact]
  rw [mulExact] at run
  simp only [bind_tc_ok] at run
  rw [modExact] at run
  simp only [bind_tc_ok] at run
  have lenScalar : Slice.len bytes = 9936#usize := by
    apply UScalar.eq_of_val_eq
    exact lengthExact
  rw [lenScalar] at run
  have wrongLengthFalse :
      (9936#usize != 9936#usize) = false := by decide
  rw [wrongLengthFalse] at run
  simp only [Bool.false_eq_true, if_false] at run
  have usedBitsNonzero :
      (4#usize != 0#usize) = true := by decide
  rw [usedBitsNonzero] at run
  simp only [if_true] at run
  obtain ⟨shifted, shiftRun, shiftSpec⟩ := WP.spec_imp_exists
    (Std.U8.ShiftLeft_spec 1#u8 4#usize (by norm_num))
  have shiftedExact : shifted = 16#u8 := by
    apply UScalar.eq_of_val_eq
    rw [shiftSpec.1]
    norm_num [Nat.shiftLeft_eq, Std.U8.size, Std.U8.numBits,
      UScalarTy.U8_numBits_eq]
  rw [shiftRun, shiftedExact] at run
  simp only [bind_tc_ok] at run
  obtain ⟨subtracted, subRun, subSpec⟩ := WP.spec_imp_exists
    (UScalar.sub_spec (x := 16#u8) (y := 1#u8) (by norm_num))
  have subtractedExact : subtracted = 15#u8 := by
    apply UScalar.eq_of_val_eq
    rw [subSpec.1]
    norm_num
  rw [subRun, subtractedExact] at run
  simp only [bind_tc_ok] at run
  rw [lastExact] at run
  have maskExact : (~~~15#u8) = 240#u8 := by
    apply UScalar.eq_of_val_eq
    decide
  rw [maskExact] at run
  simp [lengthExact, lift,
    core.option.OptionShared0T.copied,
    core.option.Option.unwrap_or_default] at run
  have highZero :
      (bytes.val[9935]'(by omega) &&& 240#u8).val = 0 := by
    change HAnd.hAnd ((bytes.val[9935]'(by omega)).val : Nat)
      (240 : Nat) = (0 : Nat)
    exact run
  refine ⟨lengthExact, ?_⟩
  change (bytes.val[9935]'(by omega)).val < 16
  exact u8_high_nibble_zero_implies_lt_16 _ highZero

theorem new_success_packed_section_padding_zero
    (bytes : Slice Std.U8) (reader : v6_onefold.V6FixedFieldReader)
    (run : v6_onefold.V6FixedFieldReader.new bytes = .ok (.Ok reader)) :
    ∃ lengthExact : bytes.val.length = 9936,
      PackedFixedPaddingZero (packedSectionOfSlice bytes lengthExact) := by
  exact padding_validation_success_last_byte_lt_16 bytes
    (new_success_exposes_padding_validation bytes reader run)

/-! ## Literal refill-loop state movement -/

private theorem next_loop_body_cont_index_and_bits
    (bytes : Slice Std.U8) (byteIndex : Std.Usize)
    (buffer : Std.U64) (bufferedBits : Std.U8)
    (next : Std.Usize × Std.U64 × Std.U8)
    (run : v6_onefold.PackedM31Reader.next_loop.body bytes byteIndex buffer
      bufferedBits = .ok (.cont next)) :
    bufferedBits.val < 31 ∧
      next.1.val = byteIndex.val + 1 ∧
      next.2.2.val = bufferedBits.val + 8 := by
  unfold v6_onefold.PackedM31Reader.next_loop.body at run
  split at run
  · rename_i active
    rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
    rcases run with ⟨_, _, run⟩
    rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
    rcases run with ⟨_, _, run⟩
    rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
    rcases run with ⟨_, _, run⟩
    rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
    rcases run with ⟨_, _, run⟩
    rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
    rcases run with ⟨_, _, run⟩
    rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
    rcases run with ⟨nextIndex, nextIndexRun, run⟩
    rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
    rcases run with ⟨nextBits, nextBitsRun, run⟩
    injection run with nextExact
    injection nextExact with nextTupleExact
    subst next
    have indexFacts := @UScalar.add_equiv .Usize byteIndex 1#usize
    rw [nextIndexRun] at indexFacts
    have bitsFacts := @UScalar.add_equiv .U8 bufferedBits 8#u8
    rw [nextBitsRun] at bitsFacts
    exact ⟨active, indexFacts.2.1, bitsFacts.2.1⟩
  · simp at run

private theorem slice_index_usize_exact
    (bytes : Slice Std.U8) (index : Std.Usize)
    (bound : index.val < bytes.val.length) :
    Slice.index_usize bytes index = .ok bytes.val[index.val] := by
  have specification := Slice.index_usize_spec bytes index (by simpa using bound)
  cases run : Slice.index_usize bytes index with
  | fail error => simp [run] at specification
  | div => simp [run] at specification
  | ok value =>
      simp [run] at specification
      simpa [run, specification]

private theorem next_loop_body_cont_exact_buffer
    (bytes : Slice Std.U8) (byteIndex : Std.Usize)
    (buffer : Std.U64) (bufferedBits : Std.U8)
    (next : Std.Usize × Std.U64 × Std.U8)
    (run : v6_onefold.PackedM31Reader.next_loop.body bytes byteIndex buffer
      bufferedBits = .ok (.cont next)) :
    ∃ bound : byteIndex.val < bytes.val.length,
      next.2.1.bv = buffer.bv |||
        (bytes.val[byteIndex.val]'bound).bv.setWidth 64 <<<
          bufferedBits.val := by
  unfold v6_onefold.PackedM31Reader.next_loop.body at run
  split at run
  · rename_i active
    rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
    rcases run with ⟨_, assertRun, run⟩
    have bound : byteIndex.val < bytes.val.length := by
      simp [massert] at assertRun
      exact assertRun
    rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
    rcases run with ⟨sourceByte, sourceByteRun, run⟩
    have sourceByteExact : sourceByte = bytes.val[byteIndex.val] := by
      exact Result.ok.inj (sourceByteRun.symm.trans
        (slice_index_usize_exact bytes byteIndex bound))
    subst sourceByte
    rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
    rcases run with ⟨wideByte, wideByteRun, run⟩
    have wideByteExact :
        wideByte = core.convert.num.FromU64U8.from bytes.val[byteIndex.val] := by
      simpa [lift] using wideByteRun.symm
    subst wideByte
    rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
    rcases run with ⟨shiftedByte, shiftedByteRun, run⟩
    have shiftedFacts := Std.U64.ShiftLeft_spec
      (core.convert.num.FromU64U8.from bytes.val[byteIndex.val])
      bufferedBits (by scalar_tac)
    rw [shiftedByteRun] at shiftedFacts
    simp at shiftedFacts
    rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
    rcases run with ⟨combined, combinedRun, run⟩
    have combinedExact : combined = buffer ||| shiftedByte := by
      simpa [lift] using combinedRun.symm
    subst combined
    rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
    rcases run with ⟨nextIndex, _, run⟩
    rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
    rcases run with ⟨nextBits, _, run⟩
    injection run with flowExact
    injection flowExact with nextExact
    subst next
    refine ⟨bound, ?_⟩
    · calc
        (buffer ||| shiftedByte).bv =
            buffer.bv ||| shiftedByte.bv := rfl
        _ = buffer.bv |||
            ((bytes.val[byteIndex.val]'bound).bv.setWidth 64 <<<
              bufferedBits.val) := by
          rw [shiftedFacts.2]
  · simp at run

private theorem next_loop_body_done_index_and_bits
    (bytes : Slice Std.U8) (byteIndex : Std.Usize)
    (buffer : Std.U64) (bufferedBits : Std.U8)
    (output : Std.Usize × Std.U64 × Std.U8)
    (run : v6_onefold.PackedM31Reader.next_loop.body bytes byteIndex buffer
      bufferedBits = .ok (.done output)) :
    31 ≤ bufferedBits.val ∧ output = (byteIndex, buffer, bufferedBits) := by
  unfold v6_onefold.PackedM31Reader.next_loop.body at run
  split at run
  · rename_i active
    rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
    rcases run with ⟨_, _, run⟩
    rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
    rcases run with ⟨_, _, run⟩
    rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
    rcases run with ⟨_, _, run⟩
    rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
    rcases run with ⟨_, _, run⟩
    rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
    rcases run with ⟨_, _, run⟩
    rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
    rcases run with ⟨_, _, run⟩
    rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
    rcases run with ⟨_, _, run⟩
    simp at run
  · rename_i inactive
    constructor
    · scalar_tac
    · exact (ControlFlow.done.inj (Result.ok.inj run)).symm

private def packedRefillMeasure
    (state : Std.Usize × Std.U64 × Std.U8) : Nat :=
  4 - state.2.2.val / 8

private theorem next_loop_body_cont_decreases
    (bytes : Slice Std.U8)
    (state next : Std.Usize × Std.U64 × Std.U8)
    (run : v6_onefold.PackedM31Reader.next_loop.body bytes state.1 state.2.1
      state.2.2 = .ok (.cont next)) :
    packedRefillMeasure next < packedRefillMeasure state := by
  obtain ⟨active, _, bitsStep⟩ :=
    next_loop_body_cont_index_and_bits bytes state.1 state.2.1 state.2.2 next run
  unfold packedRefillMeasure
  have quotientStep : next.2.2.val / 8 = state.2.2.val / 8 + 1 := by
    omega
  rw [quotientStep]
  omega

private theorem next_loop_success_has_exact_trace
    (bytes : Slice Std.U8) (byteIndex : Std.Usize)
    (buffer : Std.U64) (bufferedBits : Std.U8)
    (output : Std.Usize × Std.U64 × Std.U8)
    (run : v6_onefold.PackedM31Reader.next_loop bytes byteIndex buffer
      bufferedBits = .ok output) :
    Nonempty (AspisV7Tag73AeneasExactLoopTrace.ExactLoopTrace
      (fun state => v6_onefold.PackedM31Reader.next_loop.body bytes
        state.1 state.2.1 state.2.2)
      (byteIndex, buffer, bufferedBits) output) := by
  unfold v6_onefold.PackedM31Reader.next_loop at run
  exact AspisV7Tag73AeneasExactLoopTrace.loop_success_has_exact_trace
    (fun state => v6_onefold.PackedM31Reader.next_loop.body bytes
      state.1 state.2.1 state.2.2)
    packedRefillMeasure
    (next_loop_body_cont_decreases bytes)
    (byteIndex, buffer, bufferedBits) output run

private theorem refill_trace_exact_index_and_bits
    (bytes : Slice Std.U8)
    {state output : Std.Usize × Std.U64 × Std.U8}
    (trace : AspisV7Tag73AeneasExactLoopTrace.ExactLoopTrace
      (fun current => v6_onefold.PackedM31Reader.next_loop.body bytes
        current.1 current.2.1 current.2.2) state output) :
    output.1.val = state.1.val + trace.contCount ∧
      output.2.2.val = state.2.2.val + 8 * trace.contCount ∧
      31 ≤ output.2.2.val := by
  induction trace with
  | @done current final equation =>
      obtain ⟨threshold, outputExact⟩ :=
        next_loop_body_done_index_and_bits bytes current.1 current.2.1
          current.2.2 final equation
      subst final
      exact ⟨by simp [AspisV7Tag73AeneasExactLoopTrace.ExactLoopTrace.contCount],
        by simp [AspisV7Tag73AeneasExactLoopTrace.ExactLoopTrace.contCount],
        threshold⟩
  | @cont current next final equation tail inductionHypothesis =>
      obtain ⟨_, indexStep, bitsStep⟩ :=
        next_loop_body_cont_index_and_bits bytes current.1 current.2.1
          current.2.2 next equation
      rcases inductionHypothesis with ⟨finalIndex, finalBits, threshold⟩
      simp only [AspisV7Tag73AeneasExactLoopTrace.ExactLoopTrace.contCount]
      omega

private def sourceByteBv (bytes : Slice Std.U8) (index : Nat) : BitVec 64 :=
  if bound : index < bytes.val.length then
    (bytes.val[index]'bound).bv.setWidth 64
  else 0

private def refillBufferBv (bytes : Slice Std.U8) :
    Nat → BitVec 64 → Nat → Nat → BitVec 64
  | _, buffer, _, 0 => buffer
  | index, buffer, bits, count + 1 =>
      refillBufferBv bytes (index + 1)
        (buffer ||| (sourceByteBv bytes index <<< bits))
        (bits + 8) count

private theorem refill_trace_exact_buffer
    (bytes : Slice Std.U8)
    {state output : Std.Usize × Std.U64 × Std.U8}
    (trace : AspisV7Tag73AeneasExactLoopTrace.ExactLoopTrace
      (fun current => v6_onefold.PackedM31Reader.next_loop.body bytes
        current.1 current.2.1 current.2.2) state output) :
    output.2.1.bv = refillBufferBv bytes state.1.val state.2.1.bv
      state.2.2.val trace.contCount := by
  induction trace with
  | @done current final equation =>
      obtain ⟨_, outputExact⟩ :=
        next_loop_body_done_index_and_bits bytes current.1 current.2.1
          current.2.2 final equation
      subst final
      rfl
  | @cont current next final equation tail inductionHypothesis =>
      obtain ⟨indexStep, bitsStep⟩ :=
        (next_loop_body_cont_index_and_bits bytes current.1 current.2.1
          current.2.2 next equation).2
      obtain ⟨bound, bufferStep⟩ :=
        next_loop_body_cont_exact_buffer bytes current.1 current.2.1
          current.2.2 next equation
      simp only [AspisV7Tag73AeneasExactLoopTrace.ExactLoopTrace.contCount,
        refillBufferBv]
      rw [indexStep, bufferStep, bitsStep] at inductionHypothesis
      simpa [sourceByteBv, bound] using inductionHypothesis

private theorem refill_trace_last_input_below_threshold
    (bytes : Slice Std.U8)
    {state output : Std.Usize × Std.U64 × Std.U8}
    (trace : AspisV7Tag73AeneasExactLoopTrace.ExactLoopTrace
      (fun current => v6_onefold.PackedM31Reader.next_loop.body bytes
        current.1 current.2.1 current.2.2) state output) :
    trace.contCount = 0 ∨
      state.2.2.val + 8 * (trace.contCount - 1) < 31 := by
  induction trace with
  | @done current final equation =>
      exact Or.inl rfl
  | @cont current next final equation tail inductionHypothesis =>
      obtain ⟨active, _, bitsStep⟩ :=
        next_loop_body_cont_index_and_bits bytes current.1 current.2.1
          current.2.2 next equation
      simp only [AspisV7Tag73AeneasExactLoopTrace.ExactLoopTrace.contCount]
      rcases inductionHypothesis with tailEmpty | tailLast
      · right
        omega
      · right
        omega

private theorem refill_trace_count_from_low_buffer
    (bytes : Slice Std.U8)
    {state output : Std.Usize × Std.U64 × Std.U8}
    (lowBuffer : state.2.2.val < 8)
    (trace : AspisV7Tag73AeneasExactLoopTrace.ExactLoopTrace
      (fun current => v6_onefold.PackedM31Reader.next_loop.body bytes
        current.1 current.2.1 current.2.2) state output) :
    trace.contCount = if state.2.2.val = 7 then 3 else 4 := by
  obtain ⟨_, finalBits, threshold⟩ :=
    refill_trace_exact_index_and_bits bytes trace
  have lastInput := refill_trace_last_input_below_threshold bytes trace
  split
  · rename_i seven
    omega
  · rename_i notSeven
    omega

theorem packed_next_success_exposes_exact_refill
    (before after : v6_onefold.PackedM31Reader) (value : Std.U32)
    (run : v6_onefold.PackedM31Reader.next before = .ok (value, after)) :
    ∃ refillIndex : Std.Usize, ∃ refillBuffer : Std.U64,
      ∃ refillBits : Std.U8,
      v6_onefold.PackedM31Reader.next_loop before.bytes before.byte_index
          before.buffer before.buffered_bits =
        .ok (refillIndex, refillBuffer, refillBits) ∧
      Nonempty (AspisV7Tag73AeneasExactLoopTrace.ExactLoopTrace
        (fun state => v6_onefold.PackedM31Reader.next_loop.body before.bytes
          state.1 state.2.1 state.2.2)
        (before.byte_index, before.buffer, before.buffered_bits)
        (refillIndex, refillBuffer, refillBits)) ∧
      value.val = (refillBuffer &&& 2147483647#u64).val ∧
      after.bytes = before.bytes ∧
      after.byte_index = refillIndex ∧
      after.buffer.bv = refillBuffer.bv >>> 31 ∧
      after.buffered_bits.val + 31 = refillBits.val := by
  unfold v6_onefold.PackedM31Reader.next at run
  rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
  rcases run with ⟨refill, refillRun, run⟩
  rcases refill with ⟨refillIndex, refillBuffer, refillBits⟩
  rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
  rcases run with ⟨masked, maskedRun, run⟩
  have maskedExact : masked = refillBuffer &&& 2147483647#u64 := by
    simpa [lift] using maskedRun.symm
  subst masked
  rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
  rcases run with ⟨castValue, castRun, run⟩
  have maskedBound :
      (refillBuffer &&& 2147483647#u64).val ≤
        UScalar.max .U32 := by
    calc
      (refillBuffer &&& 2147483647#u64).val ≤
          (2147483647#u64).val := by
        change refillBuffer.val &&& 2147483647 ≤ 2147483647
        exact Nat.and_le_right
      _ ≤ UScalar.max .U32 := by scalar_tac
  have castFacts := UScalar.cast_inBounds_spec .U32
    (refillBuffer &&& 2147483647#u64) maskedBound
  rw [castRun] at castFacts
  simp at castFacts
  rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
  rcases run with ⟨shiftedBuffer, shiftedBufferRun, run⟩
  have shiftedFacts := Std.U64.ShiftRight_IScalar_spec refillBuffer 31#i32
    (by norm_num) (by norm_num)
  rw [shiftedBufferRun] at shiftedFacts
  simp at shiftedFacts
  rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
  rcases run with ⟨remainingBits, remainingBitsRun, run⟩
  have remainingBitsFacts := @UScalar.sub_equiv .U8 refillBits 31#u8
  rw [remainingBitsRun] at remainingBitsFacts
  injection run with outputExact
  injection outputExact with valueExact afterExact
  subst value
  subst after
  refine ⟨refillIndex, refillBuffer, refillBits, refillRun,
    next_loop_success_has_exact_trace before.bytes before.byte_index
      before.buffer before.buffered_bits
      (refillIndex, refillBuffer, refillBits) refillRun,
    castFacts, rfl, rfl, shiftedFacts.2, ?_⟩
  exact remainingBitsFacts.2.1.symm

theorem packed_next_success_preserves_bytes
    (before after : v6_onefold.PackedM31Reader) (value : Std.U32)
    (run : v6_onefold.PackedM31Reader.next before = .ok (value, after)) :
    after.bytes = before.bytes := by
  unfold v6_onefold.PackedM31Reader.next at run
  rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
  rcases run with ⟨_, _, run⟩
  rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
  rcases run with ⟨_, _, run⟩
  rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
  rcases run with ⟨_, _, run⟩
  rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
  rcases run with ⟨_, _, run⟩
  rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
  rcases run with ⟨_, _, run⟩
  injection run with outputExact
  injection outputExact with _ afterExact
  subst after
  rfl

def GeneratedPackedReaderGeometryAt
    (reader : v6_onefold.PackedM31Reader) (ordinal : Nat) : Prop :=
  reader.byte_index.val = readerByteIndexAtLimb ordinal ∧
    reader.buffered_bits.val = readerBufferedBitsAtLimb ordinal

private theorem reader_geometry_one_step (ordinal : Nat) :
    readerBufferedBitsAtLimb ordinal < 8 ∧
      readerByteIndexAtLimb (ordinal + 1) =
        readerByteIndexAtLimb ordinal +
          (if readerBufferedBitsAtLimb ordinal = 7 then 3 else 4) ∧
      readerBufferedBitsAtLimb (ordinal + 1) + 31 =
      readerBufferedBitsAtLimb ordinal + 8 *
          (if readerBufferedBitsAtLimb ordinal = 7 then 3 else 4) := by
  let block := ordinal / 8
  let slot := ordinal % 8
  have slotLt : slot < 8 := by
    exact Nat.mod_lt _ (by norm_num)
  have decompose : ordinal = 8 * block + slot := by
    dsimp [block, slot]
    omega
  rw [decompose]
  have current := reader_state_eight_limb_cycle block slot slotLt
  have delta := reader_next_byte_count_eight_limb_cycle block slot slotLt
  constructor
  · rw [current.2]
    exact slotLt
  constructor
  · rw [current.2]
    by_cases last : slot = 7 <;> simp [last] at delta ⊢ <;> omega
  · rw [current.2]
    simp only [readerBufferedBitsAtLimb, PackedLimbBits]
    rw [current.1] at delta
    by_cases last : slot = 7 <;> simp [last] at delta ⊢ <;> omega

theorem new_success_has_initial_packed_reader_geometry
    (bytes : Slice Std.U8) (reader : v6_onefold.V6FixedFieldReader)
    (run : v6_onefold.V6FixedFieldReader.new bytes = .ok (.Ok reader)) :
    GeneratedPackedReaderGeometryAt reader.packed 0 := by
  obtain ⟨_, _, _, indexZero, _, bitsZero⟩ :=
    new_success_exact_length_and_count bytes reader run
  exact ⟨by simpa [readerByteIndexAtLimb] using indexZero,
    by simpa [readerBufferedBitsAtLimb, readerByteIndexAtLimb] using bitsZero⟩

theorem packed_next_success_preserves_reader_geometry
    (ordinal : Nat) (before after : v6_onefold.PackedM31Reader)
    (value : Std.U32)
    (geometry : GeneratedPackedReaderGeometryAt before ordinal)
    (run : v6_onefold.PackedM31Reader.next before = .ok (value, after)) :
    GeneratedPackedReaderGeometryAt after (ordinal + 1) := by
  obtain ⟨refillIndex, refillBuffer, refillBits, refillRun,
      ⟨trace⟩, _, _, afterIndex, _, afterBits⟩ :=
    packed_next_success_exposes_exact_refill before after value run
  obtain ⟨refillIndexExact, refillBitsExact, _⟩ :=
    refill_trace_exact_index_and_bits before.bytes trace
  have geometryStep := reader_geometry_one_step ordinal
  have lowBuffer : before.buffered_bits.val < 8 := by
    rw [geometry.2]
    exact geometryStep.1
  have countExact := refill_trace_count_from_low_buffer before.bytes
    lowBuffer trace
  unfold GeneratedPackedReaderGeometryAt at geometry ⊢
  constructor
  · rw [afterIndex]
    rw [refillIndexExact, geometry.1, countExact, geometry.2]
    exact geometryStep.2.1.symm
  · simp only at refillBitsExact countExact
    rw [geometry.2] at countExact refillBitsExact
    omega

/-! ## Eight-slot bit-vector identity -/

private def widenByte (byte : BitVec 8) : BitVec 64 :=
  byte.setWidth 64

private def packedFiveByteWindowBv
    (window : Fin 5 → BitVec 8) : BitVec 64 :=
  widenByte (window 0) |||
    (widenByte (window 1) <<< 8) |||
    (widenByte (window 2) <<< 16) |||
    (widenByte (window 3) <<< 24) |||
    (widenByte (window 4) <<< 32)

private def slotByteShift (slot : Nat) : Nat :=
  if slot = 0 then 0 else 8 - slot

private theorem packedFiveByteWindowBv_toNat
    (window : Fin 5 → BitVec 8) :
    (packedFiveByteWindowBv window).toNat =
      (window 0).toNat + 256 * (window 1).toNat +
        65536 * (window 2).toNat + 16777216 * (window 3).toNat +
        4294967296 * (window 4).toNat := by
  let b0 := (window 0).toNat
  let b1 := (window 1).toNat
  let b2 := (window 2).toNat
  let b3 := (window 3).toNat
  let b4 := (window 4).toNat
  have hb0 : b0 < 256 := by dsimp [b0]; simpa using (window 0).isLt
  have hb1 : b1 < 256 := by dsimp [b1]; simpa using (window 1).isLt
  have hb2 : b2 < 256 := by dsimp [b2]; simpa using (window 2).isLt
  have hb3 : b3 < 256 := by dsimp [b3]; simpa using (window 3).isLt
  have hb4 : b4 < 256 := by dsimp [b4]; simpa using (window 4).isLt
  have h01 : b0 + 256 * b1 < 65536 := by omega
  have h012 : b0 + 256 * b1 + 65536 * b2 < 16777216 := by omega
  have h0123 :
      b0 + 256 * b1 + 65536 * b2 + 16777216 * b3 < 4294967296 := by
    omega
  have hfull :
      b0 + 256 * b1 + 65536 * b2 + 16777216 * b3 +
        4294967296 * b4 < 18446744073709551616 := by
    omega
  have or01 : b0 ||| b1 * 256 = b0 + 256 * b1 := by
    rw [Nat.or_comm, Nat.mul_comm]
    simpa [Nat.add_comm] using
      (Nat.two_pow_add_eq_or_of_lt (i := 8) hb0 b1).symm
  have or012 :
      (b0 + 256 * b1) ||| b2 * 65536 =
        b0 + 256 * b1 + 65536 * b2 := by
    rw [Nat.or_comm, Nat.mul_comm]
    simpa [Nat.add_comm] using
      (Nat.two_pow_add_eq_or_of_lt (i := 16) h01 b2).symm
  have or0123 :
      (b0 + 256 * b1 + 65536 * b2) ||| b3 * 16777216 =
        b0 + 256 * b1 + 65536 * b2 + 16777216 * b3 := by
    rw [Nat.or_comm, Nat.mul_comm]
    simpa [Nat.add_comm] using
      (Nat.two_pow_add_eq_or_of_lt (i := 24) h012 b3).symm
  have orFull :
      (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3) |||
          b4 * 4294967296 =
        b0 + 256 * b1 + 65536 * b2 + 16777216 * b3 +
          4294967296 * b4 := by
    rw [Nat.or_comm, Nat.mul_comm]
    simpa [Nat.add_comm] using
      (Nat.two_pow_add_eq_or_of_lt (i := 32) h0123 b4).symm
  simp only [packedFiveByteWindowBv, widenByte, BitVec.toNat_or,
    BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  norm_num
  change ((((b0 % 18446744073709551616 |||
      (b1 * 256) % 18446744073709551616) |||
      (b2 * 65536) % 18446744073709551616) |||
      (b3 * 16777216) % 18446744073709551616) |||
      (b4 * 4294967296) % 18446744073709551616) =
    b0 + 256 * b1 + 65536 * b2 + 16777216 * b3 + 4294967296 * b4
  rw [Nat.mod_eq_of_lt (by omega : b0 < 18446744073709551616),
    Nat.mod_eq_of_lt (by omega : b1 * 256 < 18446744073709551616),
    Nat.mod_eq_of_lt (by omega : b2 * 65536 < 18446744073709551616),
    Nat.mod_eq_of_lt (by omega : b3 * 16777216 < 18446744073709551616),
    Nat.mod_eq_of_lt (by omega : b4 * 4294967296 < 18446744073709551616)]
  change ((((b0 ||| b1 * 256) ||| b2 * 65536) |||
      b3 * 16777216) ||| b4 * 4294967296) =
    b0 + 256 * b1 + 65536 * b2 + 16777216 * b3 + 4294967296 * b4
  rw [or01, or012, or0123, orFull]

private theorem packedFiveByteWindow_masked_shift_toNat
    (window : Fin 5 → BitVec 8) (shift : Nat) (shiftLt : shift < 8) :
    ((packedFiveByteWindowBv window >>> shift) &&&
        (2147483647 : BitVec 64)).toNat =
      ((packedFiveByteWindowBv window).toNat / 2 ^ shift) % 2 ^ 31 := by
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight]
  rw [Nat.shiftRight_eq_div_pow]
  change ((packedFiveByteWindowBv window).toNat / 2 ^ shift) &&&
      (2 ^ 31 - 1) =
    ((packedFiveByteWindowBv window).toNat / 2 ^ shift) % 2 ^ 31
  exact Nat.and_two_pow_sub_one_eq_mod _ 31

private def slotRefillBv (slot : Nat)
    (window : Fin 5 → BitVec 8) : BitVec 64 :=
  match slot with
  | 0 => widenByte (window 0) |||
      (widenByte (window 1) <<< 8) |||
      (widenByte (window 2) <<< 16) |||
      (widenByte (window 3) <<< 24)
  | 1 => (widenByte (window 0) >>> 7) |||
      (widenByte (window 1) <<< 1) |||
      (widenByte (window 2) <<< 9) |||
      (widenByte (window 3) <<< 17) |||
      (widenByte (window 4) <<< 25)
  | 2 => (widenByte (window 0) >>> 6) |||
      (widenByte (window 1) <<< 2) |||
      (widenByte (window 2) <<< 10) |||
      (widenByte (window 3) <<< 18) |||
      (widenByte (window 4) <<< 26)
  | 3 => (widenByte (window 0) >>> 5) |||
      (widenByte (window 1) <<< 3) |||
      (widenByte (window 2) <<< 11) |||
      (widenByte (window 3) <<< 19) |||
      (widenByte (window 4) <<< 27)
  | 4 => (widenByte (window 0) >>> 4) |||
      (widenByte (window 1) <<< 4) |||
      (widenByte (window 2) <<< 12) |||
      (widenByte (window 3) <<< 20) |||
      (widenByte (window 4) <<< 28)
  | 5 => (widenByte (window 0) >>> 3) |||
      (widenByte (window 1) <<< 5) |||
      (widenByte (window 2) <<< 13) |||
      (widenByte (window 3) <<< 21) |||
      (widenByte (window 4) <<< 29)
  | 6 => (widenByte (window 0) >>> 2) |||
      (widenByte (window 1) <<< 6) |||
      (widenByte (window 2) <<< 14) |||
      (widenByte (window 3) <<< 22) |||
      (widenByte (window 4) <<< 30)
  | _ => (widenByte (window 0) >>> 1) |||
      (widenByte (window 1) <<< 7) |||
      (widenByte (window 2) <<< 15) |||
      (widenByte (window 3) <<< 23)

private def slotPostResidualBv (slot : Nat)
    (window : Fin 5 → BitVec 8) : BitVec 64 :=
  match slot with
  | 0 => widenByte (window 3) >>> 7
  | 1 => widenByte (window 4) >>> 6
  | 2 => widenByte (window 4) >>> 5
  | 3 => widenByte (window 4) >>> 4
  | 4 => widenByte (window 4) >>> 3
  | 5 => widenByte (window 4) >>> 2
  | 6 => widenByte (window 4) >>> 1
  | _ => 0

set_option maxHeartbeats 1000000 in
private theorem slot_refill_low31_and_residual_exact
    (slot : Nat) (slotLt : slot < 8)
    (window : Fin 5 → BitVec 8) :
    (slotRefillBv slot window &&& (2147483647 : BitVec 64)) =
        ((packedFiveByteWindowBv window >>> slotByteShift slot) &&&
          (2147483647 : BitVec 64)) ∧
      (slotRefillBv slot window >>> 31) =
        slotPostResidualBv slot window := by
  interval_cases slot <;>
    simp [slotRefillBv, slotPostResidualBv, packedFiveByteWindowBv,
      slotByteShift, widenByte] <;>
    constructor <;>
    apply BitVec.eq_of_getLsbD_eq <;> intro index indexLt <;>
    interval_cases index <;> simp

private def sourceByte8Bv (bytes : Slice Std.U8) (index : Nat) : BitVec 8 :=
  if bound : index < bytes.val.length then bytes.val[index]'bound |>.bv else 0

private theorem sourceByteBv_eq_widen_sourceByte8
    (bytes : Slice Std.U8) (index : Nat) :
    sourceByteBv bytes index = widenByte (sourceByte8Bv bytes index) := by
  unfold sourceByteBv sourceByte8Bv widenByte
  split <;> rfl

private def sourceWindow8 (bytes : Slice Std.U8) (start : Nat) :
    Fin 5 → BitVec 8 :=
  fun offset => sourceByte8Bv bytes (start + offset.val)

private theorem sourceWindow8_to_packedLimbWindow
    (bytes : Slice Std.U8) (lengthExact : bytes.val.length = 9936)
    (field : Fin FixedFieldCount) (limb : Fin LimbsPerQM31) :
    (packedFiveByteWindowBv
        (sourceWindow8 bytes (fixedLimbByteStart field limb))).toNat =
      packedLimbWindow (packedSectionOfSlice bytes lengthExact) field limb := by
  have within := fixedLimbFiveByteWindow_within_packed field limb
  norm_num [FixedPackedBytes] at within
  have h0 : fixedLimbByteStart field limb < bytes.val.length := by omega
  have h1 : fixedLimbByteStart field limb + 1 < bytes.val.length := by omega
  have h2 : fixedLimbByteStart field limb + 2 < bytes.val.length := by omega
  have h3 : fixedLimbByteStart field limb + 3 < bytes.val.length := by omega
  have h4 : fixedLimbByteStart field limb + 4 < bytes.val.length := by omega
  have p0 : fixedLimbByteStart field limb < 9936 := by omega
  have p1 : fixedLimbByteStart field limb + 1 < 9936 := by omega
  have p2 : fixedLimbByteStart field limb + 2 < 9936 := by omega
  have p3 : fixedLimbByteStart field limb + 3 < 9936 := by omega
  have p4 : fixedLimbByteStart field limb + 4 < 9936 := by omega
  rw [packedFiveByteWindowBv_toNat]
  simp [packedLimbWindow, Fin.sum_univ_succ, sourceWindow8, sourceByte8Bv,
    packedSectionByte, packedSectionOfSlice, h0, h1, h2, h3, h4,
    p0, p1, p2, p3, p4,
    Nat.add_assoc, Nat.mul_comm]

private def slotPreResidualBv (slot : Nat)
    (window : Fin 5 → BitVec 8) : BitVec 64 :=
  match slot with
  | 0 => 0
  | 1 => widenByte (window 0) >>> 7
  | 2 => widenByte (window 0) >>> 6
  | 3 => widenByte (window 0) >>> 5
  | 4 => widenByte (window 0) >>> 4
  | 5 => widenByte (window 0) >>> 3
  | 6 => widenByte (window 0) >>> 2
  | _ => widenByte (window 0) >>> 1

private theorem refillBufferBv_slot_exact
    (bytes : Slice Std.U8) (start slot : Nat) (slotLt : slot < 8) :
    refillBufferBv bytes (start + if slot = 0 then 0 else 1)
        (slotPreResidualBv slot (sourceWindow8 bytes start)) slot
        (if slot = 7 then 3 else 4) =
      slotRefillBv slot (sourceWindow8 bytes start) := by
  interval_cases slot <;>
    simp [refillBufferBv, slotPreResidualBv, slotRefillBv, sourceWindow8,
      sourceByteBv_eq_widen_sourceByte8, Nat.add_assoc]

private theorem slot_post_residual_is_next_pre_residual
    (bytes : Slice Std.U8) (start slot : Nat) (slotLt : slot < 8) :
    slotPostResidualBv slot (sourceWindow8 bytes start) =
      slotPreResidualBv ((slot + 1) % 8)
        (sourceWindow8 bytes
          (start + if slot = 0 then 3 else 4)) := by
  interval_cases slot <;>
    simp [slotPostResidualBv, slotPreResidualBv, sourceWindow8,
      Nat.add_assoc]

private theorem packed_reader_ordinal_arithmetic (ordinal : Nat) :
    let slot := ordinal % 8
    readerBufferedBitsAtLimb ordinal = slot ∧
      readerByteIndexAtLimb ordinal =
        ordinal * 31 / 8 + (if slot = 0 then 0 else 1) ∧
      slotByteShift slot = ordinal * 31 % 8 ∧
      (ordinal + 1) * 31 / 8 =
        ordinal * 31 / 8 + (if slot = 0 then 3 else 4) ∧
      (ordinal + 1) % 8 = (slot + 1) % 8 := by
  let block := ordinal / 8
  let slot := ordinal % 8
  have slotLt : slot < 8 := Nat.mod_lt _ (by norm_num)
  have decompose : ordinal = 8 * block + slot := by
    dsimp [block, slot]
    omega
  obtain ⟨indexExact, bitsExact⟩ :=
    reader_state_eight_limb_cycle block slot slotLt
  dsimp only
  rw [decompose]
  interval_cases slot <;>
    simp [readerByteIndexAtLimb, readerBufferedBitsAtLimb, slotByteShift,
      PackedLimbBits] at indexExact bitsExact ⊢ <;>
    omega

def GeneratedPackedReaderContentAt
    (reader : v6_onefold.PackedM31Reader) (ordinal : Nat) : Prop :=
  reader.buffer.bv =
    slotPreResidualBv (ordinal % 8)
      (sourceWindow8 reader.bytes (ordinal * 31 / 8))

def GeneratedPackedReaderExactAt
    (reader : v6_onefold.PackedM31Reader) (ordinal : Nat) : Prop :=
  GeneratedPackedReaderGeometryAt reader ordinal ∧
    GeneratedPackedReaderContentAt reader ordinal

theorem new_success_has_initial_packed_reader_exact_state
    (bytes : Slice Std.U8) (reader : v6_onefold.V6FixedFieldReader)
    (run : v6_onefold.V6FixedFieldReader.new bytes = .ok (.Ok reader)) :
    GeneratedPackedReaderExactAt reader.packed 0 := by
  have geometry := new_success_has_initial_packed_reader_geometry bytes reader run
  obtain ⟨_, _, _, _, bufferZero, _⟩ :=
    new_success_exact_length_and_count bytes reader run
  have bufferExact : reader.packed.buffer = 0#u64 := by
    apply UScalar.eq_of_val_eq
    exact bufferZero
  constructor
  · exact geometry
  · simp [GeneratedPackedReaderContentAt, slotPreResidualBv, bufferExact]

theorem packed_next_success_exact_window_and_state
    (ordinal : Nat) (before after : v6_onefold.PackedM31Reader)
    (value : Std.U32)
    (exactState : GeneratedPackedReaderExactAt before ordinal)
    (run : v6_onefold.PackedM31Reader.next before = .ok (value, after)) :
    value.val =
        ((packedFiveByteWindowBv
            (sourceWindow8 before.bytes (ordinal * 31 / 8)) >>>
              slotByteShift (ordinal % 8)) &&&
          (2147483647 : BitVec 64)).toNat ∧
      GeneratedPackedReaderExactAt after (ordinal + 1) := by
  let slot := ordinal % 8
  let start := ordinal * 31 / 8
  have slotLt : slot < 8 := by
    dsimp [slot]
    exact Nat.mod_lt _ (by norm_num)
  have arithmetic := packed_reader_ordinal_arithmetic ordinal
  dsimp only at arithmetic
  obtain ⟨refillIndex, refillBuffer, refillBits, refillRun,
      ⟨trace⟩, valueExact, afterBytes, afterIndex, afterBuffer, afterBits⟩ :=
    packed_next_success_exposes_exact_refill before after value run
  have geometry := exactState.1
  have beforeContent := exactState.2
  have lowBuffer : before.buffered_bits.val < 8 := by
    rw [geometry.2, arithmetic.1]
    exact slotLt
  have countExact :=
    refill_trace_count_from_low_buffer before.bytes lowBuffer trace
  have refillExact := refill_trace_exact_buffer before.bytes trace
  have refillMatches :
      refillBuffer.bv =
        slotRefillBv slot (sourceWindow8 before.bytes start) := by
    rw [refillExact, countExact]
    rw [geometry.1, geometry.2, arithmetic.1, arithmetic.2.1]
    unfold GeneratedPackedReaderContentAt at beforeContent
    rw [beforeContent]
    simpa [slot, start] using
      refillBufferBv_slot_exact before.bytes start slot slotLt
  have slotFacts := slot_refill_low31_and_residual_exact slot slotLt
    (sourceWindow8 before.bytes start)
  have lowExact :
      refillBuffer.bv &&& (2147483647 : BitVec 64) =
        (packedFiveByteWindowBv (sourceWindow8 before.bytes start) >>>
            slotByteShift slot) &&& (2147483647 : BitVec 64) := by
    rw [refillMatches]
    exact slotFacts.1
  have decodedExact :
      value.val =
        ((packedFiveByteWindowBv (sourceWindow8 before.bytes start) >>>
            slotByteShift slot) &&& (2147483647 : BitVec 64)).toNat := by
    calc
      value.val = (refillBuffer &&& 2147483647#u64).val := valueExact
      _ = (refillBuffer.bv &&& (2147483647 : BitVec 64)).toNat := rfl
      _ = ((packedFiveByteWindowBv (sourceWindow8 before.bytes start) >>>
          slotByteShift slot) &&& (2147483647 : BitVec 64)).toNat :=
        congrArg BitVec.toNat lowExact
  constructor
  · simpa [slot, start] using decodedExact
  · constructor
    · exact packed_next_success_preserves_reader_geometry ordinal before after
        value geometry run
    · unfold GeneratedPackedReaderContentAt
      rw [afterBytes, afterBuffer, refillMatches, slotFacts.2]
      rw [arithmetic.2.2.2.1, arithmetic.2.2.2.2]
      simpa [slot, start] using
        slot_post_residual_is_next_pre_residual before.bytes start slot slotLt

theorem packed_next_success_exact_limb_and_state
    (ordinal : Fin FixedLimbCount)
    (before after : v6_onefold.PackedM31Reader) (value : Std.U32)
    (lengthExact : before.bytes.val.length = 9936)
    (exactState : GeneratedPackedReaderExactAt before ordinal.val)
    (run : v6_onefold.PackedM31Reader.next before = .ok (value, after)) :
    value.val =
        packedLimbNat (packedSectionOfSlice before.bytes lengthExact)
          (fieldAtLimbOrdinal ordinal) (limbAtLimbOrdinal ordinal) ∧
      GeneratedPackedReaderExactAt after (ordinal.val + 1) := by
  let field := fieldAtLimbOrdinal ordinal
  let limb := limbAtLimbOrdinal ordinal
  have bitStart := fixedLimbBitStart_at_ordinal ordinal
  have startExact :
      fixedLimbByteStart field limb = ordinal.val * 31 / 8 := by
    unfold fixedLimbByteStart
    simpa [field, limb] using congrArg (fun value => value / 8) bitStart
  have ordinalArithmetic := packed_reader_ordinal_arithmetic ordinal.val
  dsimp only at ordinalArithmetic
  have shiftExact :
      fixedLimbByteShift field limb = slotByteShift (ordinal.val % 8) := by
    unfold fixedLimbByteShift
    rw [bitStart]
    exact ordinalArithmetic.2.2.1.symm
  have shiftLt : slotByteShift (ordinal.val % 8) < 8 := by
    rw [← shiftExact]
    exact fixedLimbByteShift_lt_eight field limb
  have windowExact := sourceWindow8_to_packedLimbWindow before.bytes
    lengthExact field limb
  rw [startExact] at windowExact
  have step := packed_next_success_exact_window_and_state ordinal.val
    before after value exactState run
  constructor
  · calc
      value.val =
          ((packedFiveByteWindowBv
              (sourceWindow8 before.bytes (ordinal.val * 31 / 8)) >>>
                slotByteShift (ordinal.val % 8)) &&&
            (2147483647 : BitVec 64)).toNat := step.1
      _ = ((packedFiveByteWindowBv
              (sourceWindow8 before.bytes (ordinal.val * 31 / 8))).toNat /
              2 ^ slotByteShift (ordinal.val % 8)) % 2 ^ 31 :=
        packedFiveByteWindow_masked_shift_toNat _ _ shiftLt
      _ = (packedLimbWindow (packedSectionOfSlice before.bytes lengthExact)
              field limb / 2 ^ fixedLimbByteShift field limb) % 2 ^ 31 := by
        rw [windowExact, shiftExact]
      _ = packedLimbNat (packedSectionOfSlice before.bytes lengthExact)
          (fieldAtLimbOrdinal ordinal) (limbAtLimbOrdinal ordinal) := by
        rfl
  · exact step.2

theorem packed_qm31_success_exposes_four_nexts
    (before after : v6_onefold.PackedM31Reader) (value : field.QM31)
    (run : v6_onefold.PackedM31Reader.qm31 before = .ok (value, after)) :
    ∃ value0 value1 value2 value3,
      ∃ reader1 reader2 reader3,
      v6_onefold.PackedM31Reader.next before = .ok (value0, reader1) ∧
      v6_onefold.PackedM31Reader.next reader1 = .ok (value1, reader2) ∧
      v6_onefold.PackedM31Reader.next reader2 = .ok (value2, reader3) ∧
      v6_onefold.PackedM31Reader.next reader3 = .ok (value3, after) ∧
      value.c0.a = value0 ∧ value.c0.b = value1 ∧
      value.c1.a = value2 ∧ value.c1.b = value3 := by
  unfold v6_onefold.PackedM31Reader.qm31 at run
  rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
  rcases run with ⟨first, firstRun, run⟩
  rcases first with ⟨value0, reader1⟩
  rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
  rcases run with ⟨second, secondRun, run⟩
  rcases second with ⟨value1, reader2⟩
  simp only [field.CM31.new, bind_tc_ok] at run
  rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
  rcases run with ⟨third, thirdRun, run⟩
  rcases third with ⟨value2, reader3⟩
  rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
  rcases run with ⟨fourth, fourthRun, run⟩
  rcases fourth with ⟨value3, reader4⟩
  simp only [field.CM31.new, bind_tc_ok] at run
  injection run with resultExact
  injection resultExact with valueExact readerExact
  subst value
  subst reader4
  exact ⟨value0, value1, value2, value3, reader1, reader2, reader3,
    firstRun, secondRun, thirdRun, fourthRun, rfl, rfl, rfl, rfl⟩

theorem packed_qm31_success_preserves_bytes
    (before after : v6_onefold.PackedM31Reader) (value : field.QM31)
    (run : v6_onefold.PackedM31Reader.qm31 before = .ok (value, after)) :
    after.bytes = before.bytes := by
  obtain ⟨value0, value1, value2, value3, reader1, reader2, reader3,
      run0, run1, run2, run3, _, _, _, _⟩ :=
    packed_qm31_success_exposes_four_nexts before after value run
  exact (packed_next_success_preserves_bytes reader3 after value3 run3).trans
    ((packed_next_success_preserves_bytes reader2 reader3 value2 run2).trans
      ((packed_next_success_preserves_bytes reader1 reader2 value1 run1).trans
        (packed_next_success_preserves_bytes before reader1 value0 run0)))

theorem fixed_next_qm31_success_exposes_packed_run
    (before after : v6_onefold.V6FixedFieldReader) (value : field.QM31)
    (run : v6_onefold.V6FixedFieldReader.next_qm31 before =
      .ok (.Ok value, after)) :
    before.remaining.val > 0 ∧
      ∃ packedAfter,
        v6_onefold.PackedM31Reader.qm31 before.packed =
          .ok (value, packedAfter) ∧
        after.packed = packedAfter ∧
        after.remaining.val + 1 = before.remaining.val := by
  unfold v6_onefold.V6FixedFieldReader.next_qm31 at run
  split at run
  · simp at run
  · rename_i nonempty
    generalize packedRun :
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
        constructor
        · simpa using nonempty
        · rfl

theorem fixed_next_qm31_success_preserves_packed_bytes
    (before after : v6_onefold.V6FixedFieldReader) (value : field.QM31)
    (run : v6_onefold.V6FixedFieldReader.next_qm31 before =
      .ok (.Ok value, after)) :
    after.packed.bytes = before.packed.bytes := by
  obtain ⟨_, packedAfter, packedRun, afterPacked, _⟩ :=
    fixed_next_qm31_success_exposes_packed_run before after value run
  rw [afterPacked]
  exact packed_qm31_success_preserves_bytes before.packed packedAfter value
    packedRun

private theorem generated_field_P_val_exact : field.P.val = 2147483647 := by
  unfold field.P
  rfl

private theorem generated_m31_modulus_eq_field_P :
    m31Modulus = field.P.val := by
  rw [generated_field_P_val_exact]
  norm_num [m31Modulus, rawCandidateCount]

def GeneratedQM31MatchesPackedField
    (packed : PackedFixedSection) (fieldIndex : Fin FixedFieldCount)
    (value : field.QM31) : Prop :=
  value.c0.a.val = packedLimbNat packed fieldIndex ⟨0, by norm_num⟩ ∧
    value.c0.b.val = packedLimbNat packed fieldIndex ⟨1, by norm_num⟩ ∧
    value.c1.a.val = packedLimbNat packed fieldIndex ⟨2, by norm_num⟩ ∧
    value.c1.b.val = packedLimbNat packed fieldIndex ⟨3, by norm_num⟩

private theorem packedSectionOfSlice_eq_of_slice_eq
    (left right : Slice Std.U8)
    (leftLength : left.val.length = 9936)
    (rightLength : right.val.length = 9936)
    (bytesExact : left = right) :
    packedSectionOfSlice left leftLength =
      packedSectionOfSlice right rightLength := by
  subst right
  rfl

theorem fixed_next_qm31_success_exact_field_and_state
    (fieldIndex : Fin FixedFieldCount)
    (before after : v6_onefold.V6FixedFieldReader) (value : field.QM31)
    (lengthExact : before.packed.bytes.val.length = 9936)
    (exactState : GeneratedPackedReaderExactAt before.packed
      (fieldIndex.val * 4))
    (run : v6_onefold.V6FixedFieldReader.next_qm31 before =
      .ok (.Ok value, after)) :
    GeneratedQM31MatchesPackedField
        (packedSectionOfSlice before.packed.bytes lengthExact) fieldIndex value ∧
      GeneratedPackedReaderExactAt after.packed (fieldIndex.val * 4 + 4) := by
  obtain ⟨_, packedAfter, packedRun, afterPacked, _⟩ :=
    fixed_next_qm31_success_exposes_packed_run before after value run
  obtain ⟨value0, value1, value2, value3, reader1, reader2, reader3,
      run0, run1, run2, run3, value0Exact, value1Exact,
      value2Exact, value3Exact⟩ :=
    packed_qm31_success_exposes_four_nexts before.packed packedAfter value
      packedRun
  have bytes1 := packed_next_success_preserves_bytes before.packed reader1
    value0 run0
  have bytes2 := packed_next_success_preserves_bytes reader1 reader2 value1 run1
  have bytes3 := packed_next_success_preserves_bytes reader2 reader3 value2 run2
  have bytes4 := packed_next_success_preserves_bytes reader3 packedAfter value3 run3
  have length1 : reader1.bytes.val.length = 9936 := by
    rw [bytes1]
    exact lengthExact
  have length2 : reader2.bytes.val.length = 9936 := by
    rw [bytes2]
    exact length1
  have length3 : reader3.bytes.val.length = 9936 := by
    rw [bytes3]
    exact length2
  let limb0 : Fin LimbsPerQM31 := ⟨0, by norm_num [LimbsPerQM31]⟩
  let limb1 : Fin LimbsPerQM31 := ⟨1, by norm_num [LimbsPerQM31]⟩
  let limb2 : Fin LimbsPerQM31 := ⟨2, by norm_num [LimbsPerQM31]⟩
  let limb3 : Fin LimbsPerQM31 := ⟨3, by norm_num [LimbsPerQM31]⟩
  let ordinal0 := fixedLimbIndex fieldIndex limb0
  let ordinal1 := fixedLimbIndex fieldIndex limb1
  let ordinal2 := fixedLimbIndex fieldIndex limb2
  let ordinal3 := fixedLimbIndex fieldIndex limb3
  have state0 : GeneratedPackedReaderExactAt before.packed ordinal0.val := by
    simpa [ordinal0, limb0] using exactState
  have step0 := packed_next_success_exact_limb_and_state ordinal0 before.packed
    reader1 value0 lengthExact state0 run0
  have state1 : GeneratedPackedReaderExactAt reader1 ordinal1.val := by
    simpa [ordinal0, ordinal1, limb0, limb1] using step0.2
  have step1 := packed_next_success_exact_limb_and_state ordinal1 reader1
    reader2 value1 length1 state1 run1
  have state2 : GeneratedPackedReaderExactAt reader2 ordinal2.val := by
    simpa [ordinal1, ordinal2, limb1, limb2] using step1.2
  have step2 := packed_next_success_exact_limb_and_state ordinal2 reader2
    reader3 value2 length2 state2 run2
  have state3 : GeneratedPackedReaderExactAt reader3 ordinal3.val := by
    simpa [ordinal2, ordinal3, limb2, limb3] using step2.2
  have step3 := packed_next_success_exact_limb_and_state ordinal3 reader3
    packedAfter value3 length3 state3 run3
  have packedSections1 :
      packedSectionOfSlice reader1.bytes length1 =
        packedSectionOfSlice before.packed.bytes lengthExact := by
    exact packedSectionOfSlice_eq_of_slice_eq reader1.bytes before.packed.bytes
      length1 lengthExact bytes1
  have packedSections2 :
      packedSectionOfSlice reader2.bytes length2 =
        packedSectionOfSlice before.packed.bytes lengthExact := by
    exact packedSectionOfSlice_eq_of_slice_eq reader2.bytes before.packed.bytes
      length2 lengthExact (bytes2.trans bytes1)
  have packedSections3 :
      packedSectionOfSlice reader3.bytes length3 =
        packedSectionOfSlice before.packed.bytes lengthExact := by
    exact packedSectionOfSlice_eq_of_slice_eq reader3.bytes before.packed.bytes
      length3 lengthExact (bytes3.trans (bytes2.trans bytes1))
  constructor
  · unfold GeneratedQM31MatchesPackedField
    constructor
    · rw [value0Exact]
      simpa [ordinal0, limb0, fieldAtLimbOrdinal_fixedLimbIndex,
        limbAtLimbOrdinal_fixedLimbIndex] using step0.1
    constructor
    · rw [value1Exact]
      rw [packedSections1] at step1
      simpa [ordinal1, limb1, fieldAtLimbOrdinal_fixedLimbIndex,
        limbAtLimbOrdinal_fixedLimbIndex] using step1.1
    constructor
    · rw [value2Exact]
      rw [packedSections2] at step2
      simpa [ordinal2, limb2, fieldAtLimbOrdinal_fixedLimbIndex,
        limbAtLimbOrdinal_fixedLimbIndex] using step2.1
    · rw [value3Exact]
      rw [packedSections3] at step3
      simpa [ordinal3, limb3, fieldAtLimbOrdinal_fixedLimbIndex,
        limbAtLimbOrdinal_fixedLimbIndex] using step3.1
  · rw [afterPacked]
    simpa [ordinal3, limb3] using step3.2

theorem successful_fixed_reader_trace_exact_range
    {first final : v6_onefold.V6FixedFieldReader}
    {values : List field.QM31}
    (start : Nat)
    (lengthExact : first.packed.bytes.val.length = 9936)
    (rangeBound : start + values.length ≤ FixedFieldCount)
    (exactState : GeneratedPackedReaderExactAt first.packed (start * 4))
    (trace : SuccessfulFixedReaderTrace first values final) :
    (∀ fieldIndex : Fin FixedFieldCount,
        start ≤ fieldIndex.val →
        fieldIndex.val < start + values.length →
        ∀ limb : Fin LimbsPerQM31,
          packedLimbNat
              (packedSectionOfSlice first.packed.bytes lengthExact)
              fieldIndex limb < m31Modulus) ∧
      GeneratedPackedReaderExactAt final.packed
        ((start + values.length) * 4) := by
  induction trace generalizing start with
  | nil =>
      constructor
      · intro fieldIndex lower upper limb
        simp only [List.length_nil, Nat.add_zero] at upper
        omega
      · simpa using exactState
  | @cons before after final value tail read rest inductionHypothesis =>
      have startLt : start < FixedFieldCount := by
        simp only [List.length_cons] at rangeBound
        omega
      let fieldIndex : Fin FixedFieldCount := ⟨start, startLt⟩
      have fieldStep := fixed_next_qm31_success_exact_field_and_state
        fieldIndex before after value lengthExact exactState read
      have bytesAfter := fixed_next_qm31_success_preserves_packed_bytes
        before after value read
      have lengthAfter : after.packed.bytes.val.length = 9936 := by
        rw [bytesAfter]
        exact lengthExact
      have tailBound : start + 1 + tail.length ≤ FixedFieldCount := by
        simp only [List.length_cons] at rangeBound
        omega
      have tailResult := inductionHypothesis (start + 1) lengthAfter tailBound
        (by convert fieldStep.2 using 1 <;> simp [fieldIndex] <;> omega)
      have packedSectionsAfter :
          packedSectionOfSlice after.packed.bytes lengthAfter =
            packedSectionOfSlice before.packed.bytes lengthExact :=
        packedSectionOfSlice_eq_of_slice_eq after.packed.bytes
          before.packed.bytes lengthAfter lengthExact bytesAfter
      rw [packedSectionsAfter] at tailResult
      constructor
      · intro target lower upper limb
        by_cases current : target.val = start
        · have targetExact : target = fieldIndex := by
            apply Fin.ext
            exact current
          subst target
          obtain ⟨_, _, canonical0, canonical1, canonical2, canonical3⟩ :=
            next_qm31_success_remaining_and_canonical before after value read
          rcases fieldStep.1 with ⟨matches0, matches1, matches2, matches3⟩
          rw [generated_m31_modulus_eq_field_P]
          fin_cases limb
          · rw [← matches0]
            exact canonical0
          · rw [← matches1]
            exact canonical1
          · rw [← matches2]
            exact canonical2
          · rw [← matches3]
            exact canonical3
        · exact tailResult.1 target (by omega) (by
            simp only [List.length_cons] at upper
            omega) limb
      · convert tailResult.2 using 1 <;>
          simp only [List.length_cons] <;> omega

/-- A complete successful production fixed-reader run constructs the exact
canonical packed section required by the frozen Tag-73 layout model.  In
particular, neither padding nor any of the 2,564 strict M31 comparisons remains
as a caller-supplied premise. -/
theorem complete_successful_fixed_reader_trace_constructs_exact_canonical_section
    (bytes : Slice Std.U8)
    (initial final : v6_onefold.V6FixedFieldReader)
    (values : List field.QM31)
    (newRun : v6_onefold.V6FixedFieldReader.new bytes = .ok (.Ok initial))
    (trace : SuccessfulFixedReaderTrace initial values final)
    (finishRun : v6_onefold.V6FixedFieldReader.finish final = .ok (.Ok ())) :
    ∃ lengthExact : bytes.val.length = 9936,
      ExactCanonicalPackedFixedSection
        (packedSectionOfSlice bytes lengthExact) := by
  obtain ⟨lengthExact, valuesLength, _⟩ :=
    complete_successful_trace_has_exact_641_canonical_values
      bytes initial final values newRun trace finishRun
  obtain ⟨_, _, initialBytes, _, _, _⟩ :=
    new_success_exact_length_and_count bytes initial newRun
  have readerLength : initial.packed.bytes.val.length = 9936 := by
    rw [initialBytes]
    exact lengthExact
  have rangeBound : 0 + values.length ≤ FixedFieldCount := by
    simp [valuesLength, FixedFieldCount]
  have rangeResult := successful_fixed_reader_trace_exact_range
    0 readerLength rangeBound
      (new_success_has_initial_packed_reader_exact_state bytes initial newRun)
      trace
  have sectionsExact :
      packedSectionOfSlice initial.packed.bytes readerLength =
        packedSectionOfSlice bytes lengthExact :=
    packedSectionOfSlice_eq_of_slice_eq initial.packed.bytes bytes
      readerLength lengthExact initialBytes
  obtain ⟨paddingLength, paddingZero⟩ :=
    new_success_packed_section_padding_zero bytes initial newRun
  refine ⟨lengthExact, ?_, ?_⟩
  · simpa using paddingZero
  · intro fieldIndex limb
    have canonical := rangeResult.1 fieldIndex (by omega) (by
      simpa [valuesLength, FixedFieldCount] using fieldIndex.isLt) limb
    rw [sectionsExact] at canonical
    exact canonical

#print axioms new_success_exposes_padding_validation
#print axioms padding_validation_success_last_byte_lt_16
#print axioms new_success_packed_section_padding_zero
#print axioms next_loop_body_cont_index_and_bits
#print axioms next_loop_body_cont_exact_buffer
#print axioms next_loop_body_done_index_and_bits
#print axioms next_loop_success_has_exact_trace
#print axioms refill_trace_exact_index_and_bits
#print axioms refill_trace_exact_buffer
#print axioms refill_trace_count_from_low_buffer
#print axioms packed_next_success_exposes_exact_refill
#print axioms new_success_has_initial_packed_reader_geometry
#print axioms packed_next_success_preserves_reader_geometry
#print axioms slot_refill_low31_and_residual_exact
#print axioms refillBufferBv_slot_exact
#print axioms slot_post_residual_is_next_pre_residual
#print axioms packed_reader_ordinal_arithmetic
#print axioms new_success_has_initial_packed_reader_exact_state
#print axioms packed_next_success_exact_window_and_state
#print axioms packed_next_success_exact_limb_and_state
#print axioms packed_qm31_success_exposes_four_nexts
#print axioms fixed_next_qm31_success_exposes_packed_run
#print axioms fixed_next_qm31_success_exact_field_and_state
#print axioms successful_fixed_reader_trace_exact_range
#print axioms complete_successful_fixed_reader_trace_constructs_exact_canonical_section

end AspisV7Tag73GeneratedPackedReaderBridge
