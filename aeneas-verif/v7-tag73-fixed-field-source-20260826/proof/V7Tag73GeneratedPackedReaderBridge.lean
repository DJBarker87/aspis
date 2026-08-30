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

end AspisV7Tag73GeneratedPackedReaderBridge
