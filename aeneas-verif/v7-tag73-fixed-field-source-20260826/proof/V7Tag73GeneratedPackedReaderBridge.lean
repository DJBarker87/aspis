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

#print axioms new_success_exposes_padding_validation
#print axioms padding_validation_success_last_byte_lt_16
#print axioms new_success_packed_section_padding_zero

end AspisV7Tag73GeneratedPackedReaderBridge
