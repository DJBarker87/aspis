import V5OpeningAccessorsGenerated.Funs
import AspisFormal.V5MerkleConsumedValueBridge

open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxRecDepth 3000

namespace AspisV5OpeningAccessorSourceProof

open aspis_core
open AspisV5MerkleConsumedValueBridge

def u8ToByte (byte : Std.U8) :
    AspisV5ComponentCQM31Representation.Byte :=
  ⟨byte.val, by
    have h := UScalar.hBounds byte
    norm_num at h ⊢
    exact h⟩

def generatedOpeningToReturned
    (opening : state_only_private_openings.StateOnlyPrivateOpening) :
    ReturnedOpening where
  count := opening.count.val
  valueWidth := opening.value_width.val
  records := opening.records.val.map u8ToByte
  frontier := opening.frontier.val.map u8ToByte
  offsets :=
    { count := opening.offsets.count.val
      records := opening.offsets.records.val
      frontierCount := opening.offsets.frontier_count.val
      frontier := opening.offsets.frontier.val
      endOffset := opening.offsets.end.val }

def extractedValueBytes
    (opening : state_only_private_openings.StateOnlyPrivateOpening)
    (ordinal : Std.Usize) : Option (List Std.U8) :=
  match state_only_private_openings.StateOnlyPrivateOpening.value
      opening ordinal with
  | .ok none => none
  | .ok (some value) => some value.val
  | .fail _ => none
  | .div => none

def extractedRecordBytes
    (opening : state_only_private_openings.StateOnlyPrivateOpening)
    (ordinal : Std.Usize) : Option (List Std.U8) :=
  match state_only_private_openings.StateOnlyPrivateOpening.record
      opening ordinal with
  | .ok none => none
  | .ok (some record) => some record.val
  | .fail _ => none
  | .div => none

def modelValueBytes
    (opening : state_only_private_openings.StateOnlyPrivateOpening)
    (ordinal : Std.Usize) : Option (List Std.U8) :=
  if ordinal.val < opening.count.val then
    some ((opening.records.val.drop
      (ordinal.val * (opening.value_width.val + 32))).take
        opening.value_width.val)
  else none

def modelRecordBytes
    (opening : state_only_private_openings.StateOnlyPrivateOpening)
    (ordinal : Std.Usize) : Option (List Std.U8) :=
  if ordinal.val < opening.count.val then
    some ((opening.records.val.drop
      (ordinal.val * (opening.value_width.val + 32))).take
        (opening.value_width.val + 32))
  else none

theorem extractedRecordBytes_eq_model
    (opening : state_only_private_openings.StateOnlyPrivateOpening)
    (ordinal : Std.Usize)
    (hwidth : opening.value_width.val + 32 ≤ Std.Usize.max)
    (hrecords : opening.records.val.length =
      opening.count.val * (opening.value_width.val + 32)) :
    extractedRecordBytes opening ordinal = modelRecordBytes opening ordinal := by
  unfold extractedRecordBytes modelRecordBytes
  unfold state_only_private_openings.StateOnlyPrivateOpening.record
  by_cases hord : ordinal.val < opening.count.val
  · have hwidthBound : opening.value_width.val + 32 <
        2 ^ UScalarTy.Usize.numBits := by scalar_tac
    have hwidthSize : opening.value_width.val + 32 <
        UScalar.size UScalarTy.Usize := by
      rw [UScalar.size]
      exact hwidthBound
    have hrecordWidthVal :
        (Std.Usize.wrapping_add opening.value_width
          state_only_private_merkle.STATE_ONLY_PRIVATE_LEAF_SALT_BYTES).val =
          opening.value_width.val + 32 := by
      simp only [Std.Usize.wrapping_add_val_eq,
        state_only_private_merkle.STATE_ONLY_PRIVATE_LEAF_SALT_BYTES]
      exact Nat.mod_eq_of_lt hwidthSize
    let recordWidth : Std.Usize := Std.Usize.ofNatCore
      (opening.value_width.val + 32) hwidthBound
    have hrecordWidth :
        Std.Usize.wrapping_add opening.value_width
          state_only_private_merkle.STATE_ONLY_PRIVATE_LEAF_SALT_BYTES =
          recordWidth := by
      apply UScalar.eq_of_val_eq
      exact hrecordWidthVal
    have htotal : opening.count.val *
        (opening.value_width.val + 32) ≤ Std.Usize.max := by
      rw [← hrecords]
      exact opening.records.property
    have hmul : ordinal.val * (opening.value_width.val + 32) ≤
        Std.Usize.max := le_trans
      (Nat.mul_le_mul_right _ (Nat.le_of_lt hord)) htotal
    have hadd : ordinal.val * (opening.value_width.val + 32) +
        (opening.value_width.val + 32) ≤ Std.Usize.max := by
      rw [← Nat.succ_mul]
      exact le_trans (Nat.mul_le_mul_right _ hord) htotal
    have hmulBound : ordinal.val * (opening.value_width.val + 32) <
        2 ^ UScalarTy.Usize.numBits := by scalar_tac
    have haddBound : ordinal.val * (opening.value_width.val + 32) +
        (opening.value_width.val + 32) <
          2 ^ UScalarTy.Usize.numBits := by scalar_tac
    have hmulSystem : ordinal.val * (opening.value_width.val + 32) <
        2 ^ System.Platform.numBits := by simpa using hmulBound
    have haddSystem : ordinal.val * (opening.value_width.val + 32) +
        (opening.value_width.val + 32) < 2 ^ System.Platform.numBits := by
      simpa using haddBound
    let start : Std.Usize := Std.Usize.ofNatCore
      (ordinal.val * (opening.value_width.val + 32)) hmulBound
    let stop : Std.Usize := Std.Usize.ofNatCore
      (ordinal.val * (opening.value_width.val + 32) +
        (opening.value_width.val + 32)) haddBound
    have hcheckedMul : Std.Usize.checked_mul ordinal recordWidth = some start := by
      simp [Std.Usize.checked_mul, core.num.checked_mul_UScalar,
        Option.ofResult, UScalar.mul, UScalar.tryMk, UScalar.tryMkOpt,
        Result.ofOption, recordWidth, start, hmulSystem]
      apply UScalar.eq_of_val_eq
      simp
    have hcheckedAdd : Std.Usize.checked_add start recordWidth = some stop := by
      unfold Std.Usize.checked_add core.num.checked_add_UScalar
      change Option.ofResult (UScalar.add start recordWidth) = some stop
      simp [Option.ofResult, UScalar.add, UScalar.tryMk, UScalar.tryMkOpt,
        Result.ofOption, start, recordWidth, stop, haddSystem]
      apply UScalar.eq_of_val_eq
      simp
    have hendRecords : ordinal.val * (opening.value_width.val + 32) +
        (opening.value_width.val + 32) ≤ opening.records.val.length := by
      rw [hrecords, ← Nat.succ_mul]
      exact Nat.mul_le_mul_right _ hord
    have hstartStop : ordinal.val * (opening.value_width.val + 32) ≤
        ordinal.val * (opening.value_width.val + 32) +
          (opening.value_width.val + 32) := Nat.le_add_right _ _
    have hnotge : ¬ opening.count.val ≤ ordinal.val := Nat.not_le_of_gt hord
    simp [hord, hnotge,
      state_only_private_openings.StateOnlyPrivateOpening.record_width,
      hrecordWidth, hcheckedMul, hcheckedAdd,
      core.slice.Slice.get, core.slice.index.SliceIndexRangeUsizeSlice.get,
      core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
      lift, hstartStop, hendRecords, start, stop, List.slice]
  · have hge : opening.count.val ≤ ordinal.val := Nat.le_of_not_gt hord
    simp [hord, hge]

theorem extractedValueBytes_eq_model
    (opening : state_only_private_openings.StateOnlyPrivateOpening)
    (ordinal : Std.Usize)
    (hwidth : opening.value_width.val + 32 ≤ Std.Usize.max)
    (hrecords : opening.records.val.length =
      opening.count.val * (opening.value_width.val + 32)) :
    extractedValueBytes opening ordinal = modelValueBytes opening ordinal := by
  unfold extractedValueBytes modelValueBytes
  unfold state_only_private_openings.StateOnlyPrivateOpening.value
  by_cases hord : ordinal.val < opening.count.val
  · have hwidthBound : opening.value_width.val + 32 <
        2 ^ UScalarTy.Usize.numBits := by scalar_tac
    have hwidthSize : opening.value_width.val + 32 <
        UScalar.size UScalarTy.Usize := by
      rw [UScalar.size]
      exact hwidthBound
    have hrecordWidthVal :
        (Std.Usize.wrapping_add opening.value_width
          state_only_private_merkle.STATE_ONLY_PRIVATE_LEAF_SALT_BYTES).val =
          opening.value_width.val + 32 := by
      simp only [Std.Usize.wrapping_add_val_eq,
        state_only_private_merkle.STATE_ONLY_PRIVATE_LEAF_SALT_BYTES]
      exact Nat.mod_eq_of_lt hwidthSize
    let recordWidth : Std.Usize := Std.Usize.ofNatCore
      (opening.value_width.val + 32) hwidthBound
    have hrecordWidth :
        Std.Usize.wrapping_add opening.value_width
          state_only_private_merkle.STATE_ONLY_PRIVATE_LEAF_SALT_BYTES =
          recordWidth := by
      apply UScalar.eq_of_val_eq
      exact hrecordWidthVal
    have htotal :
        opening.count.val * (opening.value_width.val + 32) ≤ Std.Usize.max := by
      rw [← hrecords]
      exact opening.records.property
    have hmul : ordinal.val * (opening.value_width.val + 32) ≤
        Std.Usize.max := by
      calc
        ordinal.val * (opening.value_width.val + 32) ≤
            opening.count.val * (opening.value_width.val + 32) := by
              exact Nat.mul_le_mul_right _ (Nat.le_of_lt hord)
        _ ≤ Std.Usize.max := htotal
    have hadd : ordinal.val * (opening.value_width.val + 32) +
        opening.value_width.val ≤ Std.Usize.max := by
      calc
        ordinal.val * (opening.value_width.val + 32) +
            opening.value_width.val ≤
            (ordinal.val + 1) * (opening.value_width.val + 32) := by
          rw [Nat.add_mul]
          omega
        _ ≤ opening.count.val * (opening.value_width.val + 32) := by
          exact Nat.mul_le_mul_right _ hord
        _ ≤ Std.Usize.max := htotal
    have hmulBound : ordinal.val * (opening.value_width.val + 32) <
        2 ^ UScalarTy.Usize.numBits := by scalar_tac
    have haddBound : ordinal.val * (opening.value_width.val + 32) +
        opening.value_width.val < 2 ^ UScalarTy.Usize.numBits := by scalar_tac
    have hmulSystem : ordinal.val * (opening.value_width.val + 32) <
        2 ^ System.Platform.numBits := by simpa using hmulBound
    have haddSystem : ordinal.val * (opening.value_width.val + 32) +
        opening.value_width.val < 2 ^ System.Platform.numBits := by
      simpa using haddBound
    let start : Std.Usize := Std.Usize.ofNatCore
      (ordinal.val * (opening.value_width.val + 32)) hmulBound
    let stop : Std.Usize := Std.Usize.ofNatCore
      (ordinal.val * (opening.value_width.val + 32) +
        opening.value_width.val) haddBound
    have hcheckedMul : Std.Usize.checked_mul ordinal recordWidth = some start := by
      simp [Std.Usize.checked_mul, core.num.checked_mul_UScalar,
        Option.ofResult, UScalar.mul, UScalar.tryMk, UScalar.tryMkOpt,
        Result.ofOption, recordWidth, start, hmulSystem]
      apply UScalar.eq_of_val_eq
      simp [start]
    have hcheckedAdd : Std.Usize.checked_add start opening.value_width = some stop := by
      unfold Std.Usize.checked_add core.num.checked_add_UScalar
      change Option.ofResult (UScalar.add start opening.value_width) = some stop
      simp [Option.ofResult, UScalar.add, UScalar.tryMk, UScalar.tryMkOpt,
        Result.ofOption, start, stop, haddSystem]
      apply UScalar.eq_of_val_eq
      simp [stop]
    have hendRecords : ordinal.val * (opening.value_width.val + 32) +
        opening.value_width.val ≤ opening.records.val.length := by
      rw [hrecords]
      apply le_trans _ (Nat.mul_le_mul_right _ hord)
      rw [Nat.succ_mul]
      omega
    have hstartStop : ordinal.val * (opening.value_width.val + 32) ≤
        ordinal.val * (opening.value_width.val + 32) +
          opening.value_width.val := Nat.le_add_right _ _
    have hnotge : ¬ opening.count.val ≤ ordinal.val := Nat.not_le_of_gt hord
    simp [hord, hnotge,
      state_only_private_openings.StateOnlyPrivateOpening.record_width,
      hrecordWidth, hcheckedMul, hcheckedAdd,
      core.slice.Slice.get, core.slice.index.SliceIndexRangeUsizeSlice.get,
      core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
      lift, hstartStop, hendRecords, start, stop, List.slice]
  · have hge : opening.count.val ≤ ordinal.val := Nat.le_of_not_gt hord
    simp [hord, hge]

theorem extracted_value_accessor_equals_ReturnedOpening_value
    (opening : state_only_private_openings.StateOnlyPrivateOpening)
    (ordinal : Std.Usize)
    (hwidth : opening.value_width.val + 32 ≤ Std.Usize.max)
    (hrecords : opening.records.val.length =
      opening.count.val * (opening.value_width.val + 32)) :
    (extractedValueBytes opening ordinal).map (List.map u8ToByte) =
      (generatedOpeningToReturned opening).value ordinal.val := by
  rw [extractedValueBytes_eq_model opening ordinal hwidth hrecords]
  by_cases hord : ordinal.val < opening.count.val
  · simp [modelValueBytes, generatedOpeningToReturned,
      ReturnedOpening.value, ReturnedOpening.recordWidth, hord]
  · simp [modelValueBytes, generatedOpeningToReturned,
      ReturnedOpening.value, ReturnedOpening.recordWidth, hord]

theorem extracted_record_accessor_equals_ReturnedOpening_record
    (opening : state_only_private_openings.StateOnlyPrivateOpening)
    (ordinal : Std.Usize)
    (hwidth : opening.value_width.val + 32 ≤ Std.Usize.max)
    (hrecords : opening.records.val.length =
      opening.count.val * (opening.value_width.val + 32)) :
    (extractedRecordBytes opening ordinal).map (List.map u8ToByte) =
      (generatedOpeningToReturned opening).record ordinal.val := by
  rw [extractedRecordBytes_eq_model opening ordinal hwidth hrecords]
  by_cases hord : ordinal.val < opening.count.val
  · simp [modelRecordBytes, generatedOpeningToReturned,
      ReturnedOpening.record, ReturnedOpening.recordWidth, hord]
  · simp [modelRecordBytes, generatedOpeningToReturned,
      ReturnedOpening.record, ReturnedOpening.recordWidth, hord]

#print axioms extractedRecordBytes_eq_model
#print axioms extractedValueBytes_eq_model
#print axioms extracted_record_accessor_equals_ReturnedOpening_record
#print axioms extracted_value_accessor_equals_ReturnedOpening_value

end AspisV5OpeningAccessorSourceProof
