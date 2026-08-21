import V5FriConsumerObservationBridge

/-! Exact byte adapter from the generated opening accessor to the returned
opening model used by the authenticated FRI schedule. -/

open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxRecDepth 3000

namespace AspisV5FriConsumerValueAdapter

open V5FriConsumerExact
open AspisV5MerkleConsumedValueBridge
open AspisV5FriConsumerExactProof
open AspisV5FriConsumerObservationBridge

def extractedValueBytes (opening : Opening) (ordinal : Std.Usize) :
    Option (List Std.U8) :=
  match aspis_core.state_only_private_openings.StateOnlyPrivateOpening.value
      opening ordinal with
  | .ok none => none
  | .ok (some value) => some value.val
  | .fail _ => none
  | .div => none

def modelValueBytes (opening : Opening) (ordinal : Std.Usize) :
    Option (List Std.U8) :=
  if ordinal.val < opening.count.val then
    some ((opening.records.val.drop
      (ordinal.val * (opening.value_width.val + 32))).take
        opening.value_width.val)
  else none

/-- The unchanged generated accessor has exactly the fixed-width flat-record
slicing semantics used by `ReturnedOpening.value`. -/
theorem extractedValueBytes_eq_model
    (opening : Opening) (ordinal : Std.Usize)
    (hwidth : opening.value_width.val + 32 ≤ Std.Usize.max)
    (hrecords : opening.records.val.length =
      opening.count.val * (opening.value_width.val + 32)) :
    extractedValueBytes opening ordinal = modelValueBytes opening ordinal := by
  unfold extractedValueBytes modelValueBytes
  unfold aspis_core.state_only_private_openings.StateOnlyPrivateOpening.value
  by_cases hord : ordinal.val < opening.count.val
  · have hwidthBound : opening.value_width.val + 32 <
        2 ^ UScalarTy.Usize.numBits := by scalar_tac
    have hwidthSize : opening.value_width.val + 32 <
        UScalar.size UScalarTy.Usize := by
      rw [UScalar.size]
      exact hwidthBound
    have hrecordWidthVal :
        (Std.Usize.wrapping_add opening.value_width
          32#usize).val =
          opening.value_width.val + 32 := by
      simp only [Std.Usize.wrapping_add_val_eq]
      exact Nat.mod_eq_of_lt hwidthSize
    let recordWidth : Std.Usize := Std.Usize.ofNatCore
      (opening.value_width.val + 32) hwidthBound
    have hrecordWidth :
        Std.Usize.wrapping_add opening.value_width
          32#usize =
          recordWidth := by
      apply UScalar.eq_of_val_eq
      exact hrecordWidthVal
    have htotal :
        opening.count.val * (opening.value_width.val + 32) ≤
          Std.Usize.max := by
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
    have hcheckedMul : Std.Usize.checked_mul ordinal recordWidth =
        some start := by
      simp [Std.Usize.checked_mul, core.num.checked_mul_UScalar,
        Option.ofResult, UScalar.mul, UScalar.tryMk, UScalar.tryMkOpt,
        Result.ofOption, recordWidth, start, hmulSystem]
      apply UScalar.eq_of_val_eq
      simp
    have hcheckedAdd : Std.Usize.checked_add start opening.value_width =
        some stop := by
      unfold Std.Usize.checked_add core.num.checked_add_UScalar
      change Option.ofResult (UScalar.add start opening.value_width) = some stop
      simp [Option.ofResult, UScalar.add, UScalar.tryMk, UScalar.tryMkOpt,
        Result.ofOption, start, stop, haddSystem]
      apply UScalar.eq_of_val_eq
      simp
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
      aspis_core.state_only_private_openings.StateOnlyPrivateOpening.record_width,
      aspis_core.state_only_private_merkle.STATE_ONLY_PRIVATE_LEAF_SALT_BYTES,
      hrecordWidth, hcheckedMul, hcheckedAdd,
      core.slice.Slice.get, core.slice.index.SliceIndexRangeUsizeSlice.get,
      V5FriConsumerExact.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      V5FriConsumerExact.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
      lift, hstartStop, hendRecords, start, stop, List.slice]
  · have hge : opening.count.val ≤ ordinal.val := Nat.le_of_not_gt hord
    simp [hord, hge]

theorem extracted_value_accessor_equals_returned_value
    (opening : Opening) (ordinal : Std.Usize)
    (hwidth : opening.value_width.val + 32 ≤ Std.Usize.max)
    (hrecords : opening.records.val.length =
      opening.count.val * (opening.value_width.val + 32)) :
    (extractedValueBytes opening ordinal).map
        (List.map generatedU8ToByte) =
      (generatedOpeningToReturned opening).value ordinal.val := by
  rw [extractedValueBytes_eq_model opening ordinal hwidth hrecords]
  by_cases hord : ordinal.val < opening.count.val
  · simp [modelValueBytes, generatedOpeningToReturned,
      ReturnedOpening.value, ReturnedOpening.recordWidth, hord]
  · simp [modelValueBytes, generatedOpeningToReturned,
      ReturnedOpening.value, hord]

/-- A successful production accessor returns exactly the byte list selected
by the authenticated `ReturnedOpening.value` model at the same ordinal. -/
theorem generatedOpeningToReturned_value_of_success
    (opening : Opening) (ordinal : Std.Usize) (value : Slice Std.U8)
    (hwidth : opening.value_width.val + 32 ≤ Std.Usize.max)
    (hrecords : opening.records.val.length =
      opening.count.val * (opening.value_width.val + 32))
    (hvalue :
      aspis_core.state_only_private_openings.StateOnlyPrivateOpening.value
        opening ordinal = .ok (some value)) :
    (generatedOpeningToReturned opening).value ordinal.val =
      some (value.val.map generatedU8ToByte) := by
  have extracted : extractedValueBytes opening ordinal = some value.val := by
    simp [extractedValueBytes, hvalue]
  have exact := extracted_value_accessor_equals_returned_value opening ordinal
    hwidth hrecords
  rw [extracted] at exact
  exact exact.symm

#print axioms extractedValueBytes_eq_model
#print axioms extracted_value_accessor_equals_returned_value
#print axioms generatedOpeningToReturned_value_of_success

end AspisV5FriConsumerValueAdapter
