import ComponentCRuntimeGenerated
import Mathlib

open Aeneas Aeneas.Std Result ControlFlow Error

namespace aspis_prover.ComponentCRuntimePackerProof

open aspis_prover

deriving instance Inhabited for aspis_core.field.CM31
deriving instance Inhabited for aspis_core.field.QM31

private theorem usize_small_add_val
    (left right : Std.Usize)
    (h : left.val + right.val < Std.Usize.size) :
    (Std.Usize.wrapping_add left right).val = left.val + right.val := by
  rw [Std.Usize.wrapping_add_val_eq]
  apply Nat.mod_eq_of_lt
  simpa [Usize.size] using h

private theorem usize_small_mul_val
    (left right : Std.Usize)
    (h : left.val * right.val < Std.Usize.size) :
    (Std.Usize.wrapping_mul left right).val = left.val * right.val := by
  rw [Std.Usize.wrapping_mul_val_eq]
  apply Nat.mod_eq_of_lt
  simpa [Usize.size] using h

private theorem usize_wrapping_sub_exact
    (left right : Std.Usize) (hle : right.val ≤ left.val) :
    (Std.Usize.wrapping_sub left right).val = left.val - right.val := by
  rw [Std.Usize.wrapping_sub_val_eq]
  have hSize : UScalar.size .Usize = Std.Usize.max + 1 := by
    simp [Std.Usize.size, Std.Usize.max, Std.Usize.numBits]
  have hLeftLt : left.val < UScalar.size .Usize := by
    rw [hSize]
    scalar_tac
  have hRightLeSize : right.val ≤ UScalar.size .Usize := by
    omega
  have hRewrite :
      left.val + (UScalar.size .Usize - right.val) =
        (left.val - right.val) + UScalar.size .Usize := by
    omega
  rw [hRewrite, Nat.add_mod_right, Nat.mod_eq_of_lt]
  omega

private theorem count_array_zero (n0 n1 n2 : Std.Usize) :
    Array.index_usize (Array.make 3#usize [n0, n1, n2]) 0#usize = ok n0 := by
  simp [Array.index_usize, Array.make]

private theorem count_array_one (n0 n1 n2 : Std.Usize) :
    Array.index_usize (Array.make 3#usize [n0, n1, n2]) 1#usize = ok n1 := by
  simp [Array.index_usize, Array.make]

private theorem count_array_two (n0 n1 n2 : Std.Usize) :
    Array.index_usize (Array.make 3#usize [n0, n1, n2]) 2#usize = ok n2 := by
  simp [Array.index_usize, Array.make]

private theorem list_get_eq_getElemBang
    {T : Type} [Inhabited T]
    (values : List T) (index : Nat) (hindex : index < values.length) :
    values[index] = values[index]! := by
  symm
  apply List.getElem!_of_getElem?
  simp [hindex]

private theorem generated_array_index_run
    {T : Type} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize)
    (hindex : index.val < N.val) :
    Array.index_usize values index = ok values.val[index.val]! := by
  obtain ⟨value, hrun, hvalue⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_usize_spec values index (by
      simpa [Array.length_eq] using hindex))
  have harray : index.val < values.val.length := by
    simpa [Array.length_eq] using hindex
  have helem := list_get_eq_getElemBang values.val index.val harray
  simpa [hvalue, helem] using hrun

private theorem generated_vec_index_run
    {T : Type} [Inhabited T]
    (values : alloc.vec.Vec T) (index : Std.Usize)
    (hindex : index.val < values.val.length) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice T)
        values index = ok values.val[index.val]! := by
  obtain ⟨value, hrun, hvalue⟩ := Aeneas.Std.WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec values index hindex)
  have helem := list_get_eq_getElemBang values.val index.val hindex
  simpa [alloc.vec.Vec.index_slice_index, hvalue, helem] using hrun

/-- The authentic generated Rust row-count function has the exact
runtime-sized shape `40 + 4 * (n₀+n₁+n₂)` on its full accepted domain. -/
theorem generated_runtime_rows_exact
    (n0 n1 n2 : Std.Usize)
    (h0 : n0.val ≤ 18) (h1 : n1.val ≤ 18) (h2 : n2.val ≤ 18) :
    ∃ rows,
      v5_mask.component_c_runtime.component_c_runtime_downstream_rows
          (Array.make 3#usize [n0, n1, n2]) = ok (some rows) ∧
      rows.val = 40 + 4 * (n0.val + n1.val + n2.val) := by
  simp only [
    v5_mask.component_c_runtime.component_c_runtime_downstream_rows,
    v5_mask.component_c_runtime.V5_COMPONENT_C_RUNTIME_MAX_LATER_COUNT,
    v5_mask.component_c_runtime.V5_COMPONENT_C_RUNTIME_FIXED_ROWS]
  rw [count_array_zero, count_array_one, count_array_two]
  have hn0 : ¬ 18 < n0.val := by omega
  have hn1 : ¬ 18 < n1.val := by omega
  have hn2 : ¬ 18 < n2.val := by omega
  let sum01 := Std.Usize.wrapping_add n0 n1
  let sum012 := Std.Usize.wrapping_add sum01 n2
  let scaled := Std.Usize.wrapping_mul 4#usize sum012
  let rows := Std.Usize.wrapping_add 40#usize scaled
  refine ⟨rows, ?_, ?_⟩
  · simp [hn0, hn1, hn2, Std.lift, sum01, sum012, scaled, rows]
  · have hSize01 : n0.val + n1.val < Std.Usize.size := by
      cases System.Platform.numBits_eq <;>
        simp_all [Usize.size, Usize.numBits] <;> omega
    have hSum01 : sum01.val = n0.val + n1.val := by
      exact usize_small_add_val n0 n1 hSize01
    have hSize012 : sum01.val + n2.val < Std.Usize.size := by
      rw [hSum01]
      cases System.Platform.numBits_eq <;>
        simp_all [Usize.size, Usize.numBits] <;> omega
    have hSum012 : sum012.val = n0.val + n1.val + n2.val := by
      rw [show sum012 = Std.Usize.wrapping_add sum01 n2 from rfl,
        usize_small_add_val sum01 n2 hSize012, hSum01]
    have hScaledSize : 4 * sum012.val < Std.Usize.size := by
      rw [hSum012]
      cases System.Platform.numBits_eq <;>
        simp_all [Usize.size, Usize.numBits] <;> omega
    have hScaled : scaled.val = 4 * (n0.val + n1.val + n2.val) := by
      rw [show scaled = Std.Usize.wrapping_mul 4#usize sum012 from rfl,
        usize_small_mul_val 4#usize sum012 (by simpa using hScaledSize),
        hSum012]
      norm_num
    have hRowsSize : 40 + scaled.val < Std.Usize.size := by
      rw [hScaled]
      cases System.Platform.numBits_eq <;>
        simp_all [Usize.size, Usize.numBits] <;> omega
    rw [show rows = Std.Usize.wrapping_add 40#usize scaled from rfl,
      usize_small_add_val 40#usize scaled (by simpa using hRowsSize), hScaled]
    norm_num

#print axioms generated_runtime_rows_exact

/-- Every generated row below 36 is decoded as one of the four relation
rounds, with exact quotient/remainder order (`round = row/9`, `slot = row%9`). -/
theorem generated_relation_row_exact
    (laterValueCounts : Array Std.Usize 3#usize) (row : Std.Usize)
    (hrow : row.val < 36) :
    ∃ round slot,
      v5_mask.component_c_runtime.component_c_runtime_downstream_row
          laterValueCounts row =
        ok (some (v5_mask.component_c_runtime.V5ComponentCRuntimeRow.Relation
          round slot)) ∧
      round.val = row.val / 9 ∧ slot.val = row.val % 9 := by
  have hRowScalar : row < 36#usize := by scalar_tac
  obtain ⟨quotient, hDiv, hQuotient⟩ := Aeneas.Std.WP.spec_imp_exists
    (Std.Usize.div_spec row (y := 9#usize) (by norm_num))
  obtain ⟨remainder, hRem, hRemainder⟩ := Aeneas.Std.WP.spec_imp_exists
    (Std.Usize.rem_spec row (y := 9#usize) (by norm_num))
  let round := UScalar.cast .U8 quotient
  let slot := UScalar.cast .U8 remainder
  refine ⟨round, slot, ?_, ?_, ?_⟩
  · unfold v5_mask.component_c_runtime.component_c_runtime_downstream_row
    simp [hRowScalar, hDiv, hRem, Std.lift, round, slot]
  · rw [show round.val = (UScalar.cast .U8 quotient).val from rfl,
      UScalar.cast_val_eq, hQuotient]
    apply Nat.mod_eq_of_lt
    norm_num [UScalar.size, U8.size]
    omega
  · rw [show slot.val = (UScalar.cast .U8 remainder).val from rfl,
      UScalar.cast_val_eq, hRemainder]
    apply Nat.mod_eq_of_lt
    norm_num [UScalar.size, U8.size]
    omega

#print axioms generated_relation_row_exact

/-- The first dynamic later segment begins exactly at row 36 and preserves
the runtime vector's supplied order. -/
theorem generated_later_zero_row_exact
    (n0 n1 n2 row index : Std.Usize)
    (hrow : row.val = 36 + index.val) (hindex : index.val < n0.val) :
    ∃ generatedIndex,
      v5_mask.component_c_runtime.component_c_runtime_downstream_row
          (Array.make 3#usize [n0, n1, n2]) row =
        ok (some (v5_mask.component_c_runtime.V5ComponentCRuntimeRow.Later
          0#u8 generatedIndex)) ∧
      generatedIndex.val = index.val := by
  have hNotRelation : ¬ row < 36#usize := by scalar_tac
  let tail := Std.Usize.wrapping_sub row 36#usize
  have hTail : tail.val = index.val := by
    rw [show tail = Std.Usize.wrapping_sub row 36#usize from rfl,
      usize_wrapping_sub_exact row 36#usize (by scalar_tac), hrow]
    norm_num
  have hTailLt : tail < n0 := by scalar_tac
  refine ⟨tail, ?_, hTail⟩
  unfold v5_mask.component_c_runtime.component_c_runtime_downstream_row
  rw [if_neg hNotRelation]
  simp only [Std.lift, bind_tc_ok]
  rw [count_array_zero]
  simp only [bind_tc_ok]
  have hRawTailLt : Std.Usize.wrapping_sub row 36#usize < n0 := by
    simpa [tail] using hTailLt
  rw [if_pos hRawTailLt]

#print axioms generated_later_zero_row_exact

/-- The second dynamic later segment begins immediately after the first and
preserves its supplied order for arbitrary runtime lengths. -/
theorem generated_later_one_row_exact
    (n0 n1 n2 row index : Std.Usize)
    (hrow : row.val = 36 + n0.val + index.val)
    (hindex : index.val < n1.val) :
    ∃ generatedIndex,
      v5_mask.component_c_runtime.component_c_runtime_downstream_row
          (Array.make 3#usize [n0, n1, n2]) row =
        ok (some (v5_mask.component_c_runtime.V5ComponentCRuntimeRow.Later
          1#u8 generatedIndex)) ∧
      generatedIndex.val = index.val := by
  have hNotRelation : ¬ row < 36#usize := by scalar_tac
  let tail0 := Std.Usize.wrapping_sub row 36#usize
  have hTail0 : tail0.val = n0.val + index.val := by
    rw [show tail0 = Std.Usize.wrapping_sub row 36#usize from rfl,
      usize_wrapping_sub_exact row 36#usize (by scalar_tac), hrow]
    norm_num
    omega
  have hTail0NotLt : ¬ tail0 < n0 := by scalar_tac
  let tail1 := Std.Usize.wrapping_sub tail0 n0
  have hTail1 : tail1.val = index.val := by
    rw [show tail1 = Std.Usize.wrapping_sub tail0 n0 from rfl,
      usize_wrapping_sub_exact tail0 n0 (by scalar_tac), hTail0]
    omega
  have hTail1Lt : tail1 < n1 := by scalar_tac
  refine ⟨tail1, ?_, hTail1⟩
  unfold v5_mask.component_c_runtime.component_c_runtime_downstream_row
  rw [if_neg hNotRelation]
  simp only [Std.lift, bind_tc_ok]
  rw [count_array_zero]
  simp only [bind_tc_ok]
  have hRawTail0NotLt :
      ¬ Std.Usize.wrapping_sub row 36#usize < n0 := by
    simpa [tail0] using hTail0NotLt
  rw [if_neg hRawTail0NotLt]
  rw [count_array_one]
  simp only [bind_tc_ok]
  have hRawTail1Lt :
      Std.Usize.wrapping_sub (Std.Usize.wrapping_sub row 36#usize) n0 < n1 := by
    simpa [tail0, tail1] using hTail1Lt
  rw [if_pos hRawTail1Lt]

#print axioms generated_later_one_row_exact

/-- The third dynamic later segment begins immediately after the first two and
preserves its supplied order for arbitrary runtime lengths. -/
theorem generated_later_two_row_exact
    (n0 n1 n2 row index : Std.Usize)
    (hrow : row.val = 36 + n0.val + n1.val + index.val)
    (hindex : index.val < n2.val) :
    ∃ generatedIndex,
      v5_mask.component_c_runtime.component_c_runtime_downstream_row
          (Array.make 3#usize [n0, n1, n2]) row =
        ok (some (v5_mask.component_c_runtime.V5ComponentCRuntimeRow.Later
          2#u8 generatedIndex)) ∧
      generatedIndex.val = index.val := by
  have hNotRelation : ¬ row < 36#usize := by scalar_tac
  let tail0 := Std.Usize.wrapping_sub row 36#usize
  have hTail0 : tail0.val = n0.val + n1.val + index.val := by
    rw [show tail0 = Std.Usize.wrapping_sub row 36#usize from rfl,
      usize_wrapping_sub_exact row 36#usize (by scalar_tac), hrow]
    norm_num
    omega
  have hTail0NotLt : ¬ tail0 < n0 := by scalar_tac
  let tail1 := Std.Usize.wrapping_sub tail0 n0
  have hTail1 : tail1.val = n1.val + index.val := by
    rw [show tail1 = Std.Usize.wrapping_sub tail0 n0 from rfl,
      usize_wrapping_sub_exact tail0 n0 (by scalar_tac), hTail0]
    omega
  have hTail1NotLt : ¬ tail1 < n1 := by scalar_tac
  let tail2 := Std.Usize.wrapping_sub tail1 n1
  have hTail2 : tail2.val = index.val := by
    rw [show tail2 = Std.Usize.wrapping_sub tail1 n1 from rfl,
      usize_wrapping_sub_exact tail1 n1 (by scalar_tac), hTail1]
    omega
  have hTail2Lt : tail2 < n2 := by scalar_tac
  refine ⟨tail2, ?_, hTail2⟩
  unfold v5_mask.component_c_runtime.component_c_runtime_downstream_row
  rw [if_neg hNotRelation]
  simp only [Std.lift, bind_tc_ok]
  rw [count_array_zero]
  simp only [bind_tc_ok]
  have hRawTail0NotLt :
      ¬ Std.Usize.wrapping_sub row 36#usize < n0 := by
    simpa [tail0] using hTail0NotLt
  rw [if_neg hRawTail0NotLt]
  rw [count_array_one]
  simp only [bind_tc_ok]
  have hRawTail1NotLt :
      ¬ Std.Usize.wrapping_sub
          (Std.Usize.wrapping_sub row 36#usize) n0 < n1 := by
    simpa [tail0, tail1] using hTail1NotLt
  rw [if_neg hRawTail1NotLt]
  rw [count_array_two]
  simp only [bind_tc_ok]
  have hRawTail2Lt :
      Std.Usize.wrapping_sub
          (Std.Usize.wrapping_sub
            (Std.Usize.wrapping_sub row 36#usize) n0) n1 < n2 := by
    simpa [tail0, tail1, tail2] using hTail2Lt
  rw [if_pos hRawTail2Lt]

#print axioms generated_later_two_row_exact

/-- The four final coefficients form the exact suffix after all three dynamic
later segments. -/
theorem generated_final_row_exact
    (n0 n1 n2 row coefficient : Std.Usize)
    (hrow : row.val = 36 + n0.val + n1.val + n2.val + coefficient.val)
    (hcoefficient : coefficient.val < 4) :
    ∃ generatedCoefficient,
      v5_mask.component_c_runtime.component_c_runtime_downstream_row
          (Array.make 3#usize [n0, n1, n2]) row =
        ok (some (v5_mask.component_c_runtime.V5ComponentCRuntimeRow.Final
          generatedCoefficient)) ∧
      generatedCoefficient.val = coefficient.val := by
  have hNotRelation : ¬ row < 36#usize := by scalar_tac
  let tail0 := Std.Usize.wrapping_sub row 36#usize
  have hTail0 : tail0.val = n0.val + n1.val + n2.val + coefficient.val := by
    rw [show tail0 = Std.Usize.wrapping_sub row 36#usize from rfl,
      usize_wrapping_sub_exact row 36#usize (by scalar_tac), hrow]
    norm_num
    omega
  have hTail0NotLt : ¬ tail0 < n0 := by scalar_tac
  let tail1 := Std.Usize.wrapping_sub tail0 n0
  have hTail1 : tail1.val = n1.val + n2.val + coefficient.val := by
    rw [show tail1 = Std.Usize.wrapping_sub tail0 n0 from rfl,
      usize_wrapping_sub_exact tail0 n0 (by scalar_tac), hTail0]
    omega
  have hTail1NotLt : ¬ tail1 < n1 := by scalar_tac
  let tail2 := Std.Usize.wrapping_sub tail1 n1
  have hTail2 : tail2.val = n2.val + coefficient.val := by
    rw [show tail2 = Std.Usize.wrapping_sub tail1 n1 from rfl,
      usize_wrapping_sub_exact tail1 n1 (by scalar_tac), hTail1]
    omega
  have hTail2NotLt : ¬ tail2 < n2 := by scalar_tac
  let tail3 := Std.Usize.wrapping_sub tail2 n2
  have hTail3 : tail3.val = coefficient.val := by
    rw [show tail3 = Std.Usize.wrapping_sub tail2 n2 from rfl,
      usize_wrapping_sub_exact tail2 n2 (by scalar_tac), hTail2]
    omega
  have hTail3Lt : tail3 < 4#usize := by scalar_tac
  let generatedCoefficient := UScalar.cast .U8 tail3
  have hGeneratedCoefficient :
      generatedCoefficient.val = coefficient.val := by
    rw [show generatedCoefficient.val = (UScalar.cast .U8 tail3).val from rfl,
      UScalar.cast_val_eq, hTail3]
    apply Nat.mod_eq_of_lt
    norm_num [UScalar.size, U8.size]
    omega
  refine ⟨generatedCoefficient, ?_, hGeneratedCoefficient⟩
  unfold v5_mask.component_c_runtime.component_c_runtime_downstream_row
  rw [if_neg hNotRelation]
  simp only [Std.lift, bind_tc_ok]
  rw [count_array_zero]
  simp only [bind_tc_ok]
  have hRawTail0NotLt :
      ¬ Std.Usize.wrapping_sub row 36#usize < n0 := by
    simpa [tail0] using hTail0NotLt
  rw [if_neg hRawTail0NotLt]
  rw [count_array_one]
  simp only [bind_tc_ok]
  have hRawTail1NotLt :
      ¬ Std.Usize.wrapping_sub
          (Std.Usize.wrapping_sub row 36#usize) n0 < n1 := by
    simpa [tail0, tail1] using hTail1NotLt
  rw [if_neg hRawTail1NotLt]
  rw [count_array_two]
  simp only [bind_tc_ok]
  have hRawTail2NotLt :
      ¬ Std.Usize.wrapping_sub
          (Std.Usize.wrapping_sub
            (Std.Usize.wrapping_sub row 36#usize) n0) n1 < n2 := by
    simpa [tail0, tail1, tail2] using hTail2NotLt
  rw [if_neg hRawTail2NotLt]
  have hRawTail3Lt :
      Std.Usize.wrapping_sub
          (Std.Usize.wrapping_sub
            (Std.Usize.wrapping_sub
              (Std.Usize.wrapping_sub row 36#usize) n0) n1) n2 < 4#usize := by
    simpa [tail0, tail1, tail2, tail3] using hTail3Lt
  rw [if_pos hRawTail3Lt]

#print axioms generated_final_row_exact

/-- Once the source-authentic row decoder selects an OOD relation tag, the
generated value dispatcher reads exactly that round and sample. -/
theorem generated_relation_ood_value_exact
    (oodValues : Array (Array aspis_core.field.QM31 2#usize) 4#usize)
    (polynomials : Array (Array aspis_core.field.QM31 7#usize) 4#usize)
    (later : Array (alloc.vec.Vec aspis_core.field.QM31) 3#usize)
    (finalCoefficients : Array aspis_core.field.QM31 4#usize)
    (row : Std.Usize) (round slot : Std.U8)
    (htag :
      v5_mask.component_c_runtime.component_c_runtime_downstream_row
        (Array.make 3#usize
          [alloc.vec.Vec.len later.val[(0#usize).val]!,
            alloc.vec.Vec.len later.val[(1#usize).val]!,
            alloc.vec.Vec.len later.val[(2#usize).val]!]) row =
        ok (some (v5_mask.component_c_runtime.V5ComponentCRuntimeRow.Relation
          round slot)))
    (hround : round.val < 4) (hslot : slot.val < 2) :
    v5_mask.component_c_runtime.component_c_runtime_downstream_value_at
        oodValues polynomials later finalCoefficients row =
      ok (some oodValues.val[round.val]!.val[slot.val]!) := by
  have hlater0 := generated_array_index_run later 0#usize (by norm_num)
  have hlater1 := generated_array_index_run later 1#usize (by norm_num)
  have hlater2 := generated_array_index_run later 2#usize (by norm_num)
  let roundIndex := core.convert.num.FromUsizeU8.from round
  let slotIndex := core.convert.num.FromUsizeU8.from slot
  have hroundIndex : roundIndex.val = round.val := by
    exact core.convert.num.FromUsizeU8.from_val_eq round
  have hslotIndex : slotIndex.val = slot.val := by
    exact core.convert.num.FromUsizeU8.from_val_eq slot
  have hoodRound := generated_array_index_run oodValues roundIndex (by
    rw [hroundIndex]
    exact hround)
  have hoodSlot := generated_array_index_run
    oodValues.val[round.val]! slotIndex (by
      rw [hslotIndex]
      exact hslot)
  unfold v5_mask.component_c_runtime.component_c_runtime_downstream_value_at
  rw [hlater0, hlater1, hlater2]
  simp only [bind_tc_ok]
  rw [htag]
  simp only [bind_tc_ok]
  change (do
      let round1 ← lift roundIndex
      let slot1 ← lift slotIndex
      if slot1 < 2#usize then
        let a ← Array.index_usize oodValues round1
        let q ← Array.index_usize a slot1
        ok (some q)
      else _ ) = _
  simp only [Std.lift, bind_tc_ok]
  have hslotScalar : slotIndex < 2#usize := by scalar_tac
  rw [if_pos hslotScalar, hoodRound]
  simp only [bind_tc_ok]
  rw [show oodValues.val[roundIndex.val]! =
      oodValues.val[round.val]! by rw [hroundIndex]]
  rw [hoodSlot]
  simp [hslotIndex]

#print axioms generated_relation_ood_value_exact

/-- Polynomial relation tags dispatch to the same round and to degree
`slot-2`, after the two OOD coordinates. -/
theorem generated_relation_polynomial_value_exact
    (oodValues : Array (Array aspis_core.field.QM31 2#usize) 4#usize)
    (polynomials : Array (Array aspis_core.field.QM31 7#usize) 4#usize)
    (later : Array (alloc.vec.Vec aspis_core.field.QM31) 3#usize)
    (finalCoefficients : Array aspis_core.field.QM31 4#usize)
    (row : Std.Usize) (round slot : Std.U8)
    (htag :
      v5_mask.component_c_runtime.component_c_runtime_downstream_row
        (Array.make 3#usize
          [alloc.vec.Vec.len later.val[(0#usize).val]!,
            alloc.vec.Vec.len later.val[(1#usize).val]!,
            alloc.vec.Vec.len later.val[(2#usize).val]!]) row =
        ok (some (v5_mask.component_c_runtime.V5ComponentCRuntimeRow.Relation
          round slot)))
    (hround : round.val < 4) (hslotLow : 2 ≤ slot.val)
    (hslotHigh : slot.val < 9) :
    v5_mask.component_c_runtime.component_c_runtime_downstream_value_at
        oodValues polynomials later finalCoefficients row =
      ok (some polynomials.val[round.val]!.val[slot.val - 2]!) := by
  have hlater0 := generated_array_index_run later 0#usize (by norm_num)
  have hlater1 := generated_array_index_run later 1#usize (by norm_num)
  have hlater2 := generated_array_index_run later 2#usize (by norm_num)
  let roundIndex := core.convert.num.FromUsizeU8.from round
  let slotIndex := core.convert.num.FromUsizeU8.from slot
  have hroundIndex : roundIndex.val = round.val := by
    exact core.convert.num.FromUsizeU8.from_val_eq round
  have hslotIndex : slotIndex.val = slot.val := by
    exact core.convert.num.FromUsizeU8.from_val_eq slot
  let degreeIndex := Std.Usize.wrapping_sub slotIndex 2#usize
  have hdegreeIndex : degreeIndex.val = slot.val - 2 := by
    rw [show degreeIndex = Std.Usize.wrapping_sub slotIndex 2#usize from rfl,
      usize_wrapping_sub_exact slotIndex 2#usize (by scalar_tac), hslotIndex]
    norm_num
  have hpolyRound := generated_array_index_run polynomials roundIndex (by
    rw [hroundIndex]
    exact hround)
  have hpolyDegree := generated_array_index_run
    polynomials.val[round.val]! degreeIndex (by
      rw [hdegreeIndex]
      norm_num
      omega)
  unfold v5_mask.component_c_runtime.component_c_runtime_downstream_value_at
  rw [hlater0, hlater1, hlater2]
  simp only [bind_tc_ok]
  rw [htag]
  simp only [bind_tc_ok]
  change (do
      let round1 ← lift roundIndex
      let slot1 ← lift slotIndex
      if slot1 < 2#usize then _ else
        let degree ← lift degreeIndex
        let a ← Array.index_usize polynomials round1
        let q ← Array.index_usize a degree
        ok (some q)) = _
  simp only [Std.lift, bind_tc_ok]
  have hslotScalar : ¬ slotIndex < 2#usize := by scalar_tac
  rw [if_neg hslotScalar, hpolyRound]
  simp only [bind_tc_ok]
  rw [show polynomials.val[roundIndex.val]! =
      polynomials.val[round.val]! by rw [hroundIndex]]
  rw [hpolyDegree]
  simp [hdegreeIndex]

#print axioms generated_relation_polynomial_value_exact

/-- Dynamic later tags dispatch to the selected layer and retain the supplied
deduplicated vector index exactly. -/
theorem generated_later_value_exact
    (oodValues : Array (Array aspis_core.field.QM31 2#usize) 4#usize)
    (polynomials : Array (Array aspis_core.field.QM31 7#usize) 4#usize)
    (later : Array (alloc.vec.Vec aspis_core.field.QM31) 3#usize)
    (finalCoefficients : Array aspis_core.field.QM31 4#usize)
    (row : Std.Usize) (layer : Std.U8) (index : Std.Usize)
    (htag :
      v5_mask.component_c_runtime.component_c_runtime_downstream_row
        (Array.make 3#usize
          [alloc.vec.Vec.len later.val[(0#usize).val]!,
            alloc.vec.Vec.len later.val[(1#usize).val]!,
            alloc.vec.Vec.len later.val[(2#usize).val]!]) row =
        ok (some (v5_mask.component_c_runtime.V5ComponentCRuntimeRow.Later
          layer index)))
    (hlayer : layer.val < 3)
    (hindex : index.val < later.val[layer.val]!.val.length) :
    v5_mask.component_c_runtime.component_c_runtime_downstream_value_at
        oodValues polynomials later finalCoefficients row =
      ok (some later.val[layer.val]!.val[index.val]!) := by
  have hlater0 := generated_array_index_run later 0#usize (by norm_num)
  have hlater1 := generated_array_index_run later 1#usize (by norm_num)
  have hlater2 := generated_array_index_run later 2#usize (by norm_num)
  let layerIndex := core.convert.num.FromUsizeU8.from layer
  have hlayerIndex : layerIndex.val = layer.val := by
    exact core.convert.num.FromUsizeU8.from_val_eq layer
  have hlayerRead := generated_array_index_run later layerIndex (by
    rw [hlayerIndex]
    exact hlayer)
  have hvalueRead := generated_vec_index_run later.val[layer.val]! index hindex
  unfold v5_mask.component_c_runtime.component_c_runtime_downstream_value_at
  rw [hlater0, hlater1, hlater2]
  simp only [bind_tc_ok]
  rw [htag]
  simp only [bind_tc_ok]
  change (do
      let layer1 ← lift layerIndex
      let values ← Array.index_usize later layer1
      let q ← alloc.vec.Vec.index
        (core.slice.index.SliceIndexUsizeSlice aspis_core.field.QM31)
        values index
      ok (some q)) = _
  simp only [Std.lift, bind_tc_ok]
  rw [hlayerRead]
  simp only [bind_tc_ok]
  rw [show later.val[layerIndex.val]! = later.val[layer.val]! by
    rw [hlayerIndex]]
  rw [hvalueRead]
  simp

#print axioms generated_later_value_exact

/-- Final tags dispatch to the same terminal coefficient. -/
theorem generated_final_value_exact
    (oodValues : Array (Array aspis_core.field.QM31 2#usize) 4#usize)
    (polynomials : Array (Array aspis_core.field.QM31 7#usize) 4#usize)
    (later : Array (alloc.vec.Vec aspis_core.field.QM31) 3#usize)
    (finalCoefficients : Array aspis_core.field.QM31 4#usize)
    (row : Std.Usize) (coefficient : Std.U8)
    (htag :
      v5_mask.component_c_runtime.component_c_runtime_downstream_row
        (Array.make 3#usize
          [alloc.vec.Vec.len later.val[(0#usize).val]!,
            alloc.vec.Vec.len later.val[(1#usize).val]!,
            alloc.vec.Vec.len later.val[(2#usize).val]!]) row =
        ok (some (v5_mask.component_c_runtime.V5ComponentCRuntimeRow.Final
          coefficient)))
    (hcoefficient : coefficient.val < 4) :
    v5_mask.component_c_runtime.component_c_runtime_downstream_value_at
        oodValues polynomials later finalCoefficients row =
      ok (some finalCoefficients.val[coefficient.val]!) := by
  have hlater0 := generated_array_index_run later 0#usize (by norm_num)
  have hlater1 := generated_array_index_run later 1#usize (by norm_num)
  have hlater2 := generated_array_index_run later 2#usize (by norm_num)
  let coefficientIndex := core.convert.num.FromUsizeU8.from coefficient
  have hcoefficientIndex : coefficientIndex.val = coefficient.val := by
    exact core.convert.num.FromUsizeU8.from_val_eq coefficient
  have hread := generated_array_index_run finalCoefficients coefficientIndex (by
    rw [hcoefficientIndex]
    exact hcoefficient)
  unfold v5_mask.component_c_runtime.component_c_runtime_downstream_value_at
  rw [hlater0, hlater1, hlater2]
  simp only [bind_tc_ok]
  rw [htag]
  simp only [bind_tc_ok]
  change (do
      let index ← lift coefficientIndex
      let q ← Array.index_usize finalCoefficients index
      ok (some q)) = _
  simp only [Std.lift, bind_tc_ok]
  rw [hread]
  simp [hcoefficientIndex]

#print axioms generated_final_value_exact

/-- One generated pack-loop step consumes exactly the current row, appends
exactly that value, and increments the row by one.  This rules out a hidden
permutation inside the packer loop. -/
theorem generated_pack_loop_body_exact_step
    (oodValues : Array (Array aspis_core.field.QM31 2#usize) 4#usize)
    (polynomials : Array (Array aspis_core.field.QM31 7#usize) 4#usize)
    (later : Array (alloc.vec.Vec aspis_core.field.QM31) 3#usize)
    (finalCoefficients : Array aspis_core.field.QM31 4#usize)
    (rows row : Std.Usize) (output : alloc.vec.Vec aspis_core.field.QM31)
    (value : aspis_core.field.QM31)
    (hrow : row < rows)
    (hvalue :
      v5_mask.component_c_runtime.component_c_runtime_downstream_value_at
        oodValues polynomials later finalCoefficients row = ok (some value))
    (hcapacity : output.val.length < Std.Usize.max)
    (hrowMax : row.val < Std.Usize.max) :
    ∃ outputAfter rowAfter,
      v5_mask.component_c_runtime.pack_component_c_runtime_downstream_loop.body
          oodValues polynomials later finalCoefficients rows output row =
        ok (cont (outputAfter, rowAfter)) ∧
      outputAfter.val = output.val ++ [value] ∧
      rowAfter.val = row.val + 1 := by
  obtain ⟨outputAfter, hpush, houtputAfter⟩ := Aeneas.Std.WP.spec_imp_exists
    (alloc.vec.Vec.push_spec output value hcapacity)
  let rowAfter := Std.Usize.wrapping_add row 1#usize
  have hrowAfter : rowAfter.val = row.val + 1 := by
    exact usize_small_add_val row 1#usize (by
      norm_num
      have hsize : Std.Usize.size = Std.Usize.max + 1 := by
        simp [Std.Usize.size, Std.Usize.max, Std.Usize.numBits]
      rw [hsize]
      omega)
  refine ⟨outputAfter, rowAfter, ?_, houtputAfter, hrowAfter⟩
  unfold v5_mask.component_c_runtime.pack_component_c_runtime_downstream_loop.body
  rw [if_pos hrow, hvalue]
  simp only [bind_tc_ok]
  rw [hpush]
  simp [Std.lift, rowAfter]

#print axioms generated_pack_loop_body_exact_step

/-- Concrete dedup tooth from the shared query-derivation test: `[4,3,2]`
produces 76 rows and cannot be confused with the old frozen 256-row layout. -/
theorem generated_runtime_dedup_shape_is_not_frozen :
    ∃ rows,
      v5_mask.component_c_runtime.component_c_runtime_downstream_rows
          (Array.make 3#usize [4#usize, 3#usize, 2#usize]) =
        ok (some rows) ∧ rows.val = 76 ∧ rows.val ≠ 256 := by
  obtain ⟨rows, hrun, hrows⟩ := generated_runtime_rows_exact
    4#usize 3#usize 2#usize (by norm_num) (by norm_num) (by norm_num)
  have hrows76 : rows.val = 76 := by
    norm_num at hrows ⊢
    exact hrows
  refine ⟨rows, hrun, hrows76, by omega⟩

#print axioms generated_runtime_dedup_shape_is_not_frozen

end aspis_prover.ComponentCRuntimePackerProof
