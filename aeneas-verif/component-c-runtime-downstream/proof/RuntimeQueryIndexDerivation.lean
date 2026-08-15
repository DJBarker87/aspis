import RuntimeSchedule

open Aeneas Aeneas.Std Result ControlFlow Error
open aspis_core

/-!
# Exact later-index derivation from the extracted Rust loop

The production helper scans a sorted layer-zero index list, shifts each value,
and drops a value when it is equal to the last value already returned.  This
file proves that behavior directly about the Charon/Aeneas translation.  It
also proves that the three released shifts are exact division by 4, 16, and
64.  No production source is changed.
-/

namespace RuntimeIndexProof

def appendIfDifferent (values : List Std.U32) (value : Std.U32) :
    List Std.U32 :=
  if values.length = 0 then [value]
  else if values[values.length - 1]! != value then values ++ [value]
  else values

def shiftedUnique (values : List Std.U32) (shift : Std.U32) :
    List Std.U32 :=
  values.foldl (fun result value =>
    appendIfDifferent result (Std.U32.wrapping_shr value shift)) []

theorem u32_wrapping_shr_val_of_lt (value shift : Std.U32)
    (hshift : shift.val < 32) :
    (Std.U32.wrapping_shr value shift).val =
      value.val / 2 ^ shift.val := by
  change value.bv.toNat >>> (shift.val % 32) = value.val / 2 ^ shift.val
  rw [Nat.mod_eq_of_lt hshift]
  simp only [Std.U32.bv_toNat, Nat.shiftRight_eq_div_pow]

@[simp] theorem u32_wrapping_shr_two_val (value : Std.U32) :
    (Std.U32.wrapping_shr value 2#u32).val = value.val / 4 := by
  simpa using u32_wrapping_shr_val_of_lt value 2#u32 (by norm_num)

@[simp] theorem u32_wrapping_shr_four_val (value : Std.U32) :
    (Std.U32.wrapping_shr value 4#u32).val = value.val / 16 := by
  simpa using u32_wrapping_shr_val_of_lt value 4#u32 (by norm_num)

@[simp] theorem u32_wrapping_shr_six_val (value : Std.U32) :
    (Std.U32.wrapping_shr value 6#u32).val = value.val / 64 := by
  simpa using u32_wrapping_shr_val_of_lt value 6#u32 (by norm_num)

theorem appendIfDifferent_length_le_succ
    (values : List Std.U32) (value : Std.U32) :
    (appendIfDifferent values value).length ≤ values.length + 1 := by
  unfold appendIfDifferent
  by_cases hzero : values.length = 0
  · simp [hzero]
  · rw [if_neg hzero]
    split <;> simp

theorem shiftedFold_length_le (values acc : List Std.U32)
    (shift : Std.U32) :
    (values.foldl (fun result value =>
      appendIfDifferent result (Std.U32.wrapping_shr value shift)) acc).length ≤
        acc.length + values.length := by
  induction values generalizing acc with
  | nil => simp
  | cons head tail ih =>
      simp only [List.foldl_cons, List.length_cons]
      calc
        _ ≤ (appendIfDifferent acc
              (Std.U32.wrapping_shr head shift)).length + tail.length :=
          ih _
        _ ≤ (acc.length + 1) + tail.length :=
          Nat.add_le_add_right (appendIfDifferent_length_le_succ acc _) _
        _ = acc.length + (tail.length + 1) := by omega

theorem shiftedUnique_length_le (values : List Std.U32) (shift : Std.U32) :
    (shiftedUnique values shift).length ≤ values.length := by
  simpa [shiftedUnique] using shiftedFold_length_le values [] shift

theorem shiftedUnique_take_succ (values : List Std.U32) (shift : Std.U32)
    {index : Nat} (hindex : index < values.length) :
    shiftedUnique (values.take (index + 1)) shift =
      appendIfDifferent (shiftedUnique (values.take index) shift)
        (Std.U32.wrapping_shr values[index] shift) := by
  have htake := List.take_append_getElem hindex
  unfold shiftedUnique
  rw [← htake, List.foldl_append]
  rfl

private theorem wrapping_succ_exact
    {T : Type} (values : Slice T) (index : Std.Usize)
    (hindex : index.val < values.val.length) :
    (Std.Usize.wrapping_add index 1#usize).val = index.val + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  apply Nat.mod_eq_of_lt
  have hlength := Slice.length_ineq values
  change index.val + 1 < UScalar.size .Usize
  rw [UScalar.size_UScalarTyUsize]
  have hsize := Usize.size_scalarTac_eq
  omega

private theorem wrapping_pred_exact (index : Std.Usize)
    (hpositive : 0 < index.val) :
    (Std.Usize.wrapping_sub index 1#usize).val = index.val - 1 := by
  rw [Std.Usize.wrapping_sub_val_eq]
  have hone : (1#usize : Std.Usize).val = 1 := by rfl
  rw [hone]
  have hindex := index.hSize
  have hrearrange :
      index.val + (UScalar.size .Usize - 1) =
        (index.val - 1) + UScalar.size .Usize := by omega
  rw [hrearrange, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

private theorem sorted_unique_shifted_loop_exact
    (indices : Slice Std.U32) (shift : Std.U32)
    (result : alloc.vec.Vec Std.U32) (index : Std.Usize)
    (hindex : index.val ≤ indices.val.length)
    (hresult : result.val = shiftedUnique (indices.val.take index.val) shift) :
    aspis_core.circle_line_merkle.sorted_unique_shifted_loop
      indices shift result index ⦃ output =>
        output.val = shiftedUnique indices.val shift ⦄ := by
  simp only [aspis_core.circle_line_merkle.sorted_unique_shifted_loop]
  apply loop.spec_decr_nat
    (fun state : alloc.vec.Vec Std.U32 × Std.Usize =>
      indices.val.length - state.2.val)
    (fun state =>
      state.2.val ≤ indices.val.length ∧
        state.1.val = shiftedUnique (indices.val.take state.2.val) shift)
    (fun output : alloc.vec.Vec Std.U32 =>
      output.val = shiftedUnique indices.val shift)
  · rintro ⟨current, currentIndex⟩ ⟨hcurrentBound, hcurrentPrefix⟩
    have hcurrentBound' : currentIndex.val ≤ indices.val.length := by
      simpa only using hcurrentBound
    have hcurrentPrefix' : current.val =
        shiftedUnique (indices.val.take currentIndex.val) shift := by
      simpa only using hcurrentPrefix
    unfold aspis_core.circle_line_merkle.sorted_unique_shifted_loop.body
    by_cases hactive : currentIndex.val < indices.val.length
    · have hactiveScalar : currentIndex < Slice.len indices := by scalar_tac
      rw [if_pos hactiveScalar]
      obtain ⟨inputValue, hread, hinputValue⟩ := WP.spec_imp_exists
        (Slice.index_usize_spec indices currentIndex hactive)
      rw [hread]
      simp only [bind_tc_ok, Std.lift]
      let shifted := Std.U32.wrapping_shr inputValue shift
      have hshifted : shifted =
          Std.U32.wrapping_shr indices.val[currentIndex.val] shift := by
        exact congrArg (fun value => Std.U32.wrapping_shr value shift)
          hinputValue
      by_cases hempty : current.val.length = 0
      · have hemptyScalar : alloc.vec.Vec.len current = 0#usize := by
          apply UScalar.eq_of_val_eq
          simpa using hempty
        rw [if_pos hemptyScalar]
        have hcapacity : current.val.length < Std.Usize.max := by
          have hmax : 0 < Std.Usize.max := by
            have h := (1#usize).hSize
            scalar_tac
          omega
        obtain ⟨next, hpush, hnextValues⟩ := WP.spec_imp_exists
          (alloc.vec.Vec.push_spec current shifted hcapacity)
        rw [hpush]
        simp only [bind_tc_ok]
        have hnextIndex := wrapping_succ_exact indices currentIndex hactive
        have hprefixEmpty :
            shiftedUnique (indices.val.take currentIndex.val) shift = [] := by
          apply List.eq_nil_of_length_eq_zero
          rw [← hcurrentPrefix']
          exact hempty
        simp only [WP.spec, WP.theta]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [hnextIndex]
          omega
        · rw [hnextValues, hcurrentPrefix', hnextIndex,
            shiftedUnique_take_succ indices.val shift hactive, hshifted]
          unfold appendIfDifferent
          simp [hprefixEmpty]
          rfl
        · rw [hnextIndex]
          omega
      · have hpositive : 0 < current.val.length := by omega
        have hnonemptyScalar : ¬ alloc.vec.Vec.len current = 0#usize := by
          intro hzero
          have hzeroVal := congrArg UScalar.val hzero
          simp only [alloc.vec.Vec.len_val] at hzeroVal
          exact hempty hzeroVal
        rw [if_neg hnonemptyScalar]
        let lastIndex := Std.Usize.wrapping_sub (alloc.vec.Vec.len current)
          1#usize
        have hlastIndex : lastIndex.val = current.val.length - 1 := by
          apply wrapping_pred_exact
          simpa [lastIndex] using hpositive
        have hlastBound : lastIndex.val < current.val.length := by
          rw [hlastIndex]
          omega
        have hprefixNonempty :
            (shiftedUnique (indices.val.take currentIndex.val) shift).length ≠
              0 := by
          rw [← hcurrentPrefix']
          exact hempty
        obtain ⟨lastValue, hlastRead, hlastValue⟩ := WP.spec_imp_exists
          (alloc.vec.Vec.index_usize_spec current lastIndex hlastBound)
        rw [alloc.vec.Vec.index_slice_index, hlastRead]
        simp only [bind_tc_ok]
        have hlastExact :
            current.val[current.val.length - 1]! = lastValue := by
          rw [← hlastIndex]
          apply List.getElem!_of_getElem?
          rw [List.getElem?_eq_getElem hlastBound]
          exact congrArg some hlastValue.symm
        have hmodelLast :
            (shiftedUnique (indices.val.take currentIndex.val) shift)[
              (shiftedUnique
                (indices.val.take currentIndex.val) shift).length - 1]! =
                lastValue := by
          rw [← hcurrentPrefix']
          exact hlastExact
        by_cases hdifferent : lastValue != shifted
        · rw [if_pos hdifferent]
          have hdifferent' :
              (lastValue != Std.U32.wrapping_shr
                indices.val[currentIndex.val] shift) = true := by
            simpa only [← hshifted] using hdifferent
          have hcurrentLength : current.val.length ≤ currentIndex.val := by
            rw [hcurrentPrefix']
            calc
              _ ≤ (indices.val.take currentIndex.val).length :=
                shiftedUnique_length_le _ _
              _ ≤ currentIndex.val := List.length_take_le _ _
          have hcapacity : current.val.length < Std.Usize.max := by
            have hsliceBound := Slice.length_ineq indices
            have hmax : indices.val.length ≤ Std.Usize.max := by
              simpa using hsliceBound
            omega
          obtain ⟨next, hpush, hnextValues⟩ := WP.spec_imp_exists
            (alloc.vec.Vec.push_spec current shifted hcapacity)
          rw [hpush]
          simp only [bind_tc_ok]
          have hnextIndex := wrapping_succ_exact indices currentIndex hactive
          simp only [WP.spec, WP.theta]
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · rw [hnextIndex]
            omega
          · rw [hnextValues, hcurrentPrefix', hnextIndex,
              shiftedUnique_take_succ indices.val shift hactive, hshifted]
            unfold appendIfDifferent
            rw [if_neg hprefixNonempty, hmodelLast]
            split
            · rfl
            · rename_i hnot
              exact False.elim (hnot hdifferent')
          · rw [hnextIndex]
            omega
        · rw [if_neg hdifferent]
          have hdifferent' :
              ¬(lastValue != Std.U32.wrapping_shr
                indices.val[currentIndex.val] shift) = true := by
            simpa only [← hshifted] using hdifferent
          have hnextIndex := wrapping_succ_exact indices currentIndex hactive
          simp only [WP.spec, WP.theta]
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · rw [hnextIndex]
            omega
          · rw [hcurrentPrefix', hnextIndex,
              shiftedUnique_take_succ indices.val shift hactive]
            unfold appendIfDifferent
            rw [if_neg hprefixNonempty, hmodelLast]
            split
            · rename_i hyes
              exact False.elim (hdifferent' hyes)
            · rfl
          · rw [hnextIndex]
            omega
    · rw [if_neg (show ¬ currentIndex < Slice.len indices by scalar_tac)]
      simp only [WP.spec, WP.theta, WP.wp_return]
      have hdone : currentIndex.val = indices.val.length := by
        omega
      calc
        current.val = shiftedUnique
            (indices.val.take currentIndex.val) shift := hcurrentPrefix'
        _ = shiftedUnique indices.val shift := by
          rw [hdone, List.take_length]
  · exact ⟨hindex, hresult⟩

theorem sorted_unique_shifted_exact
    (indices : Slice Std.U32) (shift : Std.U32) :
    aspis_core.circle_line_merkle.sorted_unique_shifted indices shift ⦃ output =>
      output.val = shiftedUnique indices.val shift ⦄ := by
  unfold aspis_core.circle_line_merkle.sorted_unique_shifted
  apply sorted_unique_shifted_loop_exact
  · norm_num
  · simp [alloc.vec.Vec.with_capacity, shiftedUnique]

#print axioms u32_wrapping_shr_val_of_lt
#print axioms sorted_unique_shifted_exact

end RuntimeIndexProof
