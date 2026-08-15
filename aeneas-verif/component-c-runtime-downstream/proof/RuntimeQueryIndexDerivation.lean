import RuntimeSchedule
import Mathlib.Data.List.Destutter
import Mathlib.Data.Finset.Sort

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

@[simp] theorem u32_wrapping_shr_zero (value : Std.U32) :
    Std.U32.wrapping_shr value 0#u32 = value := by
  apply UScalar.eq_of_val_eq
  simpa using u32_wrapping_shr_val_of_lt value 0#u32 (by norm_num)

@[simp] theorem u32_wrapping_shr_two_val (value : Std.U32) :
    (Std.U32.wrapping_shr value 2#u32).val = value.val / 4 := by
  simpa using u32_wrapping_shr_val_of_lt value 2#u32 (by norm_num)

@[simp] theorem u32_wrapping_shr_four_val (value : Std.U32) :
    (Std.U32.wrapping_shr value 4#u32).val = value.val / 16 := by
  simpa using u32_wrapping_shr_val_of_lt value 4#u32 (by norm_num)

@[simp] theorem u32_wrapping_shr_six_val (value : Std.U32) :
    (Std.U32.wrapping_shr value 6#u32).val = value.val / 64 := by
  simpa using u32_wrapping_shr_val_of_lt value 6#u32 (by norm_num)

/-! ## The scan is ordinary sorted-list deduplication -/

def appendDistinct {alpha : Type*} [DecidableEq alpha]
    (values : List alpha) (value : alpha) : List alpha :=
  match values.getLast? with
  | none => [value]
  | some last => if last ≠ value then values ++ [value] else values

private theorem appendDistinct_cons_cons {alpha : Type*} [DecidableEq alpha]
    (first second : alpha) (rest : List alpha) (value : alpha) :
    appendDistinct (first :: second :: rest) value =
      first :: appendDistinct (second :: rest) value := by
  unfold appendDistinct
  simp only [List.getLast?_cons, Option.getD_some]
  split <;> simp_all

private theorem destutter'_append_singleton
    {alpha : Type*} [DecidableEq alpha]
    (first : alpha) (rest : List alpha) (value : alpha) :
    List.destutter' (· ≠ ·) first (rest ++ [value]) =
      appendDistinct (List.destutter' (· ≠ ·) first rest) value := by
  induction rest generalizing first with
  | nil =>
      simp [List.destutter', appendDistinct]
  | cons head tail ih =>
      rw [List.cons_append]
      simp only [List.destutter']
      by_cases h : first ≠ head
      · rw [if_pos h, ih]
        have hne : List.destutter' (· ≠ ·) head tail ≠ [] :=
          List.destutter'_ne_nil tail (· ≠ ·) (a := head)
        cases hd : List.destutter' (· ≠ ·) head tail with
        | nil => exact False.elim (hne hd)
        | cons next more =>
            rw [if_pos h]
            exact (appendDistinct_cons_cons first next more value).symm
      · rw [if_neg h, ih]
        simp [h]

theorem destutter_append_singleton
    {alpha : Type*} [DecidableEq alpha]
    (values : List alpha) (value : alpha) :
    (values ++ [value]).destutter (· ≠ ·) =
      appendDistinct (values.destutter (· ≠ ·)) value := by
  cases values with
  | nil => simp [appendDistinct]
  | cons first rest =>
      change List.destutter' (· ≠ ·) first (rest ++ [value]) = _
      exact destutter'_append_singleton first rest value

theorem foldl_appendDistinct_eq_destutter
    {alpha : Type*} [DecidableEq alpha]
    (before remaining : List alpha) :
    remaining.foldl appendDistinct (before.destutter (· ≠ ·)) =
      (before ++ remaining).destutter (· ≠ ·) := by
  induction remaining generalizing before with
  | nil => simp
  | cons head tail ih =>
      simp only [List.foldl_cons]
      rw [← destutter_append_singleton before head]
      simpa [List.append_assoc] using ih (before ++ [head])

theorem foldl_appendDistinct_eq_dedup_of_pairwise
    {alpha : Type*} [DecidableEq alpha]
    {relation : alpha → alpha → Prop} [DecidableRel relation]
    [Std.Antisymm relation]
    (values : List alpha) (hsorted : values.Pairwise relation) :
    values.foldl appendDistinct [] = values.dedup := by
  rw [show ([] : List alpha) = [].destutter (· ≠ ·) by simp,
    foldl_appendDistinct_eq_destutter]
  simpa using hsorted.destutter_eq_dedup

theorem appendIfDifferent_eq_appendDistinct
    (values : List Std.U32) (value : Std.U32) :
    appendIfDifferent values value = appendDistinct values value := by
  cases values with
  | nil => simp [appendIfDifferent, appendDistinct]
  | cons head tail =>
      unfold appendIfDifferent appendDistinct
      simp only [List.length_cons, Nat.add_eq_zero_iff, one_ne_zero, and_false,
        ↓reduceIte, List.getLast?_eq_some_getLast (l := head :: tail) (by simp)]
      rw [List.getLast_eq_getElem]
      simp only [Nat.add_sub_cancel]
      by_cases heq : (head :: tail)[tail.length]! = value <;> simp

theorem shiftedUnique_eq_destutter
    (values : List Std.U32) (shift : Std.U32) :
    shiftedUnique values shift =
      (values.map (fun value => Std.U32.wrapping_shr value shift)).destutter
        (· ≠ ·) := by
  unfold shiftedUnique
  rw [← List.foldl_map]
  have happend :
      (appendIfDifferent : List Std.U32 → Std.U32 → List Std.U32) =
        appendDistinct := by
    funext current value
    exact appendIfDifferent_eq_appendDistinct current value
  rw [happend]
  simpa using
    (foldl_appendDistinct_eq_destutter ([] : List Std.U32)
      (values.map (fun value => Std.U32.wrapping_shr value shift)))

/-- When the shifted input is nondecreasing, the exact extracted scan is the
usual duplicate-free sorted list. -/
theorem shiftedUnique_eq_dedup_of_sorted_shifted
    (values : List Std.U32) (shift : Std.U32)
    (hsorted :
      (values.map (fun value => Std.U32.wrapping_shr value shift)).Pairwise
        (· ≤ ·)) :
    shiftedUnique values shift =
      (values.map (fun value => Std.U32.wrapping_shr value shift)).dedup := by
  rw [shiftedUnique_eq_destutter]
  exact hsorted.destutter_eq_dedup

theorem u32_wrapping_shr_mono
    (shift : Std.U32) (hshift : shift.val < 32)
    {left right : Std.U32} (hle : left ≤ right) :
    Std.U32.wrapping_shr left shift ≤
      Std.U32.wrapping_shr right shift := by
  change (Std.U32.wrapping_shr left shift).val ≤
    (Std.U32.wrapping_shr right shift).val
  rw [u32_wrapping_shr_val_of_lt left shift hshift,
    u32_wrapping_shr_val_of_lt right shift hshift]
  exact Nat.div_le_div_right hle

theorem shifted_values_pairwise
    (values : List Std.U32) (shift : Std.U32) (hshift : shift.val < 32)
    (hsorted : values.Pairwise (· ≤ ·)) :
    (values.map (fun value => Std.U32.wrapping_shr value shift)).Pairwise
      (· ≤ ·) := by
  exact hsorted.map _ (fun _ _ hle => u32_wrapping_shr_mono shift hshift hle)

/-- For sorted input and an in-range shift, the exact extracted scan is the
unique sorted list of shifted values.  This is the same list representation
used by the maintained finite-set model. -/
theorem shiftedUnique_eq_sorted_toFinset
    (values : List Std.U32) (shift : Std.U32) (hshift : shift.val < 32)
    (hsorted : values.Pairwise (· ≤ ·)) :
    shiftedUnique values shift =
      (values.map (fun value => Std.U32.wrapping_shr value shift)).toFinset.sort
        (· ≤ ·) := by
  let shiftedValues :=
    values.map (fun value => Std.U32.wrapping_shr value shift)
  have hpairwise : shiftedValues.Pairwise (· ≤ ·) :=
    shifted_values_pairwise values shift hshift hsorted
  have hdedupPairwise : shiftedValues.dedup.Pairwise (· ≤ ·) :=
    List.Pairwise.sublist (List.dedup_sublist shiftedValues) hpairwise
  have hsort : shiftedValues.dedup.toFinset.sort (· ≤ ·) =
      shiftedValues.dedup :=
    (List.toFinset_sort (· ≤ ·) (List.nodup_dedup shiftedValues)).2
      hdedupPairwise
  have hfinset : shiftedValues.dedup.toFinset = shiftedValues.toFinset := by
    ext value
    simp
  rw [shiftedUnique_eq_dedup_of_sorted_shifted values shift hpairwise]
  calc
    shiftedValues.dedup = shiftedValues.dedup.toFinset.sort (· ≤ ·) :=
      hsort.symm
    _ = shiftedValues.toFinset.sort (· ≤ ·) := by rw [hfinset]

theorem shiftedUnique_nats_eq_sorted_image
    (values : List Std.U32) (shift : Std.U32) (hshift : shift.val < 32)
    (hsorted : values.Pairwise (· ≤ ·)) :
    (shiftedUnique values shift).map (fun value => value.val) =
      ((values.map (fun value => Std.U32.wrapping_shr value shift)).toFinset.image
        (fun value => value.val)).sort (· ≤ ·) := by
  have hexact := shiftedUnique_eq_sorted_toFinset values shift hshift hsorted
  let shiftedSet :=
    (values.map (fun value => Std.U32.wrapping_shr value shift)).toFinset
  have hvalInjective : Function.Injective (fun value : Std.U32 => value.val) := by
    intro left right heq
    exact UScalar.eq_of_val_eq heq
  have houtNodup : (shiftedUnique values shift).Nodup := by
    rw [hexact]
    exact Finset.sort_nodup shiftedSet (· ≤ ·)
  have hnatNodup :
      ((shiftedUnique values shift).map (fun value => value.val)).Nodup :=
    houtNodup.map hvalInjective
  have houtPairwise : (shiftedUnique values shift).Pairwise (· ≤ ·) := by
    rw [hexact]
    exact Finset.pairwise_sort shiftedSet (· ≤ ·)
  have hnatPairwise :
      ((shiftedUnique values shift).map (fun value => value.val)).Pairwise
        (· ≤ ·) := by
    exact houtPairwise.map _ (fun _ _ hle => hle)
  have hnatSort :=
    (List.toFinset_sort (· ≤ ·) hnatNodup).2 hnatPairwise
  have hnatSet :
      ((shiftedUnique values shift).map (fun value => value.val)).toFinset =
        shiftedSet.image (fun value => value.val) := by
    rw [hexact]
    ext value
    simp [shiftedSet]
  calc
    (shiftedUnique values shift).map (fun value => value.val) =
        ((shiftedUnique values shift).map
          (fun value => value.val)).toFinset.sort (· ≤ ·) :=
      hnatSort.symm
    _ = (shiftedSet.image (fun value => value.val)).sort (· ≤ ·) := by
      rw [hnatSet]

/-- Nat-level form used by the maintained model: take the input integer set,
divide every member by the released power of two, remove duplicates, and sort
the result. -/
theorem shiftedUnique_nats_eq_sorted_division_image
    (values : List Std.U32) (shift : Std.U32) (hshift : shift.val < 32)
    (hsorted : values.Pairwise (· ≤ ·)) :
    (shiftedUnique values shift).map (fun value => value.val) =
      ((values.map (fun value => value.val)).toFinset.image
        (fun value => value / 2 ^ shift.val)).sort (· ≤ ·) := by
  rw [shiftedUnique_nats_eq_sorted_image values shift hshift hsorted]
  congr 1
  ext output
  simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨shifted, ⟨input, hinput, rfl⟩, rfl⟩
    refine ⟨input.val, ⟨input, hinput, rfl⟩, ?_⟩
    exact (u32_wrapping_shr_val_of_lt input shift hshift).symm
  · rintro ⟨inputNat, ⟨input, hinput, rfl⟩, rfl⟩
    refine ⟨Std.U32.wrapping_shr input shift, ⟨input, hinput, rfl⟩, ?_⟩
    exact u32_wrapping_shr_val_of_lt input shift hshift

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

/-! ## Exact layer-zero duplicate removal -/

def uniqueValues (values : List Std.U32) : List Std.U32 :=
  values.foldl appendIfDifferent []

theorem uniqueValues_length_le (values : List Std.U32) :
    (uniqueValues values).length ≤ values.length := by
  unfold uniqueValues
  have h := shiftedFold_length_le values [] 0#u32
  simpa using h

theorem uniqueValues_take_succ (values : List Std.U32)
    {index : Nat} (hindex : index < values.length) :
    uniqueValues (values.take (index + 1)) =
      appendIfDifferent (uniqueValues (values.take index)) values[index] := by
  have htake := List.take_append_getElem hindex
  unfold uniqueValues
  rw [← htake, List.foldl_append]
  rfl

theorem uniqueValues_eq_dedup_of_sorted
    (values : List Std.U32) (hsorted : values.Pairwise (· ≤ ·)) :
    uniqueValues values = values.dedup := by
  unfold uniqueValues
  have happend :
      (appendIfDifferent : List Std.U32 → Std.U32 → List Std.U32) =
        appendDistinct := by
    funext current value
    exact appendIfDifferent_eq_appendDistinct current value
  rw [happend]
  exact foldl_appendDistinct_eq_dedup_of_pairwise values hsorted

private theorem layer0_dedup_loop_eq_shift_zero
    (sorted layer0 : alloc.vec.Vec Std.U32) (index : Std.Usize) :
    aspis_core.circle_line_merkle.derive_circle_line_query_indices_for_count_loop0_loop1
        sorted layer0 index =
      aspis_core.circle_line_merkle.sorted_unique_shifted_loop
        (alloc.vec.Vec.deref sorted) 0#u32 layer0 index := by
  rfl

theorem extracted_layer0_unique_exact
    (sorted : alloc.vec.Vec Std.U32) :
    aspis_core.circle_line_merkle.derive_circle_line_query_indices_for_count_loop0_loop1
        sorted (alloc.vec.Vec.with_capacity Std.U32 (alloc.vec.Vec.len sorted))
          0#usize ⦃ output =>
      output.val = uniqueValues sorted.val ⦄ := by
  rw [layer0_dedup_loop_eq_shift_zero]
  simpa [shiftedUnique, uniqueValues, alloc.vec.Vec.with_capacity,
      alloc.vec.Vec.deref] using
    (sorted_unique_shifted_loop_exact (alloc.vec.Vec.deref sorted) 0#u32
      (alloc.vec.Vec.with_capacity Std.U32 (alloc.vec.Vec.len sorted))
      0#usize (by norm_num)
      (by simp [alloc.vec.Vec.with_capacity, shiftedUnique]))

theorem extracted_layer0_dedup_exact
    (sorted : alloc.vec.Vec Std.U32)
    (hsorted : sorted.val.Pairwise (· ≤ ·)) :
    aspis_core.circle_line_merkle.derive_circle_line_query_indices_for_count_loop0_loop1
        sorted (alloc.vec.Vec.with_capacity Std.U32 (alloc.vec.Vec.len sorted))
          0#usize ⦃ output =>
      output.val = sorted.val.dedup ⦄ := by
  apply WP.spec_mono (extracted_layer0_unique_exact sorted)
  intro output hout
  exact hout.trans (uniqueValues_eq_dedup_of_sorted sorted.val hsorted)

/-! ## Exact extracted adjacent-swap loop -/

def swapWithPrevious (values : List Std.U32) (position : Nat) : List Std.U32 :=
  (values.set position values[position - 1]!).set (position - 1)
    values[position]!

@[simp] theorem swapWithPrevious_length
    (values : List Std.U32) (position : Nat) :
    (swapWithPrevious values position).length = values.length := by
  simp [swapWithPrevious]

def bubbleLeft : List Std.U32 → Nat → List Std.U32
  | values, 0 => values
  | values, position + 1 =>
      if position + 1 < values.length then
        if values[position + 1]! < values[position]! then
          bubbleLeft (swapWithPrevious values (position + 1)) position
        else values
      else values
termination_by _ position => position

private theorem slice_swap_with_previous
    (values : Slice Std.U32) (position previous : Std.Usize)
    (hposition : position.val < values.val.length)
    (hprevious : previous.val = position.val - 1)
    (hpositive : 0 < position.val) :
    core.slice.Slice.swap values position previous ⦃ output =>
      output.val = swapWithPrevious values.val position.val ⦄ := by
  have hpreviousBound : previous.val < values.val.length := by omega
  obtain ⟨atPosition, hreadPosition, hatPosition⟩ := WP.spec_imp_exists
    (Slice.index_usize_spec values position hposition)
  obtain ⟨atPrevious, hreadPrevious, hatPrevious⟩ := WP.spec_imp_exists
    (Slice.index_usize_spec values previous hpreviousBound)
  obtain ⟨afterPosition, hsetPosition, hafterPosition⟩ := WP.spec_imp_exists
    (Slice.update_spec values position atPrevious hposition)
  have hafterPreviousBound :
      previous.val < afterPosition.val.length := by
    rw [hafterPosition, Slice.set_val_eq, List.length_set]
    exact hpreviousBound
  obtain ⟨output, hsetPrevious, houtput⟩ := WP.spec_imp_exists
    (Slice.update_spec afterPosition previous atPosition hafterPreviousBound)
  have hatPositionBang : atPosition = values.val[position.val]! := by
    rw [hatPosition]
    symm
    apply List.getElem!_of_getElem?
    simp [hposition]
  have hatPreviousBang :
      atPrevious = values.val[position.val - 1]! := by
    have hbang : atPrevious = values.val[previous.val]! := by
      rw [hatPrevious]
      symm
      apply List.getElem!_of_getElem?
      simp [hpreviousBound]
    simpa only [hprevious] using hbang
  simp only [core.slice.Slice.swap]
  rw [hreadPosition]
  simp only [bind_tc_ok]
  rw [hreadPrevious]
  simp only [bind_tc_ok]
  rw [hsetPosition]
  simp only [bind_tc_ok]
  rw [hsetPrevious]
  simp only [WP.spec, WP.theta, WP.wp_return]
  rw [houtput, hafterPosition, Slice.set_val_eq, Slice.set_val_eq,
    hatPositionBang, hatPreviousBang]
  rw [hprevious]
  rfl

/-- The innermost extracted Rust loop is exactly the pure operation that moves
one value left while it is smaller than its predecessor. -/
theorem generated_inner_insertion_loop_exact
    (sorted : alloc.vec.Vec Std.U32) (position : Std.Usize)
    (hbound : position.val < sorted.val.length) :
    aspis_core.circle_line_merkle.derive_circle_line_query_indices_for_count_loop0_loop0_loop0
        sorted position ⦃ output =>
      output.val = bubbleLeft sorted.val position.val ⦄ := by
  simp only [
    aspis_core.circle_line_merkle.derive_circle_line_query_indices_for_count_loop0_loop0_loop0]
  apply loop.spec_decr_nat
    (fun state : alloc.vec.Vec Std.U32 × Std.Usize => state.2.val)
    (fun state =>
      state.2.val < state.1.val.length ∧
        bubbleLeft state.1.val state.2.val =
          bubbleLeft sorted.val position.val)
    (fun output : alloc.vec.Vec Std.U32 =>
      output.val = bubbleLeft sorted.val position.val)
  · rintro ⟨current, currentPosition⟩ ⟨hcurrentBound, hcurrentModel⟩
    have hcurrentBound' : currentPosition.val < current.val.length := by
      simpa only using hcurrentBound
    have hcurrentModel' :
        bubbleLeft current.val currentPosition.val =
          bubbleLeft sorted.val position.val := by
      simpa only using hcurrentModel
    unfold
      aspis_core.circle_line_merkle.derive_circle_line_query_indices_for_count_loop0_loop0_loop0.body
    by_cases hpositive : 0 < currentPosition.val
    · have hpositiveScalar : currentPosition > 0#usize := by scalar_tac
      rw [if_pos hpositiveScalar]
      obtain ⟨atPosition, hreadPosition, hatPosition⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.index_usize_spec current currentPosition hcurrentBound')
      rw [alloc.vec.Vec.index_slice_index, hreadPosition]
      simp only [bind_tc_ok, Std.lift]
      let previous := Std.Usize.wrapping_sub currentPosition 1#usize
      have hprevious : previous.val = currentPosition.val - 1 := by
        exact wrapping_pred_exact currentPosition hpositive
      have hpreviousBound : previous.val < current.val.length := by
        omega
      obtain ⟨atPrevious, hreadPrevious, hatPrevious⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.index_usize_spec current previous hpreviousBound)
      rw [show Std.Usize.wrapping_sub currentPosition 1#usize = previous by rfl,
        alloc.vec.Vec.index_slice_index, hreadPrevious]
      simp only [bind_tc_ok]
      have hatPositionBang :
          atPosition = current.val[currentPosition.val]! := by
        rw [hatPosition]
        symm
        apply List.getElem!_of_getElem?
        simp [hcurrentBound']
      have hatPreviousBang :
          atPrevious = current.val[currentPosition.val - 1]! := by
        have hbang : atPrevious = current.val[previous.val]! := by
          rw [hatPrevious]
          symm
          apply List.getElem!_of_getElem?
          simp [hpreviousBound]
        simpa only [hprevious] using hbang
      by_cases hless : atPosition < atPrevious
      · rw [if_pos hless]
        simp only [Std.lift, bind_tc_ok, alloc.vec.Vec.deref_mut]
        obtain ⟨afterSwap, hswap, hafterSwap⟩ := WP.spec_imp_exists
          (slice_swap_with_previous (alloc.vec.Vec.deref current)
            currentPosition previous hcurrentBound' hprevious hpositive)
        have hswap' :
            core.slice.Slice.swap
                (⟨current.val, current.property⟩ : Slice Std.U32)
                currentPosition previous = ok afterSwap := by
          simpa only [alloc.vec.Vec.deref] using hswap
        rw [hswap']
        simp only [bind_tc_ok, Std.lift]
        have hafterSwap' :
            afterSwap.val =
              swapWithPrevious current.val currentPosition.val := by
          simpa only [alloc.vec.Vec.deref] using hafterSwap
        have hlessBang :
            current.val[currentPosition.val]! <
              current.val[currentPosition.val - 1]! := by
          rw [← hatPositionBang, ← hatPreviousBang]
          exact hless
        have hmodelStep :
            bubbleLeft current.val currentPosition.val =
              bubbleLeft (swapWithPrevious current.val currentPosition.val)
                previous.val := by
          have hsucc :
              currentPosition.val = (currentPosition.val - 1) + 1 := by omega
          have hsuccBound :
              currentPosition.val - 1 + 1 < current.val.length := by
            omega
          conv_lhs => rw [hsucc, bubbleLeft]
          rw [if_pos hsuccBound, if_pos (by
            rw [← hsucc]
            exact hlessBang)]
          rw [← hsucc, hprevious]
        simp only [WP.spec, WP.theta]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · change previous.val < afterSwap.val.length
          rw [hafterSwap', swapWithPrevious_length, hprevious]
          omega
        · change
            bubbleLeft afterSwap.val previous.val =
              bubbleLeft sorted.val position.val
          rw [hafterSwap']
          exact hmodelStep.symm.trans hcurrentModel'
        · rw [hprevious]
          omega
      · rw [if_neg hless]
        simp only [WP.spec, WP.theta, WP.wp_return]
        have hnotLessBang :
            ¬ current.val[currentPosition.val]! <
              current.val[currentPosition.val - 1]! := by
          intro hbang
          apply hless
          rw [hatPositionBang, hatPreviousBang]
          exact hbang
        have hstops :
            bubbleLeft current.val currentPosition.val = current.val := by
          have hsucc :
              currentPosition.val = (currentPosition.val - 1) + 1 := by omega
          have hsuccBound :
              currentPosition.val - 1 + 1 < current.val.length := by
            omega
          conv_lhs => rw [hsucc, bubbleLeft]
          rw [if_pos hsuccBound, if_neg (by
            rw [← hsucc]
            exact hnotLessBang)]
        rw [← hstops]
        exact hcurrentModel'
    · have hzero : currentPosition.val = 0 := by omega
      rw [if_neg (show ¬ currentPosition > 0#usize by scalar_tac)]
      simp only [WP.spec, WP.theta, WP.wp_return]
      calc
        current.val = bubbleLeft current.val 0 := by
          simp only [bubbleLeft]
        _ = bubbleLeft sorted.val position.val := by
          simpa only [hzero] using hcurrentModel'
  · exact ⟨hbound, rfl⟩

#print axioms u32_wrapping_shr_val_of_lt
#print axioms shiftedUnique_nats_eq_sorted_division_image
#print axioms sorted_unique_shifted_exact
#print axioms extracted_layer0_dedup_exact
#print axioms generated_inner_insertion_loop_exact

end RuntimeIndexProof
