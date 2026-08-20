import RuntimeScheduleMerkleReuse
import Init.Data.List.Nat.Perm
import Mathlib.Data.List.Destutter
import Mathlib.Data.Finset.Sort

open Aeneas Aeneas.Std Result ControlFlow Error
open V5MerkleQueryReuse

/-!
# Exact later-index derivation from the extracted Rust loop

The production helper scans a sorted layer-zero index list, shifts each value,
and drops a value when it is equal to the last value already returned.  This
file proves that behavior directly about the Charon/Aeneas translation.  It
also proves that the three released shifts are exact division by 4, 16, and
64.  No production source is changed.
-/

namespace V5MerkleQueryReuseProof

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
    V5MerkleQueryReuse.circle_line_merkle.sorted_unique_shifted_loop
      indices shift result index ⦃ output =>
        output.val = shiftedUnique indices.val shift ⦄ := by
  simp only [V5MerkleQueryReuse.circle_line_merkle.sorted_unique_shifted_loop]
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
    unfold V5MerkleQueryReuse.circle_line_merkle.sorted_unique_shifted_loop.body
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
    V5MerkleQueryReuse.circle_line_merkle.sorted_unique_shifted indices shift ⦃ output =>
      output.val = shiftedUnique indices.val shift ⦄ := by
  unfold V5MerkleQueryReuse.circle_line_merkle.sorted_unique_shifted
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
    V5MerkleQueryReuse.circle_line_merkle.derive_circle_line_query_indices_for_count_loop0_loop1
        sorted layer0 index =
      V5MerkleQueryReuse.circle_line_merkle.sorted_unique_shifted_loop
        (alloc.vec.Vec.deref sorted) 0#u32 layer0 index := by
  rfl

theorem extracted_layer0_unique_exact
    (sorted : alloc.vec.Vec Std.U32) :
    V5MerkleQueryReuse.circle_line_merkle.derive_circle_line_query_indices_for_count_loop0_loop1
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
    V5MerkleQueryReuse.circle_line_merkle.derive_circle_line_query_indices_for_count_loop0_loop1
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

private theorem inserted_prefix_pairwise
    (before after : List Std.U32) (key : Std.U32)
    (hsorted : (before ++ after).Pairwise (.≤.))
    (hbefore : ∀ x ∈ before, x ≤ key)
    (hafter : ∀ y ∈ after, key < y) :
    (before ++ key :: after).Pairwise (.≤.) := by
  rw [List.pairwise_append] at hsorted ⊢
  rcases hsorted with ⟨hbeforeSorted, hafterSorted, hcross⟩
  refine ⟨hbeforeSorted, ?_, ?_⟩
  · simp only [List.pairwise_cons]
    exact ⟨fun y hy => (hafter y hy).le, hafterSorted⟩
  · intro x hx y hy
    rcases List.mem_cons.mp hy with heq | hy
    · subst y
      exact hbefore x hx
    · exact hcross x hx y hy

private theorem pairwise_before_le_key_of_last
    (before : List Std.U32) (key : Std.U32)
    (hsorted : before.Pairwise (.≤.))
    (hne : before ≠ [])
    (hlast : before.getLast hne ≤ key) :
    ∀ x ∈ before, x ≤ key := by
  intro x hx
  have hxlast : x ≤ before.getLast hne := by
    have hdecomp := List.dropLast_concat_getLast hne
    rw [← hdecomp] at hx hsorted
    rcases List.mem_append.mp hx with hxInit | hxLast
    · exact hsorted.rel_of_mem_append hxInit (by simp)
    · have heq : x = before.getLast hne := by simpa using hxLast
      simpa [heq]
  exact hxlast.trans hlast

private def BubbleInv (original : List Std.U32) (target : Nat)
    (current : List Std.U32) (position : Nat) : Prop :=
  ∃ before after key suffix,
    before.length = position ∧
    before.length + after.length = target ∧
    original = (before ++ after) ++ key :: suffix ∧
    current = (before ++ key :: after) ++ suffix ∧
    (before ++ after).Pairwise (· ≤ ·) ∧
    ∀ value ∈ after, key < value

private theorem bubbleInv_initial
    (values : List Std.U32) (target : Nat)
    (htarget : target < values.length)
    (hsorted : (values.take target).Pairwise (· ≤ ·)) :
    BubbleInv values target values target := by
  refine ⟨values.take target, [], values[target], values.drop (target + 1),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt htarget)]
  · simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt htarget)]
  · calc
      values = values.take (target + 1) ++ values.drop (target + 1) :=
        (List.take_append_drop (target + 1) values).symm
      _ = (values.take target ++ []) ++ values[target] ::
          values.drop (target + 1) := by
        rw [List.take_succ_eq_append_getElem htarget]
        simp
  · calc
      values = values.take (target + 1) ++ values.drop (target + 1) :=
        (List.take_append_drop (target + 1) values).symm
      _ = (values.take target ++ values[target] :: []) ++
          values.drop (target + 1) := by
        rw [List.take_succ_eq_append_getElem htarget]
  · simpa
  · simp

private theorem bubbleInv_active_bounds
    {original current : List Std.U32} {target position : Nat}
    (hinv : BubbleInv original target current position) :
    position ≤ target ∧ target < current.length := by
  rcases hinv with ⟨before, after, key, suffix, hposition, htarget,
    horiginal, hcurrent, hsorted, hafter⟩
  constructor
  · omega
  · rw [hcurrent]
    simp only [List.length_append, List.length_cons]
    omega

private theorem adjacent_set_exact
    (before : List Std.U32) (previous key : Std.U32)
    (after : List Std.U32) :
    let values := before ++ previous :: key :: after
    (values.set (before.length + 1) previous).set before.length key =
      before ++ key :: previous :: after := by
  simp

private theorem bubbleInv_swap
    {original current : List Std.U32} {target position : Nat}
    (hinv : BubbleInv original target current position)
    (hpositive : 0 < position)
    (hlt : current[position]! < current[position - 1]!) :
    let swapped :=
      (current.set position current[position - 1]!).set (position - 1)
        current[position]!
    BubbleInv original target swapped (position - 1) := by
  rcases hinv with ⟨before, after, key, suffix, hposition, htarget,
    horiginal, hcurrent, hsorted, hafter⟩
  have hbefore : before ≠ [] := by
    intro hempty
    subst before
    simp at hposition
    omega
  let init := before.dropLast
  let previous := before.getLast hbefore
  have hbeforeDecomp : init ++ [previous] = before := by
    exact List.dropLast_concat_getLast hbefore
  have hpositionExact : position = init.length + 1 := by
    rw [← hposition, ← hbeforeDecomp]
    simp [init]
  have hcurrentExact :
      current = init ++ previous :: key :: (after ++ suffix) := by
    rw [hcurrent, ← hbeforeDecomp]
    simp [List.append_assoc]
  have hkeyRead : current[position]! = key := by
    rw [hcurrentExact, hpositionExact]
    simp
  have hpreviousRead : current[position - 1]! = previous := by
    rw [hcurrentExact, hpositionExact]
    simp
  have hkeyPrevious : key < previous := by
    simpa only [hkeyRead, hpreviousRead] using hlt
  refine ⟨init, previous :: after, key, suffix, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · rw [← htarget, ← hbeforeDecomp]
    simp
    omega
  · rw [horiginal, ← hbeforeDecomp]
    simp only [List.append_assoc, List.singleton_append]
  · rw [hpositionExact, hcurrentExact]
    have hkeyAt :
        (init ++ previous :: key :: (after ++ suffix))[init.length + 1]! =
          key := by simp
    have hpreviousAt :
        (init ++ previous :: key :: (after ++ suffix))[init.length + 1 - 1]! =
          previous := by simp
    rw [hkeyAt, hpreviousAt, Nat.add_sub_cancel]
    simpa only [List.append_assoc, List.cons_append] using
      (adjacent_set_exact init previous key (after ++ suffix))
  · rw [← hbeforeDecomp] at hsorted
    simpa only [List.append_assoc, List.singleton_append] using hsorted
  · intro value hvalue
    rcases List.mem_cons.mp hvalue with heq | hvalue
    · subst value
      exact hkeyPrevious
    · exact hafter value hvalue

private theorem bubbleInv_done_prefix_sorted
    {original current : List Std.U32} {target position : Nat}
    (hinv : BubbleInv original target current position)
    (hdone : position = 0 ∨ current[position - 1]! ≤ current[position]!) :
    (current.take (target + 1)).Pairwise (· ≤ ·) := by
  rcases hinv with ⟨before, after, key, suffix, hposition, htarget,
    horiginal, hcurrent, hsorted, hafter⟩
  have hprefixTake :
      current.take (target + 1) = before ++ key :: after := by
    rw [hcurrent]
    have hlength : (before ++ key :: after).length = target + 1 := by
      simp only [List.length_append, List.length_cons]
      omega
    rw [← hlength, List.take_left]
  rw [hprefixTake]
  apply inserted_prefix_pairwise before after key hsorted
  · rcases hdone with hzero | hboundary
    · have hempty : before = [] := List.eq_nil_of_length_eq_zero (by omega)
      simp [hempty]
    · by_cases hbefore : before = []
      · simp [hbefore]
      · have hpositionExact : position = before.length := hposition.symm
        have hkeyRead : current[position]! = key := by
          rw [hcurrent, hpositionExact]
          simp
        let init := before.dropLast
        let previous := before.getLast hbefore
        have hbeforeDecomp : init ++ [previous] = before :=
          List.dropLast_concat_getLast hbefore
        have hpositionInit : position = init.length + 1 := by
          rw [hpositionExact, ← hbeforeDecomp]
          simp [init]
        have hlastRead : current[position - 1]! = previous := by
          rw [hcurrent, ← hbeforeDecomp, hpositionInit]
          simp [List.append_assoc]
        exact pairwise_before_le_key_of_last before key
          (List.pairwise_append.mp hsorted).1 hbefore
          (by simpa only [previous, hlastRead, hkeyRead] using hboundary)
  · exact hafter

private theorem bubbleInv_perm
    {original current : List Std.U32} {target position : Nat}
    (hinv : BubbleInv original target current position) :
    current.Perm original := by
  rcases hinv with ⟨before, after, key, suffix, hposition, htarget,
    horiginal, hcurrent, hsorted, hafter⟩
  rw [hcurrent, horiginal]
  have hmove : List.Perm (key :: after) (after ++ [key]) := by
    simpa using
      (List.perm_append_comm : List.Perm ([key] ++ after) (after ++ [key]))
  simpa only [List.append_assoc, List.singleton_append] using
    List.Perm.append_right suffix
      (List.Perm.append_left before hmove)

private theorem bubbleLeft_reaches_done
    {original current : List Std.U32} {target position : Nat}
    (hinv : BubbleInv original target current position) :
    ∃ finalPosition,
      BubbleInv original target (bubbleLeft current position) finalPosition ∧
      (finalPosition = 0 ∨
        (bubbleLeft current position)[finalPosition - 1]! ≤
          (bubbleLeft current position)[finalPosition]!) := by
  induction position generalizing current with
  | zero =>
      refine ⟨0, ?_, Or.inl rfl⟩
      simpa only [bubbleLeft] using hinv
  | succ previous ih =>
      have hbounds := bubbleInv_active_bounds hinv
      have hactive : previous + 1 < current.length := by omega
      rw [bubbleLeft, if_pos hactive]
      by_cases hless : current[previous + 1]! < current[previous]!
      · rw [if_pos hless]
        have hnextInv :
            BubbleInv original target
              (swapWithPrevious current (previous + 1)) previous := by
          simpa only [swapWithPrevious, Nat.add_sub_cancel] using
            (bubbleInv_swap hinv (by omega) hless)
        exact ih hnextInv
      · rw [if_neg hless]
        refine ⟨previous + 1, hinv, Or.inr ?_⟩
        simp only [Nat.add_sub_cancel]
        exact le_of_not_gt hless

theorem bubbleLeft_sorted_prefix
    (values : List Std.U32) (target : Nat)
    (htarget : target < values.length)
    (hsorted : (values.take target).Pairwise (· ≤ ·)) :
    ((bubbleLeft values target).take (target + 1)).Pairwise (· ≤ ·) := by
  obtain ⟨finalPosition, hinv, hdone⟩ :=
    bubbleLeft_reaches_done (bubbleInv_initial values target htarget hsorted)
  exact bubbleInv_done_prefix_sorted hinv hdone

theorem bubbleLeft_perm
    (values : List Std.U32) (target : Nat)
    (htarget : target < values.length)
    (hsorted : (values.take target).Pairwise (· ≤ ·)) :
    (bubbleLeft values target).Perm values := by
  obtain ⟨finalPosition, hinv, hdone⟩ :=
    bubbleLeft_reaches_done (bubbleInv_initial values target htarget hsorted)
  exact bubbleInv_perm hinv

@[simp] theorem bubbleLeft_length
    (values : List Std.U32) (position : Nat) :
    (bubbleLeft values position).length = values.length := by
  induction position generalizing values with
  | zero => simp only [bubbleLeft]
  | succ previous ih =>
      rw [bubbleLeft]
      split
      · split
        · rw [ih, swapWithPrevious_length]
        · rfl
      · rfl

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
    V5MerkleQueryReuse.circle_line_merkle.derive_circle_line_query_indices_for_count_loop0_loop0_loop0
        sorted position ⦃ output =>
      output.val = bubbleLeft sorted.val position.val ⦄ := by
  simp only [
    V5MerkleQueryReuse.circle_line_merkle.derive_circle_line_query_indices_for_count_loop0_loop0_loop0]
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
      V5MerkleQueryReuse.circle_line_merkle.derive_circle_line_query_indices_for_count_loop0_loop0_loop0.body
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

private theorem wrapping_vec_succ_exact
    {T : Type} (values : alloc.vec.Vec T) (index : Std.Usize)
    (hindex : index.val < values.val.length) :
    (Std.Usize.wrapping_add index 1#usize).val = index.val + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  apply Nat.mod_eq_of_lt
  have hlength := values.property
  change index.val + 1 < UScalar.size .Usize
  rw [UScalar.size_UScalarTyUsize]
  have hsize := Usize.size_scalarTac_eq
  omega

/-- The complete extracted insertion-sort loop returns a sorted permutation
of its input whenever the prefix before `index` is already sorted. -/
theorem generated_insertion_sort_loop_exact
    (sorted : alloc.vec.Vec Std.U32) (index : Std.Usize)
    (hindex : index.val ≤ sorted.val.length)
    (hprefix : (sorted.val.take index.val).Pairwise (· ≤ ·)) :
    V5MerkleQueryReuse.circle_line_merkle.derive_circle_line_query_indices_for_count_loop0_loop0
        sorted index ⦃ output =>
      output.val.Pairwise (· ≤ ·) ∧ output.val.Perm sorted.val ⦄ := by
  simp only [
    V5MerkleQueryReuse.circle_line_merkle.derive_circle_line_query_indices_for_count_loop0_loop0]
  apply loop.spec_decr_nat
    (fun state : alloc.vec.Vec Std.U32 × Std.Usize =>
      sorted.val.length - state.2.val)
    (fun state =>
      state.2.val ≤ state.1.val.length ∧
      state.1.val.length = sorted.val.length ∧
      state.1.val.Perm sorted.val ∧
      (state.1.val.take state.2.val).Pairwise (· ≤ ·))
    (fun output : alloc.vec.Vec Std.U32 =>
      output.val.Pairwise (· ≤ ·) ∧ output.val.Perm sorted.val)
  · rintro ⟨current, currentIndex⟩
      ⟨hcurrentBound, hcurrentLength, hcurrentPerm, hcurrentPrefix⟩
    have hcurrentBound' : currentIndex.val ≤ current.val.length := by
      simpa only using hcurrentBound
    have hcurrentLength' : current.val.length = sorted.val.length := by
      simpa only using hcurrentLength
    have hcurrentPerm' : current.val.Perm sorted.val := by
      simpa only using hcurrentPerm
    have hcurrentPrefix' :
        (current.val.take currentIndex.val).Pairwise (· ≤ ·) := by
      simpa only using hcurrentPrefix
    unfold
      V5MerkleQueryReuse.circle_line_merkle.derive_circle_line_query_indices_for_count_loop0_loop0.body
    by_cases hactive : currentIndex.val < current.val.length
    · have hactiveScalar : currentIndex < alloc.vec.Vec.len current := by
        scalar_tac
      rw [if_pos hactiveScalar]
      obtain ⟨next, hnextRun, hnextModel⟩ := WP.spec_imp_exists
        (generated_inner_insertion_loop_exact current currentIndex hactive)
      rw [hnextRun]
      simp only [bind_tc_ok, Std.lift]
      let nextIndex := Std.Usize.wrapping_add currentIndex 1#usize
      have hnextIndex : nextIndex.val = currentIndex.val + 1 := by
        exact wrapping_vec_succ_exact current currentIndex hactive
      have hnextValues :
          next.val = bubbleLeft current.val currentIndex.val := hnextModel
      have hnextLength : next.val.length = current.val.length := by
        rw [hnextValues, bubbleLeft_length]
      have hnextPrefix :
          (next.val.take nextIndex.val).Pairwise (· ≤ ·) := by
        rw [hnextValues, hnextIndex]
        exact bubbleLeft_sorted_prefix current.val currentIndex.val hactive
          hcurrentPrefix'
      have hnextPermCurrent : next.val.Perm current.val := by
        rw [hnextValues]
        exact bubbleLeft_perm current.val currentIndex.val hactive
          hcurrentPrefix'
      simp only [WP.spec, WP.theta]
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [hnextIndex, hnextLength]
        omega
      · exact hnextLength.trans hcurrentLength'
      · exact hnextPermCurrent.trans hcurrentPerm'
      · exact hnextPrefix
      · rw [hnextIndex]
        omega
    · have hdone : currentIndex.val = current.val.length := by omega
      have hnotActive : ¬ currentIndex < alloc.vec.Vec.len current := by
        scalar_tac
      rw [if_neg hnotActive]
      simp only [WP.spec, WP.theta, WP.wp_return]
      constructor
      · simpa only [hdone, List.take_length] using hcurrentPrefix'
      · exact hcurrentPerm'
  · exact ⟨hindex, rfl, List.Perm.refl sorted.val, hprefix⟩

/-! ## Complete extracted query-index assembly -/

def expectedLayer0 (values : List Std.U32) : List Std.U32 :=
  values.toFinset.sort (· ≤ ·)

def expectedLater (values : List Std.U32) : List (List Std.U32) :=
  [shiftedUnique (expectedLayer0 values) 2#u32,
    shiftedUnique (expectedLayer0 values) 4#u32,
    shiftedUnique (expectedLayer0 values) 6#u32]

def QueryIndicesPost (values : List Std.U32)
    (result : core.result.Result
      circle_line_merkle.CircleLineQueryIndices
      circle_line_merkle.CircleLineMerkleError) : Prop :=
  ∃ output,
    result = core.result.Result.Ok output ∧
    output.layer0.val = expectedLayer0 values ∧
    output.later.val.map (fun later => later.val) = expectedLater values

theorem generated_insertion_sort_from_one
    (values : alloc.vec.Vec Std.U32) (hne : values.val ≠ []) :
    circle_line_merkle.derive_circle_line_query_indices_for_count_loop0_loop0
        values 1#usize ⦃ output =>
      output.val.Pairwise (· ≤ ·) ∧ output.val.Perm values.val ⦄ := by
  apply generated_insertion_sort_loop_exact
  · change 1 ≤ values.val.length
    cases hvalues : values.val with
    | nil => exact False.elim (hne hvalues)
    | cons head tail => simp
  · change (values.val.take 1).Pairwise (· ≤ ·)
    cases hvalues : values.val with
    | nil => exact False.elim (hne hvalues)
    | cons head tail => simp

theorem sorted_dedup_eq_expectedLayer0
    (sorted values : List Std.U32)
    (hsorted : sorted.Pairwise (· ≤ ·))
    (hperm : sorted.Perm values) :
    sorted.dedup = expectedLayer0 values := by
  have hdedupPairwise : sorted.dedup.Pairwise (· ≤ ·) :=
    List.Pairwise.sublist (List.dedup_sublist sorted) hsorted
  have hsort : sorted.dedup.toFinset.sort (· ≤ ·) = sorted.dedup :=
    (List.toFinset_sort (· ≤ ·) (List.nodup_dedup sorted)).2
      hdedupPairwise
  have hfinset : sorted.dedup.toFinset = values.toFinset := by
    ext value
    simp only [List.mem_toFinset, List.mem_dedup]
    exact hperm.mem_iff
  unfold expectedLayer0
  rw [← hfinset, hsort]

/-- Once range validation reaches the end, the extracted body executes the
actual Rust sort, duplicate removal, fixed shift lookup, and three later-layer
scans, and returns the exact maintained list model. -/
theorem terminal_query_index_body_exact
    (queries : Slice Std.U32) (queryLimit : Std.U32)
    (inputIndex : Std.Usize)
    (hdone : inputIndex.val = queries.val.length)
    (hne : queries.val ≠ []) :
    circle_line_merkle.derive_circle_line_query_indices_for_count_loop0.body
        queries queryLimit inputIndex ⦃ flow =>
      ∃ result,
        flow = ControlFlow.done result ∧ QueryIndicesPost queries.val result ⦄ := by
  unfold circle_line_merkle.derive_circle_line_query_indices_for_count_loop0.body
  have hnotActive : ¬ inputIndex < Slice.len queries := by scalar_tac
  rw [if_neg hnotActive]
  obtain ⟨sorted, hsortedRun, hsortedEq⟩ := WP.spec_imp_exists
    (alloc.slice.Slice.to_vec_spec core.clone.CloneU32 queries (by
      intro value hvalue
      simp))
  rw [hsortedRun]
  simp only [bind_tc_ok]
  have hsortedValues : sorted.val = queries.val := by
    exact congrArg Subtype.val hsortedEq.symm
  have hsortedNe : sorted.val ≠ [] := by
    simpa only [hsortedValues] using hne
  obtain ⟨sorted1, hsortRun, hsortPost⟩ := WP.spec_imp_exists
    (generated_insertion_sort_from_one sorted hsortedNe)
  rw [hsortRun]
  simp only [bind_tc_ok]
  obtain ⟨layer01, hlayerRun, hlayerValues⟩ := WP.spec_imp_exists
    (extracted_layer0_dedup_exact sorted1 hsortPost.1)
  rw [hlayerRun]
  simp only [bind_tc_ok]
  have hshift0 :
      Array.index_usize circle_line_merkle.CIRCLE_LINE_QUERY_SHIFTS
        0#usize = ok 2#u32 := by
    unfold circle_line_merkle.CIRCLE_LINE_QUERY_SHIFTS
    simp [Array.index_usize, Array.make]
  have hshift1 :
      Array.index_usize circle_line_merkle.CIRCLE_LINE_QUERY_SHIFTS
        1#usize = ok 4#u32 := by
    unfold circle_line_merkle.CIRCLE_LINE_QUERY_SHIFTS
    simp [Array.index_usize, Array.make]
  have hshift2 :
      Array.index_usize circle_line_merkle.CIRCLE_LINE_QUERY_SHIFTS
        2#usize = ok 6#u32 := by
    unfold circle_line_merkle.CIRCLE_LINE_QUERY_SHIFTS
    simp [Array.index_usize, Array.make]
  rw [hshift0]
  simp only [bind_tc_ok]
  obtain ⟨later0, hlater0Run, hlater0Values⟩ := WP.spec_imp_exists
    (sorted_unique_shifted_exact (alloc.vec.Vec.deref layer01) 2#u32)
  rw [hlater0Run]
  simp only [bind_tc_ok]
  rw [hshift1]
  simp only [bind_tc_ok]
  obtain ⟨later1, hlater1Run, hlater1Values⟩ := WP.spec_imp_exists
    (sorted_unique_shifted_exact (alloc.vec.Vec.deref layer01) 4#u32)
  rw [hlater1Run]
  simp only [bind_tc_ok]
  rw [hshift2]
  simp only [bind_tc_ok]
  obtain ⟨later2, hlater2Run, hlater2Values⟩ := WP.spec_imp_exists
    (sorted_unique_shifted_exact (alloc.vec.Vec.deref layer01) 6#u32)
  rw [hlater2Run]
  simp only [bind_tc_ok, WP.spec, WP.theta, WP.wp_return]
  have hsortedPermQueries : sorted1.val.Perm queries.val := by
    simpa only [hsortedValues] using hsortPost.2
  have hlayerExpected : layer01.val = expectedLayer0 queries.val := by
    calc
      layer01.val = sorted1.val.dedup := hlayerValues
      _ = expectedLayer0 queries.val :=
        sorted_dedup_eq_expectedLayer0 sorted1.val queries.val hsortPost.1
          hsortedPermQueries
  refine ⟨_, rfl, ?_⟩
  unfold QueryIndicesPost
  refine ⟨_, rfl, hlayerExpected, ?_⟩
  unfold expectedLater
  simp only [Array.make, List.map_cons, List.map_nil]
  rw [hlater0Values, hlater1Values, hlater2Values]
  simp only [alloc.vec.Vec.deref]
  rw [hlayerExpected]

private theorem query_wrapping_succ_exact
    (queries : Slice Std.U32) (index : Std.Usize)
    (hindex : index.val < queries.val.length) :
    (Std.Usize.wrapping_add index 1#usize).val = index.val + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  apply Nat.mod_eq_of_lt
  have hlength := queries.property
  change index.val + 1 < UScalar.size .Usize
  rw [UScalar.size_UScalarTyUsize]
  have hsize := Usize.size_scalarTac_eq
  omega

/-- The extracted validation loop rejects no in-range value and reaches the
exact final assembly proved above. -/
theorem generated_query_indices_loop_exact
    (queries : Slice Std.U32) (queryLimit : Std.U32)
    (hne : queries.val ≠ [])
    (hrange : ∀ query ∈ queries.val, query < queryLimit) :
    circle_line_merkle.derive_circle_line_query_indices_for_count_loop0
        queries queryLimit 0#usize ⦃ result =>
      QueryIndicesPost queries.val result ⦄ := by
  simp only [
    circle_line_merkle.derive_circle_line_query_indices_for_count_loop0]
  apply loop.spec_decr_nat
    (fun index : Std.Usize => queries.val.length - index.val)
    (fun index => index.val ≤ queries.val.length)
    (QueryIndicesPost queries.val)
  · intro index hindex
    have hindex' : index.val ≤ queries.val.length := by simpa only using hindex
    by_cases hactive : index.val < queries.val.length
    · unfold
        circle_line_merkle.derive_circle_line_query_indices_for_count_loop0.body
      have hactiveScalar : index < Slice.len queries := by scalar_tac
      rw [if_pos hactiveScalar]
      obtain ⟨query, hqueryRun, hqueryValue⟩ := WP.spec_imp_exists
        (Slice.index_usize_spec queries index hactive)
      rw [hqueryRun]
      simp only [bind_tc_ok]
      have hqueryMember : query ∈ queries.val := by
        rw [hqueryValue]
        exact List.getElem_mem hactive
      have hnotOutOfRange : ¬ query ≥ queryLimit := by
        exact not_le_of_gt (hrange query hqueryMember)
      rw [if_neg hnotOutOfRange]
      simp only [Std.lift, bind_tc_ok, WP.spec, WP.theta]
      have hnext :
          (Std.Usize.wrapping_add index 1#usize).val = index.val + 1 :=
        query_wrapping_succ_exact queries index hactive
      constructor
      · rw [hnext]
        omega
      · rw [hnext]
        omega
    · have hdone : index.val = queries.val.length := by omega
      have hterminal :=
        terminal_query_index_body_exact queries queryLimit index hdone hne
      apply WP.spec_mono hterminal
      intro flow hflow
      rcases hflow with ⟨result, rfl, hpost⟩
      exact hpost
  · norm_num

/-- The public extracted Rust helper returns the exact sorted layer-zero set
and the exact shifted unique later-layer lists for every nonempty in-range
input. -/
theorem generated_query_indices_exact
    (queries : Slice Std.U32) (queryCount : Std.Usize)
    (hne : queries.val ≠ [])
    (hrange : ∀ query ∈ queries.val,
      query < UScalar.cast .U32 queryCount) :
    circle_line_merkle.derive_circle_line_query_indices_for_count
        queries queryCount ⦃ result =>
      QueryIndicesPost queries.val result ⦄ := by
  unfold circle_line_merkle.derive_circle_line_query_indices_for_count
  have hnotEmpty : ¬ Slice.len queries = 0#usize := by
    intro hempty
    apply hne
    apply List.eq_nil_of_length_eq_zero
    scalar_tac
  rw [if_neg hnotEmpty]
  simp only [Std.lift, bind_tc_ok]
  exact generated_query_indices_loop_exact queries
    (UScalar.cast .U32 queryCount) hne hrange

#print axioms u32_wrapping_shr_val_of_lt
#print axioms shiftedUnique_nats_eq_sorted_division_image
#print axioms sorted_unique_shifted_exact
#print axioms extracted_layer0_dedup_exact
#print axioms generated_inner_insertion_loop_exact
#print axioms bubbleLeft_sorted_prefix
#print axioms bubbleLeft_perm
#print axioms generated_insertion_sort_loop_exact
#print axioms terminal_query_index_body_exact
#print axioms generated_query_indices_loop_exact
#print axioms generated_query_indices_exact

end V5MerkleQueryReuseProof
