import SumProductsArithmetic

/-!
# The generated nine-channel accumulation loops

This file reasons about the three actual Aeneas loops emitted for
`qm31_sum_products_small`.  The innermost theorem below is deliberately about
the generated range iterator, casts, wrapping multiplication, wrapping
addition, and nested mutable array update.
-/

open Aeneas Aeneas.Std Result ControlFlow

namespace AspisLane5QM31SumProductsProof

abbrev channelProductBound : Nat := (m31Modulus - 1) ^ 2

/-- Four canonical M31 channel products fit in one `u64`. -/
theorem four_channel_products_fit_u64 :
    4 * channelProductBound < u64Cardinality := by
  norm_num [channelProductBound, m31Modulus, u64Cardinality]

/-- The source's arity cap is load-bearing: the same uniform worst-case
bound no longer proves safety for five products. -/
theorem five_channel_products_exceed_u64_bound :
    u64Cardinality < 5 * channelProductBound := by
  norm_num [channelProductBound, m31Modulus, u64Cardinality]

def channelM31
    (components : Array (Array RustM31 3#usize) 3#usize)
    (component channel : Nat) : RustM31 :=
  components.val[component]!.val[channel]!

def CanonicalChannelMatrix
    (components : Array (Array RustM31 3#usize) 3#usize) : Prop :=
  ∀ component, component < 3 → ∀ channel, channel < 3 →
    CanonicalRawM31 (channelM31 components component channel).val

private theorem list_get_eq_getElemBang_loop
    {T : Type} [Inhabited T]
    (values : List T) (index : Nat) (hIndex : index < values.length) :
    values[index] = values[index]! := by
  symm
  apply List.getElem!_of_getElem?
  simp [hIndex]

private theorem generated_array_index_run_loop
    {T : Type} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize) (hIndex : index.val < N.val) :
    Array.index_usize values index = ok values.val[index.val]! := by
  obtain ⟨value, hRun, hValue⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_usize_spec values index (by
      simpa [Array.length_eq] using hIndex))
  have hArrayBound : index.val < values.val.length := by
    simpa [Array.length_eq] using hIndex
  have hElem := list_get_eq_getElemBang_loop values.val index.val hArrayBound
  simpa [hValue, hElem] using hRun

private theorem generated_array_index_mut_run_loop
    {T : Type} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize) (hIndex : index.val < N.val) :
    Array.index_mut_usize values index =
      ok (values.val[index.val]!, values.set index) := by
  obtain ⟨result, hRun, hPost⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_mut_usize_spec values index (by
      simpa [Array.length_eq] using hIndex))
  rcases result with ⟨value, back⟩
  rcases hPost with ⟨hValue, hBack⟩
  have hArrayBound : index.val < values.val.length := by
    simpa [Array.length_eq] using hIndex
  have hElem := list_get_eq_getElemBang_loop values.val index.val hArrayBound
  simpa [hValue, hBack, hElem] using hRun

private theorem generated_array_update_run_loop
    {T : Type} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize) (value : T)
    (hIndex : index.val < N.val) :
    Array.update values index value = ok (values.set index value) := by
  obtain ⟨out, hRun, hOut⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.update_spec values index value (by
      simpa [Array.length_eq] using hIndex))
  simpa [hOut] using hRun

def accumulatedChannelValue
    (sums : Array (Array Std.U64 3#usize) 3#usize)
    (leftComponents rightComponents :
      Array (Array RustM31 3#usize) 3#usize)
    (component channel : Std.Usize) : Std.U64 :=
  Std.U64.wrapping_add
    (matrixCell sums component.val channel.val)
    (Std.U64.wrapping_mul
      (UScalar.cast .U64
        (channelM31 leftComponents component.val channel.val))
      (UScalar.cast .U64
        (channelM31 rightComponents component.val channel.val)))

def accumulateChannel
    (sums : Array (Array Std.U64 3#usize) 3#usize)
    (leftComponents rightComponents :
      Array (Array RustM31 3#usize) 3#usize)
    (component channel : Std.Usize) :
    Array (Array Std.U64 3#usize) 3#usize :=
  sums.set component
    ((sums.val[component.val]!).set channel
      (accumulatedChannelValue sums leftComponents rightComponents
        component channel))

private theorem generated_channel_body_active
    (leftComponents rightComponents :
      Array (Array RustM31 3#usize) 3#usize)
    (component : Std.Usize)
    (iter : core.ops.range.Range Std.Usize)
    (sums : Array (Array Std.U64 3#usize) 3#usize)
    (hComponent : component.val < 3)
    (hActive : iter.start.val < iter.end.val)
    (hEnd : iter.end.val = 3) :
    ∃ iter',
      ComponentBGenerated.aspis_core.field.qm31_accumulate_product_channels_loop0_loop0.body
          leftComponents rightComponents component iter sums =
        ok (cont (iter', accumulateChannel sums leftComponents
          rightComponents component iter.start)) ∧
      iter'.start.val = iter.start.val + 1 ∧
      iter'.end.val = iter.end.val := by
  have hNextSpec :=
    core.iter.range.IteratorRange.next_Usize_some_spec iter hActive
  obtain ⟨⟨option, iter'⟩, hNext, hOption, hStart, hIterEnd⟩ :=
    Aeneas.Std.WP.spec_imp_exists hNextSpec
  rw [hOption] at hNext
  have hChannel : iter.start.val < 3 := by omega
  have hLeftRow := generated_array_index_run_loop
    leftComponents component hComponent
  have hLeft := generated_array_index_run_loop
    leftComponents.val[component.val]! iter.start hChannel
  have hRightRow := generated_array_index_run_loop
    rightComponents component hComponent
  have hRight := generated_array_index_run_loop
    rightComponents.val[component.val]! iter.start hChannel
  have hSumsRow := generated_array_index_run_loop sums component hComponent
  have hSumsValue := generated_array_index_run_loop
    sums.val[component.val]! iter.start hChannel
  have hSumsMut := generated_array_index_mut_run_loop sums component hComponent
  have hRowUpdate := generated_array_update_run_loop
    sums.val[component.val]! iter.start
      (accumulatedChannelValue sums leftComponents rightComponents
        component iter.start) hChannel
  refine ⟨iter', ?_, hStart, congrArg UScalar.val hIterEnd⟩
  unfold
    ComponentBGenerated.aspis_core.field.qm31_accumulate_product_channels_loop0_loop0.body
  simp only [hNext, hLeftRow, hRightRow, hSumsRow, hSumsMut,
    bind_tc_ok, Std.lift]
  change
    (do
      let m ← Array.index_usize leftComponents.val[component.val]!
        iter.start
      let m1 ← Array.index_usize rightComponents.val[component.val]!
        iter.start
      let i3 ← Array.index_usize sums.val[component.val]! iter.start
      let a4 ← Array.update sums.val[component.val]! iter.start
        (Std.U64.wrapping_add i3
          (Std.U64.wrapping_mul (UScalar.cast .U64 m)
            (UScalar.cast .U64 m1)))
      ok (cont (iter', (sums.set component) a4))) =
      ok (cont (iter', accumulateChannel sums leftComponents
        rightComponents component iter.start))
  rw [hLeft]
  simp only [bind_tc_ok]
  rw [hRight]
  simp only [bind_tc_ok]
  rw [hSumsValue]
  simp only [bind_tc_ok]
  change
    (do
      let a4 ← Array.update sums.val[component.val]! iter.start
        (accumulatedChannelValue sums leftComponents rightComponents
          component iter.start)
      ok (cont (iter', (sums.set component) a4))) = _
  rw [hRowUpdate]
  simp only [bind_tc_ok]
  rfl

def ChannelUpdateInvariant
    (base current : Array (Array Std.U64 3#usize) 3#usize)
    (leftComponents rightComponents :
      Array (Array RustM31 3#usize) 3#usize)
    (component processed : Nat) : Prop :=
  ∀ row, row < 3 → ∀ channel, channel < 3 →
    (matrixCell current row channel).val =
      if row = component ∧ channel < processed then
        (matrixCell base row channel).val +
          (channelM31 leftComponents row channel).val *
          (channelM31 rightComponents row channel).val
      else
        (matrixCell base row channel).val

private theorem channel_factor_product_le
    (components : Array (Array RustM31 3#usize) 3#usize)
    (hCanonical : CanonicalChannelMatrix components)
    (row channel : Nat) (hRow : row < 3) (hChannel : channel < 3) :
    (channelM31 components row channel).val ≤ m31Modulus - 1 := by
  have h := hCanonical row hRow channel hChannel
  change (channelM31 components row channel).val < m31Modulus at h
  omega

private theorem channel_product_le_bound
    (leftComponents rightComponents :
      Array (Array RustM31 3#usize) 3#usize)
    (hLeft : CanonicalChannelMatrix leftComponents)
    (hRight : CanonicalChannelMatrix rightComponents)
    (row channel : Nat) (hRow : row < 3) (hChannel : channel < 3) :
    (channelM31 leftComponents row channel).val *
        (channelM31 rightComponents row channel).val ≤
      channelProductBound := by
  have hl := channel_factor_product_le leftComponents hLeft row channel hRow hChannel
  have hr := channel_factor_product_le rightComponents hRight row channel hRow hChannel
  unfold channelProductBound
  nlinarith

private theorem u32_channel_product_no_wrap
    (left right : RustM31) :
    ((Std.U64.wrapping_mul (UScalar.cast .U64 left)
      (UScalar.cast .U64 right)).val) = left.val * right.val := by
  rw [Std.U64.wrapping_mul_val_eq,
    U32.cast_U64_val_eq, U32.cast_U64_val_eq]
  have hl := UScalar.hBounds left
  have hr := UScalar.hBounds right
  have hProduct : left.val * right.val < UScalar.size .U64 := by
    rw [UScalar.size, UScalarTy.U64_numBits_eq]
    norm_num at hl hr ⊢
    nlinarith
  exact Nat.mod_eq_of_lt hProduct

private theorem accumulated_channel_value_no_wrap
    (base : Array (Array Std.U64 3#usize) 3#usize)
    (leftComponents rightComponents :
      Array (Array RustM31 3#usize) 3#usize)
    (component channel : Std.Usize)
    (hBound :
      (matrixCell base component.val channel.val).val +
        (channelM31 leftComponents component.val channel.val).val *
        (channelM31 rightComponents component.val channel.val).val <
          u64Cardinality) :
    (accumulatedChannelValue base leftComponents rightComponents
      component channel).val =
      (matrixCell base component.val channel.val).val +
        (channelM31 leftComponents component.val channel.val).val *
        (channelM31 rightComponents component.val channel.val).val := by
  unfold accumulatedChannelValue
  rw [Std.U64.wrapping_add_val_eq,
    u32_channel_product_no_wrap]
  have hSize : UScalar.size .U64 = u64Cardinality := by
    exact AspisAeneasM31ReduceU64.u64_size_eq
  rw [hSize]
  exact Nat.mod_eq_of_lt hBound

private theorem matrix_cell_accumulate_same
    (sums : Array (Array Std.U64 3#usize) 3#usize)
    (leftComponents rightComponents :
      Array (Array RustM31 3#usize) 3#usize)
    (component channel : Std.Usize)
    (hComponent : component.val < 3) (hChannel : channel.val < 3) :
    matrixCell (accumulateChannel sums leftComponents rightComponents
      component channel) component.val channel.val =
      accumulatedChannelValue sums leftComponents rightComponents
        component channel := by
  unfold matrixCell rowCell accumulateChannel
  simp only [Array.set_val_eq]
  rw [List.set_getElem!_eq _ _ _ _ (by
    exact ⟨by simpa [Array.length_eq] using hComponent, rfl⟩)]
  simp only [Array.set_val_eq]
  rw [List.set_getElem!_eq _ _ _ _ (by
    exact ⟨by simpa [Array.length_eq] using hChannel, rfl⟩)]

private theorem matrix_cell_accumulate_frame
    (sums : Array (Array Std.U64 3#usize) 3#usize)
    (leftComponents rightComponents :
      Array (Array RustM31 3#usize) 3#usize)
    (component channel : Std.Usize)
    (row column : Nat) (hRow : row < 3) (_hColumn : column < 3)
    (hDifferent : row ≠ component.val ∨ column ≠ channel.val) :
    matrixCell (accumulateChannel sums leftComponents rightComponents
      component channel) row column = matrixCell sums row column := by
  unfold matrixCell rowCell accumulateChannel
  simp only [Array.set_val_eq]
  by_cases hSameRow : row = component.val
  · subst row
    rw [List.set_getElem!_eq _ _ _ _ (by
      exact ⟨by simpa [Array.length_eq] using hRow, rfl⟩)]
    simp only [Array.set_val_eq]
    rw [List.set_getElem!_ne _ _ _ _ (by omega)]
  · rw [List.set_getElem!_ne _ _ _ _ (by omega)]

private theorem channel_update_invariant_step
    (base current : Array (Array Std.U64 3#usize) 3#usize)
    (leftComponents rightComponents :
      Array (Array RustM31 3#usize) 3#usize)
    (component channel : Std.Usize)
    (hComponent : component.val < 3) (hChannel : channel.val < 3)
    (hInvariant : ChannelUpdateInvariant base current leftComponents
      rightComponents component.val channel.val)
    (hNoOverflow :
      (matrixCell base component.val channel.val).val +
        (channelM31 leftComponents component.val channel.val).val *
        (channelM31 rightComponents component.val channel.val).val <
          u64Cardinality) :
    ChannelUpdateInvariant base
      (accumulateChannel current leftComponents rightComponents
        component channel)
      leftComponents rightComponents component.val (channel.val + 1) := by
  intro row hRow column hColumn
  by_cases hSameRow : row = component.val
  · by_cases hSameColumn : column = channel.val
    · subst row
      subst column
      rw [matrix_cell_accumulate_same current leftComponents rightComponents
        component channel hComponent hChannel]
      have hOld := hInvariant component.val hComponent channel.val hChannel
      simp at hOld
      rw [accumulated_channel_value_no_wrap current leftComponents
        rightComponents component channel]
      · rw [hOld]
        simp
      · rw [hOld]
        exact hNoOverflow
    · rw [matrix_cell_accumulate_frame current leftComponents
        rightComponents component channel row column hRow hColumn
        (Or.inr hSameColumn)]
      have hOld := hInvariant row hRow column hColumn
      rw [hOld]
      simp only [hSameRow, true_and]
      by_cases hBefore : column < channel.val
      · have hAfter : column < channel.val + 1 := by omega
        rw [if_pos hBefore, if_pos hAfter]
      · have hAfter : ¬ column < channel.val + 1 := by omega
        rw [if_neg hBefore, if_neg hAfter]
  · rw [matrix_cell_accumulate_frame current leftComponents
      rightComponents component channel row column hRow hColumn
      (Or.inl hSameRow)]
    have hOld := hInvariant row hRow column hColumn
    rw [hOld]
    simp [hSameRow]

/-- Direct invariant for the actual generated channel loop.  It adds exactly
one raw channel product to each of the three channels of the selected tower
component and frames all six other cells. -/
theorem generated_channel_loop_corresponds
    (base : Array (Array Std.U64 3#usize) 3#usize)
    (leftComponents rightComponents :
      Array (Array RustM31 3#usize) 3#usize)
    (component : Std.Usize)
    (hComponent : component.val < 3)
    (hNoOverflow : ∀ channel, channel < 3 →
      (matrixCell base component.val channel).val +
        (channelM31 leftComponents component.val channel).val *
        (channelM31 rightComponents component.val channel).val <
          u64Cardinality) :
    ComponentBGenerated.aspis_core.field.qm31_accumulate_product_channels_loop0_loop0
        { start := 0#usize, «end» := 3#usize } base leftComponents
        rightComponents component
      ⦃ out => ChannelUpdateInvariant base out leftComponents
        rightComponents component.val 3 ⦄ := by
  simp only [ComponentBGenerated.aspis_core.field.qm31_accumulate_product_channels_loop0_loop0]
  apply loop.spec_decr_nat
    (fun state : core.ops.range.Range Std.Usize ×
      Array (Array Std.U64 3#usize) 3#usize => 3 - state.1.start.val)
    (fun state => state.1.end.val = 3 ∧ state.1.start.val ≤ 3 ∧
      ChannelUpdateInvariant base state.2 leftComponents rightComponents
        component.val state.1.start.val)
    (fun out => ChannelUpdateInvariant base out leftComponents
      rightComponents component.val 3)
  · rintro ⟨iter, current⟩ ⟨hEnd, hStart, hInvariant⟩
    dsimp only at hEnd hStart hInvariant ⊢
    by_cases hActive : iter.start.val < iter.end.val
    · obtain ⟨iter', hBody, hNextStart, hNextEnd⟩ :=
        generated_channel_body_active leftComponents rightComponents
          component iter current hComponent hActive hEnd
      rw [hBody]
      simp only [Aeneas.Std.WP.spec_ok]
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · rw [hNextEnd]
        exact hEnd
      · rw [hNextStart]
        omega
      · rw [hNextStart]
        apply channel_update_invariant_step base current leftComponents
          rightComponents component iter.start hComponent
          (by omega) hInvariant
        exact hNoOverflow iter.start.val (by omega)
      · rw [hNextStart]
        omega
    · have hDone : iter.start.val = 3 := by omega
      have hNextSpec := core.iter.range.IteratorRange.next_Usize_none_spec
        iter (by omega)
      obtain ⟨⟨option, iter'⟩, hNext, hOption, hIter⟩ :=
        Aeneas.Std.WP.spec_imp_exists hNextSpec
      rw [hOption, hIter] at hNext
      unfold
        ComponentBGenerated.aspis_core.field.qm31_accumulate_product_channels_loop0_loop0.body
      rw [hNext]
      simpa [hDone] using hInvariant
  · refine ⟨by norm_num, by norm_num, ?_⟩
    intro row hRow channel hChannel
    simp

#print axioms four_channel_products_fit_u64
#print axioms five_channel_products_exceed_u64_bound
#print axioms generated_channel_loop_corresponds

end AspisLane5QM31SumProductsProof
