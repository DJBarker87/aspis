import SumProductsLoop

/-!
# The generated component loop

The generated middle loop invokes the already-proved generated channel loop
for components `c0`, `c1`, and `c0+c1`, in that source order.
-/

open Aeneas Aeneas.Std Result ControlFlow

namespace AspisLane5QM31SumProductsProof

def ComponentUpdateInvariant
    (base current : Array (Array Std.U64 3#usize) 3#usize)
    (leftComponents rightComponents :
      Array (Array RustM31 3#usize) 3#usize)
    (processed : Nat) : Prop :=
  ∀ row, row < 3 → ∀ channel, channel < 3 →
    (matrixCell current row channel).val =
      if row < processed then
        (matrixCell base row channel).val +
          (channelM31 leftComponents row channel).val *
          (channelM31 rightComponents row channel).val
      else
        (matrixCell base row channel).val

private theorem component_update_invariant_step
    (base current out : Array (Array Std.U64 3#usize) 3#usize)
    (leftComponents rightComponents :
      Array (Array RustM31 3#usize) 3#usize)
    (component : Std.Usize)
    (_hComponent : component.val < 3)
    (hOuter : ComponentUpdateInvariant base current leftComponents
      rightComponents component.val)
    (hInner : ChannelUpdateInvariant current out leftComponents
      rightComponents component.val 3) :
    ComponentUpdateInvariant base out leftComponents rightComponents
      (component.val + 1) := by
  intro row hRow channel hChannel
  have hInnerCell := hInner row hRow channel hChannel
  have hOuterCell := hOuter row hRow channel hChannel
  by_cases hSame : row = component.val
  · subst row
    simp at hOuterCell
    simp [hOuterCell, hChannel] at hInnerCell
    simpa using hInnerCell
  · have hInnerFrame :
        (matrixCell out row channel).val =
          (matrixCell current row channel).val := by
      simpa [hSame] using hInnerCell
    rw [hInnerFrame, hOuterCell]
    by_cases hBefore : row < component.val
    · have hAfter : row < component.val + 1 := by omega
      rw [if_pos hBefore, if_pos hAfter]
    · have hAfter : ¬ row < component.val + 1 := by omega
      rw [if_neg hBefore, if_neg hAfter]

private theorem generated_component_body_active
    (leftComponents rightComponents :
      Array (Array RustM31 3#usize) 3#usize)
    (iter : core.ops.range.Range Std.Usize)
    (current : Array (Array Std.U64 3#usize) 3#usize)
    (hActive : iter.start.val < iter.end.val)
    (hEnd : iter.end.val = 3)
    (hNoOverflow : ∀ channel, channel < 3 →
      (matrixCell current iter.start.val channel).val +
        (channelM31 leftComponents iter.start.val channel).val *
        (channelM31 rightComponents iter.start.val channel).val <
          u64Cardinality) :
    ∃ iter' out,
      ComponentBGenerated.aspis_core.field.qm31_accumulate_product_channels_loop0.body
          leftComponents rightComponents iter current =
        ok (cont (iter', out)) ∧
      iter'.start.val = iter.start.val + 1 ∧
      iter'.end.val = iter.end.val ∧
      ChannelUpdateInvariant current out leftComponents rightComponents
        iter.start.val 3 := by
  have hNextSpec :=
    core.iter.range.IteratorRange.next_Usize_some_spec iter hActive
  obtain ⟨⟨option, iter'⟩, hNext, hOption, hStart, hIterEnd⟩ :=
    Aeneas.Std.WP.spec_imp_exists hNextSpec
  rw [hOption] at hNext
  have hComponent : iter.start.val < 3 := by omega
  have hChannelSpec := generated_channel_loop_corresponds current
    leftComponents rightComponents iter.start hComponent hNoOverflow
  obtain ⟨out, hChannelRun, hChannelPost⟩ :=
    Aeneas.Std.WP.spec_imp_exists hChannelSpec
  refine ⟨iter', out, ?_, hStart, congrArg UScalar.val hIterEnd,
    hChannelPost⟩
  unfold
    ComponentBGenerated.aspis_core.field.qm31_accumulate_product_channels_loop0.body
  rw [hNext]
  simp only [bind_tc_ok]
  change
    (do
      let sums1 ←
        ComponentBGenerated.aspis_core.field.qm31_accumulate_product_channels_loop0_loop0
          { start := 0#usize, «end» := 3#usize } current
          leftComponents rightComponents iter.start
      ok (cont (iter', sums1))) = ok (cont (iter', out))
  rw [hChannelRun]
  simp only [bind_tc_ok]

/-- Direct invariant for the actual generated component loop.  On success it
has updated all nine `(tower component, CM31 channel)` cells exactly once. -/
theorem generated_component_loop_corresponds
    (base : Array (Array Std.U64 3#usize) 3#usize)
    (leftComponents rightComponents :
      Array (Array RustM31 3#usize) 3#usize)
    (hNoOverflow : ∀ row, row < 3 → ∀ channel, channel < 3 →
      (matrixCell base row channel).val +
        (channelM31 leftComponents row channel).val *
        (channelM31 rightComponents row channel).val <
          u64Cardinality) :
    ComponentBGenerated.aspis_core.field.qm31_accumulate_product_channels_loop0
        { start := 0#usize, «end» := 3#usize } base leftComponents
        rightComponents
      ⦃ out => ComponentUpdateInvariant base out leftComponents
        rightComponents 3 ⦄ := by
  simp only [ComponentBGenerated.aspis_core.field.qm31_accumulate_product_channels_loop0]
  apply loop.spec_decr_nat
    (fun state : core.ops.range.Range Std.Usize ×
      Array (Array Std.U64 3#usize) 3#usize => 3 - state.1.start.val)
    (fun state => state.1.end.val = 3 ∧ state.1.start.val ≤ 3 ∧
      ComponentUpdateInvariant base state.2 leftComponents rightComponents
        state.1.start.val)
    (fun out => ComponentUpdateInvariant base out leftComponents
      rightComponents 3)
  · rintro ⟨iter, current⟩ ⟨hEnd, hStart, hInvariant⟩
    dsimp only at hEnd hStart hInvariant ⊢
    by_cases hActive : iter.start.val < iter.end.val
    · have hComponent : iter.start.val < 3 := by omega
      have hCurrentNoOverflow : ∀ channel, channel < 3 →
          (matrixCell current iter.start.val channel).val +
            (channelM31 leftComponents iter.start.val channel).val *
            (channelM31 rightComponents iter.start.val channel).val <
              u64Cardinality := by
        intro channel hChannel
        have hCurrent := hInvariant iter.start.val hComponent channel hChannel
        have hNotBefore : ¬ iter.start.val < iter.start.val := by omega
        rw [if_neg hNotBefore] at hCurrent
        rw [hCurrent]
        exact hNoOverflow iter.start.val hComponent channel hChannel
      obtain ⟨iter', out, hBody, hNextStart, hNextEnd, hInner⟩ :=
        generated_component_body_active leftComponents rightComponents
          iter current hActive hEnd hCurrentNoOverflow
      rw [hBody]
      simp only [Aeneas.Std.WP.spec_ok]
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · rw [hNextEnd]
        exact hEnd
      · rw [hNextStart]
        omega
      · rw [hNextStart]
        exact component_update_invariant_step base current out
          leftComponents rightComponents iter.start hComponent hInvariant
          hInner
      · rw [hNextStart]
        omega
    · have hDone : iter.start.val = 3 := by omega
      have hNextSpec := core.iter.range.IteratorRange.next_Usize_none_spec
        iter (by omega)
      obtain ⟨⟨option, iter'⟩, hNext, hOption, hIter⟩ :=
        Aeneas.Std.WP.spec_imp_exists hNextSpec
      rw [hOption, hIter] at hNext
      unfold
        ComponentBGenerated.aspis_core.field.qm31_accumulate_product_channels_loop0.body
      rw [hNext]
      simpa [hDone] using hInvariant
  · refine ⟨by norm_num, by norm_num, ?_⟩
    intro row hRow channel hChannel
    simp

def zeroU64ChannelMatrix :
    Array (Array Std.U64 3#usize) 3#usize :=
  Array.repeat 3#usize (Array.repeat 3#usize 0#u64)

def zeroM31ChannelMatrix :
    Array (Array RustM31 3#usize) 3#usize :=
  Array.repeat 3#usize (Array.repeat 3#usize 0#u32)

private theorem zero_u64_channel_cell
    (row channel : Nat) (hRow : row < 3) (hChannel : channel < 3) :
    matrixCell zeroU64ChannelMatrix row channel = 0#u64 := by
  have hRow' : row < (3#usize).val := by simpa using hRow
  have hChannel' : channel < (3#usize).val := by simpa using hChannel
  unfold matrixCell rowCell zeroU64ChannelMatrix
  rw [Array.repeat_val, List.getElem!_replicate _ hRow']
  rw [Array.repeat_val, List.getElem!_replicate _ hChannel']

private theorem zero_m31_channel_cell
    (row channel : Nat) (hRow : row < 3) (hChannel : channel < 3) :
    channelM31 zeroM31ChannelMatrix row channel = 0#u32 := by
  have hRow' : row < (3#usize).val := by simpa using hRow
  have hChannel' : channel < (3#usize).val := by simpa using hChannel
  unfold channelM31 zeroM31ChannelMatrix
  rw [Array.repeat_val, List.getElem!_replicate _ hRow']
  rw [Array.repeat_val, List.getElem!_replicate _ hChannel']

/-- Concrete non-vacuity witness for the full generated nine-cell component
loop: all-zero channels satisfy the real no-overflow premise and the generated
loop returns successfully. -/
theorem generated_component_loop_zero_nonvacuous :
    ∃ out,
      ComponentBGenerated.aspis_core.field.qm31_accumulate_product_channels_loop0
          { start := 0#usize, «end» := 3#usize }
          zeroU64ChannelMatrix zeroM31ChannelMatrix zeroM31ChannelMatrix =
        ok out ∧
      ComponentUpdateInvariant zeroU64ChannelMatrix out
        zeroM31ChannelMatrix zeroM31ChannelMatrix 3 := by
  have hNoOverflow : ∀ row, row < 3 → ∀ channel, channel < 3 →
      (matrixCell zeroU64ChannelMatrix row channel).val +
        (channelM31 zeroM31ChannelMatrix row channel).val *
        (channelM31 zeroM31ChannelMatrix row channel).val <
          u64Cardinality := by
    intro row hRow channel hChannel
    rw [zero_u64_channel_cell row channel hRow hChannel,
      zero_m31_channel_cell row channel hRow hChannel]
    norm_num [u64Cardinality]
  have hSpec := generated_component_loop_corresponds zeroU64ChannelMatrix
    zeroM31ChannelMatrix zeroM31ChannelMatrix hNoOverflow
  obtain ⟨out, hRun, hPost⟩ := Aeneas.Std.WP.spec_imp_exists hSpec
  exact ⟨out, hRun, hPost⟩

#print axioms generated_component_loop_corresponds
#print axioms generated_component_loop_zero_nonvacuous

end AspisLane5QM31SumProductsProof
