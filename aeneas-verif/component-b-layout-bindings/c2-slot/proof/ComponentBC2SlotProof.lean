import ComponentBC2SlotGenerated
import ComponentBEncodedMessageBindingProof

open Aeneas Aeneas.Std Result ControlFlow Error

namespace ComponentBC2SlotProof

open ComponentBGenerated
open ComponentBC2SlotGenerated
open ComponentBLayoutBindingsProof

abbrev QM31 := ComponentBGenerated.aspis_core.field.QM31
abbrev Lane :=
  ComponentBGenerated.v5_mask.spend_messages.V5StructuredBLane

private theorem component_b_message_values_loop_exact
    (componentB : Lane) (values : alloc.vec.Vec QM31)
    (row : Std.Usize) (hrow : row.val ≤ 1024)
    (hprefix : values.val = componentB.values.val.take row.val) :
    component_b_message_values_loop componentB values row ⦃ out =>
      out.val = componentB.values.val ⦄ := by
  simp only [component_b_message_values_loop]
  apply loop.spec_decr_nat
    (fun state : alloc.vec.Vec QM31 × Std.Usize => 1024 - state.2.val)
    (fun state =>
      state.2.val ≤ 1024 ∧
        state.1.val = componentB.values.val.take state.2.val)
    (fun out : alloc.vec.Vec QM31 => out.val = componentB.values.val)
  · rintro ⟨current, currentRow⟩ ⟨hcurrentBound, hcurrentPrefix⟩
    have hcurrentBound' : currentRow.val ≤ 1024 := by
      simpa only using hcurrentBound
    have hcurrentPrefix' :
        current.val = componentB.values.val.take currentRow.val := by
      simpa only using hcurrentPrefix
    unfold component_b_message_values_loop.body
    by_cases hactive : currentRow < V5_TRACE_ROWS
    · rw [if_pos hactive]
      have hactiveVal : currentRow.val < 1024 := by
        simpa [V5_TRACE_ROWS] using hactive
      obtain ⟨value, hindex, hvalue⟩ := Aeneas.Std.WP.spec_imp_exists
        (Array.index_usize_spec componentB.values currentRow (by
          simpa [Array.length_eq] using hactiveVal))
      rw [hindex]
      simp only [bind_tc_ok]
      have hcapacity : current.val.length < Std.Usize.max := by
        rw [hcurrentPrefix', List.length_take,
          Array.length_eq componentB.values]
        have hmax : 1024 < Std.Usize.max := by
          have h := (1025#usize).hSize
          scalar_tac
        omega
      obtain ⟨next, hpush, hnextValues⟩ := Aeneas.Std.WP.spec_imp_exists
        (alloc.vec.Vec.push_spec current value hcapacity)
      rw [hpush]
      simp only [bind_tc_ok, lift]
      have hnextRow :
          (currentRow.wrapping_add 1#usize).val = currentRow.val + 1 := by
        apply ComponentBLayoutBindingsProof.wrapping_add_val_of_lt
        have hsize : 1025 < Usize.size := by
          simpa using UScalar.hSize (1025#usize)
        calc
          currentRow.val + (1#usize).val = currentRow.val + 1 := rfl
          _ < 1025 := by omega
          _ < Usize.size := hsize
      simp only [WP.spec, WP.theta]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [hnextRow]
        omega
      · rw [hnextValues, hcurrentPrefix', hvalue, hnextRow]
        have hlistBound :
            currentRow.val < componentB.values.val.length := by
          simpa [Array.length_eq] using hactiveVal
        exact List.take_append_getElem hlistBound
      · rw [hnextRow]
        omega
    · rw [if_neg hactive]
      simp only [WP.spec, WP.theta, WP.wp_return]
      have hdone : currentRow.val = 1024 := by
        have hnot : ¬ currentRow.val < 1024 := by
          intro hsmall
          exact hactive (by simpa [V5_TRACE_ROWS] using hsmall)
        omega
      rw [hcurrentPrefix', hdone]
      apply List.take_of_length_le
      have hlength : componentB.values.val.length = 1024 := by
        exact Array.length_eq componentB.values
      omega
  · exact ⟨hrow, hprefix⟩

/-- The generated source helper copies all 1,024 Component-B values in exact
increasing physical-row order. -/
theorem extracted_component_b_message_values_exact
    (componentB : Lane) :
    component_b_message_values componentB ⦃ out =>
      out.val = componentB.values.val ⦄ := by
  unfold component_b_message_values
  apply component_b_message_values_loop_exact
  · norm_num
  · simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]

/-- The generated move-only C2 constructor places the Component-B vector in
exactly slot one. -/
theorem extracted_assemble_v5_c2_messages_slot_one
    (hcopy componentB componentC : alloc.vec.Vec QM31) :
    assemble_v5_c2_messages hcopy componentB componentC =
      ok (Array.make 3#usize [hcopy, componentB, componentC]) ∧
    (Array.make 3#usize [hcopy, componentB, componentC]).val[1]! = componentB := by
  constructor
  · rfl
  · rfl

end ComponentBC2SlotProof
