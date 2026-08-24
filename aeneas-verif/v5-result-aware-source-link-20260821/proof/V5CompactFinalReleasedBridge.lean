import V5CompactFinalSourceUnroll
import V5CompactFinalFieldSemantics

/-!
# Released-selector bridge for the compact final scatter

The extracted source accepts a selector byte in each compact block.  The
arithmetic normal form is intentionally specialized to the released selector
table `[0, 1, 2, 3, 4, 5, 6, 28, 29, 30]`.  This module states that premise
explicitly and proves the two programs equal under it.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5CompactFinalReleasedBridge

open V5RelationCompactFinalGenerated

abbrev State :=
  V5RelationCompactFinalGenerated.v5_cu_probe.CompactBTerminalWeights

abbrev Raw := V5RelationCompactFinalGenerated.aspis_core.field.QM31
abbrev Block :=
  V5RelationCompactFinalGenerated.v5_cu_probe.CompactBTerminalBlock

local instance : Inhabited Raw :=
  ⟨V5RelationCompactFinalGenerated.aspis_core.field.QM31.ZERO⟩

local instance : Inhabited Block :=
  ⟨{ scale := V5RelationCompactFinalGenerated.aspis_core.field.QM31.ZERO
     power_lo := V5RelationCompactFinalGenerated.aspis_core.field.QM31.ZERO
     power_hi := V5RelationCompactFinalGenerated.aspis_core.field.QM31.ZERO
     selector := 0#u8 }⟩

private theorem fixedArray_getBang_eq_get
    {T : Type} [Inhabited T] {count : Std.Usize}
    (values : Array T count) (index : Fin count.val) :
    values.val[index.val]! = values.val[index.val] := by
  apply List.getElem!_of_getElem?
  simp [index.isLt]

private theorem array_index_run
    {T : Type} [Inhabited T] {count : Std.Usize}
    (values : Array T count) (index : Std.Usize)
    (bound : index.val < count.val) :
    Array.index_usize values index = .ok values.val[index.val]! := by
  obtain ⟨value, run, valueExact⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_usize_spec values index (by
      simpa [Array.length_eq] using bound))
  have listBound : index.val < values.val.length := by
    simpa [Array.length_eq] using bound
  have bangExact : values.val[index.val]! = values.val[index.val]'listBound := by
    apply List.getElem!_of_getElem?
    simp
  simpa [valueExact, bangExact] using run

private theorem array_index_zero
    {T : Type} [Inhabited T] (values : Array T 4#usize) :
    Array.index_usize values 0#usize = .ok values.val[0]! := by
  exact array_index_run values 0#usize (by decide)

private theorem array_index_three
    {T : Type} [Inhabited T] (values : Array T 4#usize) :
    Array.index_usize values 3#usize = .ok values.val[3]! := by
  exact array_index_run values 3#usize (by decide)

private theorem array_update_run
    {T : Type} {count : Std.Usize}
    (values : Array T count) (index : Std.Usize) (value : T)
    (bound : index.val < count.val) :
    Array.update values index value = .ok (values.set index value) := by
  obtain ⟨output, run, outputExact⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.update_spec values index value (by
      simpa [Array.length_eq] using bound))
  simpa [outputExact] using run

private theorem array_update_zero
    {T : Type} (values : Array T 4#usize) (value : T) :
    Array.update values 0#usize value = .ok (values.set 0#usize value) := by
  exact array_update_run values 0#usize value (by decide)

private theorem array_update_three
    {T : Type} (values : Array T 4#usize) (value : T) :
    Array.update values 3#usize value = .ok (values.set 3#usize value) := by
  exact array_update_run values 3#usize value (by decide)

private theorem selector_zero
    (state : State)
    (selectors : AspisV5CompactFinalFieldSemantics.ReleasedSelectors state) :
    (AspisV5CompactFinalFieldSemantics.blockAt state 0).selector = 0#u8 := by
  apply UScalar.eq_of_val_eq
  simpa [AspisV5CompactTerminal.blockSelector] using selectors 0

private theorem selector_one
    (state : State)
    (selectors : AspisV5CompactFinalFieldSemantics.ReleasedSelectors state) :
    (AspisV5CompactFinalFieldSemantics.blockAt state 1).selector = 1#u8 := by
  apply UScalar.eq_of_val_eq
  simpa [AspisV5CompactTerminal.blockSelector] using selectors 1

private theorem selector_two
    (state : State)
    (selectors : AspisV5CompactFinalFieldSemantics.ReleasedSelectors state) :
    (AspisV5CompactFinalFieldSemantics.blockAt state 2).selector = 2#u8 := by
  apply UScalar.eq_of_val_eq
  simpa [AspisV5CompactTerminal.blockSelector] using selectors 2

private theorem selector_three
    (state : State)
    (selectors : AspisV5CompactFinalFieldSemantics.ReleasedSelectors state) :
    (AspisV5CompactFinalFieldSemantics.blockAt state 3).selector = 3#u8 := by
  apply UScalar.eq_of_val_eq
  simpa [AspisV5CompactTerminal.blockSelector] using selectors 3

private theorem selector_four
    (state : State)
    (selectors : AspisV5CompactFinalFieldSemantics.ReleasedSelectors state) :
    (AspisV5CompactFinalFieldSemantics.blockAt state 4).selector = 4#u8 := by
  apply UScalar.eq_of_val_eq
  simpa [AspisV5CompactTerminal.blockSelector] using selectors 4

private theorem selector_five
    (state : State)
    (selectors : AspisV5CompactFinalFieldSemantics.ReleasedSelectors state) :
    (AspisV5CompactFinalFieldSemantics.blockAt state 5).selector = 5#u8 := by
  apply UScalar.eq_of_val_eq
  simpa [AspisV5CompactTerminal.blockSelector] using selectors 5

private theorem selector_six
    (state : State)
    (selectors : AspisV5CompactFinalFieldSemantics.ReleasedSelectors state) :
    (AspisV5CompactFinalFieldSemantics.blockAt state 6).selector = 6#u8 := by
  apply UScalar.eq_of_val_eq
  simpa [AspisV5CompactTerminal.blockSelector] using selectors 6

private theorem selector_seven
    (state : State)
    (selectors : AspisV5CompactFinalFieldSemantics.ReleasedSelectors state) :
    (AspisV5CompactFinalFieldSemantics.blockAt state 7).selector = 28#u8 := by
  apply UScalar.eq_of_val_eq
  simpa [AspisV5CompactTerminal.blockSelector] using selectors 7

private theorem selector_eight
    (state : State)
    (selectors : AspisV5CompactFinalFieldSemantics.ReleasedSelectors state) :
    (AspisV5CompactFinalFieldSemantics.blockAt state 8).selector = 29#u8 := by
  apply UScalar.eq_of_val_eq
  simpa [AspisV5CompactTerminal.blockSelector] using selectors 8

private theorem selector_nine
    (state : State)
    (selectors : AspisV5CompactFinalFieldSemantics.ReleasedSelectors state) :
    (AspisV5CompactFinalFieldSemantics.blockAt state 9).selector = 30#u8 := by
  apply UScalar.eq_of_val_eq
  simpa [AspisV5CompactTerminal.blockSelector] using selectors 9

theorem generated_final_weights_eq_released_program
    (state : State)
    (selectors : AspisV5CompactFinalFieldSemantics.ReleasedSelectors state) :
    V5RelationCompactFinalGenerated.v5_cu_probe.CompactBTerminalWeights.final_weights
        state = AspisV5CompactFinalFieldSemantics.finalProgram state := by
  rw [AspisV5CompactFinalSourceUnroll.final_weights_eq_unrolled]
  have s0 := selector_zero state selectors
  have s1 := selector_one state selectors
  have s2 := selector_two state selectors
  have s3 := selector_three state selectors
  have s4 := selector_four state selectors
  have s5 := selector_five state selectors
  have s6 := selector_six state selectors
  have s7 := selector_seven state selectors
  have s8 := selector_eight state selectors
  have s9 := selector_nine state selectors
  unfold AspisV5CompactFinalSourceUnroll.unrolled
    AspisV5CompactFinalSourceUnroll.step
  rw [show (state.blocks.val[0]!).selector = 0#u8 by
      simpa [AspisV5CompactFinalFieldSemantics.blockAt] using s0,
    show (state.blocks.val[1]!).selector = 1#u8 by
      simpa [AspisV5CompactFinalFieldSemantics.blockAt] using s1,
    show (state.blocks.val[2]!).selector = 2#u8 by
      simpa [AspisV5CompactFinalFieldSemantics.blockAt] using s2,
    show (state.blocks.val[3]!).selector = 3#u8 by
      simpa [AspisV5CompactFinalFieldSemantics.blockAt] using s3,
    show (state.blocks.val[4]!).selector = 4#u8 by
      simpa [AspisV5CompactFinalFieldSemantics.blockAt] using s4,
    show (state.blocks.val[5]!).selector = 5#u8 by
      simpa [AspisV5CompactFinalFieldSemantics.blockAt] using s5,
    show (state.blocks.val[6]!).selector = 6#u8 by
      simpa [AspisV5CompactFinalFieldSemantics.blockAt] using s6,
    show (state.blocks.val[7]!).selector = 28#u8 by
      simpa [AspisV5CompactFinalFieldSemantics.blockAt] using s7,
    show (state.blocks.val[8]!).selector = 29#u8 by
      simpa [AspisV5CompactFinalFieldSemantics.blockAt] using s8,
    show (state.blocks.val[9]!).selector = 30#u8 by
      simpa [AspisV5CompactFinalFieldSemantics.blockAt] using s9]
  have shift0 : Std.U8.wrapping_shr 0#u8 3#u32 = 0#u8 := by decide
  have shift1 : Std.U8.wrapping_shr 1#u8 3#u32 = 0#u8 := by decide
  have shift2 : Std.U8.wrapping_shr 2#u8 3#u32 = 0#u8 := by decide
  have shift3 : Std.U8.wrapping_shr 3#u8 3#u32 = 0#u8 := by decide
  have shift4 : Std.U8.wrapping_shr 4#u8 3#u32 = 0#u8 := by decide
  have shift5 : Std.U8.wrapping_shr 5#u8 3#u32 = 0#u8 := by decide
  have shift6 : Std.U8.wrapping_shr 6#u8 3#u32 = 0#u8 := by decide
  have shift28 : Std.U8.wrapping_shr 28#u8 3#u32 = 3#u8 := by decide
  have shift29 : Std.U8.wrapping_shr 29#u8 3#u32 = 3#u8 := by decide
  have shift30 : Std.U8.wrapping_shr 30#u8 3#u32 = 3#u8 := by decide
  rw [shift0, shift1, shift2, shift3, shift4, shift5, shift6,
    shift28, shift29, shift30]
  simp only [Aeneas.Std.lift, bind_tc_ok]
  have cast0 : core.convert.num.FromUsizeU8.from 0#u8 = 0#usize := by
    apply UScalar.eq_of_val_eq
    simp
  have cast3 : core.convert.num.FromUsizeU8.from 3#u8 = 3#usize := by
    apply UScalar.eq_of_val_eq
    simp
  rw [cast0, cast3]
  have finalValues :
      V5RelationCompactFinalGenerated.v5_cu_probe.V5_CU_PROBE_RELATION_FINAL_VALUES =
        4#usize := by
    unfold V5RelationCompactFinalGenerated.v5_cu_probe.V5_CU_PROBE_RELATION_FINAL_VALUES
    rfl
  rw [finalValues]
  have finalIndex : Std.Usize.wrapping_sub 4#usize 1#usize = 3#usize := by
    apply UScalar.eq_of_val_eq
    rw [Std.Usize.wrapping_sub_val_eq, UScalar.size_UScalarTyUsize]
    rcases System.Platform.numBits_eq with h | h <;>
      simp [Usize.size, Usize.numBits, h]
  rw [finalIndex]
  unfold AspisV5CompactFinalFieldSemantics.finalProgram
    AspisV5CompactFinalFieldSemantics.blockAt
  simp only [array_index_zero, array_index_three,
    array_update_zero, array_update_three, bind_tc_ok]
  simp [Array.repeat, Aeneas.Std.Array.make]
  intros
  apply Subtype.ext
  simp [Array.set_val_eq]

#print axioms generated_final_weights_eq_released_program

end AspisV5CompactFinalReleasedBridge
