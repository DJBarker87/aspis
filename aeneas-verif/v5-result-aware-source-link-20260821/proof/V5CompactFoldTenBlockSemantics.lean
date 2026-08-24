import V5CompactFoldIteratorSemantics
import V5CompactFoldSourceModel

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V5CompactFoldSource

open V5RelationCompactFoldGenerated
open AspisV5RelationCompactFoldKernelProof
open V5CompactFoldIteratorSemantics

local instance : Inhabited Block :=
  ⟨{ scale := aspis_core.field.QM31.ZERO
     power_lo := aspis_core.field.QM31.ZERO
     power_hi := aspis_core.field.QM31.ZERO
     selector := 0#u8 }⟩

private theorem list_get_eq_getElemBang
    {T : Type} [Inhabited T]
    (values : List T) (index : Nat) (hIndex : index < values.length) :
    values[index] = values[index]! := by
  symm
  apply List.getElem!_of_getElem?
  simp [hIndex]

@[simp] theorem rebuilt_slice_get_eq_bang
    {T : Type} [Inhabited T] (slice : Slice T) (index : Nat)
    (bound : index < slice.val.length) :
    slice[index]'(by simpa only using bound) = slice.val[index]! := by
  change slice.val[index]'(by simpa only using bound) = slice.val[index]!
  simpa only using list_get_eq_getElemBang slice.val index bound

private theorem array_index_run
    {T : Type} [Inhabited T] {count : Std.Usize}
    (values : Array T count) (index : Std.Usize)
    (hIndex : index.val < count.val) :
    Array.index_usize values index = ok values.val[index.val]! := by
  obtain ⟨value, run, valueExact⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_usize_spec values index (by
      simpa [Array.length_eq] using hIndex))
  have arrayBound : index.val < values.val.length := by
    simpa [Array.length_eq] using hIndex
  have getExact := list_get_eq_getElemBang values.val index.val arrayBound
  simpa [valueExact, getExact] using run

theorem foldBlock_zero (alpha alpha2 alpha3 : Raw)
    (prepared : Array Prepared 3#usize) (block : Block) :
    foldBlock 0#u8 alpha alpha2 alpha3 prepared block =
      foldZeroBlock prepared block := by
  rfl

theorem ten_reverse_sets_exact (values : List Block)
    (lengthExact : values.length = 10)
    (output0 output1 output2 output3 output4 output5 output6 output7 output8
      output9 : Block) :
    ((((((((((values.set 9 output9).set 8 output8).set 7 output7).set 6
      output6).set 5 output5).set 4 output4).set 3 output3).set 2 output2).set
      1 output1).set 0 output0) =
      [output0, output1, output2, output3, output4, output5, output6, output7,
        output8, output9] := by
  apply List.ext_getElem
  · simp [lengthExact]
  · intro index leftBound rightBound
    have indexBound : index < 10 := by simpa using rightBound
    have indexCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
        index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 ∨
        index = 9 := by omega
    rcases indexCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> simp [lengthExact]

theorem ten_list_eta (values : List Block) (lengthExact : values.length = 10) :
    values = [values[0]!, values[1]!, values[2]!, values[3]!, values[4]!,
      values[5]!, values[6]!, values[7]!, values[8]!, values[9]!] := by
  apply List.ext_getElem
  · simp [lengthExact]
  · intro index leftBound rightBound
    have indexBound : index < 10 := by
      rw [lengthExact] at leftBound
      exact leftBound
    have indexCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
        index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 ∨
        index = 9 := by omega
    rcases indexCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> simp [lengthExact]

theorem generated_zero_loop_ten
    (alpha alpha2 alpha3 : Raw)
    (prepared : Array Prepared 3#usize)
    (blocks : Array Block 10#usize) :
    v5_cu_probe.CompactBTerminalWeights.fold_loop
        { slice := Array.to_slice blocks } (fun current => current) 0#u8
        alpha alpha2 alpha3 prepared =
      zeroBackN 10 prepared { slice := Array.to_slice blocks }
        (fun current => current) := by
  apply generated_zero_loop_eq_zeroBackN
  change 0 + 10 = blocks.val.length
  simpa using blocks.property.symm

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 24000 in
theorem fold_zero_success_unrolled
    (state output : State) (alpha : Raw)
    (foldExact : state.folds = 0#u8)
    (run : V5CompactFoldCorrectedWrapper.fold state alpha = .ok output) :
    unrolledFold state alpha = .ok output := by
  rcases state with ⟨blocks, deltaScale, folds⟩
  simp only at foldExact
  subst folds
  unfold V5CompactFoldCorrectedWrapper.fold at run
  simp only [
    MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter,
    bind_tc_ok] at run
  simp only [generated_zero_loop_ten] at run
  have index0 := array_index_run blocks 0#usize (by decide)
  have index1 := array_index_run blocks 1#usize (by decide)
  have index2 := array_index_run blocks 2#usize (by decide)
  have index3 := array_index_run blocks 3#usize (by decide)
  have index4 := array_index_run blocks 4#usize (by decide)
  have index5 := array_index_run blocks 5#usize (by decide)
  have index6 := array_index_run blocks 6#usize (by decide)
  have index7 := array_index_run blocks 7#usize (by decide)
  have index8 := array_index_run blocks 8#usize (by decide)
  have index9 := array_index_run blocks 9#usize (by decide)
  have blocksEta : blocks.val =
      [blocks.val[0]!, blocks.val[1]!, blocks.val[2]!, blocks.val[3]!,
        blocks.val[4]!, blocks.val[5]!, blocks.val[6]!, blocks.val[7]!,
        blocks.val[8]!, blocks.val[9]!] :=
    ten_list_eta blocks.val (by simpa using blocks.property)
  convert run using 1 <;>
    simp (config := { maxSteps := 2000000 })
    [unrolledFold, foldBlock_zero,
      zeroBackN, core.slice.iter.IteratorIterMut.next, Slice.setAtNat,
      Array.to_slice, Array.from_slice, Slice.getElem_Nat_eq,
      rebuilt_slice_get_eq_bang, Array.getElem_Nat_eq, Array.val_to_slice,
      Array.make,
      index0, index1, index2, index3, index4,
      index5, index6, index7, index8, index9,
      ten_reverse_sets_exact]
  all_goals intros <;> rfl

#print axioms generated_zero_loop_ten
#print axioms fold_zero_success_unrolled

end V5CompactFoldSource
