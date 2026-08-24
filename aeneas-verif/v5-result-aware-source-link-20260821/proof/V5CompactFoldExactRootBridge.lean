import V5CompactFoldExactIteratorBridge

namespace AspisV5CompactFoldExactRootBridge

open Aeneas Aeneas.Std Result ControlFlow Error
open AspisV5CompactFoldExactCallerBridge
open AspisV5CompactFoldExactIteratorBridge
open V5RelationCompactFoldGeneratedExact

local instance : Inhabited Block :=
  ⟨{ scale :=
        V5RelationCompactFoldGeneratedExact.aspis_core.field.QM31.ZERO
     power_lo :=
        V5RelationCompactFoldGeneratedExact.aspis_core.field.QM31.ZERO
     power_hi :=
        V5RelationCompactFoldGeneratedExact.aspis_core.field.QM31.ZERO
     selector := 0#u8 }⟩

private theorem list_get_eq_getElemBang
    {T : Type} [Inhabited T] (values : List T) (index : Nat)
    (hIndex : index < values.length) : values[index] = values[index]! := by
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
        index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 ∨
        index = 8 ∨ index = 9 := by omega
    rcases indexCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> simp [lengthExact]

theorem generated_loop_ten (folds : Std.U8) (foldBound : folds.val < 4)
    (alpha alpha2 alpha3 : Raw) (prepared : Array Prepared 3#usize)
    (blocks : Array Block 10#usize) :
    V5RelationCompactFoldGeneratedExact.v5_cu_probe.CompactBTerminalWeights.fold_loop
        { slice := Array.to_slice blocks } (fun current => current) folds
        alpha alpha2 alpha3 prepared =
      sourceIterN 10 folds alpha alpha2 alpha3 prepared
        { slice := Array.to_slice blocks } (fun current => current) := by
  apply generated_loop_eq_sourceIterN 10 folds foldBound
  change 0 + 10 = blocks.val.length
  simpa using blocks.property.symm

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 24000 in
theorem generated_fold_eq_unrolled (state : ExactState) (alpha : ExactRaw)
    (foldBound : state.folds.val < 4) :
    V5RelationCompactFoldGeneratedExact.v5_cu_probe.CompactBTerminalWeights.fold
        state alpha =
      AspisV5CompactFoldExactSource.unrolledFold state alpha := by
  rcases state with ⟨blocks, deltaScale, folds⟩
  unfold V5RelationCompactFoldGeneratedExact.v5_cu_probe.CompactBTerminalWeights.fold
  simp only [
    MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter,
    bind_tc_ok]
  simp only [generated_loop_ten folds foldBound]
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
  simp (config := { maxSteps := 2000000 })
    [AspisV5CompactFoldExactSource.unrolledFold, sourceIterN,
      core.slice.iter.IteratorIterMut.next, Slice.setAtNat,
      Array.to_slice, Array.from_slice, Slice.getElem_Nat_eq,
      rebuilt_slice_get_eq_bang, Array.getElem_Nat_eq, Array.val_to_slice,
      Array.make, index0, index1, index2, index3, index4, index5, index6,
      index7, index8, index9, ten_reverse_sets_exact]
  all_goals intros <;> rfl

theorem extracted_root_eq_unrolled (state : ExactState) (alpha : ExactRaw)
    (foldBound : state.folds.val < 4) :
    V5RelationCompactFoldGeneratedExact.v5_cu_probe.aeneas_extract_compact_fold
        state alpha =
      AspisV5CompactFoldExactSource.unrolledFold state alpha := by
  unfold V5RelationCompactFoldGeneratedExact.v5_cu_probe.aeneas_extract_compact_fold
  exact generated_fold_eq_unrolled state alpha foldBound

#print axioms generated_loop_ten
#print axioms generated_fold_eq_unrolled
#print axioms extracted_root_eq_unrolled

end AspisV5CompactFoldExactRootBridge
