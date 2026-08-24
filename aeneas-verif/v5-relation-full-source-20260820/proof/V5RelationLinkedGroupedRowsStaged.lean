import V5RelationLinkedGroupedRows

/-!
# Staged execution of the released grouped-row loops

The older fixed-release proof evaluated an entire grouped-row loop with one
large `simp`.  This file splits the execution into source-level loop-body
steps.  Besides being easier to audit, the staged form stays within ordinary
Lean resource limits and can be composed with the maintained tuple semantics.
-/

namespace AspisV5RelationLinkedGroupedRowsStaged

open Aeneas Aeneas.Std Result ControlFlow
open AspisV5RelationLinkedGroupedRows

abbrev RawQM31 := V5RelationLinkedGenerated.aspis_core.field.QM31

private def chunk4 (a b c d : Std.U8) : Slice Std.U8 :=
  ⟨[a, b, c, d], by scalar_tac⟩

private def emptyRemainder : Slice Std.U8 := ⟨[], by scalar_tac⟩

private def secondIter0 : core.slice.iter.ChunksExact Std.U8 :=
  { chunks := [
      chunk4 0#u8 1#u8 1#u8 1#u8,
      chunk4 1#u8 2#u8 1#u8 1#u8,
      chunk4 1#u8 1#u8 2#u8 3#u8,
      chunk4 4#u8 5#u8 6#u8 6#u8]
    remainder := emptyRemainder }

private def secondIter1 : core.slice.iter.ChunksExact Std.U8 :=
  { chunks := [
      chunk4 1#u8 2#u8 1#u8 1#u8,
      chunk4 1#u8 1#u8 2#u8 3#u8,
      chunk4 4#u8 5#u8 6#u8 6#u8]
    remainder := emptyRemainder }

private def secondIter2 : core.slice.iter.ChunksExact Std.U8 :=
  { chunks := [
      chunk4 1#u8 1#u8 2#u8 3#u8,
      chunk4 4#u8 5#u8 6#u8 6#u8]
    remainder := emptyRemainder }

private def secondIter3 : core.slice.iter.ChunksExact Std.U8 :=
  { chunks := [chunk4 4#u8 5#u8 6#u8 6#u8]
    remainder := emptyRemainder }

private def secondIter4 : core.slice.iter.ChunksExact Std.U8 :=
  { chunks := []
    remainder := emptyRemainder }

private theorem second_next0 :
    core.slice.iter.IteratorChunksExact.next secondIter0 =
      ok (some (chunk4 0#u8 1#u8 1#u8 1#u8), secondIter1) := by rfl
private theorem second_next1 :
    core.slice.iter.IteratorChunksExact.next secondIter1 =
      ok (some (chunk4 1#u8 2#u8 1#u8 1#u8), secondIter2) := by rfl
private theorem second_next2 :
    core.slice.iter.IteratorChunksExact.next secondIter2 =
      ok (some (chunk4 1#u8 1#u8 2#u8 3#u8), secondIter3) := by rfl
private theorem second_next3 :
    core.slice.iter.IteratorChunksExact.next secondIter3 =
      ok (some (chunk4 4#u8 5#u8 6#u8 6#u8), secondIter4) := by rfl

private theorem slice_index_run
    {T : Type} [Inhabited T] (values : Slice T) (index : Std.Usize)
    (hindex : index.val < values.val.length) :
    Slice.index_usize values index = ok values.val[index.val]! := by
  unfold Slice.index_usize
  rw [Slice.getElem?_Usize_eq]
  simp [hindex]

private theorem chunk4_index0 (a b c d : Std.U8) :
    Slice.index_usize (chunk4 a b c d) 0#usize = ok a := by
  simpa [chunk4] using
    slice_index_run (chunk4 a b c d) 0#usize (by simp [chunk4])
private theorem chunk4_index1 (a b c d : Std.U8) :
    Slice.index_usize (chunk4 a b c d) 1#usize = ok b := by
  simpa [chunk4] using
    slice_index_run (chunk4 a b c d) 1#usize (by simp [chunk4])
private theorem chunk4_index2 (a b c d : Std.U8) :
    Slice.index_usize (chunk4 a b c d) 2#usize = ok c := by
  simpa [chunk4] using
    slice_index_run (chunk4 a b c d) 2#usize (by simp [chunk4])
private theorem chunk4_index3 (a b c d : Std.U8) :
    Slice.index_usize (chunk4 a b c d) 3#usize = ok d := by
  simpa [chunk4] using
    slice_index_run (chunk4 a b c d) 3#usize (by simp [chunk4])

private def tuple0 : Array Std.U8 4#usize :=
  Array.make 4#usize [0#u8, 1#u8, 1#u8, 1#u8]
private def tuple1 : Array Std.U8 4#usize :=
  Array.make 4#usize [1#u8, 2#u8, 1#u8, 1#u8]
private def tuple2 : Array Std.U8 4#usize :=
  Array.make 4#usize [1#u8, 1#u8, 2#u8, 3#u8]
private def tuple3 : Array Std.U8 4#usize :=
  Array.make 4#usize [4#u8, 5#u8, 6#u8, 6#u8]

private theorem tuple0_wire :
    (Array.make 4#usize [0#u8, 1#u8, 1#u8, 1#u8] :
      Array Std.U8 4#usize) = tuple0 := by rfl
private theorem tuple1_wire :
    (Array.make 4#usize [1#u8, 2#u8, 1#u8, 1#u8] :
      Array Std.U8 4#usize) = tuple1 := by rfl
private theorem tuple2_wire :
    (Array.make 4#usize [1#u8, 1#u8, 2#u8, 3#u8] :
      Array Std.U8 4#usize) = tuple2 := by rfl
private theorem tuple3_wire :
    (Array.make 4#usize [4#u8, 5#u8, 6#u8, 6#u8] :
      Array Std.U8 4#usize) = tuple3 := by rfl

private theorem usize_size_gt_three : 3 < Std.Usize.size := by
  rcases Usize.size_scalarTac_eq with ⟨hsize, _⟩
  rcases Usize.cMax_bound_concrete with ⟨hmax, _⟩
  omega

private theorem one_mod_usize_size : 1 % Std.Usize.size = 1 := by
  apply Nat.mod_eq_of_lt
  exact lt_trans (by decide) usize_size_gt_three
private theorem two_mod_usize_size : 2 % Std.Usize.size = 2 := by
  apply Nat.mod_eq_of_lt
  exact lt_trans (by decide) usize_size_gt_three
private theorem three_mod_usize_size : 3 % Std.Usize.size = 3 := by
  apply Nat.mod_eq_of_lt
  exact usize_size_gt_three

private def tuples0 : alloc.vec.Vec (Array Std.U8 4#usize) :=
  ⟨[], by scalar_tac⟩
private def tuples1 : alloc.vec.Vec (Array Std.U8 4#usize) :=
  ⟨[tuple0], by scalar_tac⟩
private def tuples2 : alloc.vec.Vec (Array Std.U8 4#usize) :=
  ⟨[tuple0, tuple1], by scalar_tac⟩
private def tuples3 : alloc.vec.Vec (Array Std.U8 4#usize) :=
  ⟨[tuple0, tuple1, tuple2], by scalar_tac⟩
private def tuples4 : alloc.vec.Vec (Array Std.U8 4#usize) :=
  ⟨[tuple0, tuple1, tuple2, tuple3], by scalar_tac⟩

private theorem len_tuples0 : alloc.vec.Vec.len tuples0 = 0#usize := by
  apply UScalar.val_eq_imp
  rw [alloc.vec.Vec.len_val]
  rfl
private theorem len_tuples1 : alloc.vec.Vec.len tuples1 = 1#usize := by
  apply UScalar.val_eq_imp
  rw [alloc.vec.Vec.len_val]
  rfl
private theorem len_tuples2 : alloc.vec.Vec.len tuples2 = 2#usize := by
  apply UScalar.val_eq_imp
  rw [alloc.vec.Vec.len_val]
  rfl
private theorem len_tuples3 : alloc.vec.Vec.len tuples3 = 3#usize := by
  apply UScalar.val_eq_imp
  rw [alloc.vec.Vec.len_val]
  rfl

private def groups0 : alloc.vec.Vec Std.U8 := ⟨[], by scalar_tac⟩
private def groups1 : alloc.vec.Vec Std.U8 := ⟨[0#u8], by scalar_tac⟩
private def groups2 : alloc.vec.Vec Std.U8 := ⟨[0#u8, 1#u8], by scalar_tac⟩
private def groups3 : alloc.vec.Vec Std.U8 :=
  ⟨[0#u8, 1#u8, 2#u8], by scalar_tac⟩
private def groups4 : alloc.vec.Vec Std.U8 :=
  ⟨[0#u8, 1#u8, 2#u8, 3#u8], by scalar_tac⟩

private def values0 : alloc.vec.Vec RawQM31 := ⟨[], by scalar_tac⟩
private def values1 (out0 : RawQM31) : alloc.vec.Vec RawQM31 :=
  ⟨[out0], by scalar_tac⟩
private def values2 (out0 out1 : RawQM31) : alloc.vec.Vec RawQM31 :=
  ⟨[out0, out1], by scalar_tac⟩
private def values3 (out0 out1 out2 : RawQM31) : alloc.vec.Vec RawQM31 :=
  ⟨[out0, out1, out2], by scalar_tac⟩
def releasedFourValues (out0 out1 out2 out3 : RawQM31) :
    alloc.vec.Vec RawQM31 :=
  ⟨[out0, out1, out2, out3], by scalar_tac⟩

private theorem usize_max_gt_four : 4 < Std.Usize.max := by
  rcases Usize.cMax_bound_concrete with ⟨hmax, _⟩
  omega

private theorem vec_push_to
    {T : Type} (input output : alloc.vec.Vec T) (value : T)
    (bound : input.val.length < Std.Usize.max)
    (shape : output.val = input.val ++ [value]) :
    alloc.vec.Vec.push input value = ok output := by
  obtain ⟨actual, run, actualShape⟩ := Aeneas.Std.WP.spec_imp_exists
    (alloc.vec.Vec.push_spec input value bound)
  rw [run]
  congr 1
  apply Subtype.ext
  rw [actualShape, shape]

private theorem push_tuples0 :
    alloc.vec.Vec.push tuples0 tuple0 = ok tuples1 := by
  apply vec_push_to
  · have h := usize_max_gt_four
    simp [tuples0]
    omega
  · rfl
private theorem push_tuples1 :
    alloc.vec.Vec.push tuples1 tuple1 = ok tuples2 := by
  apply vec_push_to
  · have h := usize_max_gt_four
    simp [tuples1]
    omega
  · rfl
private theorem push_tuples2 :
    alloc.vec.Vec.push tuples2 tuple2 = ok tuples3 := by
  apply vec_push_to
  · have h := usize_max_gt_four
    simp [tuples2]
    omega
  · rfl
private theorem push_tuples3 :
    alloc.vec.Vec.push tuples3 tuple3 = ok tuples4 := by
  apply vec_push_to
  · have h := usize_max_gt_four
    simp [tuples3]
    omega
  · rfl

private theorem push_values0 (out0 : RawQM31) :
    alloc.vec.Vec.push values0 out0 = ok (values1 out0) := by
  apply vec_push_to
  · have h := usize_max_gt_four
    simp [values0]
    omega
  · rfl
private theorem push_values1 (out0 out1 : RawQM31) :
    alloc.vec.Vec.push (values1 out0) out1 = ok (values2 out0 out1) := by
  apply vec_push_to
  · have h := usize_max_gt_four
    simp [values1]
    omega
  · rfl
private theorem push_values2 (out0 out1 out2 : RawQM31) :
    alloc.vec.Vec.push (values2 out0 out1) out2 =
      ok (values3 out0 out1 out2) := by
  apply vec_push_to
  · have h := usize_max_gt_four
    simp [values2]
    omega
  · rfl
private theorem push_values3 (out0 out1 out2 out3 : RawQM31) :
    alloc.vec.Vec.push (values3 out0 out1 out2) out3 =
      ok (releasedFourValues out0 out1 out2 out3) := by
  apply vec_push_to
  · have h := usize_max_gt_four
    simp [values3]
    omega
  · rfl

private theorem push_groups0 :
    alloc.vec.Vec.push groups0 0#u8 = ok groups1 := by
  apply vec_push_to
  · have h := usize_max_gt_four
    simp [groups0]
    omega
  · rfl
private theorem push_groups1 :
    alloc.vec.Vec.push groups1 1#u8 = ok groups2 := by
  apply vec_push_to
  · have h := usize_max_gt_four
    simp [groups1]
    omega
  · rfl
private theorem push_groups2 :
    alloc.vec.Vec.push groups2 2#u8 = ok groups3 := by
  apply vec_push_to
  · have h := usize_max_gt_four
    simp [groups2]
    omega
  · rfl
private theorem push_groups3 :
    alloc.vec.Vec.push groups3 3#u8 = ok groups4 := by
  apply vec_push_to
  · have h := usize_max_gt_four
    simp [groups3]
    omega
  · rfl

private theorem cast_group0 : UScalar.cast .U8 0#usize = 0#u8 := by
  apply UScalar.val_eq_imp
  rw [UScalar.cast_val_eq]
  rfl
private theorem cast_group1 : UScalar.cast .U8 1#usize = 1#u8 := by
  apply UScalar.val_eq_imp
  rw [UScalar.cast_val_eq]
  rfl
private theorem cast_group2 : UScalar.cast .U8 2#usize = 2#u8 := by
  apply UScalar.val_eq_imp
  rw [UScalar.cast_val_eq]
  rfl
private theorem cast_group3 : UScalar.cast .U8 3#usize = 3#u8 := by
  apply UScalar.val_eq_imp
  rw [UScalar.cast_val_eq]
  rfl

macro "solve_concrete_group_lookup_body" : tactic =>
  `(tactic| simp (config := { maxSteps := 300000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0_loop0.body,
      tuples0, tuples1, tuples2, tuples3, tuple0, tuple1, tuple2, tuple3,
      Array.make, alloc.vec.Vec.len, alloc.vec.Vec.index, Slice.index_usize,
      Array.index_usize, core.array.equality.PartialEqArray.ne,
      core.array.equality.PartialEqArray.eq, core.cmp.PartialEqU8,
      List.allM, UScalar.eq_equiv, UScalar.lt_equiv, Std.lift, pure,
      one_mod_usize_size, two_mod_usize_size, three_mod_usize_size])

private theorem lookup0_done :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0_loop0.body
      tuples0 tuple0 0#usize = ok (done 0#usize) := by
  solve_concrete_group_lookup_body

private theorem lookup1_step0 :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0_loop0.body
      tuples1 tuple1 0#usize = ok (cont 1#usize) := by
  solve_concrete_group_lookup_body
private theorem lookup1_done :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0_loop0.body
      tuples1 tuple1 1#usize = ok (done 1#usize) := by
  solve_concrete_group_lookup_body

private theorem lookup2_step0 :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0_loop0.body
      tuples2 tuple2 0#usize = ok (cont 1#usize) := by
  solve_concrete_group_lookup_body
private theorem lookup2_step1 :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0_loop0.body
      tuples2 tuple2 1#usize = ok (cont 2#usize) := by
  solve_concrete_group_lookup_body
private theorem lookup2_done :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0_loop0.body
      tuples2 tuple2 2#usize = ok (done 2#usize) := by
  solve_concrete_group_lookup_body

private theorem lookup3_step0 :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0_loop0.body
      tuples3 tuple3 0#usize = ok (cont 1#usize) := by
  solve_concrete_group_lookup_body
private theorem lookup3_step1 :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0_loop0.body
      tuples3 tuple3 1#usize = ok (cont 2#usize) := by
  solve_concrete_group_lookup_body
private theorem lookup3_step2 :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0_loop0.body
      tuples3 tuple3 2#usize = ok (cont 3#usize) := by
  solve_concrete_group_lookup_body
private theorem lookup3_done :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0_loop0.body
      tuples3 tuple3 3#usize = ok (done 3#usize) := by
  solve_concrete_group_lookup_body

private theorem second_lookup0 :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0_loop0
      tuples0 tuple0 0#usize = ok 0#usize := by
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0_loop0
  rw [loop.eq_1]
  rw [lookup0_done]

private theorem second_lookup1 :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0_loop0
      tuples1 tuple1 0#usize = ok 1#usize := by
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0_loop0
  rw [loop.eq_1]
  rw [lookup1_step0]
  simp only
  rw [loop.eq_1, lookup1_done]

private theorem second_lookup2 :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0_loop0
      tuples2 tuple2 0#usize = ok 2#usize := by
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0_loop0
  rw [loop.eq_1]
  rw [lookup2_step0]
  simp only
  rw [loop.eq_1, lookup2_step1]
  simp only
  rw [loop.eq_1, lookup2_done]

private theorem second_lookup3 :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0_loop0
      tuples3 tuple3 0#usize = ok 3#usize := by
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0_loop0
  rw [loop.eq_1]
  rw [lookup3_step0]
  simp only
  rw [loop.eq_1, lookup3_step1]
  simp only
  rw [loop.eq_1, lookup3_step2]
  simp only
  rw [loop.eq_1, lookup3_done]

set_option maxRecDepth 12000 in
private theorem second_step0
    (groupValues : Slice RawQM31) (alpha alpha2 alpha3 out0 : RawQM31)
    (run0 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple tuple0
        groupValues alpha alpha2 alpha3 = ok out0) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0.body
        groupValues alpha alpha2 alpha3 secondIter0 tuples0 groups0 values0 =
      ok (cont (secondIter1, tuples1, groups1, values1 out0)) := by
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0.body
  rw [second_next0]
  simp only [bind_tc_ok]
  rw [chunk4_index0, chunk4_index1, chunk4_index2, chunk4_index3]
  simp only [bind_tc_ok]
  rw [tuple0_wire]
  rw [second_lookup0]
  simp only [bind_tc_ok]
  rw [len_tuples0]
  simp only [if_true]
  rw [push_tuples0, run0]
  simp only [bind_tc_ok]
  rw [push_values0]
  simp only [bind_tc_ok, Std.lift, cast_group0]
  rw [push_groups0]
  simp only [bind_tc_ok]

set_option maxRecDepth 12000 in
private theorem second_step1
    (groupValues : Slice RawQM31) (alpha alpha2 alpha3 out0 out1 : RawQM31)
    (run1 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple tuple1
        groupValues alpha alpha2 alpha3 = ok out1) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0.body
        groupValues alpha alpha2 alpha3 secondIter1 tuples1 groups1
          (values1 out0) =
      ok (cont (secondIter2, tuples2, groups2, values2 out0 out1)) := by
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0.body
  rw [second_next1]
  simp only [bind_tc_ok]
  rw [chunk4_index0, chunk4_index1, chunk4_index2, chunk4_index3]
  simp only [bind_tc_ok]
  rw [tuple1_wire]
  rw [second_lookup1]
  simp only [bind_tc_ok]
  rw [len_tuples1]
  simp only [if_true]
  rw [push_tuples1, run1]
  simp only [bind_tc_ok]
  rw [push_values1]
  simp only [bind_tc_ok, Std.lift, cast_group1]
  rw [push_groups1]
  simp only [bind_tc_ok]

set_option maxRecDepth 12000 in
private theorem second_step2
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 out0 out1 out2 : RawQM31)
    (run2 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple tuple2
        groupValues alpha alpha2 alpha3 = ok out2) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0.body
        groupValues alpha alpha2 alpha3 secondIter2 tuples2 groups2
          (values2 out0 out1) =
      ok (cont (secondIter3, tuples3, groups3, values3 out0 out1 out2)) := by
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0.body
  rw [second_next2]
  simp only [bind_tc_ok]
  rw [chunk4_index0, chunk4_index1, chunk4_index2, chunk4_index3]
  simp only [bind_tc_ok]
  rw [tuple2_wire]
  rw [second_lookup2]
  simp only [bind_tc_ok]
  rw [len_tuples2]
  simp only [if_true]
  rw [push_tuples2, run2]
  simp only [bind_tc_ok]
  rw [push_values2]
  simp only [bind_tc_ok, Std.lift, cast_group2]
  rw [push_groups2]
  simp only [bind_tc_ok]

set_option maxRecDepth 12000 in
private theorem second_step3
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 out0 out1 out2 out3 : RawQM31)
    (run3 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple tuple3
        groupValues alpha alpha2 alpha3 = ok out3) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0.body
        groupValues alpha alpha2 alpha3 secondIter3 tuples3 groups3
          (values3 out0 out1 out2) =
      ok (cont (secondIter4, tuples4, groups4,
        releasedFourValues out0 out1 out2 out3)) := by
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0.body
  rw [second_next3]
  simp only [bind_tc_ok]
  rw [chunk4_index0, chunk4_index1, chunk4_index2, chunk4_index3]
  simp only [bind_tc_ok]
  rw [tuple3_wire]
  rw [second_lookup3]
  simp only [bind_tc_ok]
  rw [len_tuples3]
  simp only [if_true]
  rw [push_tuples3, run3]
  simp only [bind_tc_ok]
  rw [push_values3]
  simp only [bind_tc_ok, Std.lift, cast_group3]
  rw [push_groups3]
  simp only [bind_tc_ok]

private theorem second_done
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 out0 out1 out2 out3 : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0.body
        groupValues alpha alpha2 alpha3 secondIter4 tuples4 groups4
          (releasedFourValues out0 out1 out2 out3) =
      ok (done (groups4, releasedFourValues out0 out1 out2 out3)) := by
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0.body,
    secondIter4, emptyRemainder, core.slice.iter.IteratorChunksExact.next]

theorem released_second_grouped_rows_loop_exact
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 out0 out1 out2 out3 : RawQM31)
    (run0 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple tuple0
        groupValues alpha alpha2 alpha3 = ok out0)
    (run1 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple tuple1
        groupValues alpha alpha2 alpha3 = ok out1)
    (run2 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple tuple2
        groupValues alpha alpha2 alpha3 = ok out2)
    (run3 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple tuple3
        groupValues alpha alpha2 alpha3 = ok out3) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0
        secondIter0 groupValues alpha alpha2 alpha3 tuples0 groups0 values0 =
      ok (groups4, releasedFourValues out0 out1 out2 out3) := by
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0
  rw [loop.eq_1]
  dsimp only
  rw [second_step0 groupValues alpha alpha2 alpha3 out0 run0]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [second_step1 groupValues alpha alpha2 alpha3 out0 out1 run1]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [second_step2 groupValues alpha alpha2 alpha3 out0 out1 out2 run2]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [second_step3 groupValues alpha alpha2 alpha3 out0 out1 out2 out3 run3]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [second_done groupValues alpha alpha2 alpha3 out0 out1 out2 out3]

private theorem released_row_groups16_len :
    Slice.len (alloc.vec.Vec.deref releasedRowGroups16) = 16#usize := by
  apply UScalar.val_eq_imp
  rw [Slice.len_val]
  rfl

private theorem released_row_groups16_folded_len :
    Slice.len (alloc.vec.Vec.deref releasedRowGroups16) / 4#usize =
      ok 4#usize := by
  rw [released_row_groups16_len]
  obtain ⟨result, run, value⟩ :=
    UScalar.div_spec (16#usize : Std.Usize) (y := 4#usize) (by norm_num)
  rw [run]
  congr 1
  apply UScalar.val_eq_imp
  norm_num at value
  exact value

private theorem released_rows16_iterator_is_second_iter0 :
    releasedRows16ExplicitIterator = secondIter0 := by
  rfl

private theorem released_empty_tuples :
    alloc.vec.Vec.with_capacity (Array Std.U8 4#usize) 4#usize = tuples0 := by
  apply Subtype.ext
  rfl

private theorem released_empty_groups :
    alloc.vec.Vec.with_capacity Std.U8 4#usize = groups0 := by
  apply Subtype.ext
  rfl

private theorem released_empty_values :
    alloc.vec.Vec.with_capacity RawQM31 4#usize = values0 := by
  apply Subtype.ext
  rfl

private theorem released_groups4_exact : groups4 = releasedRowGroups4 := by
  apply Subtype.ext
  rfl

/-- Staged replacement for the former monolithic second grouped-row source
proof. -/
theorem released_second_grouped_rows_source_exact
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 out0 out1 out2 out3 : RawQM31)
    (run0 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple tuple0
        groupValues alpha alpha2 alpha3 = ok out0)
    (run1 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple tuple1
        groupValues alpha alpha2 alpha3 = ok out1)
    (run2 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple tuple2
        groupValues alpha alpha2 alpha3 = ok out2)
    (run3 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple tuple3
        groupValues alpha alpha2 alpha3 = ok out3) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows
        (alloc.vec.Vec.deref releasedRowGroups16) groupValues alpha alpha2 alpha3 =
      ok (releasedRowGroups4, releasedFourValues out0 out1 out2 out3) := by
  have loopRun := released_second_grouped_rows_loop_exact groupValues alpha
    alpha2 alpha3 out0 out1 out2 out3 run0 run1 run2 run3
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows
  dsimp only
  rw [released_row_groups16_folded_len]
  simp only [bind_tc_ok]
  rw [releasedRows16ChunksExactExplicit]
  simp only [bind_tc_ok]
  rw [released_rows16_iterator_is_second_iter0, released_empty_tuples,
    released_empty_groups, released_empty_values, loopRun, released_groups4_exact]

#print axioms released_second_grouped_rows_loop_exact
#print axioms released_second_grouped_rows_source_exact

end AspisV5RelationLinkedGroupedRowsStaged
