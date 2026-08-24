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

/-! ## The released 64-to-16 pass -/

private def firstChunks : List (Slice Std.U8) :=
  [chunk4 0#u8 0#u8 1#u8 1#u8,
   chunk4 1#u8 1#u8 1#u8 1#u8,
   chunk4 1#u8 1#u8 1#u8 1#u8,
   chunk4 1#u8 1#u8 1#u8 1#u8,
   chunk4 1#u8 1#u8 1#u8 1#u8,
   chunk4 1#u8 1#u8 1#u8 2#u8,
   chunk4 1#u8 1#u8 1#u8 1#u8,
   chunk4 1#u8 1#u8 1#u8 1#u8,
   chunk4 1#u8 1#u8 1#u8 1#u8,
   chunk4 1#u8 1#u8 1#u8 1#u8,
   chunk4 1#u8 1#u8 1#u8 2#u8,
   chunk4 0#u8 2#u8 0#u8 1#u8,
   chunk4 1#u8 3#u8 3#u8 3#u8,
   chunk4 3#u8 4#u8 5#u8 6#u8,
   chunk4 6#u8 6#u8 6#u8 6#u8,
   chunk4 6#u8 6#u8 6#u8 6#u8]

private def firstIter (offset : Nat) : core.slice.iter.ChunksExact Std.U8 :=
  { chunks := firstChunks.drop offset
    remainder := emptyRemainder }

private def firstTuple0 : Array Std.U8 4#usize :=
  Array.make 4#usize [0#u8, 0#u8, 1#u8, 1#u8]
private def firstTuple1 : Array Std.U8 4#usize :=
  Array.make 4#usize [1#u8, 1#u8, 1#u8, 1#u8]
private def firstTuple2 : Array Std.U8 4#usize :=
  Array.make 4#usize [1#u8, 1#u8, 1#u8, 2#u8]
private def firstTuple3 : Array Std.U8 4#usize :=
  Array.make 4#usize [0#u8, 2#u8, 0#u8, 1#u8]
private def firstTuple4 : Array Std.U8 4#usize :=
  Array.make 4#usize [1#u8, 3#u8, 3#u8, 3#u8]
private def firstTuple5 : Array Std.U8 4#usize :=
  Array.make 4#usize [3#u8, 4#u8, 5#u8, 6#u8]
private def firstTuple6 : Array Std.U8 4#usize :=
  Array.make 4#usize [6#u8, 6#u8, 6#u8, 6#u8]

private def firstTuples0 : alloc.vec.Vec (Array Std.U8 4#usize) :=
  ⟨[], by scalar_tac⟩
private def firstTuples1 : alloc.vec.Vec (Array Std.U8 4#usize) :=
  ⟨[firstTuple0], by scalar_tac⟩
private def firstTuples2 : alloc.vec.Vec (Array Std.U8 4#usize) :=
  ⟨[firstTuple0, firstTuple1], by scalar_tac⟩
private def firstTuples3 : alloc.vec.Vec (Array Std.U8 4#usize) :=
  ⟨[firstTuple0, firstTuple1, firstTuple2], by scalar_tac⟩
private def firstTuples4 : alloc.vec.Vec (Array Std.U8 4#usize) :=
  ⟨[firstTuple0, firstTuple1, firstTuple2, firstTuple3], by scalar_tac⟩
private def firstTuples5 : alloc.vec.Vec (Array Std.U8 4#usize) :=
  ⟨[firstTuple0, firstTuple1, firstTuple2, firstTuple3, firstTuple4],
    by scalar_tac⟩
private def firstTuples6 : alloc.vec.Vec (Array Std.U8 4#usize) :=
  ⟨[firstTuple0, firstTuple1, firstTuple2, firstTuple3, firstTuple4,
    firstTuple5], by scalar_tac⟩
private def firstTuples7 : alloc.vec.Vec (Array Std.U8 4#usize) :=
  ⟨[firstTuple0, firstTuple1, firstTuple2, firstTuple3, firstTuple4,
    firstTuple5, firstTuple6], by scalar_tac⟩

private def firstGroups (count : Nat) : alloc.vec.Vec Std.U8 :=
  ⟨releasedRowGroups16.val.take count, by
    have bound := releasedRowGroups16.property
    rw [List.length_take]
    omega⟩

private def firstValues0 : alloc.vec.Vec RawQM31 := ⟨[], by scalar_tac⟩
private def firstValues1 (out0 : RawQM31) : alloc.vec.Vec RawQM31 :=
  ⟨[out0], by scalar_tac⟩
private def firstValues2 (out0 out1 : RawQM31) : alloc.vec.Vec RawQM31 :=
  ⟨[out0, out1], by scalar_tac⟩
private def firstValues3 (out0 out1 out2 : RawQM31) : alloc.vec.Vec RawQM31 :=
  ⟨[out0, out1, out2], by scalar_tac⟩
private def firstValues4 (out0 out1 out2 out3 : RawQM31) :
    alloc.vec.Vec RawQM31 :=
  ⟨[out0, out1, out2, out3], by scalar_tac⟩
private def firstValues5 (out0 out1 out2 out3 out4 : RawQM31) :
    alloc.vec.Vec RawQM31 :=
  ⟨[out0, out1, out2, out3, out4], by scalar_tac⟩
private def firstValues6 (out0 out1 out2 out3 out4 out5 : RawQM31) :
    alloc.vec.Vec RawQM31 :=
  ⟨[out0, out1, out2, out3, out4, out5], by scalar_tac⟩
def releasedSevenValuesStaged
    (out0 out1 out2 out3 out4 out5 out6 : RawQM31) :
    alloc.vec.Vec RawQM31 :=
  ⟨[out0, out1, out2, out3, out4, out5, out6], by scalar_tac⟩

private theorem usize_max_gt_sixteen : 16 < Std.Usize.max := by
  rcases Usize.cMax_bound_concrete with ⟨hmax, _⟩
  omega

private theorem usize_size_gt_six : 6 < Std.Usize.size := by
  rcases Usize.size_scalarTac_eq with ⟨hsize, _⟩
  rcases Usize.cMax_bound_concrete with ⟨hmax, _⟩
  omega

private theorem four_mod_usize_size : 4 % Std.Usize.size = 4 := by
  apply Nat.mod_eq_of_lt
  exact lt_trans (by decide) usize_size_gt_six
private theorem five_mod_usize_size : 5 % Std.Usize.size = 5 := by
  apply Nat.mod_eq_of_lt
  exact lt_trans (by decide) usize_size_gt_six
private theorem six_mod_usize_size : 6 % Std.Usize.size = 6 := by
  apply Nat.mod_eq_of_lt
  exact usize_size_gt_six

private theorem cast_group4 : UScalar.cast .U8 4#usize = 4#u8 := by
  apply UScalar.val_eq_imp
  rw [UScalar.cast_val_eq]
  rfl
private theorem cast_group5 : UScalar.cast .U8 5#usize = 5#u8 := by
  apply UScalar.val_eq_imp
  rw [UScalar.cast_val_eq]
  rfl
private theorem cast_group6 : UScalar.cast .U8 6#usize = 6#u8 := by
  apply UScalar.val_eq_imp
  rw [UScalar.cast_val_eq]
  rfl

private theorem first_next0 :
    core.slice.iter.IteratorChunksExact.next (firstIter 0) =
      ok (some (chunk4 0#u8 0#u8 1#u8 1#u8), firstIter 1) := by rfl
private theorem first_next1 :
    core.slice.iter.IteratorChunksExact.next (firstIter 1) =
      ok (some (chunk4 1#u8 1#u8 1#u8 1#u8), firstIter 2) := by rfl
private theorem first_next2 :
    core.slice.iter.IteratorChunksExact.next (firstIter 2) =
      ok (some (chunk4 1#u8 1#u8 1#u8 1#u8), firstIter 3) := by rfl
private theorem first_next3 :
    core.slice.iter.IteratorChunksExact.next (firstIter 3) =
      ok (some (chunk4 1#u8 1#u8 1#u8 1#u8), firstIter 4) := by rfl
private theorem first_next4 :
    core.slice.iter.IteratorChunksExact.next (firstIter 4) =
      ok (some (chunk4 1#u8 1#u8 1#u8 1#u8), firstIter 5) := by rfl
private theorem first_next5 :
    core.slice.iter.IteratorChunksExact.next (firstIter 5) =
      ok (some (chunk4 1#u8 1#u8 1#u8 2#u8), firstIter 6) := by rfl
private theorem first_next6 :
    core.slice.iter.IteratorChunksExact.next (firstIter 6) =
      ok (some (chunk4 1#u8 1#u8 1#u8 1#u8), firstIter 7) := by rfl
private theorem first_next7 :
    core.slice.iter.IteratorChunksExact.next (firstIter 7) =
      ok (some (chunk4 1#u8 1#u8 1#u8 1#u8), firstIter 8) := by rfl
private theorem first_next8 :
    core.slice.iter.IteratorChunksExact.next (firstIter 8) =
      ok (some (chunk4 1#u8 1#u8 1#u8 1#u8), firstIter 9) := by rfl
private theorem first_next9 :
    core.slice.iter.IteratorChunksExact.next (firstIter 9) =
      ok (some (chunk4 1#u8 1#u8 1#u8 1#u8), firstIter 10) := by rfl
private theorem first_next10 :
    core.slice.iter.IteratorChunksExact.next (firstIter 10) =
      ok (some (chunk4 1#u8 1#u8 1#u8 2#u8), firstIter 11) := by rfl
private theorem first_next11 :
    core.slice.iter.IteratorChunksExact.next (firstIter 11) =
      ok (some (chunk4 0#u8 2#u8 0#u8 1#u8), firstIter 12) := by rfl
private theorem first_next12 :
    core.slice.iter.IteratorChunksExact.next (firstIter 12) =
      ok (some (chunk4 1#u8 3#u8 3#u8 3#u8), firstIter 13) := by rfl
private theorem first_next13 :
    core.slice.iter.IteratorChunksExact.next (firstIter 13) =
      ok (some (chunk4 3#u8 4#u8 5#u8 6#u8), firstIter 14) := by rfl
private theorem first_next14 :
    core.slice.iter.IteratorChunksExact.next (firstIter 14) =
      ok (some (chunk4 6#u8 6#u8 6#u8 6#u8), firstIter 15) := by rfl
private theorem first_next15 :
    core.slice.iter.IteratorChunksExact.next (firstIter 15) =
      ok (some (chunk4 6#u8 6#u8 6#u8 6#u8), firstIter 16) := by rfl
private theorem first_next16 :
    core.slice.iter.IteratorChunksExact.next (firstIter 16) =
      ok (none, firstIter 16) := by rfl

private theorem vec_push_short_to
    {T : Type} (input output : alloc.vec.Vec T) (value : T)
    (lengthBound : input.val.length ≤ 16)
    (shape : output.val = input.val ++ [value]) :
    alloc.vec.Vec.push input value = ok output := by
  apply vec_push_to input output value
  · exact lt_of_le_of_lt lengthBound usize_max_gt_sixteen
  · exact shape

macro "solve_first_small_push" : tactic =>
  `(tactic| apply vec_push_short_to <;>
    simp [firstTuples0, firstTuples1, firstTuples2, firstTuples3,
      firstTuples4, firstTuples5, firstTuples6, firstTuples7,
      firstValues0, firstValues1, firstValues2, firstValues3,
      firstValues4, firstValues5, firstValues6, releasedSevenValuesStaged])

private theorem first_push_tuple0 :
    alloc.vec.Vec.push firstTuples0 firstTuple0 = ok firstTuples1 := by
  solve_first_small_push
private theorem first_push_tuple1 :
    alloc.vec.Vec.push firstTuples1 firstTuple1 = ok firstTuples2 := by
  solve_first_small_push
private theorem first_push_tuple2 :
    alloc.vec.Vec.push firstTuples2 firstTuple2 = ok firstTuples3 := by
  solve_first_small_push
private theorem first_push_tuple3 :
    alloc.vec.Vec.push firstTuples3 firstTuple3 = ok firstTuples4 := by
  solve_first_small_push
private theorem first_push_tuple4 :
    alloc.vec.Vec.push firstTuples4 firstTuple4 = ok firstTuples5 := by
  solve_first_small_push
private theorem first_push_tuple5 :
    alloc.vec.Vec.push firstTuples5 firstTuple5 = ok firstTuples6 := by
  solve_first_small_push
private theorem first_push_tuple6 :
    alloc.vec.Vec.push firstTuples6 firstTuple6 = ok firstTuples7 := by
  solve_first_small_push

private theorem first_push_value0 (out0 : RawQM31) :
    alloc.vec.Vec.push firstValues0 out0 = ok (firstValues1 out0) := by
  solve_first_small_push
private theorem first_push_value1 (out0 out1 : RawQM31) :
    alloc.vec.Vec.push (firstValues1 out0) out1 =
      ok (firstValues2 out0 out1) := by
  solve_first_small_push
private theorem first_push_value2 (out0 out1 out2 : RawQM31) :
    alloc.vec.Vec.push (firstValues2 out0 out1) out2 =
      ok (firstValues3 out0 out1 out2) := by
  solve_first_small_push
private theorem first_push_value3 (out0 out1 out2 out3 : RawQM31) :
    alloc.vec.Vec.push (firstValues3 out0 out1 out2) out3 =
      ok (firstValues4 out0 out1 out2 out3) := by
  solve_first_small_push
private theorem first_push_value4 (out0 out1 out2 out3 out4 : RawQM31) :
    alloc.vec.Vec.push (firstValues4 out0 out1 out2 out3) out4 =
      ok (firstValues5 out0 out1 out2 out3 out4) := by
  solve_first_small_push
private theorem first_push_value5
    (out0 out1 out2 out3 out4 out5 : RawQM31) :
    alloc.vec.Vec.push (firstValues5 out0 out1 out2 out3 out4) out5 =
      ok (firstValues6 out0 out1 out2 out3 out4 out5) := by
  solve_first_small_push
private theorem first_push_value6
    (out0 out1 out2 out3 out4 out5 out6 : RawQM31) :
    alloc.vec.Vec.push (firstValues6 out0 out1 out2 out3 out4 out5) out6 =
      ok (releasedSevenValuesStaged out0 out1 out2 out3 out4 out5 out6) := by
  solve_first_small_push

macro "solve_first_group_push" : tactic =>
  `(tactic| apply vec_push_short_to <;>
    simp [firstGroups, releasedRowGroups16])

private theorem first_push_group0 :
    alloc.vec.Vec.push (firstGroups 0) 0#u8 = ok (firstGroups 1) := by
  solve_first_group_push
private theorem first_push_group1 :
    alloc.vec.Vec.push (firstGroups 1) 1#u8 = ok (firstGroups 2) := by
  solve_first_group_push
private theorem first_push_group2 :
    alloc.vec.Vec.push (firstGroups 2) 1#u8 = ok (firstGroups 3) := by
  solve_first_group_push
private theorem first_push_group3 :
    alloc.vec.Vec.push (firstGroups 3) 1#u8 = ok (firstGroups 4) := by
  solve_first_group_push
private theorem first_push_group4 :
    alloc.vec.Vec.push (firstGroups 4) 1#u8 = ok (firstGroups 5) := by
  solve_first_group_push
private theorem first_push_group5 :
    alloc.vec.Vec.push (firstGroups 5) 2#u8 = ok (firstGroups 6) := by
  solve_first_group_push
private theorem first_push_group6 :
    alloc.vec.Vec.push (firstGroups 6) 1#u8 = ok (firstGroups 7) := by
  solve_first_group_push
private theorem first_push_group7 :
    alloc.vec.Vec.push (firstGroups 7) 1#u8 = ok (firstGroups 8) := by
  solve_first_group_push
private theorem first_push_group8 :
    alloc.vec.Vec.push (firstGroups 8) 1#u8 = ok (firstGroups 9) := by
  solve_first_group_push
private theorem first_push_group9 :
    alloc.vec.Vec.push (firstGroups 9) 1#u8 = ok (firstGroups 10) := by
  solve_first_group_push
private theorem first_push_group10 :
    alloc.vec.Vec.push (firstGroups 10) 2#u8 = ok (firstGroups 11) := by
  solve_first_group_push
private theorem first_push_group11 :
    alloc.vec.Vec.push (firstGroups 11) 3#u8 = ok (firstGroups 12) := by
  solve_first_group_push
private theorem first_push_group12 :
    alloc.vec.Vec.push (firstGroups 12) 4#u8 = ok (firstGroups 13) := by
  solve_first_group_push
private theorem first_push_group13 :
    alloc.vec.Vec.push (firstGroups 13) 5#u8 = ok (firstGroups 14) := by
  solve_first_group_push
private theorem first_push_group14 :
    alloc.vec.Vec.push (firstGroups 14) 6#u8 = ok (firstGroups 15) := by
  solve_first_group_push
private theorem first_push_group15 :
    alloc.vec.Vec.push (firstGroups 15) 6#u8 = ok (firstGroups 16) := by
  solve_first_group_push

macro "solve_first_tuple_len" : tactic =>
  `(tactic| apply UScalar.val_eq_imp <;>
    simp [alloc.vec.Vec.len_val, firstTuples0, firstTuples1, firstTuples2,
      firstTuples3, firstTuples4, firstTuples5, firstTuples6, firstTuples7])

private theorem first_len_tuples0 :
    alloc.vec.Vec.len firstTuples0 = 0#usize := by solve_first_tuple_len
private theorem first_len_tuples1 :
    alloc.vec.Vec.len firstTuples1 = 1#usize := by solve_first_tuple_len
private theorem first_len_tuples2 :
    alloc.vec.Vec.len firstTuples2 = 2#usize := by solve_first_tuple_len
private theorem first_len_tuples3 :
    alloc.vec.Vec.len firstTuples3 = 3#usize := by solve_first_tuple_len
private theorem first_len_tuples4 :
    alloc.vec.Vec.len firstTuples4 = 4#usize := by solve_first_tuple_len
private theorem first_len_tuples5 :
    alloc.vec.Vec.len firstTuples5 = 5#usize := by solve_first_tuple_len
private theorem first_len_tuples6 :
    alloc.vec.Vec.len firstTuples6 = 6#usize := by solve_first_tuple_len
private theorem first_len_tuples7 :
    alloc.vec.Vec.len firstTuples7 = 7#usize := by solve_first_tuple_len

macro "solve_first_lookup" : tactic =>
  `(tactic| simp (config := { maxSteps := 500000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0_loop0,
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0_loop0.body,
      loop.eq_1, firstTuples0, firstTuples1, firstTuples2, firstTuples3,
      firstTuples4, firstTuples5, firstTuples6, firstTuples7,
      firstTuple0, firstTuple1, firstTuple2, firstTuple3, firstTuple4,
      firstTuple5, firstTuple6, Array.make, alloc.vec.Vec.len,
      alloc.vec.Vec.index, alloc.vec.Vec.index_usize, Slice.index_usize,
      Array.index_usize, core.array.equality.PartialEqArray.ne,
      core.array.equality.PartialEqArray.eq, core.cmp.PartialEqU8,
      List.allM, UScalar.eq_equiv, UScalar.lt_equiv, Std.lift, pure,
      one_mod_usize_size, two_mod_usize_size, three_mod_usize_size,
      four_mod_usize_size, five_mod_usize_size, six_mod_usize_size])

private theorem first_lookup_new0 :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0_loop0
      firstTuples0 firstTuple0 0#usize = ok 0#usize := by
  solve_first_lookup
private theorem first_lookup_new1 :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0_loop0
      firstTuples1 firstTuple1 0#usize = ok 1#usize := by
  solve_first_lookup
private theorem first_lookup_existing1_from2 :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0_loop0
      firstTuples2 firstTuple1 0#usize = ok 1#usize := by
  solve_first_lookup
private theorem first_lookup_new2 :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0_loop0
      firstTuples2 firstTuple2 0#usize = ok 2#usize := by
  solve_first_lookup
private theorem first_lookup_existing1_from3 :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0_loop0
      firstTuples3 firstTuple1 0#usize = ok 1#usize := by
  solve_first_lookup
private theorem first_lookup_existing2_from3 :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0_loop0
      firstTuples3 firstTuple2 0#usize = ok 2#usize := by
  solve_first_lookup
private theorem first_lookup_new3 :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0_loop0
      firstTuples3 firstTuple3 0#usize = ok 3#usize := by
  solve_first_lookup
private theorem first_lookup_new4 :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0_loop0
      firstTuples4 firstTuple4 0#usize = ok 4#usize := by
  solve_first_lookup
private theorem first_lookup_new5 :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0_loop0
      firstTuples5 firstTuple5 0#usize = ok 5#usize := by
  solve_first_lookup
private theorem first_lookup_new6 :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0_loop0
      firstTuples6 firstTuple6 0#usize = ok 6#usize := by
  solve_first_lookup
private theorem first_lookup_existing6_from7 :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0_loop0
      firstTuples7 firstTuple6 0#usize = ok 6#usize := by
  solve_first_lookup

private theorem first_one_ne_len2 :
    ¬ 1#usize = alloc.vec.Vec.len firstTuples2 := by
  rw [first_len_tuples2]
  decide
private theorem first_one_ne_len3 :
    ¬ 1#usize = alloc.vec.Vec.len firstTuples3 := by
  rw [first_len_tuples3]
  decide
private theorem first_two_ne_len3 :
    ¬ 2#usize = alloc.vec.Vec.len firstTuples3 := by
  rw [first_len_tuples3]
  decide
private theorem first_six_ne_len7 :
    ¬ 6#usize = alloc.vec.Vec.len firstTuples7 := by
  rw [first_len_tuples7]
  decide

set_option maxRecDepth 12000 in
private theorem first_new_step
    (groupValues : Slice RawQM31) (alpha alpha2 alpha3 : RawQM31)
    {iter nextIter : core.slice.iter.ChunksExact Std.U8}
    (a b c d : Std.U8) (tuple : Array Std.U8 4#usize)
    (tuples tuplesOut : alloc.vec.Vec (Array Std.U8 4#usize))
    (groups groupsOut : alloc.vec.Vec Std.U8)
    (values valuesOut : alloc.vec.Vec RawQM31)
    (group : Std.Usize) (groupByte : Std.U8) (out : RawQM31)
    (nextRun : core.slice.iter.IteratorChunksExact.next iter =
      ok (some (chunk4 a b c d), nextIter))
    (tupleWire : (Array.make 4#usize [a, b, c, d] :
      Array Std.U8 4#usize) = tuple)
    (lookup :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0_loop0
        tuples tuple 0#usize = ok group)
    (lengthRun : alloc.vec.Vec.len tuples = group)
    (tuplePush : alloc.vec.Vec.push tuples tuple = ok tuplesOut)
    (foldRun :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple tuple
        groupValues alpha alpha2 alpha3 = ok out)
    (valuePush : alloc.vec.Vec.push values out = ok valuesOut)
    (castRun : UScalar.cast .U8 group = groupByte)
    (groupPush : alloc.vec.Vec.push groups groupByte = ok groupsOut) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0.body
        groupValues alpha alpha2 alpha3 iter tuples groups values =
      ok (cont (nextIter, tuplesOut, groupsOut, valuesOut)) := by
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0.body
  rw [nextRun]
  simp only [bind_tc_ok]
  rw [chunk4_index0, chunk4_index1, chunk4_index2, chunk4_index3]
  simp only [bind_tc_ok]
  rw [tupleWire, lookup]
  simp only [bind_tc_ok]
  rw [lengthRun]
  simp only [if_true]
  rw [tuplePush, foldRun]
  simp only [bind_tc_ok]
  rw [valuePush]
  simp only [bind_tc_ok, Std.lift, castRun]
  rw [groupPush]
  simp only [bind_tc_ok]

set_option maxRecDepth 12000 in
private theorem first_existing_step
    (groupValues : Slice RawQM31) (alpha alpha2 alpha3 : RawQM31)
    {iter nextIter : core.slice.iter.ChunksExact Std.U8}
    (a b c d : Std.U8) (tuple : Array Std.U8 4#usize)
    (tuples : alloc.vec.Vec (Array Std.U8 4#usize))
    (groups groupsOut : alloc.vec.Vec Std.U8)
    (values : alloc.vec.Vec RawQM31)
    (group : Std.Usize) (groupByte : Std.U8)
    (nextRun : core.slice.iter.IteratorChunksExact.next iter =
      ok (some (chunk4 a b c d), nextIter))
    (tupleWire : (Array.make 4#usize [a, b, c, d] :
      Array Std.U8 4#usize) = tuple)
    (lookup :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0_loop0
        tuples tuple 0#usize = ok group)
    (notNew : ¬ group = alloc.vec.Vec.len tuples)
    (castRun : UScalar.cast .U8 group = groupByte)
    (groupPush : alloc.vec.Vec.push groups groupByte = ok groupsOut) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0.body
        groupValues alpha alpha2 alpha3 iter tuples groups values =
      ok (cont (nextIter, tuples, groupsOut, values)) := by
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0.body
  rw [nextRun]
  simp only [bind_tc_ok]
  rw [chunk4_index0, chunk4_index1, chunk4_index2, chunk4_index3]
  simp only [bind_tc_ok]
  rw [tupleWire, lookup]
  simp only [bind_tc_ok, if_neg notNew, Std.lift, castRun]
  rw [groupPush]
  simp only [bind_tc_ok]

private theorem first_step0
    (groupValues : Slice RawQM31) (alpha alpha2 alpha3 out0 : RawQM31)
    (run0 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
        firstTuple0 groupValues alpha alpha2 alpha3 = ok out0) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0.body
        groupValues alpha alpha2 alpha3 (firstIter 0) firstTuples0
          (firstGroups 0) firstValues0 =
      ok (cont (firstIter 1, firstTuples1, firstGroups 1,
        firstValues1 out0)) := by
  apply first_new_step (a := 0#u8) (b := 0#u8) (c := 1#u8) (d := 1#u8)
    (tuple := firstTuple0) (group := 0#usize) (groupByte := 0#u8)
    (out := out0)
  · exact first_next0
  · rfl
  · exact first_lookup_new0
  · exact first_len_tuples0
  · exact first_push_tuple0
  · exact run0
  · exact first_push_value0 out0
  · exact cast_group0
  · exact first_push_group0

private theorem first_step1
    (groupValues : Slice RawQM31) (alpha alpha2 alpha3 out0 out1 : RawQM31)
    (run1 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
        firstTuple1 groupValues alpha alpha2 alpha3 = ok out1) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0.body
        groupValues alpha alpha2 alpha3 (firstIter 1) firstTuples1
          (firstGroups 1) (firstValues1 out0) =
      ok (cont (firstIter 2, firstTuples2, firstGroups 2,
        firstValues2 out0 out1)) := by
  apply first_new_step (a := 1#u8) (b := 1#u8) (c := 1#u8) (d := 1#u8)
    (tuple := firstTuple1) (group := 1#usize) (groupByte := 1#u8)
    (out := out1)
  · exact first_next1
  · rfl
  · exact first_lookup_new1
  · exact first_len_tuples1
  · exact first_push_tuple1
  · exact run1
  · exact first_push_value1 out0 out1
  · exact cast_group1
  · exact first_push_group1

private theorem first_step2
    (groupValues : Slice RawQM31) (alpha alpha2 alpha3 out0 out1 : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0.body
        groupValues alpha alpha2 alpha3 (firstIter 2) firstTuples2
          (firstGroups 2) (firstValues2 out0 out1) =
      ok (cont (firstIter 3, firstTuples2, firstGroups 3,
        firstValues2 out0 out1)) := by
  apply first_existing_step (a := 1#u8) (b := 1#u8) (c := 1#u8)
    (d := 1#u8) (tuple := firstTuple1) (group := 1#usize)
    (groupByte := 1#u8)
  · exact first_next2
  · rfl
  · exact first_lookup_existing1_from2
  · exact first_one_ne_len2
  · exact cast_group1
  · exact first_push_group2

private theorem first_step3
    (groupValues : Slice RawQM31) (alpha alpha2 alpha3 out0 out1 : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0.body
        groupValues alpha alpha2 alpha3 (firstIter 3) firstTuples2
          (firstGroups 3) (firstValues2 out0 out1) =
      ok (cont (firstIter 4, firstTuples2, firstGroups 4,
        firstValues2 out0 out1)) := by
  apply first_existing_step (a := 1#u8) (b := 1#u8) (c := 1#u8)
    (d := 1#u8) (tuple := firstTuple1) (group := 1#usize)
    (groupByte := 1#u8)
  · exact first_next3
  · rfl
  · exact first_lookup_existing1_from2
  · exact first_one_ne_len2
  · exact cast_group1
  · exact first_push_group3

private theorem first_step4
    (groupValues : Slice RawQM31) (alpha alpha2 alpha3 out0 out1 : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0.body
        groupValues alpha alpha2 alpha3 (firstIter 4) firstTuples2
          (firstGroups 4) (firstValues2 out0 out1) =
      ok (cont (firstIter 5, firstTuples2, firstGroups 5,
        firstValues2 out0 out1)) := by
  apply first_existing_step (a := 1#u8) (b := 1#u8) (c := 1#u8)
    (d := 1#u8) (tuple := firstTuple1) (group := 1#usize)
    (groupByte := 1#u8)
  · exact first_next4
  · rfl
  · exact first_lookup_existing1_from2
  · exact first_one_ne_len2
  · exact cast_group1
  · exact first_push_group4

private theorem first_step5
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 out0 out1 out2 : RawQM31)
    (run2 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
        firstTuple2 groupValues alpha alpha2 alpha3 = ok out2) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0.body
        groupValues alpha alpha2 alpha3 (firstIter 5) firstTuples2
          (firstGroups 5) (firstValues2 out0 out1) =
      ok (cont (firstIter 6, firstTuples3, firstGroups 6,
        firstValues3 out0 out1 out2)) := by
  apply first_new_step (a := 1#u8) (b := 1#u8) (c := 1#u8) (d := 2#u8)
    (tuple := firstTuple2) (group := 2#usize) (groupByte := 2#u8)
    (out := out2)
  · exact first_next5
  · rfl
  · exact first_lookup_new2
  · exact first_len_tuples2
  · exact first_push_tuple2
  · exact run2
  · exact first_push_value2 out0 out1 out2
  · exact cast_group2
  · exact first_push_group5

private theorem first_step6
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 out0 out1 out2 : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0.body
        groupValues alpha alpha2 alpha3 (firstIter 6) firstTuples3
          (firstGroups 6) (firstValues3 out0 out1 out2) =
      ok (cont (firstIter 7, firstTuples3, firstGroups 7,
        firstValues3 out0 out1 out2)) := by
  apply first_existing_step (a := 1#u8) (b := 1#u8) (c := 1#u8)
    (d := 1#u8) (tuple := firstTuple1) (group := 1#usize)
    (groupByte := 1#u8)
  · exact first_next6
  · rfl
  · exact first_lookup_existing1_from3
  · exact first_one_ne_len3
  · exact cast_group1
  · exact first_push_group6

private theorem first_step7
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 out0 out1 out2 : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0.body
        groupValues alpha alpha2 alpha3 (firstIter 7) firstTuples3
          (firstGroups 7) (firstValues3 out0 out1 out2) =
      ok (cont (firstIter 8, firstTuples3, firstGroups 8,
        firstValues3 out0 out1 out2)) := by
  apply first_existing_step (a := 1#u8) (b := 1#u8) (c := 1#u8)
    (d := 1#u8) (tuple := firstTuple1) (group := 1#usize)
    (groupByte := 1#u8)
  · exact first_next7
  · rfl
  · exact first_lookup_existing1_from3
  · exact first_one_ne_len3
  · exact cast_group1
  · exact first_push_group7

private theorem first_step8
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 out0 out1 out2 : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0.body
        groupValues alpha alpha2 alpha3 (firstIter 8) firstTuples3
          (firstGroups 8) (firstValues3 out0 out1 out2) =
      ok (cont (firstIter 9, firstTuples3, firstGroups 9,
        firstValues3 out0 out1 out2)) := by
  apply first_existing_step (a := 1#u8) (b := 1#u8) (c := 1#u8)
    (d := 1#u8) (tuple := firstTuple1) (group := 1#usize)
    (groupByte := 1#u8)
  · exact first_next8
  · rfl
  · exact first_lookup_existing1_from3
  · exact first_one_ne_len3
  · exact cast_group1
  · exact first_push_group8

private theorem first_step9
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 out0 out1 out2 : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0.body
        groupValues alpha alpha2 alpha3 (firstIter 9) firstTuples3
          (firstGroups 9) (firstValues3 out0 out1 out2) =
      ok (cont (firstIter 10, firstTuples3, firstGroups 10,
        firstValues3 out0 out1 out2)) := by
  apply first_existing_step (a := 1#u8) (b := 1#u8) (c := 1#u8)
    (d := 1#u8) (tuple := firstTuple1) (group := 1#usize)
    (groupByte := 1#u8)
  · exact first_next9
  · rfl
  · exact first_lookup_existing1_from3
  · exact first_one_ne_len3
  · exact cast_group1
  · exact first_push_group9

private theorem first_step10
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 out0 out1 out2 : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0.body
        groupValues alpha alpha2 alpha3 (firstIter 10) firstTuples3
          (firstGroups 10) (firstValues3 out0 out1 out2) =
      ok (cont (firstIter 11, firstTuples3, firstGroups 11,
        firstValues3 out0 out1 out2)) := by
  apply first_existing_step (a := 1#u8) (b := 1#u8) (c := 1#u8)
    (d := 2#u8) (tuple := firstTuple2) (group := 2#usize)
    (groupByte := 2#u8)
  · exact first_next10
  · rfl
  · exact first_lookup_existing2_from3
  · exact first_two_ne_len3
  · exact cast_group2
  · exact first_push_group10

private theorem first_step11
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 out0 out1 out2 out3 : RawQM31)
    (run3 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
        firstTuple3 groupValues alpha alpha2 alpha3 = ok out3) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0.body
        groupValues alpha alpha2 alpha3 (firstIter 11) firstTuples3
          (firstGroups 11) (firstValues3 out0 out1 out2) =
      ok (cont (firstIter 12, firstTuples4, firstGroups 12,
        firstValues4 out0 out1 out2 out3)) := by
  apply first_new_step (a := 0#u8) (b := 2#u8) (c := 0#u8) (d := 1#u8)
    (tuple := firstTuple3) (group := 3#usize) (groupByte := 3#u8)
    (out := out3)
  · exact first_next11
  · rfl
  · exact first_lookup_new3
  · exact first_len_tuples3
  · exact first_push_tuple3
  · exact run3
  · exact first_push_value3 out0 out1 out2 out3
  · exact cast_group3
  · exact first_push_group11

private theorem first_step12
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 out0 out1 out2 out3 out4 : RawQM31)
    (run4 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
        firstTuple4 groupValues alpha alpha2 alpha3 = ok out4) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0.body
        groupValues alpha alpha2 alpha3 (firstIter 12) firstTuples4
          (firstGroups 12) (firstValues4 out0 out1 out2 out3) =
      ok (cont (firstIter 13, firstTuples5, firstGroups 13,
        firstValues5 out0 out1 out2 out3 out4)) := by
  apply first_new_step (a := 1#u8) (b := 3#u8) (c := 3#u8) (d := 3#u8)
    (tuple := firstTuple4) (group := 4#usize) (groupByte := 4#u8)
    (out := out4)
  · exact first_next12
  · rfl
  · exact first_lookup_new4
  · exact first_len_tuples4
  · exact first_push_tuple4
  · exact run4
  · exact first_push_value4 out0 out1 out2 out3 out4
  · exact cast_group4
  · exact first_push_group12

private theorem first_step13
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 out0 out1 out2 out3 out4 out5 : RawQM31)
    (run5 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
        firstTuple5 groupValues alpha alpha2 alpha3 = ok out5) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0.body
        groupValues alpha alpha2 alpha3 (firstIter 13) firstTuples5
          (firstGroups 13) (firstValues5 out0 out1 out2 out3 out4) =
      ok (cont (firstIter 14, firstTuples6, firstGroups 14,
        firstValues6 out0 out1 out2 out3 out4 out5)) := by
  apply first_new_step (a := 3#u8) (b := 4#u8) (c := 5#u8) (d := 6#u8)
    (tuple := firstTuple5) (group := 5#usize) (groupByte := 5#u8)
    (out := out5)
  · exact first_next13
  · rfl
  · exact first_lookup_new5
  · exact first_len_tuples5
  · exact first_push_tuple5
  · exact run5
  · exact first_push_value5 out0 out1 out2 out3 out4 out5
  · exact cast_group5
  · exact first_push_group13

private theorem first_step14
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 out0 out1 out2 out3 out4 out5 out6 : RawQM31)
    (run6 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
        firstTuple6 groupValues alpha alpha2 alpha3 = ok out6) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0.body
        groupValues alpha alpha2 alpha3 (firstIter 14) firstTuples6
          (firstGroups 14) (firstValues6 out0 out1 out2 out3 out4 out5) =
      ok (cont (firstIter 15, firstTuples7, firstGroups 15,
        releasedSevenValuesStaged out0 out1 out2 out3 out4 out5 out6)) := by
  apply first_new_step (a := 6#u8) (b := 6#u8) (c := 6#u8) (d := 6#u8)
    (tuple := firstTuple6) (group := 6#usize) (groupByte := 6#u8)
    (out := out6)
  · exact first_next14
  · rfl
  · exact first_lookup_new6
  · exact first_len_tuples6
  · exact first_push_tuple6
  · exact run6
  · exact first_push_value6 out0 out1 out2 out3 out4 out5 out6
  · exact cast_group6
  · exact first_push_group14

private theorem first_step15
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 out0 out1 out2 out3 out4 out5 out6 : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0.body
        groupValues alpha alpha2 alpha3 (firstIter 15) firstTuples7
          (firstGroups 15)
          (releasedSevenValuesStaged out0 out1 out2 out3 out4 out5 out6) =
      ok (cont (firstIter 16, firstTuples7, firstGroups 16,
        releasedSevenValuesStaged out0 out1 out2 out3 out4 out5 out6)) := by
  apply first_existing_step (a := 6#u8) (b := 6#u8) (c := 6#u8)
    (d := 6#u8) (tuple := firstTuple6) (group := 6#usize)
    (groupByte := 6#u8)
  · exact first_next15
  · rfl
  · exact first_lookup_existing6_from7
  · exact first_six_ne_len7
  · exact cast_group6
  · exact first_push_group15

private theorem first_done
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 out0 out1 out2 out3 out4 out5 out6 : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0.body
        groupValues alpha alpha2 alpha3 (firstIter 16) firstTuples7
          (firstGroups 16)
          (releasedSevenValuesStaged out0 out1 out2 out3 out4 out5 out6) =
      ok (done (firstGroups 16,
        releasedSevenValuesStaged out0 out1 out2 out3 out4 out5 out6)) := by
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0.body
  rw [first_next16]

theorem released_first_grouped_rows_loop_exact
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 out0 out1 out2 out3 out4 out5 out6 : RawQM31)
    (run0 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
        firstTuple0 groupValues alpha alpha2 alpha3 = ok out0)
    (run1 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
        firstTuple1 groupValues alpha alpha2 alpha3 = ok out1)
    (run2 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
        firstTuple2 groupValues alpha alpha2 alpha3 = ok out2)
    (run3 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
        firstTuple3 groupValues alpha alpha2 alpha3 = ok out3)
    (run4 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
        firstTuple4 groupValues alpha alpha2 alpha3 = ok out4)
    (run5 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
        firstTuple5 groupValues alpha alpha2 alpha3 = ok out5)
    (run6 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
        firstTuple6 groupValues alpha alpha2 alpha3 = ok out6) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0
        (firstIter 0) groupValues alpha alpha2 alpha3 firstTuples0
          (firstGroups 0) firstValues0 =
      ok (firstGroups 16,
        releasedSevenValuesStaged out0 out1 out2 out3 out4 out5 out6) := by
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0
  rw [loop.eq_1]
  dsimp only
  rw [first_step0 groupValues alpha alpha2 alpha3 out0 run0]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [first_step1 groupValues alpha alpha2 alpha3 out0 out1 run1]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [first_step2 groupValues alpha alpha2 alpha3 out0 out1]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [first_step3 groupValues alpha alpha2 alpha3 out0 out1]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [first_step4 groupValues alpha alpha2 alpha3 out0 out1]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [first_step5 groupValues alpha alpha2 alpha3 out0 out1 out2 run2]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [first_step6 groupValues alpha alpha2 alpha3 out0 out1 out2]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [first_step7 groupValues alpha alpha2 alpha3 out0 out1 out2]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [first_step8 groupValues alpha alpha2 alpha3 out0 out1 out2]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [first_step9 groupValues alpha alpha2 alpha3 out0 out1 out2]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [first_step10 groupValues alpha alpha2 alpha3 out0 out1 out2]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [first_step11 groupValues alpha alpha2 alpha3 out0 out1 out2 out3 run3]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [first_step12 groupValues alpha alpha2 alpha3 out0 out1 out2 out3 out4 run4]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [first_step13 groupValues alpha alpha2 alpha3 out0 out1 out2 out3 out4
    out5 run5]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [first_step14 groupValues alpha alpha2 alpha3 out0 out1 out2 out3 out4
    out5 out6 run6]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [first_step15 groupValues alpha alpha2 alpha3 out0 out1 out2 out3 out4
    out5 out6]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [first_done groupValues alpha alpha2 alpha3 out0 out1 out2 out3 out4
    out5 out6]

private theorem released_row_groups64_len :
    Slice.len (alloc.vec.Vec.deref releasedRowGroups64) = 64#usize := by
  apply UScalar.val_eq_imp
  rw [Slice.len_val]
  rfl

private theorem released_row_groups64_folded_len :
    Slice.len (alloc.vec.Vec.deref releasedRowGroups64) / 4#usize =
      ok 16#usize := by
  rw [released_row_groups64_len]
  obtain ⟨result, run, value⟩ :=
    UScalar.div_spec (64#usize : Std.Usize) (y := 4#usize) (by norm_num)
  rw [run]
  congr 1
  apply UScalar.val_eq_imp
  norm_num at value
  exact value

private theorem released_rows64_iterator_is_first_iter0 :
    releasedRows64ExplicitIterator = firstIter 0 := by
  rfl

private theorem released_first_empty_tuples :
    alloc.vec.Vec.with_capacity (Array Std.U8 4#usize) 16#usize =
      firstTuples0 := by
  apply Subtype.ext
  rfl

private theorem released_first_empty_groups :
    alloc.vec.Vec.with_capacity Std.U8 16#usize = firstGroups 0 := by
  apply Subtype.ext
  rfl

private theorem released_first_empty_values :
    alloc.vec.Vec.with_capacity RawQM31 16#usize = firstValues0 := by
  apply Subtype.ext
  rfl

private theorem released_first_groups_exact :
    firstGroups 16 = releasedRowGroups16 := by
  apply Subtype.ext
  rfl

/-- Staged source-level replacement for the former monolithic 64-to-16
grouped-row proof. -/
theorem released_first_grouped_rows_source_exact
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 out0 out1 out2 out3 out4 out5 out6 : RawQM31)
    (run0 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
        firstTuple0 groupValues alpha alpha2 alpha3 = ok out0)
    (run1 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
        firstTuple1 groupValues alpha alpha2 alpha3 = ok out1)
    (run2 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
        firstTuple2 groupValues alpha alpha2 alpha3 = ok out2)
    (run3 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
        firstTuple3 groupValues alpha alpha2 alpha3 = ok out3)
    (run4 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
        firstTuple4 groupValues alpha alpha2 alpha3 = ok out4)
    (run5 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
        firstTuple5 groupValues alpha alpha2 alpha3 = ok out5)
    (run6 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
        firstTuple6 groupValues alpha alpha2 alpha3 = ok out6) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows
        (alloc.vec.Vec.deref releasedRowGroups64) groupValues alpha alpha2 alpha3 =
      ok (releasedRowGroups16,
        releasedSevenValuesStaged out0 out1 out2 out3 out4 out5 out6) := by
  have loopRun := released_first_grouped_rows_loop_exact groupValues alpha
    alpha2 alpha3 out0 out1 out2 out3 out4 out5 out6 run0 run1 run2 run3
      run4 run5 run6
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows
  dsimp only
  rw [released_row_groups64_folded_len]
  simp only [bind_tc_ok]
  rw [releasedRows64ChunksExactExplicit]
  simp only [bind_tc_ok]
  rw [released_rows64_iterator_is_first_iter0, released_first_empty_tuples,
    released_first_empty_groups, released_first_empty_values, loopRun,
    released_first_groups_exact]

/-- Public wire-shaped form of the staged 64-to-16 theorem. -/
theorem released_first_grouped_rows_source_wire_exact
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 out0 out1 out2 out3 out4 out5 out6 : RawQM31)
    (run0 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
        (Array.make 4#usize [0#u8, 0#u8, 1#u8, 1#u8])
          groupValues alpha alpha2 alpha3 = ok out0)
    (run1 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
        (Array.make 4#usize [1#u8, 1#u8, 1#u8, 1#u8])
          groupValues alpha alpha2 alpha3 = ok out1)
    (run2 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
        (Array.make 4#usize [1#u8, 1#u8, 1#u8, 2#u8])
          groupValues alpha alpha2 alpha3 = ok out2)
    (run3 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
        (Array.make 4#usize [0#u8, 2#u8, 0#u8, 1#u8])
          groupValues alpha alpha2 alpha3 = ok out3)
    (run4 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
        (Array.make 4#usize [1#u8, 3#u8, 3#u8, 3#u8])
          groupValues alpha alpha2 alpha3 = ok out4)
    (run5 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
        (Array.make 4#usize [3#u8, 4#u8, 5#u8, 6#u8])
          groupValues alpha alpha2 alpha3 = ok out5)
    (run6 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
        (Array.make 4#usize [6#u8, 6#u8, 6#u8, 6#u8])
          groupValues alpha alpha2 alpha3 = ok out6) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows
        (alloc.vec.Vec.deref releasedRowGroups64) groupValues alpha alpha2 alpha3 =
      ok (releasedRowGroups16,
        releasedSevenValuesStaged out0 out1 out2 out3 out4 out5 out6) := by
  apply released_first_grouped_rows_source_exact groupValues alpha alpha2
    alpha3 out0 out1 out2 out3 out4 out5 out6
  · simpa [firstTuple0] using run0
  · simpa [firstTuple1] using run1
  · simpa [firstTuple2] using run2
  · simpa [firstTuple3] using run3
  · simpa [firstTuple4] using run4
  · simpa [firstTuple5] using run5
  · simpa [firstTuple6] using run6

/-- Public wire-shaped form of the staged 16-to-4 theorem. -/
theorem released_second_grouped_rows_source_wire_exact
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 out0 out1 out2 out3 : RawQM31)
    (run0 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
        (Array.make 4#usize [0#u8, 1#u8, 1#u8, 1#u8])
          groupValues alpha alpha2 alpha3 = ok out0)
    (run1 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
        (Array.make 4#usize [1#u8, 2#u8, 1#u8, 1#u8])
          groupValues alpha alpha2 alpha3 = ok out1)
    (run2 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
        (Array.make 4#usize [1#u8, 1#u8, 2#u8, 3#u8])
          groupValues alpha alpha2 alpha3 = ok out2)
    (run3 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
        (Array.make 4#usize [4#u8, 5#u8, 6#u8, 6#u8])
          groupValues alpha alpha2 alpha3 = ok out3) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows
        (alloc.vec.Vec.deref releasedRowGroups16) groupValues alpha alpha2 alpha3 =
      ok (releasedRowGroups4, releasedFourValues out0 out1 out2 out3) := by
  apply released_second_grouped_rows_source_exact groupValues alpha alpha2
    alpha3 out0 out1 out2 out3
  · simpa [tuple0] using run0
  · simpa [tuple1] using run1
  · simpa [tuple2] using run2
  · simpa [tuple3] using run3

#print axioms released_second_grouped_rows_loop_exact
#print axioms released_second_grouped_rows_source_exact
#print axioms released_first_grouped_rows_loop_exact
#print axioms released_first_grouped_rows_source_exact

end AspisV5RelationLinkedGroupedRowsStaged
