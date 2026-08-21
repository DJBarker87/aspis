import V5RelationLinkedGroupedRows

namespace AspisV5RelationLinkedGroupedRowsSource

open Aeneas Aeneas.Std Result ControlFlow
open AspisV5RelationLinkedGroupedRows

abbrev RawQM31 := V5RelationLinkedGenerated.aspis_core.field.QM31

def releasedSevenValues
    (value0 value1 value2 value3 value4 value5 value6 : RawQM31) :
    alloc.vec.Vec RawQM31 :=
  ⟨[value0, value1, value2, value3, value4, value5, value6], by scalar_tac⟩

def releasedFourValues
    (value0 value1 value2 value3 : RawQM31) : alloc.vec.Vec RawQM31 :=
  ⟨[value0, value1, value2, value3], by scalar_tac⟩

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 12000 in
theorem releasedFirstGroupedRowsSourceExact
    (groupValues : alloc.vec.Vec RawQM31)
    (alpha alpha2 alpha3 : RawQM31)
    (out0 out1 out2 out3 out4 out5 out6 : RawQM31)
    (run0 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
          (Array.make 4#usize [0#u8, 0#u8, 1#u8, 1#u8])
          (alloc.vec.Vec.deref groupValues) alpha alpha2 alpha3 = ok out0)
    (run1 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
          (Array.make 4#usize [1#u8, 1#u8, 1#u8, 1#u8])
          (alloc.vec.Vec.deref groupValues) alpha alpha2 alpha3 = ok out1)
    (run2 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
          (Array.make 4#usize [1#u8, 1#u8, 1#u8, 2#u8])
          (alloc.vec.Vec.deref groupValues) alpha alpha2 alpha3 = ok out2)
    (run3 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
          (Array.make 4#usize [0#u8, 2#u8, 0#u8, 1#u8])
          (alloc.vec.Vec.deref groupValues) alpha alpha2 alpha3 = ok out3)
    (run4 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
          (Array.make 4#usize [1#u8, 3#u8, 3#u8, 3#u8])
          (alloc.vec.Vec.deref groupValues) alpha alpha2 alpha3 = ok out4)
    (run5 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
          (Array.make 4#usize [3#u8, 4#u8, 5#u8, 6#u8])
          (alloc.vec.Vec.deref groupValues) alpha alpha2 alpha3 = ok out5)
    (run6 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
          (Array.make 4#usize [6#u8, 6#u8, 6#u8, 6#u8])
          (alloc.vec.Vec.deref groupValues) alpha alpha2 alpha3 = ok out6) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows
        (alloc.vec.Vec.deref releasedRowGroups64)
        (alloc.vec.Vec.deref groupValues) alpha alpha2 alpha3 =
      ok (releasedRowGroups16,
        releasedSevenValues out0 out1 out2 out3 out4 out5 out6) := by
  simp (config := { maxSteps := 3000000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows,
     V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0,
     V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0.body,
     V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0_loop0,
     V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0_loop0.body,
     releasedRows64ChunksExactExplicit, releasedRows64ExplicitIterator,
     releasedRowGroups64, releasedRowGroups16, releasedSevenValues,
     alloc.vec.Vec.deref, alloc.vec.Vec.len, alloc.vec.Vec.push,
     alloc.vec.Vec.index, alloc.vec.Vec.index_usize,
     Slice.len, Slice.index_usize, Array.index_usize,
     core.array.equality.PartialEqArray.ne,
     core.array.equality.PartialEqArray.eq,
     core.cmp.PartialEqU8, Std.lift, UScalar.lt_equiv,
     loop.eq_1, run0, run1, run2, run3, run4, run5, run6]

set_option maxHeartbeats 800000 in
set_option maxRecDepth 12000 in
theorem releasedSecondGroupedRowsSourceExact
    (groupValues : alloc.vec.Vec RawQM31)
    (alpha alpha2 alpha3 : RawQM31)
    (out0 out1 out2 out3 : RawQM31)
    (run0 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
          (Array.make 4#usize [0#u8, 1#u8, 1#u8, 1#u8])
          (alloc.vec.Vec.deref groupValues) alpha alpha2 alpha3 = ok out0)
    (run1 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
          (Array.make 4#usize [1#u8, 2#u8, 1#u8, 1#u8])
          (alloc.vec.Vec.deref groupValues) alpha alpha2 alpha3 = ok out1)
    (run2 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
          (Array.make 4#usize [1#u8, 1#u8, 2#u8, 3#u8])
          (alloc.vec.Vec.deref groupValues) alpha alpha2 alpha3 = ok out2)
    (run3 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
          (Array.make 4#usize [4#u8, 5#u8, 6#u8, 6#u8])
          (alloc.vec.Vec.deref groupValues) alpha alpha2 alpha3 = ok out3) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows
        (alloc.vec.Vec.deref releasedRowGroups16)
        (alloc.vec.Vec.deref groupValues) alpha alpha2 alpha3 =
      ok (releasedRowGroups4, releasedFourValues out0 out1 out2 out3) := by
  simp (config := { maxSteps := 1500000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows,
     V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0,
     V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0.body,
     V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0_loop0,
     V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows_loop0_loop0.body,
     releasedRows16ChunksExactExplicit, releasedRows16ExplicitIterator,
     releasedRowGroups16, releasedRowGroups4, releasedFourValues,
     alloc.vec.Vec.deref, alloc.vec.Vec.len, alloc.vec.Vec.push,
     alloc.vec.Vec.index, alloc.vec.Vec.index_usize,
     Slice.len, Slice.index_usize, Array.index_usize,
     core.array.equality.PartialEqArray.ne,
     core.array.equality.PartialEqArray.eq,
     core.cmp.PartialEqU8, Std.lift, UScalar.lt_equiv,
     loop.eq_1, run0, run1, run2, run3]

end AspisV5RelationLinkedGroupedRowsSource
