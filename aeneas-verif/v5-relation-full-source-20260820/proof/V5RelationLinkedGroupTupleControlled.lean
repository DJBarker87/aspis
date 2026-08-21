import V5RelationLinkedGroupTuple

namespace AspisV5RelationLinkedGroupTupleControlled

open Aeneas Aeneas.Std Result ControlFlow

abbrev RawQM31 := V5RelationLinkedGenerated.aspis_core.field.QM31

def tripleFirstProgram
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 : RawQM31) : Result RawQM31 := do
  let coefficient0 ← V5RelationLinkedGenerated.aspis_core.field.QM31.add
    V5RelationLinkedGenerated.aspis_core.field.QM31.ONE alpha3
  let coefficient1 ← V5RelationLinkedGenerated.aspis_core.field.QM31.add
    coefficient0 alpha2
  let value0 ← Slice.index_usize groupValues 1#usize
  let value1 ← Slice.index_usize groupValues 2#usize
  let contribution0 ← V5RelationLinkedGenerated.aspis_core.field.QM31.mul
    value0 coefficient1
  let contribution1 ← V5RelationLinkedGenerated.aspis_core.field.QM31.mul
    value1 alpha
  let sum0 ← V5RelationLinkedGenerated.aspis_core.field.QM31.add
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO contribution0
  let sum1 ← V5RelationLinkedGenerated.aspis_core.field.QM31.add
    sum0 contribution1
  let half1 ← V5RelationLinkedGenerated.aspis_core.field.QM31.half sum1
  V5RelationLinkedGenerated.aspis_core.field.QM31.half half1

private def tripleUnique1 : Array Std.U8 4#usize :=
  Array.make 4#usize [1#u8, 0#u8, 0#u8, 0#u8]

private theorem tripleFindEmpty :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1
        (Array.repeat 4#usize 0#u8) 0#usize 1#u8 0#usize = ok 0#usize := by
  decide

private theorem tripleFindExisting :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1
        tripleUnique1 1#usize 1#u8 0#usize = ok 0#usize := by
  decide

private theorem tripleFindNew :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1
        tripleUnique1 1#usize 2#u8 0#usize = ok 1#usize := by
  decide

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 12000 in
theorem tripleFirstControlled :
    ∀ (groupValues : Slice RawQM31) (alpha alpha2 alpha3 : RawQM31),
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
        (Array.make 4#usize [1#u8, 1#u8, 1#u8, 2#u8])
        groupValues alpha alpha2 alpha3 =
      tripleFirstProgram groupValues alpha alpha2 alpha3 := by
  intro groupValues alpha alpha2 alpha3
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0
  rw [loop.eq_1]
  dsimp only
  simp (config := { maxSteps := 300000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    tripleFindEmpty, core.iter.range.IteratorRange.next,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked,
    core.cmp.impls.PartialOrdUsize.lt, Array.index_usize, Array.update,
    UScalar.lt_equiv, Std.lift]

end AspisV5RelationLinkedGroupTupleControlled
