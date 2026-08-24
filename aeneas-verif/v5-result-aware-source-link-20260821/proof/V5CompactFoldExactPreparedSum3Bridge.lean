import V5CompactFoldExactPreparedSumBridge

namespace AspisV5CompactFoldExactPreparedSum3Bridge

open Aeneas Aeneas.Std Result ControlFlow Error
open AspisV5CompactFoldExactCallerBridge
open AspisV5CompactFoldExactUnrolledTypes
open AspisV5CompactFoldExactArrayBridge
open AspisV5CompactFoldExactPreparedSumBridge

theorem channel3_body_to_legacy
    (left : Array ExactPrepared 3#usize) (index : Std.Usize)
    (rightComponents : ComponentMatrix)
    (component : Std.Usize) (iter : core.ops.range.Range Std.Usize)
    (sums : SumMatrix) :
    V5RelationCompactFoldGeneratedExact.aspis_core.field.qm31_sum_products3_prepared_loop0_loop0_loop0.body
        left index rightComponents component iter sums =
      V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products3_prepared_loop0_loop0_loop0.body
        (exactPreparedArrayToLegacy left) index rightComponents component iter sums := by
  unfold
    V5RelationCompactFoldGeneratedExact.aspis_core.field.qm31_sum_products3_prepared_loop0_loop0_loop0.body
    V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products3_prepared_loop0_loop0_loop0.body
  generalize nextRun :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = next
  cases next with
  | fail error => simp
  | div => simp
  | ok pair =>
    rcases pair with ⟨option, iter1⟩
    cases option with
    | none => simp
    | some channel =>
      simp only [bind_tc_ok]
      apply prepared_channel_bind_eq

theorem channel3_loop_to_legacy
    (iter : core.ops.range.Range Std.Usize)
    (left : Array ExactPrepared 3#usize) (sums : SumMatrix)
    (index : Std.Usize) (rightComponents : ComponentMatrix)
    (component : Std.Usize) :
    V5RelationCompactFoldGeneratedExact.aspis_core.field.qm31_sum_products3_prepared_loop0_loop0_loop0
        iter left sums index rightComponents component =
      V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products3_prepared_loop0_loop0_loop0
        iter (exactPreparedArrayToLegacy left) sums index rightComponents component := by
  unfold
    V5RelationCompactFoldGeneratedExact.aspis_core.field.qm31_sum_products3_prepared_loop0_loop0_loop0
    V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products3_prepared_loop0_loop0_loop0
  apply congrArg (fun body => Aeneas.Std.loop body (iter, sums))
  funext state
  rcases state with ⟨iter1, sums1⟩
  exact channel3_body_to_legacy left index rightComponents component iter1 sums1

theorem component3_body_to_legacy
    (left : Array ExactPrepared 3#usize) (index : Std.Usize)
    (rightComponents : ComponentMatrix)
    (iter : core.ops.range.Range Std.Usize) (sums : SumMatrix) :
    V5RelationCompactFoldGeneratedExact.aspis_core.field.qm31_sum_products3_prepared_loop0_loop0.body
        left index rightComponents iter sums =
      V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products3_prepared_loop0_loop0.body
        (exactPreparedArrayToLegacy left) index rightComponents iter sums := by
  unfold
    V5RelationCompactFoldGeneratedExact.aspis_core.field.qm31_sum_products3_prepared_loop0_loop0.body
    V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products3_prepared_loop0_loop0.body
  generalize nextRun :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = next
  cases next with
  | fail error => simp
  | div => simp
  | ok pair =>
    rcases pair with ⟨option, iter1⟩
    cases option with
    | none => simp
    | some component =>
      simp only [bind_tc_ok]
      rw [channel3_loop_to_legacy]

theorem component3_loop_to_legacy
    (iter : core.ops.range.Range Std.Usize)
    (left : Array ExactPrepared 3#usize) (sums : SumMatrix)
    (index : Std.Usize) (rightComponents : ComponentMatrix) :
    V5RelationCompactFoldGeneratedExact.aspis_core.field.qm31_sum_products3_prepared_loop0_loop0
        iter left sums index rightComponents =
      V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products3_prepared_loop0_loop0
        iter (exactPreparedArrayToLegacy left) sums index rightComponents := by
  unfold
    V5RelationCompactFoldGeneratedExact.aspis_core.field.qm31_sum_products3_prepared_loop0_loop0
    V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products3_prepared_loop0_loop0
  apply congrArg (fun body => Aeneas.Std.loop body (iter, sums))
  funext state
  rcases state with ⟨iter1, sums1⟩
  exact component3_body_to_legacy left index rightComponents iter1 sums1

def legacyItem3After (left : Array LegacyPrepared 3#usize)
    (sums : SumMatrix) (index : Std.Usize)
    (iter1 : core.ops.range.Range Std.Usize) (value : LegacyRaw) :
    Result ItemFlow := do
  let rightSum ← V5RelationCompactFoldGenerated.aspis_core.field.CM31.add
    value.c0 value.c1
  let m0 ← V5RelationCompactFoldGenerated.aspis_core.field.M31.add
    value.c0.a value.c0.b
  let m1 ← V5RelationCompactFoldGenerated.aspis_core.field.M31.add
    value.c1.a value.c1.b
  let m2 ← V5RelationCompactFoldGenerated.aspis_core.field.M31.add
    rightSum.a rightSum.b
  let sums1 ←
    V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products3_prepared_loop0_loop0
      { start := 0#usize, «end» := 3#usize } left sums index
      (Array.make 3#usize [
        Array.make 3#usize [value.c0.a, value.c0.b, m0],
        Array.make 3#usize [value.c1.a, value.c1.b, m1],
        Array.make 3#usize [rightSum.a, rightSum.b, m2]])
  ok (cont (iter1, sums1))

theorem item3_after_raw_to_legacy
    (left : Array ExactPrepared 3#usize) (sums : SumMatrix)
    (index : Std.Usize) (iter1 : core.ops.range.Range Std.Usize)
    (value : ExactRaw) :
    (do
      let rightSum ←
        V5RelationCompactFoldGeneratedExact.aspis_core.field.CM31.add
          value.c0 value.c1
      let m0 ← V5RelationCompactFoldGeneratedExact.aspis_core.field.M31.add
        value.c0.a value.c0.b
      let m1 ← V5RelationCompactFoldGeneratedExact.aspis_core.field.M31.add
        value.c1.a value.c1.b
      let m2 ← V5RelationCompactFoldGeneratedExact.aspis_core.field.M31.add
        rightSum.a rightSum.b
      let sums1 ←
        V5RelationCompactFoldGeneratedExact.aspis_core.field.qm31_sum_products3_prepared_loop0_loop0
          { start := 0#usize, «end» := 3#usize } left sums index
          (Array.make 3#usize [
            Array.make 3#usize [value.c0.a, value.c0.b, m0],
            Array.make 3#usize [value.c1.a, value.c1.b, m1],
            Array.make 3#usize [rightSum.a, rightSum.b, m2]])
      ok (cont (iter1, sums1) : ItemFlow)) =
      legacyItem3After (exactPreparedArrayToLegacy left) sums index iter1
        (exactToLegacyRaw value) := by
  simp [legacyItem3After,
    V5RelationCompactFoldGeneratedExact.aspis_core.field.CM31.add,
    V5RelationCompactFoldGenerated.aspis_core.field.CM31.add,
    V5RelationCompactFoldGeneratedExact.aspis_core.field.M31.add,
    V5RelationCompactFoldGenerated.aspis_core.field.M31.add,
    V5RelationCompactFoldGeneratedExact.aspis_core.field.P,
    V5RelationCompactFoldGenerated.aspis_core.field.P,
    exactToLegacyRaw, component3_loop_to_legacy]

theorem item3_body_to_legacy
    (left : Array ExactPrepared 3#usize)
    (right : Array ExactRaw 3#usize)
    (iter : core.ops.range.Range Std.Usize) (sums : SumMatrix) :
    V5RelationCompactFoldGeneratedExact.aspis_core.field.qm31_sum_products3_prepared_loop0.body
        left right iter sums =
      V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products3_prepared_loop0.body
        (exactPreparedArrayToLegacy left) (exactRawArrayToLegacy right)
        iter sums := by
  unfold
    V5RelationCompactFoldGeneratedExact.aspis_core.field.qm31_sum_products3_prepared_loop0.body
    V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products3_prepared_loop0.body
  generalize nextRun :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = next
  cases next with
  | fail error => simp
  | div => simp
  | ok pair =>
    rcases pair with ⟨option, iter1⟩
    cases option with
    | none => simp
    | some index =>
      simp only [bind_tc_ok]
      simp only [item3_after_raw_to_legacy]
      change
        (do
          let value ← Array.index_usize right index
          legacyItem3After (exactPreparedArrayToLegacy left) sums index iter1
            (exactToLegacyRaw value)) =
        (do
          let value ← Array.index_usize (exactRawArrayToLegacy right) index
          legacyItem3After (exactPreparedArrayToLegacy left) sums index iter1
            value)
      exact raw_index_bind_eq (Output := ItemFlow) right index _

theorem item3_loop_to_legacy
    (iter : core.ops.range.Range Std.Usize)
    (left : Array ExactPrepared 3#usize)
    (right : Array ExactRaw 3#usize) (sums : SumMatrix) :
    V5RelationCompactFoldGeneratedExact.aspis_core.field.qm31_sum_products3_prepared_loop0
        iter left right sums =
      V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products3_prepared_loop0
        iter (exactPreparedArrayToLegacy left)
        (exactRawArrayToLegacy right) sums := by
  unfold
    V5RelationCompactFoldGeneratedExact.aspis_core.field.qm31_sum_products3_prepared_loop0
    V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products3_prepared_loop0
  apply congrArg (fun body => Aeneas.Std.loop body (iter, sums))
  funext state
  rcases state with ⟨iter1, sums1⟩
  exact item3_body_to_legacy left right iter1 sums1

theorem sum_products3_arrays_to_legacy
    (left : Array ExactPrepared 3#usize)
    (right : Array ExactRaw 3#usize) :
    (do
      let output ←
        V5RelationCompactFoldGeneratedExact.aspis_core.field.qm31_sum_products3_prepared
          left right
      ok (exactToLegacyRaw output)) =
      V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products3_prepared
        (exactPreparedArrayToLegacy left) (exactRawArrayToLegacy right) := by
  unfold
    V5RelationCompactFoldGeneratedExact.aspis_core.field.qm31_sum_products3_prepared
    V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products3_prepared
  simp only [item3_loop_to_legacy]
  simp only [bind_assoc]
  exact karatsuba_after_source_to_legacy _

#print axioms channel3_body_to_legacy
#print axioms channel3_loop_to_legacy
#print axioms component3_body_to_legacy
#print axioms component3_loop_to_legacy
#print axioms item3_after_raw_to_legacy
#print axioms item3_body_to_legacy
#print axioms item3_loop_to_legacy
#print axioms sum_products3_arrays_to_legacy

end AspisV5CompactFoldExactPreparedSum3Bridge
