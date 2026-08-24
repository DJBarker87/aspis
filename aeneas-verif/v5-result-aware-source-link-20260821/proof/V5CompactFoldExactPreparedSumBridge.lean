import V5CompactFoldExactArrayBridge

namespace AspisV5CompactFoldExactPreparedSumBridge

open Aeneas Aeneas.Std Result ControlFlow Error
open AspisV5CompactFoldExactCallerBridge
open AspisV5CompactFoldExactUnrolledTypes
open AspisV5CompactFoldExactArrayBridge

abbrev ComponentMatrix := Array (Array Std.U32 3#usize) 3#usize
abbrev SumMatrix := Array (Array Std.U64 3#usize) 3#usize
abbrev ItemFlow := ControlFlow
  (core.ops.range.Range Std.Usize × SumMatrix) SumMatrix

theorem karatsuba_after_source_to_legacy (source : Result SumMatrix) :
    (do
      let sums ← source
      let output ←
        V5RelationCompactFoldGeneratedExact.aspis_core.field.qm31_from_karatsuba_channel_sums
          sums
      ok (exactToLegacyRaw output)) =
    (do
      let sums ← source
      V5RelationCompactFoldGenerated.aspis_core.field.qm31_from_karatsuba_channel_sums
        sums) := by
  cases source with
  | fail error => rfl
  | div => rfl
  | ok sums =>
    exact AspisV5CompactFoldExactFieldBridge.karatsuba_sums_to_legacy sums

def exactRightComponents (value : ExactRaw) : Result ComponentMatrix := do
  let rightSum ←
    V5RelationCompactFoldGeneratedExact.aspis_core.field.CM31.add
      value.c0 value.c1
  let m0 ← V5RelationCompactFoldGeneratedExact.aspis_core.field.M31.add
    value.c0.a value.c0.b
  let m1 ← V5RelationCompactFoldGeneratedExact.aspis_core.field.M31.add
    value.c1.a value.c1.b
  let m2 ← V5RelationCompactFoldGeneratedExact.aspis_core.field.M31.add
    rightSum.a rightSum.b
  ok (Array.make 3#usize [
    Array.make 3#usize [value.c0.a, value.c0.b, m0],
    Array.make 3#usize [value.c1.a, value.c1.b, m1],
    Array.make 3#usize [rightSum.a, rightSum.b, m2]])

def legacyRightComponents (value : LegacyRaw) : Result ComponentMatrix := do
  let rightSum ← V5RelationCompactFoldGenerated.aspis_core.field.CM31.add
    value.c0 value.c1
  let m0 ← V5RelationCompactFoldGenerated.aspis_core.field.M31.add
    value.c0.a value.c0.b
  let m1 ← V5RelationCompactFoldGenerated.aspis_core.field.M31.add
    value.c1.a value.c1.b
  let m2 ← V5RelationCompactFoldGenerated.aspis_core.field.M31.add
    rightSum.a rightSum.b
  ok (Array.make 3#usize [
    Array.make 3#usize [value.c0.a, value.c0.b, m0],
    Array.make 3#usize [value.c1.a, value.c1.b, m1],
    Array.make 3#usize [rightSum.a, rightSum.b, m2]])

theorem right_components_to_legacy (value : ExactRaw) :
    exactRightComponents value =
      legacyRightComponents (exactToLegacyRaw value) := by
  simp [exactRightComponents, legacyRightComponents,
    V5RelationCompactFoldGeneratedExact.aspis_core.field.CM31.add,
    V5RelationCompactFoldGenerated.aspis_core.field.CM31.add,
    V5RelationCompactFoldGeneratedExact.aspis_core.field.M31.add,
    V5RelationCompactFoldGenerated.aspis_core.field.M31.add,
    V5RelationCompactFoldGeneratedExact.aspis_core.field.P,
    V5RelationCompactFoldGenerated.aspis_core.field.P,
    exactToLegacyRaw, exactToLegacyCM]

theorem channel_body_to_legacy
    (left : Array ExactPrepared 2#usize) (index : Std.Usize)
    (rightComponents : Array (Array Std.U32 3#usize) 3#usize)
    (component : Std.Usize) (iter : core.ops.range.Range Std.Usize)
    (sums : Array (Array Std.U64 3#usize) 3#usize) :
    V5RelationCompactFoldGeneratedExact.aspis_core.field.qm31_sum_products2_prepared_loop0_loop0_loop0.body
        left index rightComponents component iter sums =
      V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products2_prepared_loop0_loop0_loop0.body
        (exactPreparedArrayToLegacy left) index rightComponents component iter sums := by
  unfold
    V5RelationCompactFoldGeneratedExact.aspis_core.field.qm31_sum_products2_prepared_loop0_loop0_loop0.body
    V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products2_prepared_loop0_loop0_loop0.body
  generalize nextRun :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = next
  cases next with
  | fail error => simp [nextRun]
  | div => simp [nextRun]
  | ok pair =>
    rcases pair with ⟨option, iter1⟩
    cases option with
    | none => simp [nextRun]
    | some channel =>
      simp only [nextRun, bind_tc_ok]
      apply prepared_channel_bind_eq

theorem channel_loop_to_legacy
    (iter : core.ops.range.Range Std.Usize)
    (left : Array ExactPrepared 2#usize)
    (sums : Array (Array Std.U64 3#usize) 3#usize)
    (index : Std.Usize)
    (rightComponents : Array (Array Std.U32 3#usize) 3#usize)
    (component : Std.Usize) :
    V5RelationCompactFoldGeneratedExact.aspis_core.field.qm31_sum_products2_prepared_loop0_loop0_loop0
        iter left sums index rightComponents component =
      V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products2_prepared_loop0_loop0_loop0
        iter (exactPreparedArrayToLegacy left) sums index rightComponents component := by
  unfold
    V5RelationCompactFoldGeneratedExact.aspis_core.field.qm31_sum_products2_prepared_loop0_loop0_loop0
    V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products2_prepared_loop0_loop0_loop0
  apply congrArg (fun body => Aeneas.Std.loop body (iter, sums))
  funext state
  rcases state with ⟨iter1, sums1⟩
  exact channel_body_to_legacy left index rightComponents component iter1 sums1

theorem component_body_to_legacy
    (left : Array ExactPrepared 2#usize) (index : Std.Usize)
    (rightComponents : Array (Array Std.U32 3#usize) 3#usize)
    (iter : core.ops.range.Range Std.Usize)
    (sums : Array (Array Std.U64 3#usize) 3#usize) :
    V5RelationCompactFoldGeneratedExact.aspis_core.field.qm31_sum_products2_prepared_loop0_loop0.body
        left index rightComponents iter sums =
      V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products2_prepared_loop0_loop0.body
        (exactPreparedArrayToLegacy left) index rightComponents iter sums := by
  unfold
    V5RelationCompactFoldGeneratedExact.aspis_core.field.qm31_sum_products2_prepared_loop0_loop0.body
    V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products2_prepared_loop0_loop0.body
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
      rw [channel_loop_to_legacy]

theorem component_loop_to_legacy
    (iter : core.ops.range.Range Std.Usize)
    (left : Array ExactPrepared 2#usize)
    (sums : Array (Array Std.U64 3#usize) 3#usize)
    (index : Std.Usize)
    (rightComponents : Array (Array Std.U32 3#usize) 3#usize) :
    V5RelationCompactFoldGeneratedExact.aspis_core.field.qm31_sum_products2_prepared_loop0_loop0
        iter left sums index rightComponents =
      V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products2_prepared_loop0_loop0
        iter (exactPreparedArrayToLegacy left) sums index rightComponents := by
  unfold
    V5RelationCompactFoldGeneratedExact.aspis_core.field.qm31_sum_products2_prepared_loop0_loop0
    V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products2_prepared_loop0_loop0
  apply congrArg (fun body => Aeneas.Std.loop body (iter, sums))
  funext state
  rcases state with ⟨iter1, sums1⟩
  exact component_body_to_legacy left index rightComponents iter1 sums1

def legacyItemAfter (left : Array LegacyPrepared 2#usize)
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
    V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products2_prepared_loop0_loop0
      { start := 0#usize, «end» := 3#usize } left sums index
      (Array.make 3#usize [
        Array.make 3#usize [value.c0.a, value.c0.b, m0],
        Array.make 3#usize [value.c1.a, value.c1.b, m1],
        Array.make 3#usize [rightSum.a, rightSum.b, m2]])
  ok (cont (iter1, sums1))

theorem item_after_raw_to_legacy
    (left : Array ExactPrepared 2#usize)
    (sums : Array (Array Std.U64 3#usize) 3#usize)
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
        V5RelationCompactFoldGeneratedExact.aspis_core.field.qm31_sum_products2_prepared_loop0_loop0
          { start := 0#usize, «end» := 3#usize } left sums index
          (Array.make 3#usize [
            Array.make 3#usize [value.c0.a, value.c0.b, m0],
            Array.make 3#usize [value.c1.a, value.c1.b, m1],
            Array.make 3#usize [rightSum.a, rightSum.b, m2]])
      ok (cont (iter1, sums1) : ItemFlow)) =
    legacyItemAfter (exactPreparedArrayToLegacy left) sums index iter1
      (exactToLegacyRaw value) := by
  simp [legacyItemAfter,
    V5RelationCompactFoldGeneratedExact.aspis_core.field.CM31.add,
    V5RelationCompactFoldGenerated.aspis_core.field.CM31.add,
    V5RelationCompactFoldGeneratedExact.aspis_core.field.M31.add,
    V5RelationCompactFoldGenerated.aspis_core.field.M31.add,
    V5RelationCompactFoldGeneratedExact.aspis_core.field.P,
    V5RelationCompactFoldGenerated.aspis_core.field.P,
    exactToLegacyRaw, component_loop_to_legacy]

theorem item_body_to_legacy
    (left : Array ExactPrepared 2#usize)
    (right : Array ExactRaw 2#usize)
    (iter : core.ops.range.Range Std.Usize)
    (sums : Array (Array Std.U64 3#usize) 3#usize) :
    V5RelationCompactFoldGeneratedExact.aspis_core.field.qm31_sum_products2_prepared_loop0.body
        left right iter sums =
      V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products2_prepared_loop0.body
        (exactPreparedArrayToLegacy left) (exactRawArrayToLegacy right)
        iter sums := by
  unfold
    V5RelationCompactFoldGeneratedExact.aspis_core.field.qm31_sum_products2_prepared_loop0.body
    V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products2_prepared_loop0.body
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
      simp only [item_after_raw_to_legacy]
      change
        (do
          let value ← Array.index_usize right index
          legacyItemAfter (exactPreparedArrayToLegacy left) sums index iter1
            (exactToLegacyRaw value)) =
        (do
          let value ← Array.index_usize (exactRawArrayToLegacy right) index
          legacyItemAfter (exactPreparedArrayToLegacy left) sums index iter1
            value)
      exact raw_index_bind_eq (Output := ItemFlow) right index _

theorem item_loop_to_legacy
    (iter : core.ops.range.Range Std.Usize)
    (left : Array ExactPrepared 2#usize)
    (right : Array ExactRaw 2#usize) (sums : SumMatrix) :
    V5RelationCompactFoldGeneratedExact.aspis_core.field.qm31_sum_products2_prepared_loop0
        iter left right sums =
      V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products2_prepared_loop0
        iter (exactPreparedArrayToLegacy left)
        (exactRawArrayToLegacy right) sums := by
  unfold
    V5RelationCompactFoldGeneratedExact.aspis_core.field.qm31_sum_products2_prepared_loop0
    V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products2_prepared_loop0
  apply congrArg (fun body => Aeneas.Std.loop body (iter, sums))
  funext state
  rcases state with ⟨iter1, sums1⟩
  exact item_body_to_legacy left right iter1 sums1

theorem sum_products2_arrays_to_legacy
    (left : Array ExactPrepared 2#usize)
    (right : Array ExactRaw 2#usize) :
    (do
      let output ←
        V5RelationCompactFoldGeneratedExact.aspis_core.field.qm31_sum_products2_prepared
          left right
      ok (exactToLegacyRaw output)) =
      V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products2_prepared
        (exactPreparedArrayToLegacy left) (exactRawArrayToLegacy right) := by
  unfold
    V5RelationCompactFoldGeneratedExact.aspis_core.field.qm31_sum_products2_prepared
    V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products2_prepared
  simp only [item_loop_to_legacy]
  simp only [bind_assoc]
  exact karatsuba_after_source_to_legacy _

#print axioms channel_body_to_legacy
#print axioms right_components_to_legacy
#print axioms channel_loop_to_legacy
#print axioms component_body_to_legacy
#print axioms component_loop_to_legacy
#print axioms item_after_raw_to_legacy
#print axioms item_body_to_legacy
#print axioms item_loop_to_legacy
#print axioms sum_products2_arrays_to_legacy
#print axioms karatsuba_after_source_to_legacy

end AspisV5CompactFoldExactPreparedSumBridge
