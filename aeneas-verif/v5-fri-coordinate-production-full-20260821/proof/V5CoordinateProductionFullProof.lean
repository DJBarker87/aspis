import V5CoordinateProductionFull.FunsDriver
import V5CoordinateSelectedProductionProof

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 24000

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V5CoordinateProductionFullProof

open V5CoordinateSelectedProductionProof
open AspisV5FriCoordinateFieldSemantics
open AspisV5FriCoordinatePointLoops
open AspisV5FriCoordinateMathematics
open AspisV5FriCoordinateReleasedPointConnection
open AspisCircleGroupOrder

namespace Source
open V5CoordinateSelectedProductionSource
end Source

namespace Adapter
open V5FriCoordinateAdapter
end Adapter

abbrev SourcePoint :=
  V5CoordinateSelectedProductionSource.circle_fri.BaseCirclePoint

abbrev AdapterPoint :=
  V5FriCoordinateAdapter.aspis_core.circle_fri.BaseCirclePoint

abbrev SourcePointVec := alloc.vec.Vec SourcePoint
abbrev AdapterPointVec := alloc.vec.Vec AdapterPoint

def toAdapterPointVec (points : SourcePointVec) : AdapterPointVec :=
  ⟨points.val.map toAdapterPoint, by simpa using points.property⟩

@[simp] theorem toAdapterPointVec_val (points : SourcePointVec) :
    (toAdapterPointVec points).val = points.val.map toAdapterPoint := rfl

private theorem adapter_p_eq_arithmetic :
    V5FriCoordinateAdapter.aspis_core.field.P =
      V5FriArithmeticExact.field.P := by
  unfold V5FriCoordinateAdapter.aspis_core.field.P
    V5FriArithmeticExact.field.P
  apply UScalar.eq_of_val_eq
  rfl

private theorem adapter_add_call_eq_arithmetic
    (left right : Std.U32) :
    V5FriCoordinateAdapter.aspis_core.field.M31.add left right =
      V5FriArithmeticExact.field.M31.add left right := by
  unfold V5FriCoordinateAdapter.aspis_core.field.M31.add
    V5FriArithmeticExact.field.M31.add
  rw [adapter_p_eq_arithmetic]

private theorem adapter_sub_call_eq_arithmetic
    (left right : Std.U32) :
    V5FriCoordinateAdapter.aspis_core.field.M31.sub left right =
      V5FriArithmeticExact.field.M31.sub left right := by
  unfold V5FriCoordinateAdapter.aspis_core.field.M31.sub
    V5FriArithmeticExact.field.M31.sub
  rw [adapter_p_eq_arithmetic]

private theorem add_produces_canonical
    (left right : Std.U32)
    (hleft : canonicalM31 left) (hright : canonicalM31 right) :
    ∃ output : Std.U32,
      V5FriCoordinateAdapter.aspis_core.field.M31.add left right =
          .ok output ∧
      canonicalM31 output ∧
      m31Value output = m31Value left + m31Value right := by
  obtain ⟨output, hrun, hcanonical, hvalue⟩ :=
    AspisV5FriArithmeticSemantics.m31_add_corresponds
      left right hleft hright
  refine ⟨output, ?_, hcanonical, hvalue⟩
  rw [adapter_add_call_eq_arithmetic]
  exact hrun

private theorem sub_produces_canonical
    (left right : Std.U32)
    (hleft : canonicalM31 left) (hright : canonicalM31 right) :
    ∃ output : Std.U32,
      V5FriCoordinateAdapter.aspis_core.field.M31.sub left right =
          .ok output ∧
      canonicalM31 output ∧
      m31Value output = m31Value left - m31Value right := by
  obtain ⟨output, hrun, hcanonical, hvalue⟩ :=
    AspisV5FriArithmeticSemantics.m31_sub_corresponds
      left right hleft hright
  refine ⟨output, ?_, hcanonical, hvalue⟩
  rw [adapter_sub_call_eq_arithmetic]
  exact hrun

theorem source_double_eq_adapter_double
    (value : Std.U32) (hvalue : canonicalM31 value) :
    V5CoordinateSelectedProductionSource.field.M31.double value =
      V5FriCoordinateAdapter.aspis_core.field.M31.double value := by
  unfold V5CoordinateSelectedProductionSource.field.M31.double
    V5FriCoordinateAdapter.aspis_core.field.M31.double
  exact source_add_eq_adapter_add value value
    (canonical_m31_lt value hvalue) (canonical_m31_lt value hvalue)

theorem source_neg_eq_adapter_neg
    (value : Std.U32) (hvalue : canonicalM31 value) :
    V5CoordinateSelectedProductionSource.field.M31.neg value =
      V5FriCoordinateAdapter.aspis_core.field.M31.neg value := by
  unfold V5CoordinateSelectedProductionSource.field.M31.neg
    V5FriCoordinateAdapter.aspis_core.field.M31.neg
  rw [p_eq]
  by_cases hzero : value = 0#u32
  · simp [hzero]
  · simp only [hzero, if_false]
    rw [checked_sub_eq_wrapping]
    · simp [Std.lift, generic_wrapping_sub_eq_u32_wrapping_sub]
    · have hlt := canonical_m31_lt value hvalue
      have hp : V5FriCoordinateAdapter.aspis_core.field.P.val =
          2147483647 := adapter_p_val_eq
      exact (show value.val ≤
        V5FriCoordinateAdapter.aspis_core.field.P.val by omega)

theorem source_double_point_maps_adapter
    (point : SourcePoint)
    (hpoint : pointCanonical (toAdapterPoint point)) :
    mapSourcePointResult
        (V5CoordinateSelectedProductionSource.circle_fri.double_point point) =
      V5FriCoordinateAdapter.aspis_core.circle_fri.double_point
        (toAdapterPoint point) := by
  obtain ⟨sum, hsum, hsumCanonical, _hsumValue⟩ :=
    add_produces_canonical point.x point.y hpoint.1 hpoint.2
  obtain ⟨difference, hdifference, hdifferenceCanonical,
      _hdifferenceValue⟩ :=
    sub_produces_canonical point.x point.y hpoint.1 hpoint.2
  obtain ⟨x, hx, _hxCanonical, _hxValue⟩ :=
    mul_produces_canonical sum difference hsumCanonical
      hdifferenceCanonical
  obtain ⟨product, hproduct, hproductCanonical, _hproductValue⟩ :=
    mul_produces_canonical point.x point.y hpoint.1 hpoint.2
  obtain ⟨y, hy, _hyCanonical, _hyValue⟩ :=
    double_produces_canonical product hproductCanonical
  have hsumSource :
      V5CoordinateSelectedProductionSource.field.M31.add point.x point.y =
        .ok sum := by
    rw [source_add_eq_adapter_add point.x point.y
      (canonical_m31_lt point.x hpoint.1)
      (canonical_m31_lt point.y hpoint.2)]
    exact hsum
  have hdifferenceSource :
      V5CoordinateSelectedProductionSource.field.M31.sub point.x point.y =
        .ok difference := by
    rw [source_sub_eq_adapter_sub point.x point.y
      (canonical_m31_lt point.x hpoint.1)
      (canonical_m31_lt point.y hpoint.2)]
    exact hdifference
  have hxSource :
      V5CoordinateSelectedProductionSource.field.M31.mul sum difference =
        .ok x := by
    rw [source_mul_eq_adapter_mul sum difference
      (canonical_m31_lt sum hsumCanonical)
      (canonical_m31_lt difference hdifferenceCanonical)]
    exact hx
  have hproductSource :
      V5CoordinateSelectedProductionSource.field.M31.mul point.x point.y =
        .ok product := by
    rw [source_mul_eq_adapter_mul point.x point.y
      (canonical_m31_lt point.x hpoint.1)
      (canonical_m31_lt point.y hpoint.2)]
    exact hproduct
  have hySource :
      V5CoordinateSelectedProductionSource.field.M31.double product =
        .ok y := by
    rw [source_double_eq_adapter_double product hproductCanonical]
    exact hy
  unfold V5CoordinateSelectedProductionSource.circle_fri.double_point
    V5FriCoordinateAdapter.aspis_core.circle_fri.double_point
  simp [hsumSource, hdifferenceSource, hxSource, hproductSource, hySource,
    hsum, hdifference, hx, hproduct, hy, mapSourcePointResult,
    toAdapterPoint]

theorem source_remove_rotation_maps_adapter
    (point : SourcePoint) (slot : Std.U32)
    (hslot : slot.val < 4)
    (hpoint : pointCanonical (toAdapterPoint point)) :
    mapSourcePointResult
        (V5CoordinateSelectedProductionSource.circle_fri.remove_line_slot_rotation
          point slot) =
      V5FriCoordinateAdapter.aspis_core.circle_fri.remove_line_slot_rotation
        (toAdapterPoint point) slot := by
  have hx := source_neg_eq_adapter_neg point.x hpoint.1
  have hy := source_neg_eq_adapter_neg point.y hpoint.2
  have hcases : slot.val = 0 ∨ slot.val = 1 ∨
      slot.val = 2 ∨ slot.val = 3 := by omega
  rcases hcases with hzero | hone | htwo | hthree
  · have hsource : slot = (0#32#uscalar : Std.U32) :=
      UScalar.eq_of_val_eq (by norm_num at hzero ⊢; exact hzero)
    subst slot
    simp [V5CoordinateSelectedProductionSource.circle_fri.remove_line_slot_rotation,
      V5FriCoordinateAdapter.aspis_core.circle_fri.remove_line_slot_rotation,
      mapSourcePointResult, toAdapterPoint]
  · have hsource : slot = (1#32#uscalar : Std.U32) :=
      UScalar.eq_of_val_eq (by norm_num at hone ⊢; exact hone)
    subst slot
    simp only [V5CoordinateSelectedProductionSource.circle_fri.remove_line_slot_rotation,
      V5FriCoordinateAdapter.aspis_core.circle_fri.remove_line_slot_rotation,
      hx, hy, mapSourcePointResult, toAdapterPoint]
    generalize hnegX :
      V5FriCoordinateAdapter.aspis_core.field.M31.neg point.x = negX
    cases negX <;> simp [Bind.bind, Aeneas.Std.bind]
    generalize hnegY :
      V5FriCoordinateAdapter.aspis_core.field.M31.neg point.y = negY
    cases negY <;> simp [Bind.bind, Aeneas.Std.bind]
  · have hsource : slot = (2#32#uscalar : Std.U32) :=
      UScalar.eq_of_val_eq (by norm_num at htwo ⊢; exact htwo)
    subst slot
    simp only [V5CoordinateSelectedProductionSource.circle_fri.remove_line_slot_rotation,
      V5FriCoordinateAdapter.aspis_core.circle_fri.remove_line_slot_rotation,
      hy, mapSourcePointResult, toAdapterPoint]
    generalize hnegY :
      V5FriCoordinateAdapter.aspis_core.field.M31.neg point.y = negY
    cases negY <;> simp [Bind.bind, Aeneas.Std.bind]
  · have hsource : slot = (3#32#uscalar : Std.U32) :=
      UScalar.eq_of_val_eq (by norm_num at hthree ⊢; exact hthree)
    subst slot
    simp only [V5CoordinateSelectedProductionSource.circle_fri.remove_line_slot_rotation,
      V5FriCoordinateAdapter.aspis_core.circle_fri.remove_line_slot_rotation,
      hx, mapSourcePointResult, toAdapterPoint]
    generalize hnegX :
      V5FriCoordinateAdapter.aspis_core.field.M31.neg point.x = negX
    cases negX <;> simp [Bind.bind, Aeneas.Std.bind]

theorem source_double_point_exact
    (input : SourcePoint) (expected : AspisCircleGroupOrder.C)
    (hinput : SourceRepresents input expected) :
    ∃ output : SourcePoint,
      V5CoordinateSelectedProductionSource.circle_fri.double_point input =
          .ok output ∧
      SourceRepresents output (expected ^ 2) := by
  obtain ⟨adapterOutput, hadapterRun, hadapterRepresents⟩ :=
    double_point_produces_square (toAdapterPoint input) expected hinput
  have hmapped :
      mapSourcePointResult
          (V5CoordinateSelectedProductionSource.circle_fri.double_point input) =
        .ok adapterOutput := by
    rw [source_double_point_maps_adapter input hinput.1, hadapterRun]
  cases hsource :
      V5CoordinateSelectedProductionSource.circle_fri.double_point input with
  | fail error => simp [hsource, mapSourcePointResult] at hmapped
  | div => simp [hsource, mapSourcePointResult] at hmapped
  | ok sourceOutput =>
      have houtput : toAdapterPoint sourceOutput = adapterOutput := by
        simpa [hsource, mapSourcePointResult] using hmapped
      refine ⟨sourceOutput, rfl, ?_⟩
      unfold SourceRepresents
      rw [houtput]
      exact hadapterRepresents

theorem source_remove_rotation_exact
    (input : SourcePoint) (expected : AspisCircleGroupOrder.C)
    (slot : Std.U32) (hslot : slot.val < 4)
    (hinput : SourceRepresents input expected) :
    ∃ output : SourcePoint,
      V5CoordinateSelectedProductionSource.circle_fri.remove_line_slot_rotation
          input slot = .ok output ∧
      SourceRepresents output
        (removeLineSlotRotation expected ⟨slot.val, hslot⟩) := by
  obtain ⟨adapterOutput, hadapterRun, hadapterRepresents⟩ :=
    remove_line_slot_rotation_produces (toAdapterPoint input) expected
      slot hslot hinput
  have hmapped :
      mapSourcePointResult
          (V5CoordinateSelectedProductionSource.circle_fri.remove_line_slot_rotation
            input slot) = .ok adapterOutput := by
    rw [source_remove_rotation_maps_adapter input slot hslot hinput.1,
      hadapterRun]
  cases hsource :
      V5CoordinateSelectedProductionSource.circle_fri.remove_line_slot_rotation
        input slot with
  | fail error => simp [hsource, mapSourcePointResult] at hmapped
  | div => simp [hsource, mapSourcePointResult] at hmapped
  | ok sourceOutput =>
      have houtput : toAdapterPoint sourceOutput = adapterOutput := by
        simpa [hsource, mapSourcePointResult] using hmapped
      refine ⟨sourceOutput, rfl, ?_⟩
      unfold SourceRepresents
      rw [houtput]
      exact hadapterRepresents

def sourceParentPointCall (input : SourcePoint) (childIndex : Std.U32)
    (doublings : Std.U8) : Result SourcePoint := do
  let point ←
    V5CoordinateSelectedProductionSource.circle_fri.double_point input
  let point1 ←
    if doublings = 2#u8 then
      V5CoordinateSelectedProductionSource.circle_fri.double_point point
    else ok point
  let slot ← lift (childIndex &&& 3#u32)
  V5CoordinateSelectedProductionSource.circle_fri.remove_line_slot_rotation
    point1 slot

theorem source_parent_point_call_exact
    (input : SourcePoint) (expected : AspisCircleGroupOrder.C)
    (childIndex : Std.U32) (doublings : Std.U8)
    (hinput : SourceRepresents input expected) :
    ∃ output : SourcePoint,
      sourceParentPointCall input childIndex doublings = .ok output ∧
      SourceRepresents output
        (parentTransform doublings expected childIndex) := by
  obtain ⟨first, hfirstRun, hfirstRep⟩ :=
    source_double_point_exact input expected hinput
  by_cases htwo : doublings = 2#u8
  · obtain ⟨second, hsecondRun, hsecondRep⟩ :=
      source_double_point_exact first (expected ^ 2) hfirstRep
    have hslotBound : (childIndex &&& 3#u32).val < 4 := by
      rw [source_slot_value]
      exact Nat.mod_lt _ (by norm_num)
    obtain ⟨output, hrotationRun, hrotationRep⟩ :=
      source_remove_rotation_exact second ((expected ^ 2) ^ 2)
        (childIndex &&& 3#u32) hslotBound hsecondRep
    refine ⟨output, ?_, ?_⟩
    · simp [sourceParentPointCall, hfirstRun, htwo, hsecondRun,
        hrotationRun, Std.lift]
    · unfold parentTransform
      simp only [htwo, if_pos]
      have hfin :
          (⟨(childIndex &&& 3#u32).val, hslotBound⟩ : Fin 4) =
            ⟨childIndex.val % 4, Nat.mod_lt _ (by norm_num)⟩ := by
        apply Fin.ext
        exact source_slot_value childIndex
      rw [hfin] at hrotationRep
      exact hrotationRep
  · have hslotBound : (childIndex &&& 3#u32).val < 4 := by
      rw [source_slot_value]
      exact Nat.mod_lt _ (by norm_num)
    obtain ⟨output, hrotationRun, hrotationRep⟩ :=
      source_remove_rotation_exact first (expected ^ 2)
        (childIndex &&& 3#u32) hslotBound hfirstRep
    refine ⟨output, ?_, ?_⟩
    · simp [sourceParentPointCall, hfirstRun, htwo, hrotationRun, Std.lift]
    · unfold parentTransform
      simp only [htwo, if_neg]
      have hfin :
          (⟨(childIndex &&& 3#u32).val, hslotBound⟩ : Fin 4) =
            ⟨childIndex.val % 4, Nat.mod_lt _ (by norm_num)⟩ := by
        apply Fin.ext
        exact source_slot_value childIndex
      rw [hfin] at hrotationRep
      exact hrotationRep

theorem checked_u32_shr_i32_two_eq_wrapping (value : Std.U32) :
    value >>> (2#i32 : Std.I32) =
      Aeneas.Std.Result.ok
        (Std.U32.wrapping_shr value 2#u32) := by
  obtain ⟨output, hrun, _hval, hbv⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (UScalar.ShiftRight_IScalar_spec value (2#i32 : Std.I32)
        (by norm_num) (by norm_num))
  rw [hrun]
  congr 2
  apply UScalar.eq_of_val_eq
  change output.bv.toNat =
    (Std.U32.wrapping_shr value 2#u32).bv.toNat
  rw [hbv, Std.U32.wrapping_shr_bv_eq]
  simp [IScalar.toNat]

private def SourceSearchInvariant (childIndices : Slice Std.U32)
    (ordinal : Std.Usize) : Prop :=
  ordinal.val ≤ childIndices.val.length

private theorem source_wrapping_add_one_exact (value : Std.Usize)
    (hsmall : value.val + 1 < UScalar.size .Usize) :
    (Std.Usize.wrapping_add value 1#usize).val = value.val + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  exact Nat.mod_eq_of_lt (by simpa using hsmall)

private theorem uscalar_usize_max_eq :
    UScalar.max .Usize = Std.Usize.max := by
  rcases System.Platform.numBits_eq with hbits | hbits <;>
    simp [UScalar.max, Std.Usize.max, Std.Usize.numBits, hbits]

/-- The unchanged production inner scan stays within the supplied child
index slice. -/
theorem source_parent_search_bounded
    (childIndices : Slice Std.U32) (start : Std.Usize)
    (parent : Std.U32) (hstart : start.val ≤ childIndices.val.length) :
    V5CoordinateSelectedProductionSource.circle_fri.derive_parent_line_points_loop0_loop0
        childIndices start parent
      ⦃ output => SearchPost childIndices output ⦄ := by
  unfold
    V5CoordinateSelectedProductionSource.circle_fri.derive_parent_line_points_loop0_loop0
  apply loop.spec_decr_nat
    (fun ordinal => childIndices.val.length - ordinal.val)
    (SourceSearchInvariant childIndices)
    (SearchPost childIndices)
  · intro ordinal hordinal
    unfold
      V5CoordinateSelectedProductionSource.circle_fri.derive_parent_line_points_loop0_loop0.body
    by_cases hactive : ordinal.val < childIndices.val.length
    · have hcondition : ordinal < Slice.len childIndices := by
        simpa [UScalar.lt_equiv, Slice.len_val] using hactive
      obtain ⟨child, hchildRun, _hchildValue⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (Slice.index_usize_spec childIndices ordinal hactive)
      let shifted := Std.U32.wrapping_shr child 2#u32
      by_cases hless : shifted < parent
      · have hsmall : ordinal.val + 1 ≤ UScalar.max .Usize := by
          have hmax := childIndices.property
          rw [uscalar_usize_max_eq]
          omega
        have hsmallSize : ordinal.val + 1 < UScalar.size .Usize := by
          rw [UScalar.size_UScalarTyUsize]
          have hsize : Std.Usize.size = Std.Usize.max + 1 := by
            simp [Std.Usize.size, Std.Usize.max, Std.Usize.numBits]
          rw [hsize]
          exact Nat.lt_succ_of_le (by
            rw [uscalar_usize_max_eq] at hsmall
            exact hsmall)
        let next := Std.Usize.wrapping_add ordinal 1#usize
        have hnext : next.val = ordinal.val + 1 := by
          unfold next
          exact source_wrapping_add_one_exact ordinal hsmallSize
        have hcheckedAdd :
            ordinal + 1#usize = Aeneas.Std.Result.ok next := by
          unfold next
          apply checked_add_eq_wrapping
          simpa using hsmall
        simp only [if_pos hcondition]
        rw [hchildRun]
        simp only [bind_tc_ok]
        rw [checked_u32_shr_i32_two_eq_wrapping]
        have hlessSource :
            Std.U32.wrapping_shr child 2#u32 < parent := by
          simpa [shifted] using hless
        simp only [bind_tc_ok, if_pos hlessSource]
        rw [hcheckedAdd]
        simp only [bind_tc_ok, WP.spec_ok]
        change SourceSearchInvariant childIndices next ∧
          childIndices.val.length - next.val <
            childIndices.val.length - ordinal.val
        exact ⟨by unfold SourceSearchInvariant; rw [hnext]; omega,
          by rw [hnext]; omega⟩
      · simp only [if_pos hcondition]
        rw [hchildRun]
        simp only [bind_tc_ok]
        rw [checked_u32_shr_i32_two_eq_wrapping]
        have hlessSource :
            ¬ Std.U32.wrapping_shr child 2#u32 < parent := by
          simpa [shifted] using hless
        simp only [bind_tc_ok, if_neg hlessSource, WP.spec_ok]
        exact hordinal
    · unfold SourceSearchInvariant at hordinal
      have hdone : ordinal.val = childIndices.val.length := by omega
      have hcondition : ¬ ordinal < Slice.len childIndices := by
        simpa [UScalar.lt_equiv, Slice.len_val] using hactive
      simp only [if_neg hcondition, WP.spec_ok]
      unfold SearchPost
      omega
  · exact (by unfold SourceSearchInvariant; exact hstart)

private theorem source_getElemBang_eq_getElem
    {T : Type*} [Inhabited T]
    (values : List T) (index : Nat) (hindex : index < values.length) :
    values[index]! = values[index] := by
  apply List.getElem!_of_getElem?
  simp [hindex]

private theorem source_slice_iterator_next_some
    (values : Slice Std.U32) (index : Nat)
    (hindex : index < values.val.length) :
    core.slice.iter.IteratorSliceIter.next
        ({ slice := values, i := index } : core.slice.iter.Iter Std.U32) =
      .ok (some values.val[index]!,
        ({ slice := values, i := index + 1 } :
          core.slice.iter.Iter Std.U32)) := by
  unfold core.slice.iter.IteratorSliceIter.next
  simp only [Slice.len_val, hindex, dite_true, bind_tc_ok]
  congr 2
  apply congrArg some
  change values.val[index] = values.val[index]!
  exact (source_getElemBang_eq_getElem _ _ hindex).symm

private theorem source_slice_iterator_next_none
    (values : Slice Std.U32) :
    core.slice.iter.IteratorSliceIter.next
        ({ slice := values, i := values.val.length } :
          core.slice.iter.Iter Std.U32) =
      .ok (none,
        ({ slice := values, i := values.val.length } :
          core.slice.iter.Iter Std.U32)) := by
  unfold core.slice.iter.IteratorSliceIter.next
  simp [Slice.len_val]

private theorem source_slice_iterator_next_some_of_slice
    (iter : core.slice.iter.Iter Std.U32) (values : Slice Std.U32)
    (hslice : iter.slice = values)
    (hindex : iter.i < values.val.length) :
    core.slice.iter.IteratorSliceIter.next iter =
      .ok (some values.val[iter.i]!,
        ({ slice := values, i := iter.i + 1 } :
          core.slice.iter.Iter Std.U32)) := by
  rcases iter with ⟨iterSlice, index⟩
  simp only at hslice hindex ⊢
  subst iterSlice
  exact source_slice_iterator_next_some values index hindex

private theorem source_slice_iterator_next_none_of_slice
    (iter : core.slice.iter.Iter Std.U32) (values : Slice Std.U32)
    (hslice : iter.slice = values)
    (hindex : iter.i = values.val.length) :
    core.slice.iter.IteratorSliceIter.next iter =
      .ok (none,
        ({ slice := values, i := values.val.length } :
          core.slice.iter.Iter Std.U32)) := by
  rcases iter with ⟨iterSlice, index⟩
  simp only at hslice hindex ⊢
  subst iterSlice
  subst index
  exact source_slice_iterator_next_none values

private theorem source_slice_get_some
    {T : Type} [Inhabited T] (values : Slice T) (index : Std.Usize)
    (hindex : index.val < values.val.length) :
    core.slice.Slice.get (core.slice.index.SliceIndexUsizeSlice T)
        values index = .ok (some values.val[index.val]!) := by
  unfold core.slice.Slice.get core.slice.index.SliceIndexUsizeSlice
    core.slice.index.Usize.get
  simp only [Slice.getElem?_Usize_eq]
  rw [List.getElem?_eq_getElem hindex,
    source_getElemBang_eq_getElem _ _ hindex]

private theorem source_slice_get_none
    {T : Type} (values : Slice T) (index : Std.Usize)
    (hindex : values.val.length ≤ index.val) :
    core.slice.Slice.get (core.slice.index.SliceIndexUsizeSlice T)
        values index = .ok none := by
  unfold core.slice.Slice.get core.slice.index.SliceIndexUsizeSlice
    core.slice.index.Usize.get
  simp only [Slice.getElem?_Usize_eq]
  rw [List.getElem?_eq_none hindex]

def SourceParentWitness (childIndices : Slice Std.U32)
    (childExpected : Nat → AspisCircleGroupOrder.C)
    (doublings : Std.U8) (parentIndex : Std.U32)
    (point : SourcePoint) : Prop :=
  ∃ childOrdinal : Nat,
    childOrdinal < childIndices.val.length ∧
    childIndices.val[childOrdinal]!.val / 4 = parentIndex.val ∧
    SourceRepresents point
      (parentTransform doublings (childExpected childOrdinal)
        childIndices.val[childOrdinal]!)

def SourceParentResultPost (childIndices parentIndices : Slice Std.U32)
    (childExpected : Nat → AspisCircleGroupOrder.C)
    (doublings : Std.U8)
    (output : core.result.Result SourcePointVec
      V5CoordinateSelectedProductionSource.circle_fri.CircleFriError) : Prop :=
  match output with
  | .Err _ => True
  | .Ok points =>
      points.val.length = parentIndices.val.length ∧
      ∀ (parentOrdinal : Nat)
        (hparent : parentOrdinal < parentIndices.val.length),
        SourceParentWitness childIndices childExpected doublings
          parentIndices.val[parentOrdinal]! points.val[parentOrdinal]!

private def SourceParentLoopInvariant
    (childIndices : Slice Std.U32) (parentIndices : Slice Std.U32)
    (childExpected : Nat → AspisCircleGroupOrder.C)
    (doublings : Std.U8) :
    (core.slice.iter.Iter Std.U32 × SourcePointVec × Std.Usize) → Prop
  | (iter, parents, childOrdinal) =>
      iter.slice = parentIndices ∧
      iter.i ≤ parentIndices.val.length ∧
      childOrdinal.val ≤ childIndices.val.length ∧
      parents.val.length = iter.i ∧
      ∀ (ordinal : Nat) (hordinal : ordinal < iter.i),
        SourceParentWitness childIndices childExpected doublings
          parentIndices.val[ordinal]! parents.val[ordinal]!

private def SourceParentLoopMeasure (parentIndices : Slice Std.U32) :
    core.slice.iter.Iter Std.U32 × SourcePointVec × Std.Usize → Nat
  | (iter, _, _) => parentIndices.val.length - iter.i

private theorem source_generated_parent_continuation_eq
    (input : SourcePoint) (childIndex : Std.U32)
    (doublings : Std.U8) (parents : SourcePointVec) :
    (do
      let point ←
        V5CoordinateSelectedProductionSource.circle_fri.double_point input
      let point1 ←
        if doublings = 2#u8 then
          V5CoordinateSelectedProductionSource.circle_fri.double_point point
        else ok point
      let slot ← lift (childIndex &&& 3#u32)
      let parentPoint ←
        V5CoordinateSelectedProductionSource.circle_fri.remove_line_slot_rotation
          point1 slot
      alloc.vec.Vec.push parents parentPoint) =
      (do
        let parentPoint ← sourceParentPointCall input childIndex doublings
        alloc.vec.Vec.push parents parentPoint) := by
  by_cases htwo : doublings = 2#u8 <;>
    simp [sourceParentPointCall, htwo, Std.lift, bind_assoc]

private theorem source_generated_parent_loop_continuation_eq
    (input : SourcePoint) (childIndex : Std.U32)
    (doublings : Std.U8) (parents : SourcePointVec)
    (nextIter : core.slice.iter.Iter Std.U32)
    (childOrdinal : Std.Usize) :
    (do
      let point ←
        V5CoordinateSelectedProductionSource.circle_fri.double_point input
      let point1 ←
        if doublings = 2#u8 then
          V5CoordinateSelectedProductionSource.circle_fri.double_point point
        else ok point
      let slot ← lift (childIndex &&& 3#u32)
      let parentPoint ←
        V5CoordinateSelectedProductionSource.circle_fri.remove_line_slot_rotation
          point1 slot
      let nextParents ← alloc.vec.Vec.push parents parentPoint
      ok (cont (nextIter, nextParents, childOrdinal) :
        ControlFlow
          (core.slice.iter.Iter Std.U32 × SourcePointVec × Std.Usize)
          (core.result.Result SourcePointVec
            V5CoordinateSelectedProductionSource.circle_fri.CircleFriError))) =
      (do
        let parentPoint ← sourceParentPointCall input childIndex doublings
        let nextParents ← alloc.vec.Vec.push parents parentPoint
        ok (cont (nextIter, nextParents, childOrdinal) :
          ControlFlow
            (core.slice.iter.Iter Std.U32 × SourcePointVec × Std.Usize)
            (core.result.Result SourcePointVec
              V5CoordinateSelectedProductionSource.circle_fri.CircleFriError))) := by
  by_cases htwo : doublings = 2#u8 <;>
    simp [sourceParentPointCall, htwo, Std.lift, bind_assoc]

private theorem source_generated_parent_loop_branches_eq
    (input : SourcePoint) (childIndex : Std.U32)
    (doublings : Std.U8) (parents : SourcePointVec)
    (nextIter : core.slice.iter.Iter Std.U32)
    (childOrdinal : Std.Usize) :
    (do
      let point ←
        V5CoordinateSelectedProductionSource.circle_fri.double_point input
      if doublings = 2#u8 then
        let point1 ←
          V5CoordinateSelectedProductionSource.circle_fri.double_point point
        let slot ← lift (childIndex &&& 3#u32)
        let parentPoint ←
          V5CoordinateSelectedProductionSource.circle_fri.remove_line_slot_rotation
            point1 slot
        let nextParents ← alloc.vec.Vec.push parents parentPoint
        ok (cont (nextIter, nextParents, childOrdinal) :
          ControlFlow
            (core.slice.iter.Iter Std.U32 × SourcePointVec × Std.Usize)
            (core.result.Result SourcePointVec
              V5CoordinateSelectedProductionSource.circle_fri.CircleFriError))
      else
        let slot ← lift (childIndex &&& 3#u32)
        let parentPoint ←
          V5CoordinateSelectedProductionSource.circle_fri.remove_line_slot_rotation
            point slot
        let nextParents ← alloc.vec.Vec.push parents parentPoint
        ok (cont (nextIter, nextParents, childOrdinal) :
          ControlFlow
            (core.slice.iter.Iter Std.U32 × SourcePointVec × Std.Usize)
            (core.result.Result SourcePointVec
              V5CoordinateSelectedProductionSource.circle_fri.CircleFriError))) =
      (do
        let parentPoint ← sourceParentPointCall input childIndex doublings
        let nextParents ← alloc.vec.Vec.push parents parentPoint
        ok (cont (nextIter, nextParents, childOrdinal) :
          ControlFlow
            (core.slice.iter.Iter Std.U32 × SourcePointVec × Std.Usize)
            (core.result.Result SourcePointVec
              V5CoordinateSelectedProductionSource.circle_fri.CircleFriError))) := by
  by_cases htwo : doublings = 2#u8 <;>
    simp [sourceParentPointCall, htwo, Std.lift, bind_assoc]

private theorem source_doublings_gate
    {T : Type} (doublings : Std.U8)
    (hdoublings : doublings = 1#u8 ∨ doublings = 2#u8)
    (next : Result T) :
    (if doublings = 1#u8 then next
      else do
        massert (doublings = 2#u8)
        next) = next := by
  rcases hdoublings with hone | htwo
  · simp [hone]
  · simp [htwo]

/-- Accepted semantics of the unchanged production parent loop.  Rejection
branches are allowed, but a returned `Ok` vector has one authenticated point
for every requested parent, in caller order. -/
theorem source_parent_points_loop_exact
    (childIndices : Slice Std.U32) (childPoints : Slice SourcePoint)
    (parentIndices : Slice Std.U32) (doublings : Std.U8)
    (parents : SourcePointVec)
    (childExpected : Nat → AspisCircleGroupOrder.C)
    (hlengths : childPoints.val.length = childIndices.val.length)
    (hdoublings : doublings = 1#u8 ∨ doublings = 2#u8)
    (hparents : parents.val = [])
    (hchildren : ∀ (ordinal : Nat)
      (hordinal : ordinal < childPoints.val.length),
      SourceRepresents childPoints.val[ordinal]! (childExpected ordinal)) :
    V5CoordinateSelectedProductionSource.circle_fri.derive_parent_line_points_loop0
        ({ slice := parentIndices, i := 0 } : core.slice.iter.Iter Std.U32)
        childIndices childPoints doublings parents 0#usize
      ⦃ output => SourceParentResultPost childIndices parentIndices
        childExpected doublings output ⦄ := by
  unfold
    V5CoordinateSelectedProductionSource.circle_fri.derive_parent_line_points_loop0
  apply loop.spec_decr_nat
    (SourceParentLoopMeasure parentIndices)
    (SourceParentLoopInvariant childIndices parentIndices childExpected
      doublings)
    (SourceParentResultPost childIndices parentIndices childExpected
      doublings)
  · rintro ⟨iter, currentParents, childOrdinal⟩ hstate
    rcases hstate with
      ⟨hiterSlice, hiterBound, hchildBound, hparentsLength,
        hparentWitness⟩
    let parentOrdinal := iter.i
    unfold
      V5CoordinateSelectedProductionSource.circle_fri.derive_parent_line_points_loop0.body
    simp only
    by_cases hparentActive : parentOrdinal < parentIndices.val.length
    · rw [source_slice_iterator_next_some_of_slice iter parentIndices
          hiterSlice (by simpa [parentOrdinal] using hparentActive)]
      simp only [bind_tc_ok]
      let parent := parentIndices.val[parentOrdinal]!
      obtain ⟨selectedChild, hsearchRun, hsearchBound⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (source_parent_search_bounded childIndices childOrdinal parent
            hchildBound)
      rw [hsearchRun]
      simp only [bind_tc_ok]
      by_cases hchildActive : selectedChild.val < childIndices.val.length
      · rw [source_slice_get_some childIndices selectedChild hchildActive]
        simp only [bind_tc_ok, core.option.Option.ok_or,
          core.result.Result.Insts.CoreOpsTry.branch]
        let childIndex := childIndices.val[selectedChild.val]!
        rw [checked_u32_shr_i32_two_eq_wrapping childIndex]
        simp only [bind_tc_ok]
        let shifted := Std.U32.wrapping_shr childIndex 2#u32
        by_cases hmatched : shifted = parent
        ·
          have hbneFalse :
              (Std.U32.wrapping_shr childIndex 2#u32 !=
                parentIndices.val[iter.i]!) = false := by
            apply (bne_eq_false_iff_eq).2
            simpa [shifted, parent, parentOrdinal] using hmatched
          rw [hbneFalse]
          simp only [Bool.false_eq_true, if_false]
          rw [source_doublings_gate doublings hdoublings]
          have hchildPointActive :
              selectedChild.val < childPoints.val.length := by omega
          obtain ⟨childPoint, hchildPointRun, hchildPointValue⟩ :=
            Aeneas.Std.WP.spec_imp_exists
              (Slice.index_usize_spec childPoints selectedChild
                hchildPointActive)
          rw [hchildPointRun]
          simp only [bind_tc_ok]
          have hchildBang :
              childPoints.val[selectedChild.val]! = childPoint := by
            rw [source_getElemBang_eq_getElem _ _ hchildPointActive]
            exact hchildPointValue.symm
          have hinputRep :
              SourceRepresents childPoint
                (childExpected selectedChild.val) := by
            rw [← hchildBang]
            exact hchildren selectedChild.val hchildPointActive
          obtain ⟨parentPoint, hpointRun, hpointRep⟩ :=
            source_parent_point_call_exact childPoint
              (childExpected selectedChild.val) childIndex doublings
              hinputRep
          rw [source_generated_parent_loop_branches_eq childPoint
              childIndices.val[selectedChild.val]! doublings currentParents
              ({ slice := parentIndices, i := iter.i + 1 }) selectedChild,
            hpointRun]
          simp only [bind_tc_ok]
          have hcapacity :
              currentParents.val.length < Std.Usize.max := by
            have hmax := parentIndices.property
            omega
          obtain ⟨nextParents, hpushRun, hnextParents⟩ :=
            Aeneas.Std.WP.spec_imp_exists
              (alloc.vec.Vec.push_spec currentParents parentPoint hcapacity)
          rw [hpushRun]
          simp only [bind_tc_ok, WP.spec_ok]
          change
            SourceParentLoopInvariant childIndices parentIndices
                childExpected doublings
                (({ slice := parentIndices, i := parentOrdinal + 1 } :
                    core.slice.iter.Iter Std.U32), nextParents,
                  selectedChild) ∧
              SourceParentLoopMeasure parentIndices
                  (({ slice := parentIndices, i := parentOrdinal + 1 } :
                    core.slice.iter.Iter Std.U32), nextParents,
                  selectedChild) <
                SourceParentLoopMeasure parentIndices
                  (iter, currentParents, childOrdinal)
          refine ⟨?_, ?_⟩
          · unfold SourceParentLoopInvariant
            simp only [parentOrdinal]
            refine ⟨True.intro, by omega, hsearchBound, ?_, ?_⟩
            · rw [hnextParents, List.length_append, hparentsLength]
              simp
            · intro ordinal hord
              by_cases hprior : ordinal < parentOrdinal
              · have hleft : ordinal < currentParents.val.length := by
                  simpa [hparentsLength] using hprior
                have happendBang :
                    (currentParents.val ++ [parentPoint])[ordinal]! =
                      currentParents.val[ordinal]! := by
                  rw [source_getElemBang_eq_getElem _ _
                      (by simp only [List.length_append,
                          List.length_singleton]; omega),
                    source_getElemBang_eq_getElem _ _ hleft,
                    List.getElem_append_left hleft]
                rw [hnextParents, happendBang]
                exact hparentWitness ordinal hprior
              · have hlast : ordinal = parentOrdinal := by omega
                subst ordinal
                have happendBang :
                    (currentParents.val ++ [parentPoint])[parentOrdinal]! =
                      parentPoint := by
                  rw [source_getElemBang_eq_getElem _ _
                      (by simp [hparentsLength, parentOrdinal])]
                  simp [hparentsLength, parentOrdinal]
                rw [hnextParents, happendBang]
                refine ⟨selectedChild.val, hchildActive, ?_, ?_⟩
                · have hvalues := congrArg UScalar.val hmatched
                  simpa [shifted, childIndex, parent,
                    shifted_parent_value] using hvalues
                · exact hpointRep
          · unfold SourceParentLoopMeasure
            simp only [parentOrdinal]
            omega
        ·
          have hbneTrue :
              (Std.U32.wrapping_shr childIndex 2#u32 !=
                parentIndices.val[iter.i]!) = true := by
            apply (bne_iff_ne).2
            intro heq
            apply hmatched
            simpa [shifted, parent, parentOrdinal] using heq
          rw [hbneTrue]
          simp only [if_true]
          simp [SourceParentResultPost]
      · rw [source_slice_get_none childIndices selectedChild
            (by omega)]
        simp [core.option.Option.ok_or,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          SourceParentResultPost, WP.spec_ok]
    · have hdone : iter.i = parentIndices.val.length := by
        simpa [parentOrdinal] using (show parentOrdinal =
          parentIndices.val.length by omega)
      rw [source_slice_iterator_next_none_of_slice iter parentIndices
        hiterSlice hdone]
      simp only [bind_tc_ok, WP.spec_ok]
      unfold SourceParentResultPost
      refine ⟨by omega, ?_⟩
      intro ordinal hord
      exact hparentWitness ordinal (by omega)
  · unfold SourceParentLoopInvariant
    simp [hparents]

/-- Exact accepted semantics of the unchanged public Rust parent helper. -/
theorem source_derive_parent_line_points_success
    (childIndices : Slice Std.U32) (childPoints : Slice SourcePoint)
    (parentIndices : Slice Std.U32) (doublings : Std.U8)
    (childExpected : Nat → AspisCircleGroupOrder.C)
    (output : SourcePointVec)
    (hlengths : childPoints.val.length = childIndices.val.length)
    (hdoublings : doublings = 1#u8 ∨ doublings = 2#u8)
    (hchildren : ∀ (ordinal : Nat)
      (hordinal : ordinal < childPoints.val.length),
      SourceRepresents childPoints.val[ordinal]! (childExpected ordinal))
    (hrun :
      V5CoordinateSelectedProductionSource.circle_fri.derive_parent_line_points
          childIndices childPoints parentIndices doublings =
        .ok (.Ok output)) :
    output.val.length = parentIndices.val.length ∧
      ∀ (parentOrdinal : Nat)
        (hparent : parentOrdinal < parentIndices.val.length),
        SourceParentWitness childIndices childExpected doublings
          parentIndices.val[parentOrdinal]! output.val[parentOrdinal]! := by
  let initial : SourcePointVec :=
    alloc.vec.Vec.with_capacity SourcePoint (Slice.len parentIndices)
  have hinitial : initial.val = [] := by rfl
  obtain ⟨built, hbuiltRun, hbuiltPost⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (source_parent_points_loop_exact childIndices childPoints parentIndices
        doublings initial childExpected hlengths hdoublings hinitial hchildren)
  have hlengthCondition : Slice.len childIndices = Slice.len childPoints := by
    apply UScalar.eq_of_val_eq
    simpa [Slice.len_val] using hlengths.symm
  unfold
    V5CoordinateSelectedProductionSource.circle_fri.derive_parent_line_points
    at hrun
  have hnotMismatch :
      ¬ ((Slice.len childIndices != Slice.len childPoints) = true) := by
    simp [hlengthCondition]
  simp only [if_neg hnotMismatch] at hrun
  change
    (do
      let iter ←
        SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
          parentIndices
      V5CoordinateSelectedProductionSource.circle_fri.derive_parent_line_points_loop0
        iter childIndices childPoints doublings initial 0#usize) =
      .ok (.Ok output) at hrun
  simp only [
    SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,
    bind_tc_ok] at hrun
  rw [hbuiltRun] at hrun
  have heq : built = .Ok output := Result.ok.inj hrun
  rw [heq] at hbuiltPost
  exact hbuiltPost

/-- A successful unchanged production parent helper returns the requested
released point whenever the released child/parent index relation is
compatible with the parent transformation. -/
theorem source_parent_success_exact_expected
    (childIndices : Slice Std.U32) (childPoints : Slice SourcePoint)
    (parentIndices : Slice Std.U32) (doublings : Std.U8)
    (childExpected parentExpected : Nat → AspisCircleGroupOrder.C)
    (output : SourcePointVec)
    (hlengths : childPoints.val.length = childIndices.val.length)
    (hdoublings : doublings = 1#u8 ∨ doublings = 2#u8)
    (hchildren : ∀ ordinal, ordinal < childPoints.val.length →
      SourceRepresents childPoints.val[ordinal]! (childExpected ordinal))
    (hcompatible :
      AspisV5FriCoordinateTopLevel.ParentExpectedCompatible childIndices
        parentIndices childExpected parentExpected doublings)
    (hrun :
      V5CoordinateSelectedProductionSource.circle_fri.derive_parent_line_points
          childIndices childPoints parentIndices doublings =
        .ok (.Ok output)) :
    output.val.length = parentIndices.val.length ∧
      ∀ ordinal, ordinal < output.val.length →
        SourceRepresents output.val[ordinal]! (parentExpected ordinal) := by
  have hpost := source_derive_parent_line_points_success childIndices
    childPoints parentIndices doublings childExpected output hlengths
    hdoublings hchildren hrun
  refine ⟨hpost.1, ?_⟩
  intro ordinal hordinal
  have hparent : ordinal < parentIndices.val.length := by
    simpa [hpost.1] using hordinal
  rcases hpost.2 ordinal hparent with
    ⟨childOrdinal, hchild, hmapped, hrepresents⟩
  have heq := hcompatible childOrdinal ordinal hchild hparent hmapped
  rw [heq] at hrepresents
  exact hrepresents

structure SourceReleasedPointListsEvidence
    (layer0 line1 line2 line3 : Slice Std.U32)
    (circlePoints line1Points line2Points line3Points : SourcePointVec) :
    Prop where
  circleLength : circlePoints.val.length = layer0.val.length
  line1Length : line1Points.val.length = line1.val.length
  line2Length : line2Points.val.length = line2.val.length
  line3Length : line3Points.val.length = line3.val.length
  circle : ∀ ordinal, ordinal < circlePoints.val.length →
    SourceRepresents circlePoints.val[ordinal]!
      (ReleasedCircleExpected layer0 ordinal)
  line1 : ∀ ordinal, ordinal < line1Points.val.length →
    SourceRepresents line1Points.val[ordinal]!
      (ReleasedLine1Expected line1 ordinal)
  line2 : ∀ ordinal, ordinal < line2Points.val.length →
    SourceRepresents line2Points.val[ordinal]!
      (ReleasedLine2Expected line2 ordinal)
  line3 : ∀ ordinal, ordinal < line3Points.val.length →
    SourceRepresents line3Points.val[ordinal]!
      (ReleasedLine3Expected line3 ordinal)

/-- The four successful point-helper calls in the unchanged production
driver return precisely the released circle and line points, in source order. -/
theorem source_accepted_point_helpers_represent_released
    (layer0 line1 line2 line3 : Slice Std.U32)
    (circlePoints line1Points line2Points line3Points : SourcePointVec)
    (hlayer0 : IndicesBelow layer0 131072)
    (hline1 : IndicesBelow line1 32768)
    (hline2 : IndicesBelow line2 8192)
    (hline3 : IndicesBelow line3 2048)
    (hcircleCall :
      V5CoordinateSelectedProductionSource.circle_fri.selected_circle_fiber_points_shared
          19#u32 layer0 = .ok (.Ok circlePoints))
    (hline1Call :
      V5CoordinateSelectedProductionSource.circle_fri.derive_parent_line_points
          layer0 (alloc.vec.Vec.deref circlePoints) line1 1#u8 =
        .ok (.Ok line1Points))
    (hline2Call :
      V5CoordinateSelectedProductionSource.circle_fri.derive_parent_line_points
          line1 (alloc.vec.Vec.deref line1Points) line2 2#u8 =
        .ok (.Ok line2Points))
    (hline3Call :
      V5CoordinateSelectedProductionSource.circle_fri.derive_parent_line_points
          line2 (alloc.vec.Vec.deref line2Points) line3 2#u8 =
        .ok (.Ok line3Points)) :
    SourceReleasedPointListsEvidence layer0 line1 line2 line3 circlePoints
      line1Points line2Points line3Points := by
  obtain ⟨exactCirclePoints, hexactCircleCall, hcirclePost⟩ :=
    source_selected_circle_fiber_points_shared_domain19_exact layer0 hlayer0
  have hcircleEq : exactCirclePoints = circlePoints := by
    rw [hexactCircleCall] at hcircleCall
    exact core.result.Result.Ok.inj (Result.ok.inj hcircleCall)
  subst exactCirclePoints
  have hcircleReleased :
      ∀ ordinal, ordinal < circlePoints.val.length →
        SourceRepresents circlePoints.val[ordinal]!
          (ReleasedCircleExpected layer0 ordinal) := by
    intro ordinal hordinal
    have hlayerOrdinal : ordinal < layer0.val.length := by
      simpa [hcirclePost.1] using hordinal
    have hmeaning := hcirclePost.2 ordinal hlayerOrdinal
    rw [selectedExpectedPoint_eq_releasedCirclePoint
      layer0.val[ordinal]! (hlayer0 ordinal hlayerOrdinal)] at hmeaning
    exact hmeaning
  have hline1Post := source_parent_success_exact_expected layer0
    (alloc.vec.Vec.deref circlePoints) line1 1#u8
    (ReleasedCircleExpected layer0) (ReleasedLine1Expected line1)
    line1Points hcirclePost.1 (Or.inl rfl) hcircleReleased
    (circle_parent_expected_compatible layer0 line1 hlayer0 hline1)
    hline1Call
  have hline2Post := source_parent_success_exact_expected line1
    (alloc.vec.Vec.deref line1Points) line2 2#u8
    (ReleasedLine1Expected line1) (ReleasedLine2Expected line2)
    line2Points hline1Post.1 (Or.inr rfl) hline1Post.2
    (line1_parent_expected_compatible line1 line2 hline1 hline2)
    hline2Call
  have hline3Post := source_parent_success_exact_expected line2
    (alloc.vec.Vec.deref line2Points) line3 2#u8
    (ReleasedLine2Expected line2) (ReleasedLine3Expected line3)
    line3Points hline2Post.1 (Or.inr rfl) hline2Post.2
    (line2_parent_expected_compatible line2 line3 hline2 hline3)
    hline3Call
  exact {
    circleLength := hcirclePost.1
    line1Length := hline1Post.1
    line2Length := hline2Post.1
    line3Length := hline3Post.1
    circle := hcircleReleased
    line1 := hline1Post.2
    line2 := hline2Post.2
    line3 := hline3Post.2
  }

#print axioms source_double_point_maps_adapter
#print axioms source_remove_rotation_maps_adapter
#print axioms source_parent_point_call_exact
#print axioms source_parent_search_bounded
#print axioms source_parent_points_loop_exact
#print axioms source_derive_parent_line_points_success
#print axioms source_parent_success_exact_expected
#print axioms source_accepted_point_helpers_represent_released

end V5CoordinateProductionFullProof
