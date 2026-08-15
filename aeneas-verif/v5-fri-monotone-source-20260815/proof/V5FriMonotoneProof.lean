import V5FriMonotone.Funs

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V5FriMonotoneProof

open V5FriMonotoneGenerated

private theorem slice_index_run
    {T : Type} [Inhabited T]
    (values : Slice T) (index : Std.Usize)
    (hindex : index.val < values.val.length) :
    Slice.index_usize values index = ok values.val[index.val]! := by
  unfold Slice.index_usize
  rw [Slice.getElem?_Usize_eq]
  simp [hindex]

private theorem wrapping_succ_exact
    {T : Type} (values : Slice T) (index : Std.Usize)
    (hindex : index.val < values.val.length) :
    (Std.Usize.wrapping_add index 1#usize).val = index.val + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  apply Nat.mod_eq_of_lt
  have hlength := Slice.length_ineq values
  change index.val + 1 < UScalar.size .Usize
  rw [UScalar.size_UScalarTyUsize]
  have hsize := Usize.size_scalarTac_eq
  omega

private theorem core_slice_get_run
    {T : Type} [Inhabited T]
    (values : Slice T) (index : Std.Usize)
    (hindex : index.val < values.val.length) :
    core.slice.Slice.get
        (core.slice.index.SliceIndexUsizeSlice T) values index =
      ok (some values.val[index.val]!) := by
  unfold core.slice.Slice.get core.slice.index.SliceIndexUsizeSlice
    core.slice.index.Usize.get
  change ok values.val[index.val]? = ok (some values.val[index.val]!)
  simp [hindex]

/-- The recursive extraction-only spelling of the production monotone scan
stops on the requested entry whenever every earlier entry is smaller. -/
theorem advance_monotone_ordinal_hits
    (indices : Slice Std.U32) (ordinal target : Std.Usize)
    (index : Std.U32)
    (horder : ordinal.val <= target.val)
    (htargetBound : target.val < indices.val.length)
    (hbefore : forall position,
      ordinal.val <= position -> position < target.val ->
        indices.val[position]!.val < index.val)
    (htarget : indices.val[target.val]! = index) :
    V5FriMonotoneGenerated.fri_checks.advance_monotone_ordinal
        indices ordinal index = ok target := by
  rw [V5FriMonotoneGenerated.fri_checks.advance_monotone_ordinal.eq_1]
  have hordBound : ordinal.val < indices.val.length := by omega
  have hactive : ordinal < Slice.len indices := by scalar_tac
  rw [if_pos hactive]
  rw [slice_index_run indices ordinal hordBound]
  simp only [bind_tc_ok]
  by_cases heq : ordinal.val = target.val
  · have hordTarget : ordinal = target := UScalar.eq_of_val_eq heq
    subst target
    have hat : indices.val[ordinal.val]! = index := htarget
    rw [hat]
    have hnotlt : ¬ (index < index) := by exact lt_irrefl _
    rw [if_neg hnotlt]
  · have hstrict : ordinal.val < target.val := by omega
    have hltNat := hbefore ordinal.val (by omega) hstrict
    have hlt : indices.val[ordinal.val]! < index := by scalar_tac
    rw [if_pos hlt]
    simp only [Std.lift, bind_tc_ok]
    let next := Std.Usize.wrapping_add ordinal 1#usize
    have hnextVal : next.val = ordinal.val + 1 :=
      wrapping_succ_exact indices ordinal hordBound
    apply advance_monotone_ordinal_hits indices next target index
    · rw [hnextVal]
      omega
    · exact htargetBound
    · intro position hnextLe hposition
      apply hbefore position
      · rw [hnextVal] at hnextLe
        omega
      · exact hposition
    · exact htarget
termination_by target.val - ordinal.val
decreasing_by
  rw [hnextVal]
  omega

/-- The extracted helper returns the value at exactly the ordinal found by
the monotone scan; it cannot silently substitute a neighboring opening. -/
theorem opening_value_for_monotone_index_hits
    (opening :
      V5FriMonotoneGenerated.aspis_core.state_only_private_openings.StateOnlyPrivateOpening)
    (indices : Slice Std.U32) (ordinal target : Std.Usize)
    (index : Std.U32) (layer : Std.U8) (value : Slice Std.U8)
    (hadvance :
      V5FriMonotoneGenerated.fri_checks.advance_monotone_ordinal
        indices ordinal index = ok target)
    (htargetBound : target.val < indices.val.length)
    (htarget : indices.val[target.val]! = index)
    (hvalue :
      V5FriMonotoneGenerated.aspis_core.state_only_private_openings.StateOnlyPrivateOpening.value
        opening target = ok (some value)) :
    V5FriMonotoneGenerated.fri_checks.opening_value_for_monotone_index
        opening indices ordinal index layer =
      ok (core.result.Result.Ok value, target) := by
  unfold V5FriMonotoneGenerated.fri_checks.opening_value_for_monotone_index
  rw [hadvance]
  simp only [bind_tc_ok]
  rw [core_slice_get_run indices target htargetBound]
  simp only [bind_tc_ok]
  rw [htarget]
  simp [core.option.OptionShared0T.copied,
    core.option.Option.Insts.CoreCmpPartialEqOption.eq,
    core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
    hvalue,
    core.option.Option.ok_or]

#print axioms advance_monotone_ordinal_hits
#print axioms opening_value_for_monotone_index_hits

end V5FriMonotoneProof
