import V5FriConsumerValueAdapter

/-!
# Exact semantics of the production monotone opening lookup

This file proves directly from the unchanged Charon/Aeneas translation that
the mutable parent-opening scan returns the requested sorted index and the
value at that exact ordinal.  It removes the remaining temporary-recursion
boundary between accepted FRI read witnesses and authenticated opening bytes.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 3200000

namespace AspisV5FriConsumerReadSemantics

open V5FriConsumerExact
open AspisV5FriConsumerObservationBridge
open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleConsumedValueBridge
open AspisV5MerkleRustBridge

private theorem slice_index_run
    {T : Type} [Inhabited T]
    (values : Slice T) (index : Std.Usize)
    (hindex : index.val < values.val.length) :
    Slice.index_usize values index = .ok values.val[index.val]! := by
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
      .ok (some values.val[index.val]!) := by
  unfold core.slice.Slice.get core.slice.index.SliceIndexUsizeSlice
    core.slice.index.Usize.get
  change ok values.val[index.val]? = ok (some values.val[index.val]!)
  simp [hindex]

/-- The actual generated `while` loop stops at the requested ordinal whenever
the source list is sorted across the part it scans. -/
theorem production_monotone_loop_hits
    (indices : Slice Std.U32) (ordinal target : Std.Usize)
    (index : Std.U32)
    (horder : ordinal.val ≤ target.val)
    (htargetBound : target.val < indices.val.length)
    (hbefore : ∀ position,
      ordinal.val ≤ position → position < target.val →
        indices.val[position]!.val < index.val)
    (htarget : indices.val[target.val]! = index) :
    fri_checks.opening_value_for_monotone_index_loop indices ordinal index =
      .ok target := by
  unfold fri_checks.opening_value_for_monotone_index_loop
  rw [loop.eq_def]
  unfold fri_checks.opening_value_for_monotone_index_loop.body
  have hordBound : ordinal.val < indices.val.length := by omega
  have hactive : ordinal < Slice.len indices := by scalar_tac
  rw [if_pos hactive]
  rw [slice_index_run indices ordinal hordBound]
  simp only [bind_tc_ok]
  by_cases heq : ordinal.val = target.val
  · have hordTarget : ordinal = target := UScalar.eq_of_val_eq heq
    subst target
    rw [htarget]
    have hnotlt : ¬ index < index := lt_irrefl _
    rw [if_neg hnotlt]
  · have hstrict : ordinal.val < target.val := by omega
    have hltNat := hbefore ordinal.val (by omega) hstrict
    have hlt : indices.val[ordinal.val]! < index := by scalar_tac
    rw [if_pos hlt]
    simp only [Std.lift, bind_tc_ok]
    let next := Std.Usize.wrapping_add ordinal 1#usize
    have hnextVal : next.val = ordinal.val + 1 :=
      wrapping_succ_exact indices ordinal hordBound
    apply production_monotone_loop_hits indices next target index
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

/-- The unchanged production helper returns the value at exactly the ordinal
selected by the proved scan. -/
theorem production_monotone_value_hits
    (opening :
      aspis_core.state_only_private_openings.StateOnlyPrivateOpening)
    (indices : Slice Std.U32) (ordinal target : Std.Usize)
    (index : Std.U32) (layer : Std.U8) (value : Slice Std.U8)
    (hloop :
      fri_checks.opening_value_for_monotone_index_loop indices ordinal index =
        .ok target)
    (htargetBound : target.val < indices.val.length)
    (htarget : indices.val[target.val]! = index)
    (hvalue :
      aspis_core.state_only_private_openings.StateOnlyPrivateOpening.value
        opening target = .ok (some value)) :
    fri_checks.opening_value_for_monotone_index opening indices ordinal index
        layer = .ok (.Ok value, target) := by
  unfold fri_checks.opening_value_for_monotone_index
  rw [hloop]
  simp only [bind_tc_ok]
  rw [core_slice_get_run indices target htargetBound]
  simp only [bind_tc_ok]
  rw [htarget]
  simp [core.option.OptionShared0T.copied,
    core.option.Option.Insts.CoreCmpPartialEqOption.eq,
    core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
    hvalue, core.option.Option.ok_or]

/-- Successful use of the production helper identifies both the exact target
ordinal and the exact opening accessor result.  No second implementation of
the mutable scan is used. -/
theorem accepted_production_monotone_call_hits
    (opening :
      aspis_core.state_only_private_openings.StateOnlyPrivateOpening)
    (indices : Slice Std.U32) (ordinal target resultOrdinal : Std.Usize)
    (index : Std.U32) (layer : Std.U8) (value : Slice Std.U8)
    (horder : ordinal.val ≤ target.val)
    (htargetBound : target.val < indices.val.length)
    (hbefore : ∀ position,
      ordinal.val ≤ position → position < target.val →
        indices.val[position]!.val < index.val)
    (htarget : indices.val[target.val]! = index)
    (hcall :
      fri_checks.opening_value_for_monotone_index opening indices ordinal index
          layer = .ok (.Ok value, resultOrdinal)) :
    resultOrdinal = target ∧
      aspis_core.state_only_private_openings.StateOnlyPrivateOpening.value
        opening target = .ok (some value) := by
  have hloop := production_monotone_loop_hits indices ordinal target index
    horder htargetBound hbefore htarget
  unfold fri_checks.opening_value_for_monotone_index at hcall
  rw [hloop] at hcall
  simp only [bind_tc_ok] at hcall
  rw [core_slice_get_run indices target htargetBound] at hcall
  simp only [bind_tc_ok] at hcall
  rw [htarget] at hcall
  generalize hvalue :
      aspis_core.state_only_private_openings.StateOnlyPrivateOpening.value
        opening target = valueResult at hcall
  cases valueResult with
  | fail error =>
    simp [core.option.OptionShared0T.copied,
      core.option.Option.Insts.CoreCmpPartialEqOption.eq,
      core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
      Bind.bind, Aeneas.Std.bind] at hcall
  | div =>
    simp [core.option.OptionShared0T.copied,
      core.option.Option.Insts.CoreCmpPartialEqOption.eq,
      core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
      Bind.bind, Aeneas.Std.bind] at hcall
  | ok optional =>
    cases optional with
    | none =>
      simp [core.option.OptionShared0T.copied,
        core.option.Option.Insts.CoreCmpPartialEqOption.eq,
        core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
        core.option.Option.ok_or] at hcall
    | some returned =>
      simp [core.option.OptionShared0T.copied,
        core.option.Option.Insts.CoreCmpPartialEqOption.eq,
        core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
        core.option.Option.ok_or] at hcall
      exact ⟨hcall.2.symm, by simpa [hcall.1] using hvalue⟩

/-- Equality with one exact parser section supplies the two flat-record shape
facts required by the extracted opening accessor. -/
theorem generated_opening_shape_of_exact_section
    {sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32}
    {tree : V5PrivateSection} {root : Digest32}
    {queries : Finset V5Query}
    (opening :
      aspis_core.state_only_private_openings.StateOnlyPrivateOpening)
    (trace : ExactSectionTrace sha256 tree root queries)
    (heq : generatedOpeningToReturned opening = openingOfTrace trace) :
    opening.value_width.val + 32 ≤ Std.Usize.max ∧
      opening.records.val.length =
        opening.count.val * (opening.value_width.val + 32) := by
  have hcount := congrArg ReturnedOpening.count heq
  have hwidth := congrArg ReturnedOpening.valueWidth heq
  have hrecords := congrArg (fun output => output.records.length) heq
  simp only [generatedOpeningToReturned, openingOfTrace_count] at hcount
  simp only [generatedOpeningToReturned, openingOfTrace_valueWidth] at hwidth
  simp only [generatedOpeningToReturned, openingOfTrace_records,
    List.length_map] at hrecords
  have hflat : trace.records.flatten.length =
      trace.records.length * (valueWidth tree + 32) := by
    rw [List.length_flatten]
    have hlengths : trace.records.map List.length =
        List.replicate trace.records.length (valueWidth tree + 32) := by
      apply List.eq_replicate_iff.mpr
      constructor
      · simp
      · intro length hlength
        simp only [List.mem_map] at hlength
        obtain ⟨record, hrecord, rfl⟩ := hlength
        exact exactSection_records_uniform_length trace record hrecord
    rw [hlengths, List.sum_replicate]
    simp [Nat.mul_comm]
  constructor
  · rw [hwidth]
    cases tree <;>
      rcases System.Platform.numBits_eq with hbits | hbits <;>
      norm_num [valueWidth, Std.Usize.max, UScalar.max, UScalar.size,
        Std.Usize.size, Std.Usize.numBits, UScalarTy.Usize_numBits_eq,
        hbits]
  · rw [hrecords, hflat, hcount, hwidth]

#print axioms production_monotone_loop_hits
#print axioms production_monotone_value_hits
#print axioms accepted_production_monotone_call_hits
#print axioms generated_opening_shape_of_exact_section

end AspisV5FriConsumerReadSemantics
