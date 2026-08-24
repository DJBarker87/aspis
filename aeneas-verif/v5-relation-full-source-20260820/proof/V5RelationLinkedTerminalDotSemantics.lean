import V5RelationLinkedGroupedLowSemantics

/-!
# Exact semantics of the released terminal main dot

At the end of the four relation rounds the production accumulator has
`log_len = 2` and the final polynomial has four coefficients.  The Rust
implementation therefore evaluates each remaining component directly rather
than calling the deliberately opaque generic `weight_at` fallback.

This file first proves the exact maintained-field meaning of the two small
loops used by the direct path: an ordinary four-entry dense dot and the
four-entry deferred-group dot.  Later sections lift those loop facts through
the component iterator and the public `WeightAccumulator.dot` call.
-/

namespace AspisV5RelationLinkedTerminalDotSemantics

open Aeneas Aeneas.Std Result ControlFlow Error
open AspisV5RelationLinkedFieldProjection
open AspisV5RelationLinkedGroupedLowSemantics

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

abbrev RawQM31 := V5RelationLinkedGenerated.aspis_core.field.QM31
abbrev ExactQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

deriving instance Inhabited for V5RelationLinkedGenerated.aspis_core.field.CM31
deriving instance Inhabited for V5RelationLinkedGenerated.aspis_core.field.QM31

def CanonicalList (values : List RawQM31) : Prop :=
  ∀ index, index < values.length → CanonicalQM31 values[index]!

private theorem zeroCanonical :
    CanonicalQM31 V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO := by
  norm_num [CanonicalQM31, CanonicalCM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO,
    AspisAeneasCM31Multiplicative.m31Modulus]

private theorem sliceIndexRun
    (values : Slice RawQM31) (index : Std.Usize)
    (hindex : index.val < values.val.length) :
    Slice.index_usize values index = ok values.val[index.val]! := by
  unfold Slice.index_usize
  rw [Slice.getElem?_Usize_eq]
  simp [hindex]

private theorem vecIndexRun
    {T : Type} [Inhabited T] (values : alloc.vec.Vec T)
    (index : Std.Usize) (hindex : index.val < values.val.length) :
    alloc.vec.Vec.index
        (core.slice.index.SliceIndexUsizeSlice T) values index =
      ok values.val[index.val]! := by
  rw [alloc.vec.Vec.index_slice_index]
  obtain ⟨value, run, valueEq⟩ := Aeneas.Std.WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec values index hindex)
  have exactGet : values.val[index.val] = values.val[index.val]! := by
    symm
    apply List.getElem!_of_getElem?
    simp [hindex]
  simpa [valueEq, exactGet] using run

private theorem wrappingSuccExact
    (values : Slice RawQM31) (index : Std.Usize)
    (hindex : index.val < values.val.length) :
    (Std.Usize.wrapping_add index 1#usize).val = index.val + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  apply Nat.mod_eq_of_lt
  have hlength := Slice.length_ineq values
  change index.val + 1 < UScalar.size .Usize
  rw [UScalar.size_UScalarTyUsize]
  have hsize := Usize.size_scalarTac_eq
  omega

private theorem exactSliceEntryEq
    (values : Slice RawQM31) (index : Nat)
    (hindex : index < values.val.length) :
    toMaintainedExact values.val[index]! =
      toMaintainedExact values.val[index] := by
  congr 1
  apply List.getElem!_of_getElem?
  simp [hindex]

private theorem exactVecEntryEq
    (values : alloc.vec.Vec RawQM31) (index : Nat)
    (hindex : index < values.val.length) :
    toMaintainedExact values.val[index]! =
      toMaintainedExact values.val[index] := by
  congr 1
  apply List.getElem!_of_getElem?
  simp [hindex]

/-- Exact source semantics of the dense component loop.  The theorem is
stated from an arbitrary in-bounds cursor because the iterator proof reuses
it without unrolling four copies of the source body. -/
theorem denseDotLoopExact
    (values : Slice RawQM31) (weights : alloc.vec.Vec RawQM31)
    (hlen : values.val.length = weights.val.length)
    (hbound : values.val.length ≤ 4)
    (hvalues : CanonicalList values.val)
    (hweights : CanonicalList weights.val)
    (sum : RawQM31) (hsum : CanonicalQM31 sum)
    (index : Std.Usize) (hindex : index.val ≤ values.val.length) :
    ∃ out,
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0_loop0
          values weights sum index = ok out ∧
      CanonicalQM31 out ∧
      toMaintainedExact out = toMaintainedExact sum +
        ∑ row ∈ Finset.Ico index.val values.val.length,
          toMaintainedExact values.val[row]! *
            toMaintainedExact weights.val[row]! := by
  unfold
    V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0_loop0
  by_cases more : index.val < values.val.length
  · have moreScalar : index < Slice.len values := by scalar_tac
    have valueRead := sliceIndexRun values index more
    have weightBound : index.val < weights.val.length := by omega
    have weightRead := vecIndexRun weights index weightBound
    let value := values.val[index.val]!
    let weight := weights.val[index.val]!
    have valueCanonical : CanonicalQM31 value := hvalues index.val more
    have weightCanonical : CanonicalQM31 weight :=
      hweights index.val weightBound
    obtain ⟨product, productRun, productCanonical, _⟩ :=
      generated_qm31_mul_corresponds value weight valueCanonical weightCanonical
    have productExact := (mul_run_corresponds
      value weight product valueCanonical weightCanonical productRun).2
    obtain ⟨nextSum, nextSumRun, nextSumCanonical, _⟩ :=
      generated_qm31_add_corresponds sum product hsum productCanonical
    have nextSumExact := (add_run_corresponds sum product nextSum hsum
      productCanonical nextSumRun).2
    let nextIndex := Std.Usize.wrapping_add index 1#usize
    have nextIndexValue : nextIndex.val = index.val + 1 := by
      exact wrappingSuccExact values index more
    have nextBound : nextIndex.val ≤ values.val.length := by omega
    have bodyRun :
        V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0_loop0.body
            values weights sum index = ok (cont (nextSum, nextIndex)) := by
      unfold
        V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0_loop0.body
      rw [if_pos moreScalar, valueRead, weightRead]
      simp only [bind_tc_ok]
      have productRunRaw :
          V5RelationLinkedGenerated.aspis_core.field.QM31.mul
              values.val[index.val]! weights.val[index.val]! = ok product := by
        simpa [value, weight] using productRun
      rw [productRunRaw]
      simp only [bind_tc_ok]
      rw [nextSumRun]
      rfl
    rw [loop.eq_1]
    simp only [Prod.fst, Prod.snd]
    rw [bodyRun]
    simp only [bind_tc_ok]
    obtain ⟨out, loopRun, outCanonical, outExact⟩ :=
      denseDotLoopExact values weights hlen hbound hvalues hweights nextSum
        nextSumCanonical nextIndex nextBound
    have loopRun' :
        loop
            (fun state =>
              V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0_loop0.body
                values weights state.1 state.2)
            (nextSum, nextIndex) = ok out := by
      simpa only [
        V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0_loop0]
        using loopRun
    rw [loopRun']
    refine ⟨out, rfl, outCanonical, ?_⟩
    rw [outExact, nextSumExact, productExact, nextIndexValue]
    let summand := fun row : Nat =>
      toMaintainedExact values.val[row]! *
        toMaintainedExact weights.val[row]!
    have split := Finset.sum_Ico_consecutive summand
      (Nat.le_succ index.val)
      (show index.val + 1 ≤ values.val.length by omega)
    have singleton :
        ∑ row ∈ Finset.Ico index.val (index.val + 1), summand row =
          summand index.val := by
      rw [Finset.sum_Ico_succ_top (Nat.le_refl index.val)]
      simp
    rw [← split, singleton]
    dsimp only [summand, value, weight] at productExact ⊢
    simp only [Nat.succ_eq_add_one] at *
    ring
  · have doneIndex : index.val = values.val.length := by omega
    have doneScalar : ¬ index < Slice.len values := by scalar_tac
    have bodyRun :
        V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0_loop0.body
            values weights sum index = ok (ControlFlow.done sum) := by
      simp [
        V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0_loop0.body,
        doneScalar]
    rw [loop.eq_1]
    simp only [Prod.fst, Prod.snd]
    rw [bodyRun]
    refine ⟨sum, rfl, hsum, ?_⟩
    simp [doneIndex]
termination_by values.val.length - index.val
decreasing_by
  rw [nextIndexValue]
  omega

/-- Exact source semantics of the released deferred-group terminal loop. -/
theorem groupedDotLoopExact
    (values : Slice RawQM31) (rowGroups : alloc.vec.Vec Std.U8)
    (groupValues : alloc.vec.Vec RawQM31)
    (hrows : values.val.length = rowGroups.val.length)
    (hbound : values.val.length ≤ 4)
    (hvalues : CanonicalList values.val)
    (hgroups : CanonicalList groupValues.val)
    (hrouting : ∀ row, row < rowGroups.val.length →
      (rowGroups.val[row]!).val < groupValues.val.length)
    (sum : RawQM31) (hsum : CanonicalQM31 sum)
    (index : Std.Usize) (hindex : index.val ≤ values.val.length) :
    ∃ out,
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0_loop1
          values rowGroups groupValues sum index = ok out ∧
      CanonicalQM31 out ∧
      toMaintainedExact out = toMaintainedExact sum +
        ∑ row ∈ Finset.Ico index.val values.val.length,
          toMaintainedExact values.val[row]! *
            toMaintainedExact
              groupValues.val[(rowGroups.val[row]!).val]! := by
  unfold
    V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0_loop1
  by_cases more : index.val < values.val.length
  · have moreScalar : index < Slice.len values := by scalar_tac
    have valueRead := sliceIndexRun values index more
    have rowBound : index.val < rowGroups.val.length := by omega
    have rowRead := vecIndexRun rowGroups index rowBound
    let group := rowGroups.val[index.val]!
    have groupBound : group.val < groupValues.val.length := by
      exact hrouting index.val rowBound
    let groupIndex := core.convert.num.FromUsizeU8.from group
    have groupIndexVal : groupIndex.val = group.val := by
      unfold groupIndex
      rw [core.convert.num.FromUsizeU8.from_val_eq]
    have castExact : core.convert.num.FromUsizeU8.from group = groupIndex := by
      rfl
    have groupValueRead := vecIndexRun groupValues groupIndex (by
      rw [groupIndexVal]
      exact groupBound)
    let value := values.val[index.val]!
    let groupValue := groupValues.val[groupIndex.val]!
    have valueCanonical : CanonicalQM31 value := hvalues index.val more
    have groupIndexBound : groupIndex.val < groupValues.val.length := by
      simpa [groupIndexVal] using groupBound
    have groupCanonical : CanonicalQM31 groupValue :=
      hgroups groupIndex.val groupIndexBound
    obtain ⟨product, productRun, productCanonical, _⟩ :=
      generated_qm31_mul_corresponds value groupValue valueCanonical
        groupCanonical
    have productExact := (mul_run_corresponds value groupValue product
      valueCanonical groupCanonical productRun).2
    obtain ⟨nextSum, nextSumRun, nextSumCanonical, _⟩ :=
      generated_qm31_add_corresponds sum product hsum productCanonical
    have nextSumExact := (add_run_corresponds sum product nextSum hsum
      productCanonical nextSumRun).2
    let nextIndex := Std.Usize.wrapping_add index 1#usize
    have nextIndexValue : nextIndex.val = index.val + 1 := by
      exact wrappingSuccExact values index more
    have nextBound : nextIndex.val ≤ values.val.length := by omega
    have bodyRun :
        V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0_loop1.body
            values rowGroups groupValues sum index =
          ok (cont (nextSum, nextIndex)) := by
      unfold
        V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0_loop1.body
      rw [if_pos moreScalar, valueRead, rowRead]
      simp only [bind_tc_ok, Aeneas.Std.lift]
      rw [castExact, groupValueRead]
      simp only [bind_tc_ok]
      have productRunRaw :
          V5RelationLinkedGenerated.aspis_core.field.QM31.mul
              values.val[index.val]! groupValues.val[groupIndex.val]! =
            ok product := by
        simpa [value, groupValue] using productRun
      rw [productRunRaw]
      simp only [bind_tc_ok]
      rw [nextSumRun]
      rfl
    rw [loop.eq_1]
    simp only [Prod.fst, Prod.snd]
    rw [bodyRun]
    simp only [bind_tc_ok]
    obtain ⟨out, loopRun, outCanonical, outExact⟩ :=
      groupedDotLoopExact values rowGroups groupValues hrows hbound hvalues
        hgroups hrouting nextSum nextSumCanonical nextIndex nextBound
    have loopRun' :
        loop
            (fun state =>
              V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0_loop1.body
                values rowGroups groupValues state.1 state.2)
            (nextSum, nextIndex) = ok out := by
      simpa only [
        V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0_loop1]
        using loopRun
    rw [loopRun']
    refine ⟨out, rfl, outCanonical, ?_⟩
    rw [outExact, nextSumExact, productExact, nextIndexValue]
    let summand := fun row : Nat =>
      toMaintainedExact values.val[row]! *
        toMaintainedExact groupValues.val[(rowGroups.val[row]!).val]!
    have split := Finset.sum_Ico_consecutive summand
      (Nat.le_succ index.val)
      (show index.val + 1 ≤ values.val.length by omega)
    have singleton :
        ∑ row ∈ Finset.Ico index.val (index.val + 1), summand row =
          summand index.val := by
      rw [Finset.sum_Ico_succ_top (Nat.le_refl index.val)]
      simp
    rw [← split, singleton]
    dsimp only [summand, value, groupValue] at productExact ⊢
    simp only [groupIndexVal, Nat.succ_eq_add_one] at *
    ring
  · have doneIndex : index.val = values.val.length := by omega
    have doneScalar : ¬ index < Slice.len values := by scalar_tac
    have bodyRun :
        V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0_loop1.body
            values rowGroups groupValues sum index =
          ok (ControlFlow.done sum) := by
      simp [
        V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0_loop1.body,
        doneScalar]
    rw [loop.eq_1]
    simp only [Prod.fst, Prod.snd]
    rw [bodyRun]
    refine ⟨sum, rfl, hsum, ?_⟩
    simp [doneIndex]
termination_by values.val.length - index.val
decreasing_by
  rw [nextIndexValue]
  omega

#print axioms denseDotLoopExact
#print axioms groupedDotLoopExact

end AspisV5RelationLinkedTerminalDotSemantics
