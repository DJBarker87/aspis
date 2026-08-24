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
deriving instance Inhabited for
  V5RelationLinkedGenerated.aspis_core.sumcheck.WeightComponent

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

private theorem usizeZeroVal : (0#usize).val = 0 := by
  norm_num

private theorem maintainedZeroExact :
    toMaintainedExact
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO = 0 := by
  exact zero_toMaintained

private theorem sumIcoFour (summand : Nat → ExactQM31) :
    ∑ row ∈ Finset.Ico 0 4, summand row =
      summand 0 + summand 1 + summand 2 + summand 3 := by
  norm_num [Finset.sum_Ico_succ_top, Finset.sum_range_succ]

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

/-! ## Direct component meaning -/

abbrev Component :=
  V5RelationLinkedGenerated.aspis_core.sumcheck.WeightComponent

/-- Exact four-entry covector denoted by one supported terminal component.
The two unsupported grouped encodings and the release-unreachable geometric
and product encodings are assigned zero; `ReleasedTerminalComponent` below
excludes them from every theorem. -/
def terminalComponentWeights (component : Component) : Fin 4 → ExactQM31 :=
  match component with
  | .Multilinear scale point =>
      let s := toMaintainedExact scale
      let high := toMaintainedExact point.val[0]!
      let low := toMaintainedExact point.val[1]!
      ![s * (1 - high) * (1 - low),
        s * (1 - high) * low,
        s * high * (1 - low),
        s * high * low]
  | .Tensor scale factors =>
      let s := toMaintainedExact scale
      let high := toMaintainedExact factors.val[0]!
      let low := toMaintainedExact factors.val[1]!
      ![s, s * low, s * high, s * high * low]
  | .Dense weights => fun index => toMaintainedExact weights.val[index.val]!
  | .Grouped64x16BinaryDeferred rowGroups _ _ groupValues =>
      fun index =>
        toMaintainedExact
          groupValues.val[(rowGroups.val[index.val]!).val]!
  | _ => fun _ => 0

def terminalValues (values : Slice RawQM31) : Fin 4 → ExactQM31 :=
  fun index => toMaintainedExact values.val[index.val]!

def terminalComponentContribution
    (component : Component) (values : Slice RawQM31) : ExactQM31 :=
  AspisV5FriRelationCandidateBridge.candidateClaim
    (terminalComponentWeights component) (terminalValues values)

/-- Exactly the component shapes reachable after four successful folds in the
released verifier, together with the length/canonicality facts needed to give
their raw field values an exact mathematical meaning. -/
def ReleasedTerminalComponent : Component → Prop
  | .Multilinear scale point =>
      CanonicalQM31 scale ∧ point.val.length = 2 ∧ CanonicalList point.val
  | .Tensor scale factors =>
      CanonicalQM31 scale ∧ factors.val.length = 2 ∧ CanonicalList factors.val
  | .Dense weights => weights.val.length = 4 ∧ CanonicalList weights.val
  | .Grouped64x16BinaryDeferred rowGroups _ _ groupValues =>
      rowGroups.val.length = 4 ∧ CanonicalList groupValues.val ∧
        (∀ row, row < 4 →
          (rowGroups.val[row]!).val < groupValues.val.length)
  | _ => False

private theorem addExistsExact
    (left right : RawQM31)
    (hleft : CanonicalQM31 left) (hright : CanonicalQM31 right) :
    ∃ out,
      V5RelationLinkedGenerated.aspis_core.field.QM31.add left right = ok out ∧
      CanonicalQM31 out ∧
      toMaintainedExact out =
        toMaintainedExact left + toMaintainedExact right := by
  obtain ⟨out, run, canonical, _⟩ :=
    generated_qm31_add_corresponds left right hleft hright
  exact ⟨out, run, canonical,
    (add_run_corresponds left right out hleft hright run).2⟩

private theorem subExistsExact
    (left right : RawQM31)
    (hleft : CanonicalQM31 left) (hright : CanonicalQM31 right) :
    ∃ out,
      V5RelationLinkedGenerated.aspis_core.field.QM31.sub left right = ok out ∧
      CanonicalQM31 out ∧
      toMaintainedExact out =
        toMaintainedExact left - toMaintainedExact right := by
  obtain ⟨out, run, canonical, _⟩ :=
    generated_qm31_sub_corresponds left right hleft hright
  exact ⟨out, run, canonical,
    (sub_run_corresponds left right out hleft hright run).2⟩

private theorem mulExistsExact
    (left right : RawQM31)
    (hleft : CanonicalQM31 left) (hright : CanonicalQM31 right) :
    ∃ out,
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul left right = ok out ∧
      CanonicalQM31 out ∧
      toMaintainedExact out =
        toMaintainedExact left * toMaintainedExact right := by
  obtain ⟨out, run, canonical, _⟩ :=
    generated_qm31_mul_corresponds left right hleft hright
  exact ⟨out, run, canonical,
    (mul_run_corresponds left right out hleft hright run).2⟩

private theorem squareExistsExact
    (value : RawQM31) (hvalue : CanonicalQM31 value) :
    ∃ out,
      V5RelationLinkedGenerated.aspis_core.field.QM31.square value = ok out ∧
      CanonicalQM31 out ∧
      toMaintainedExact out = toMaintainedExact value ^ 2 := by
  obtain ⟨out, run, canonical, _⟩ :=
    generated_qm31_square_corresponds value hvalue
  exact ⟨out, run, canonical,
    (square_run_corresponds value out hvalue run).2⟩

private theorem terminalRead
    (values : Slice RawQM31) (hlen : values.val.length = 4)
    (index : Std.Usize) (hindex : index.val < 4) :
    Slice.index_usize values index =
      ok values.val[index.val]! := by
  apply sliceIndexRun
  omega

private theorem terminalVecRead
    (values : alloc.vec.Vec RawQM31) (hlen : values.val.length = 2)
    (index : Std.Usize) (hindex : index.val < 2) :
    alloc.vec.Vec.index
        (core.slice.index.SliceIndexUsizeSlice RawQM31) values
        index = ok values.val[index.val]! := by
  apply vecIndexRun
  omega

/-- The direct multilinear branch computes the dot product with its exact
four multilinear basis weights. -/
private theorem multilinearBodyExact
    (iter nextIter : core.slice.iter.Iter Component)
    (values : Slice RawQM31) (total : RawQM31)
    (scale : RawQM31) (point : alloc.vec.Vec RawQM31)
    (nextRun : core.slice.iter.IteratorSliceIter.next iter =
      ok (some (.Multilinear scale point), nextIter))
    (hlen : values.val.length = 4)
    (hvalues : CanonicalList values.val)
    (htotal : CanonicalQM31 total)
    (hcomponent : ReleasedTerminalComponent (.Multilinear scale point)) :
    ∃ nextTotal,
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0.body
          values iter total = ok (cont (nextIter, nextTotal)) ∧
      CanonicalQM31 nextTotal ∧
      toMaintainedExact nextTotal = toMaintainedExact total +
        terminalComponentContribution (.Multilinear scale point) values := by
  rcases hcomponent with ⟨hscale, hpointLength, hpoint⟩
  have read0 := terminalRead values hlen 0#usize (by decide)
  have read1 := terminalRead values hlen 1#usize (by decide)
  have read2 := terminalRead values hlen 2#usize (by decide)
  have read3 := terminalRead values hlen 3#usize (by decide)
  have point0Read := terminalVecRead point hpointLength 0#usize (by decide)
  have point1Read := terminalVecRead point hpointLength 1#usize (by decide)
  let v0 := values.val[0]!
  let v1 := values.val[1]!
  let v2 := values.val[2]!
  let v3 := values.val[3]!
  let p0 := point.val[0]!
  let p1 := point.val[1]!
  have hv0 : CanonicalQM31 v0 := hvalues 0 (by omega)
  have hv1 : CanonicalQM31 v1 := hvalues 1 (by omega)
  have hv2 : CanonicalQM31 v2 := hvalues 2 (by omega)
  have hv3 : CanonicalQM31 v3 := hvalues 3 (by omega)
  have hp0 : CanonicalQM31 p0 := hpoint 0 (by omega)
  have hp1 : CanonicalQM31 p1 := hpoint 1 (by omega)
  obtain ⟨lowDelta, lowDeltaRun, hLowDelta, eLowDelta⟩ :=
    subExistsExact v1 v0 hv1 hv0
  obtain ⟨lowTerm, lowTermRun, hLowTerm, eLowTerm⟩ :=
    mulExistsExact p1 lowDelta hp1 hLowDelta
  obtain ⟨low, lowRun, hLow, eLow⟩ :=
    addExistsExact v0 lowTerm hv0 hLowTerm
  obtain ⟨highDelta, highDeltaRun, hHighDelta, eHighDelta⟩ :=
    subExistsExact v3 v2 hv3 hv2
  obtain ⟨highTerm, highTermRun, hHighTerm, eHighTerm⟩ :=
    mulExistsExact p1 highDelta hp1 hHighDelta
  obtain ⟨high, highRun, hHigh, eHigh⟩ :=
    addExistsExact v2 highTerm hv2 hHighTerm
  obtain ⟨outerDelta, outerDeltaRun, hOuterDelta, eOuterDelta⟩ :=
    subExistsExact high low hHigh hLow
  obtain ⟨outerTerm, outerTermRun, hOuterTerm, eOuterTerm⟩ :=
    mulExistsExact p0 outerDelta hp0 hOuterDelta
  obtain ⟨evaluation, evaluationRun, hEvaluation, eEvaluation⟩ :=
    addExistsExact low outerTerm hLow hOuterTerm
  obtain ⟨contribution, contributionRun, hContribution, eContribution⟩ :=
    mulExistsExact scale evaluation hscale hEvaluation
  obtain ⟨nextTotal, nextTotalRun, hNextTotal, eNextTotal⟩ :=
    addExistsExact total contribution htotal hContribution
  have lowDeltaRunWire :
      V5RelationLinkedGenerated.aspis_core.field.QM31.sub
        values.val[(1#usize).val]! values.val[(0#usize).val]! = ok lowDelta := by
    simpa [v0, v1] using lowDeltaRun
  have lowTermRunWire :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
        point.val[(1#usize).val]! lowDelta = ok lowTerm := by
    simpa [p1] using lowTermRun
  have lowRunWire :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
        values.val[(0#usize).val]! lowTerm = ok low := by
    simpa [v0] using lowRun
  have highDeltaRunWire :
      V5RelationLinkedGenerated.aspis_core.field.QM31.sub
        values.val[(3#usize).val]! values.val[(2#usize).val]! = ok highDelta := by
    simpa [v2, v3] using highDeltaRun
  have highTermRunWire :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
        point.val[(1#usize).val]! highDelta = ok highTerm := by
    simpa [p1] using highTermRun
  have highRunWire :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
        values.val[(2#usize).val]! highTerm = ok high := by
    simpa [v2] using highRun
  have outerTermRunWire :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
        point.val[(0#usize).val]! outerDelta = ok outerTerm := by
    simpa [p0] using outerTermRun
  refine ⟨nextTotal, ?_, hNextTotal, ?_⟩
  · unfold
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0.body
    rw [nextRun]
    simp only [bind_tc_ok]
    rw [read0, point1Read, read1]
    simp only [bind_tc_ok]
    rw [lowDeltaRunWire]
    simp only [bind_tc_ok]
    rw [lowTermRunWire]
    simp only [bind_tc_ok]
    rw [lowRunWire]
    simp only [bind_tc_ok]
    rw [read2, read3]
    simp only [bind_tc_ok]
    rw [highDeltaRunWire]
    simp only [bind_tc_ok]
    rw [highTermRunWire]
    simp only [bind_tc_ok]
    rw [highRunWire, point0Read]
    simp only [bind_tc_ok]
    rw [outerDeltaRun]
    simp only [bind_tc_ok]
    rw [outerTermRunWire]
    simp only [bind_tc_ok]
    rw [evaluationRun]
    simp only [bind_tc_ok]
    rw [contributionRun]
    simp only [bind_tc_ok]
    rw [nextTotalRun]
    rfl
  · rw [eNextTotal, eContribution, eEvaluation, eOuterTerm, eOuterDelta,
      eHigh, eHighTerm, eHighDelta, eLow, eLowTerm, eLowDelta]
    simp [terminalComponentContribution, terminalComponentWeights,
      terminalValues, AspisV5FriRelationCandidateBridge.candidateClaim,
      Fin.sum_univ_four, v0, v1, v2, v3, p0, p1]
    ring

/-- The direct tensor branch computes the dot product with `[1, low, high,
high*low]`, scaled by the component scale. -/
private theorem tensorBodyExact
    (iter nextIter : core.slice.iter.Iter Component)
    (values : Slice RawQM31) (total : RawQM31)
    (scale : RawQM31) (factors : alloc.vec.Vec RawQM31)
    (nextRun : core.slice.iter.IteratorSliceIter.next iter =
      ok (some (.Tensor scale factors), nextIter))
    (hlen : values.val.length = 4)
    (hvalues : CanonicalList values.val)
    (htotal : CanonicalQM31 total)
    (hcomponent : ReleasedTerminalComponent (.Tensor scale factors)) :
    ∃ nextTotal,
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0.body
          values iter total = ok (cont (nextIter, nextTotal)) ∧
      CanonicalQM31 nextTotal ∧
      toMaintainedExact nextTotal = toMaintainedExact total +
        terminalComponentContribution (.Tensor scale factors) values := by
  rcases hcomponent with ⟨hscale, hfactorsLength, hfactors⟩
  have read0 := terminalRead values hlen 0#usize (by decide)
  have read1 := terminalRead values hlen 1#usize (by decide)
  have read2 := terminalRead values hlen 2#usize (by decide)
  have read3 := terminalRead values hlen 3#usize (by decide)
  have factor0Read := terminalVecRead factors hfactorsLength 0#usize (by decide)
  have factor1Read := terminalVecRead factors hfactorsLength 1#usize (by decide)
  let v0 := values.val[0]!
  let v1 := values.val[1]!
  let v2 := values.val[2]!
  let v3 := values.val[3]!
  let f0 := factors.val[0]!
  let f1 := factors.val[1]!
  have hv0 : CanonicalQM31 v0 := hvalues 0 (by omega)
  have hv1 : CanonicalQM31 v1 := hvalues 1 (by omega)
  have hv2 : CanonicalQM31 v2 := hvalues 2 (by omega)
  have hv3 : CanonicalQM31 v3 := hvalues 3 (by omega)
  have hf0 : CanonicalQM31 f0 := hfactors 0 (by omega)
  have hf1 : CanonicalQM31 f1 := hfactors 1 (by omega)
  obtain ⟨lowTerm, lowTermRun, hLowTerm, eLowTerm⟩ :=
    mulExistsExact f1 v1 hf1 hv1
  obtain ⟨low, lowRun, hLow, eLow⟩ :=
    addExistsExact v0 lowTerm hv0 hLowTerm
  obtain ⟨highTerm, highTermRun, hHighTerm, eHighTerm⟩ :=
    mulExistsExact f1 v3 hf1 hv3
  obtain ⟨high, highRun, hHigh, eHigh⟩ :=
    addExistsExact v2 highTerm hv2 hHighTerm
  obtain ⟨outerTerm, outerTermRun, hOuterTerm, eOuterTerm⟩ :=
    mulExistsExact f0 high hf0 hHigh
  obtain ⟨evaluation, evaluationRun, hEvaluation, eEvaluation⟩ :=
    addExistsExact low outerTerm hLow hOuterTerm
  obtain ⟨contribution, contributionRun, hContribution, eContribution⟩ :=
    mulExistsExact scale evaluation hscale hEvaluation
  obtain ⟨nextTotal, nextTotalRun, hNextTotal, eNextTotal⟩ :=
    addExistsExact total contribution htotal hContribution
  have lowTermRunWire :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
        factors.val[(1#usize).val]! values.val[(1#usize).val]! = ok lowTerm := by
    simpa [f1, v1] using lowTermRun
  have lowRunWire :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
        values.val[(0#usize).val]! lowTerm = ok low := by
    simpa [v0] using lowRun
  have highTermRunWire :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
        factors.val[(1#usize).val]! values.val[(3#usize).val]! = ok highTerm := by
    simpa [f1, v3] using highTermRun
  have highRunWire :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
        values.val[(2#usize).val]! highTerm = ok high := by
    simpa [v2] using highRun
  have outerTermRunWire :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
        factors.val[(0#usize).val]! high = ok outerTerm := by
    simpa [f0] using outerTermRun
  refine ⟨nextTotal, ?_, hNextTotal, ?_⟩
  · unfold
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0.body
    rw [nextRun]
    simp only [bind_tc_ok]
    rw [read0, factor1Read, read1]
    simp only [bind_tc_ok]
    rw [lowTermRunWire]
    simp only [bind_tc_ok]
    rw [lowRunWire]
    simp only [bind_tc_ok]
    rw [read2, read3]
    simp only [bind_tc_ok]
    rw [highTermRunWire]
    simp only [bind_tc_ok]
    rw [highRunWire, factor0Read]
    simp only [bind_tc_ok]
    rw [outerTermRunWire]
    simp only [bind_tc_ok]
    rw [evaluationRun]
    simp only [bind_tc_ok]
    rw [contributionRun]
    simp only [bind_tc_ok]
    rw [nextTotalRun]
    rfl
  · rw [eNextTotal, eContribution, eEvaluation, eOuterTerm, eHigh,
      eHighTerm, eLow, eLowTerm]
    simp [terminalComponentContribution, terminalComponentWeights,
      terminalValues, AspisV5FriRelationCandidateBridge.candidateClaim,
      Fin.sum_univ_four, v0, v1, v2, v3, f0, f1]
    ring

/-- The direct dense branch adds precisely the four-entry dense
contribution. -/
private theorem denseBodyExact
    (iter nextIter : core.slice.iter.Iter Component)
    (values : Slice RawQM31) (total : RawQM31)
    (weights : alloc.vec.Vec RawQM31)
    (nextRun : core.slice.iter.IteratorSliceIter.next iter =
      ok (some (.Dense weights), nextIter))
    (hlen : values.val.length = 4)
    (hvalues : CanonicalList values.val)
    (htotal : CanonicalQM31 total)
    (hcomponent : ReleasedTerminalComponent (.Dense weights)) :
    ∃ nextTotal,
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0.body
          values iter total = ok (cont (nextIter, nextTotal)) ∧
      CanonicalQM31 nextTotal ∧
      toMaintainedExact nextTotal = toMaintainedExact total +
        terminalComponentContribution (.Dense weights) values := by
  rcases hcomponent with ⟨hweightsLength, hweights⟩
  obtain ⟨contribution, contributionRun, hContribution, eContribution⟩ :=
    denseDotLoopExact values weights (by omega) (by omega) hvalues hweights
      V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO zeroCanonical
      0#usize (by norm_num)
  obtain ⟨nextTotal, nextTotalRun, hNextTotal, eNextTotal⟩ :=
    addExistsExact total contribution htotal hContribution
  refine ⟨nextTotal, ?_, hNextTotal, ?_⟩
  · unfold
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0.body
    rw [nextRun]
    simp only [bind_tc_ok]
    rw [contributionRun]
    simp only [bind_tc_ok]
    rw [nextTotalRun]
    simp only [bind_tc_ok]
  · rw [eNextTotal, eContribution]
    rw [usizeZeroVal, hlen, sumIcoFour, maintainedZeroExact]
    simp only [terminalComponentContribution, terminalComponentWeights,
      terminalValues, AspisV5FriRelationCandidateBridge.candidateClaim,
      Fin.sum_univ_four]
    norm_num

/-- The direct deferred-group branch adds precisely the four routed group
values. -/
private theorem groupedBodyExact
    (iter nextIter : core.slice.iter.Iter Component)
    (values : Slice RawQM31) (total : RawQM31)
    (rowGroups : alloc.vec.Vec Std.U8)
    (groupIds : alloc.vec.Vec Std.U16) (maybeGroup : Option RawQM31)
    (groupValues : alloc.vec.Vec RawQM31)
    (nextRun : core.slice.iter.IteratorSliceIter.next iter =
      ok (some (.Grouped64x16BinaryDeferred rowGroups groupIds maybeGroup
        groupValues), nextIter))
    (hlen : values.val.length = 4)
    (hvalues : CanonicalList values.val)
    (htotal : CanonicalQM31 total)
    (hcomponent : ReleasedTerminalComponent
      (.Grouped64x16BinaryDeferred rowGroups groupIds maybeGroup
        groupValues)) :
    ∃ nextTotal,
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0.body
          values iter total = ok (cont (nextIter, nextTotal)) ∧
      CanonicalQM31 nextTotal ∧
      toMaintainedExact nextTotal = toMaintainedExact total +
        terminalComponentContribution
          (.Grouped64x16BinaryDeferred rowGroups groupIds maybeGroup
            groupValues) values := by
  rcases hcomponent with ⟨hrowsLength, hgroups, hrouting⟩
  have routing : ∀ row, row < rowGroups.val.length →
      (rowGroups.val[row]!).val < groupValues.val.length := by
    intro row rowBound
    apply hrouting row
    omega
  obtain ⟨contribution, contributionRun, hContribution, eContribution⟩ :=
    groupedDotLoopExact values rowGroups groupValues (by omega) (by omega)
      hvalues hgroups routing
      V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO zeroCanonical
      0#usize (by norm_num)
  obtain ⟨nextTotal, nextTotalRun, hNextTotal, eNextTotal⟩ :=
    addExistsExact total contribution htotal hContribution
  refine ⟨nextTotal, ?_, hNextTotal, ?_⟩
  · unfold
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0.body
    rw [nextRun]
    simp only [bind_tc_ok]
    rw [contributionRun]
    simp only [bind_tc_ok]
    rw [nextTotalRun]
    simp only [bind_tc_ok]
  · rw [eNextTotal, eContribution]
    rw [usizeZeroVal, hlen, sumIcoFour, maintainedZeroExact]
    simp only [terminalComponentContribution, terminalComponentWeights,
      terminalValues, AspisV5FriRelationCandidateBridge.candidateClaim,
      Fin.sum_univ_four]
    norm_num

/-- One released terminal component advances the extracted component iterator
and adds exactly its mathematical four-entry dot contribution. -/
theorem releasedComponentBodyExact
    (iter nextIter : core.slice.iter.Iter Component)
    (values : Slice RawQM31) (total : RawQM31) (component : Component)
    (nextRun : core.slice.iter.IteratorSliceIter.next iter =
      ok (some component, nextIter))
    (hlen : values.val.length = 4)
    (hvalues : CanonicalList values.val)
    (htotal : CanonicalQM31 total)
    (hcomponent : ReleasedTerminalComponent component) :
    ∃ nextTotal,
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0.body
          values iter total = ok (cont (nextIter, nextTotal)) ∧
      CanonicalQM31 nextTotal ∧
      toMaintainedExact nextTotal = toMaintainedExact total +
        terminalComponentContribution component values := by
  cases component with
  | Geometric scale base => simp [ReleasedTerminalComponent] at hcomponent
  | Multilinear scale point =>
      exact multilinearBodyExact iter nextIter values total scale point nextRun
        hlen hvalues htotal hcomponent
  | Tensor scale factors =>
      exact tensorBodyExact iter nextIter values total scale factors nextRun
        hlen hvalues htotal hcomponent
  | Product scale pairs => simp [ReleasedTerminalComponent] at hcomponent
  | Dense weights =>
      exact denseBodyExact iter nextIter values total weights nextRun hlen
        hvalues htotal hcomponent
  | Grouped64x16 rowGroups groupValues groupCount =>
      simp [ReleasedTerminalComponent] at hcomponent
  | Grouped64x16BinaryDeferred rowGroups groupIds maybeGroup groupValues =>
      exact groupedBodyExact iter nextIter values total rowGroups groupIds
        maybeGroup groupValues nextRun hlen hvalues htotal hcomponent
  | Grouped128x16 rowGroups groupValues groupCount =>
      simp [ReleasedTerminalComponent] at hcomponent

/-! ## Complete direct component iterator -/

def terminalIteratorContribution
    (iter : core.slice.iter.Iter Component) (values : Slice RawQM31) :
    ExactQM31 :=
  ∑ index ∈ Finset.Ico iter.i iter.slice.val.length,
    terminalComponentContribution iter.slice.val[index]! values

private theorem iteratorNextSome
    (iter : core.slice.iter.Iter Component)
    (hactive : iter.i < iter.slice.val.length) :
    core.slice.iter.IteratorSliceIter.next iter =
      ok (some iter.slice.val[iter.i]!,
        ({ slice := iter.slice, i := iter.i + 1 } :
          core.slice.iter.Iter Component)) := by
  unfold core.slice.iter.IteratorSliceIter.next
  rw [dif_pos (by simpa [Slice.len, Slice.length] using hactive)]
  simp only
  apply congrArg (fun value : Component =>
    (Result.ok (some value,
      ({ slice := iter.slice, i := iter.i + 1 } :
        core.slice.iter.Iter Component)) :
      Result (Option Component × core.slice.iter.Iter Component)))
  exact (Slice.getElem_Nat_eq iter.slice iter.i hactive).trans
    (List.Inhabited_getElem_eq_getElem! _ _ hactive)

private theorem iteratorNextNone
    (iter : core.slice.iter.Iter Component)
    (hdone : iter.i = iter.slice.val.length) :
    core.slice.iter.IteratorSliceIter.next iter = ok (none, iter) := by
  rcases iter with ⟨slice, index⟩
  simp only at hdone ⊢
  subst index
  simp [core.slice.iter.IteratorSliceIter.next, Slice.len, Slice.length]

/-- Exact semantics of the complete extracted fast-path iterator, from any
in-bounds cursor.  This is constructive: under the released component-shape
invariant the extracted loop is proved to return, rather than merely being
classified after a successful call. -/
theorem releasedDirectDotLoopExact
    (iter : core.slice.iter.Iter Component)
    (values : Slice RawQM31) (total : RawQM31)
    (hcursor : iter.i ≤ iter.slice.val.length)
    (hcomponents : ∀ index, index < iter.slice.val.length →
      ReleasedTerminalComponent iter.slice.val[index]!)
    (hlen : values.val.length = 4)
    (hvalues : CanonicalList values.val)
    (htotal : CanonicalQM31 total) :
    ∃ out,
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0
          iter values total = ok out ∧
      CanonicalQM31 out ∧
      toMaintainedExact out = toMaintainedExact total +
        terminalIteratorContribution iter values := by
  unfold
    V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0
  by_cases hactive : iter.i < iter.slice.val.length
  · let component := iter.slice.val[iter.i]!
    let nextIter : core.slice.iter.Iter Component :=
      { slice := iter.slice, i := iter.i + 1 }
    have nextRun : core.slice.iter.IteratorSliceIter.next iter =
        ok (some component, nextIter) := by
      simpa [component, nextIter] using iteratorNextSome iter hactive
    have hcomponent : ReleasedTerminalComponent component :=
      hcomponents iter.i hactive
    obtain ⟨nextTotal, bodyRun, hNextTotal, eNextTotal⟩ :=
      releasedComponentBodyExact iter nextIter values total component nextRun
        hlen hvalues htotal hcomponent
    have nextCursor : nextIter.i ≤ nextIter.slice.val.length := by
      simp only [nextIter]
      omega
    have nextComponents : ∀ index, index < nextIter.slice.val.length →
        ReleasedTerminalComponent nextIter.slice.val[index]! := by
      intro index indexBound
      simpa [nextIter] using hcomponents index (by simpa [nextIter] using indexBound)
    obtain ⟨out, nextLoopRun, hOut, eOut⟩ :=
      releasedDirectDotLoopExact nextIter values nextTotal nextCursor
        nextComponents hlen hvalues hNextTotal
    have nextLoopRun' :
        loop
            (fun state =>
              V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0.body
                values state.1 state.2)
            (nextIter, nextTotal) = ok out := by
      simpa only [
        V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0]
        using nextLoopRun
    rw [loop.eq_1]
    simp only [Prod.fst, Prod.snd]
    rw [bodyRun]
    simp only [bind_tc_ok]
    rw [nextLoopRun']
    refine ⟨out, rfl, hOut, ?_⟩
    rw [eOut, eNextTotal]
    let summand := fun index : Nat =>
      terminalComponentContribution iter.slice.val[index]! values
    have split := Finset.sum_Ico_consecutive summand
      (Nat.le_succ iter.i)
      (show iter.i + 1 ≤ iter.slice.val.length by omega)
    have singleton :
        ∑ index ∈ Finset.Ico iter.i (iter.i + 1), summand index =
          summand iter.i := by
      rw [Finset.sum_Ico_succ_top (Nat.le_refl iter.i)]
      simp
    simp only [terminalIteratorContribution, nextIter, component, summand]
    rw [← split, singleton]
    ring
  · have doneIndex : iter.i = iter.slice.val.length := by omega
    have nextRun := iteratorNextNone iter doneIndex
    have bodyRun :
        V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0.body
            values iter total = ok (ControlFlow.done total) := by
      unfold
        V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0.body
      rw [nextRun]
      rfl
    rw [loop.eq_1]
    simp only [Prod.fst, Prod.snd]
    rw [bodyRun]
    refine ⟨total, rfl, htotal, ?_⟩
    change toMaintainedExact total = toMaintainedExact total +
      ∑ index ∈ Finset.Ico iter.i iter.slice.val.length,
        terminalComponentContribution iter.slice.val[index]! values
    rw [doneIndex]
    simp
termination_by iter.slice.val.length - iter.i
decreasing_by
  omega

/-! ## Public released terminal dot -/

abbrev RawWeights :=
  V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator

def terminalAccumulatorContribution
    (weights : RawWeights) (values : Slice RawQM31) : ExactQM31 :=
  ∑ index ∈ Finset.range weights.components.val.length,
    terminalComponentContribution weights.components.val[index]! values

def terminalAccumulatorWeights
    (weights : RawWeights) : Fin 4 → ExactQM31 :=
  fun coordinate =>
    ∑ index ∈ Finset.range weights.components.val.length,
      terminalComponentWeights weights.components.val[index]! coordinate

/-- The exact extracted public `WeightAccumulator.dot` call at the released
terminal shape returns the sum of the exact contributions of every stored
component.  The theorem also proves successful execution and a canonical raw
field result. -/
theorem releasedTerminalDotExact
    (weights : RawWeights) (values : Array RawQM31 4#usize)
    (logLength : weights.log_len = 2#u32)
    (hcomponents : ∀ index, index < weights.components.val.length →
      ReleasedTerminalComponent weights.components.val[index]!)
    (hvalues : ∀ index, index < 4 →
      CanonicalQM31 values.val[index]!) :
    ∃ out,
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot
          weights (Array.to_slice values) = ok out ∧
      CanonicalQM31 out ∧
      toMaintainedExact out =
        terminalAccumulatorContribution weights (Array.to_slice values) := by
  let valueSlice := Array.to_slice values
  let iter : core.slice.iter.Iter Component :=
    { slice := ⟨weights.components.val, weights.components.property⟩, i := 0 }
  have valueLength : valueSlice.val.length = 4 := by
    simpa [valueSlice, Array.to_slice] using values.property
  have valueCanonical : CanonicalList valueSlice.val := by
    intro index indexBound
    apply hvalues index
    omega
  have iterComponents : ∀ index, index < iter.slice.val.length →
      ReleasedTerminalComponent iter.slice.val[index]! := by
    intro index indexBound
    apply hcomponents index
    simpa [iter] using indexBound
  obtain ⟨out, loopRun, hOut, eOut⟩ :=
    releasedDirectDotLoopExact iter valueSlice
      V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
      (by simp [iter]) iterComponents valueLength valueCanonical zeroCanonical
  refine ⟨out, ?_, hOut, ?_⟩
  · have valueCount : Slice.len (Array.to_slice values) = 4#usize := by
      apply UScalar.eq_of_val_eq
      simp [Slice.len, Array.to_slice, values.property]
    unfold
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot
    rw [logLength]
    simp only [if_true]
    rw [valueCount]
    simp only [if_true]
    unfold
      SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter
    simp only [bind_tc_ok]
    simpa [iter, valueSlice] using loopRun
  · rw [eOut, maintainedZeroExact]
    change 0 + terminalIteratorContribution iter valueSlice =
      terminalAccumulatorContribution weights valueSlice
    simp [terminalIteratorContribution, terminalAccumulatorContribution, iter]

/-- Summing the component dots is the same as first summing their four
weights coordinatewise and then taking one four-entry dot. -/
theorem terminalAccumulatorContribution_eq_candidateClaim
    (weights : RawWeights) (values : Slice RawQM31) :
    terminalAccumulatorContribution weights values =
      AspisV5FriRelationCandidateBridge.candidateClaim
        (terminalAccumulatorWeights weights) (terminalValues values) := by
  unfold terminalAccumulatorContribution terminalComponentContribution
    terminalAccumulatorWeights terminalValues
    AspisV5FriRelationCandidateBridge.candidateClaim
  let components := weights.components.val
  change
    (∑ index ∈ Finset.range components.length,
      ∑ coordinate : Fin 4,
        terminalValues values coordinate *
          terminalComponentWeights components[index]! coordinate) =
    ∑ coordinate : Fin 4,
      terminalValues values coordinate *
        (∑ index ∈ Finset.range components.length,
          terminalComponentWeights components[index]! coordinate)
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Release-facing form: the extracted terminal call returns exactly the
candidate claim for the accumulator's combined four weights. -/
theorem releasedTerminalDotCandidateExact
    (weights : RawWeights) (values : Array RawQM31 4#usize)
    (logLength : weights.log_len = 2#u32)
    (hcomponents : ∀ index, index < weights.components.val.length →
      ReleasedTerminalComponent weights.components.val[index]!)
    (hvalues : ∀ index, index < 4 →
      CanonicalQM31 values.val[index]!) :
    ∃ out,
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot
          weights (Array.to_slice values) = ok out ∧
      CanonicalQM31 out ∧
      toMaintainedExact out =
        AspisV5FriRelationCandidateBridge.candidateClaim
          (terminalAccumulatorWeights weights)
          (terminalValues (Array.to_slice values)) := by
  obtain ⟨out, run, canonical, exact⟩ :=
    releasedTerminalDotExact weights values logLength hcomponents hvalues
  exact ⟨out, run, canonical,
    exact.trans (terminalAccumulatorContribution_eq_candidateClaim weights
      (Array.to_slice values))⟩

#print axioms denseDotLoopExact
#print axioms groupedDotLoopExact
#print axioms multilinearBodyExact
#print axioms tensorBodyExact
#print axioms releasedComponentBodyExact
#print axioms releasedDirectDotLoopExact
#print axioms releasedTerminalDotExact
#print axioms releasedTerminalDotCandidateExact

end AspisV5RelationLinkedTerminalDotSemantics
