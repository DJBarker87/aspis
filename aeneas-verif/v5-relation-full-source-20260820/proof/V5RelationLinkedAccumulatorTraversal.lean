import V5RelationLinkedSupportedFold

/-!
# Exact component traversal for the production weight accumulator

The public `WeightAccumulator.fold` computes the challenge powers once and
then mutates every stored component in place.  The component-specific proofs
are useful only after we know that a particular output cell really is the
result of dispatching the corresponding input cell.  This file proves that
connection directly from the complete Charon/Aeneas definition.

The statements are pointwise.  For every in-bounds released input component,
one successful public fold exposes the exact dispatcher call, its output cell,
and all field/prepared-multiplier calls shared by the traversal.
-/

namespace AspisV5RelationLinkedAccumulatorTraversal

open Aeneas Aeneas.Std Result ControlFlow
open AspisV5RelationLinkedSupportedFold

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

abbrev RawQM31 := V5RelationLinkedGenerated.aspis_core.field.QM31
abbrev RawPrepared :=
  V5RelationLinkedGenerated.aspis_core.field.PreparedQm31Multiplier
abbrev Component :=
  V5RelationLinkedGenerated.aspis_core.sumcheck.WeightComponent
abbrev RawWeights :=
  V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator

deriving instance Inhabited for
  V5RelationLinkedGenerated.aspis_core.sumcheck.WeightComponent

private theorem generatedVecIndexMutSuccess
    (values : alloc.vec.Vec Component) (index : Std.Usize)
    (inBounds : index.val < values.length) :
    ∃ value back,
      alloc.vec.Vec.index_mut
          (core.slice.index.SliceIndexUsizeSlice Component) values index =
        .ok (value, back) ∧
      value = values.val[index.val]! ∧
      back = alloc.vec.Vec.set values index := by
  obtain ⟨pair, run, post⟩ := Aeneas.Std.WP.spec_imp_exists
    (alloc.vec.Vec.index_mut_usize_spec values index inBounds)
  rcases pair with ⟨value, back⟩
  refine ⟨value, back, ?_, ?_, post.2⟩
  · rw [alloc.vec.Vec.index_mut_slice_index]
    exact run
  · rw [post.1]
    symm
    apply List.getElem!_of_getElem?
    simpa using inBounds

private theorem wrappingSuccValue
    (components : alloc.vec.Vec Component) (index : Std.Usize)
    (active : index.val < components.length) :
    (Std.Usize.wrapping_add index 1#usize).val = index.val + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  have oneValue : (1#usize : Std.Usize).val = 1 := rfl
  rw [oneValue]
  apply Nat.mod_eq_of_lt
  have lengthWithinScalar : components.length < UScalar.size .Usize := by
    simpa using (alloc.vec.Vec.len components).hSize
  omega

/-- Once the loop cursor has passed a cell, all later iterations leave that
cell unchanged. -/
private theorem loopPreservesEarlierCell
    (current : RawWeights) (componentIndex : Std.Usize)
    (currentLog : Std.U32) (alpha alpha2 alpha3 : RawQM31)
    (preparedAlpha preparedAlpha2 : RawPrepared)
    (outputLog : Std.U32) (outputComponents : alloc.vec.Vec Component)
    (target : Nat)
    (targetBefore : target < componentIndex.val)
    (targetBound : target < current.components.val.length)
    (success :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_all_components_arity4_loop
          current currentLog alpha alpha2 alpha3 preparedAlpha preparedAlpha2
            componentIndex = .ok (outputLog, outputComponents)) :
    outputComponents.val[target]! = current.components.val[target]! := by
  unfold
    V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_all_components_arity4_loop
    at success
  rw [Aeneas.Std.loop.eq_def] at success
  unfold
    V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_all_components_arity4_loop.body
    at success
  simp only at success
  by_cases active : componentIndex < alloc.vec.Vec.len current.components
  · rw [if_pos active] at success
    have activeNat : componentIndex.val < current.components.length := by
      scalar_tac
    obtain ⟨component, back, indexRun, componentExact, backExact⟩ :=
      generatedVecIndexMutSuccess current.components componentIndex activeNat
    rw [indexRun] at success
    simp only [bind_tc_ok] at success
    generalize dispatchRun :
        V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_component_arity4
          component currentLog alpha alpha2 alpha3 preparedAlpha
            preparedAlpha2 = dispatchResult at success
    cases dispatchResult with
    | fail error => simp at success
    | div => simp at success
    | ok pair =>
      rcases pair with ⟨replacement, componentOut⟩
      cases replacement with
      | none =>
        simp only [bind_tc_ok, Aeneas.Std.lift] at success
        let next := Std.Usize.wrapping_add componentIndex 1#usize
        have nextValue : next.val = componentIndex.val + 1 := by
          exact wrappingSuccValue current.components componentIndex activeNat
        have targetBeforeNext : target < next.val := by omega
        have targetNe : componentIndex.val ≠ target := by omega
        have targetAtNext :
            (back componentOut).val[target]! =
              current.components.val[target]! := by
          rw [backExact]
          exact List.set_getElem!_ne _ _ _ _ (by omega)
        have targetBoundNext : target < (back componentOut).val.length := by
          simpa [backExact, alloc.vec.Vec.set_val_eq] using targetBound
        have recurse := loopPreservesEarlierCell
          ({ current with components := back componentOut } : RawWeights)
          next currentLog alpha alpha2 alpha3 preparedAlpha preparedAlpha2
          outputLog outputComponents target targetBeforeNext targetBoundNext
          success
        exact recurse.trans targetAtNext
      | some replacementValue =>
        simp only [bind_tc_ok, Aeneas.Std.lift] at success
        let next := Std.Usize.wrapping_add componentIndex 1#usize
        have nextValue : next.val = componentIndex.val + 1 := by
          exact wrappingSuccValue current.components componentIndex activeNat
        have targetBeforeNext : target < next.val := by omega
        have targetNe : componentIndex.val ≠ target := by omega
        have targetAtNext :
            (back replacementValue).val[target]! =
              current.components.val[target]! := by
          rw [backExact]
          exact List.set_getElem!_ne _ _ _ _ (by omega)
        have targetBoundNext : target < (back replacementValue).val.length := by
          simpa [backExact, alloc.vec.Vec.set_val_eq] using targetBound
        have recurse := loopPreservesEarlierCell
          ({ current with components := back replacementValue } : RawWeights)
          next currentLog alpha alpha2 alpha3 preparedAlpha preparedAlpha2
          outputLog outputComponents target targetBeforeNext targetBoundNext
          success
        exact recurse.trans targetAtNext
  · rw [if_neg active] at success
    simp only [Result.ok.injEq, Prod.mk.injEq] at success
    rcases success with ⟨_, rfl⟩
    rfl
termination_by current.components.length - componentIndex.val
decreasing_by
  all_goals
    rw [backExact, alloc.vec.Vec.set_length, nextValue]
    omega

/-- Starting at or before a target cell, a successful loop exposes the exact
released dispatcher call used for that cell and the cell stored in the final
output vector. -/
private theorem loopExposesTargetCell
    (current : RawWeights) (componentIndex : Std.Usize)
    (currentLog : Std.U32) (alpha alpha2 alpha3 : RawQM31)
    (preparedAlpha preparedAlpha2 : RawPrepared)
    (outputLog : Std.U32) (outputComponents : alloc.vec.Vec Component)
    (target : Nat)
    (cursorBefore : componentIndex.val ≤ target)
    (targetBound : target < current.components.val.length)
    (targetReleased : ReleasedComponent current.components.val[target]!)
    (success :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_all_components_arity4_loop
          current currentLog alpha alpha2 alpha3 preparedAlpha preparedAlpha2
            componentIndex = .ok (outputLog, outputComponents)) :
    ∃ componentOut,
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_component_arity4
          current.components.val[target]! currentLog alpha alpha2 alpha3
            preparedAlpha preparedAlpha2 = .ok (none, componentOut) ∧
      outputComponents.val[target]! = componentOut ∧
      ReleasedComponent componentOut := by
  unfold
    V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_all_components_arity4_loop
    at success
  rw [Aeneas.Std.loop.eq_def] at success
  unfold
    V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_all_components_arity4_loop.body
    at success
  simp only at success
  have active : componentIndex < alloc.vec.Vec.len current.components := by
    scalar_tac
  rw [if_pos active] at success
  have activeNat : componentIndex.val < current.components.length := by
    scalar_tac
  obtain ⟨component, back, indexRun, componentExact, backExact⟩ :=
    generatedVecIndexMutSuccess current.components componentIndex activeNat
  rw [indexRun] at success
  simp only [bind_tc_ok] at success
  generalize dispatchRun :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_component_arity4
        component currentLog alpha alpha2 alpha3 preparedAlpha preparedAlpha2 =
      dispatchResult at success
  cases dispatchResult with
  | fail error => simp at success
  | div => simp at success
  | ok pair =>
    rcases pair with ⟨replacement, componentOut⟩
    let next := Std.Usize.wrapping_add componentIndex 1#usize
    have nextValue : next.val = componentIndex.val + 1 := by
      exact wrappingSuccValue current.components componentIndex activeNat
    by_cases atTarget : componentIndex.val = target
    · have componentIsTarget : component = current.components.val[target]! := by
        rw [componentExact, atTarget]
      have releasedComponent : ReleasedComponent component := by
        simpa [componentIsTarget] using targetReleased
      have noReplacement := released_component_success_no_replacement
        component componentOut replacement currentLog alpha alpha2 alpha3
        preparedAlpha preparedAlpha2 releasedComponent dispatchRun
      cases noReplacement.1
      simp only [bind_tc_ok, Aeneas.Std.lift] at success
      have targetAtNext :
          (back componentOut).val[target]! = componentOut := by
        rw [backExact]
        exact List.set_getElem!_eq _ _ _ _ ⟨targetBound, atTarget⟩
      have targetBoundNext : target < (back componentOut).val.length := by
        simpa [backExact, alloc.vec.Vec.set_val_eq] using targetBound
      have preserved := loopPreservesEarlierCell
        ({ current with components := back componentOut } : RawWeights)
        next currentLog alpha alpha2 alpha3 preparedAlpha preparedAlpha2
        outputLog outputComponents target (by rw [nextValue]; omega)
        targetBoundNext success
      refine ⟨componentOut, ?_, preserved.trans targetAtNext, noReplacement.2⟩
      rw [← componentIsTarget]
      exact dispatchRun
    · have cursorStrict : componentIndex.val < target := by omega
      cases replacement with
      | none =>
        simp only [bind_tc_ok, Aeneas.Std.lift] at success
        have targetNe : componentIndex.val ≠ target := atTarget
        have targetAtNext :
            (back componentOut).val[target]! =
              current.components.val[target]! := by
          rw [backExact]
          exact List.set_getElem!_ne _ _ _ _ (by omega)
        have targetBoundNext : target < (back componentOut).val.length := by
          simpa [backExact, alloc.vec.Vec.set_val_eq] using targetBound
        have releasedNext :
            ReleasedComponent (back componentOut).val[target]! := by
          rw [targetAtNext]
          exact targetReleased
        obtain ⟨targetOut, targetRun, finalCell, finalReleased⟩ :=
          loopExposesTargetCell
            ({ current with components := back componentOut } : RawWeights)
            next currentLog alpha alpha2 alpha3 preparedAlpha preparedAlpha2
            outputLog outputComponents target (by rw [nextValue]; omega)
            targetBoundNext releasedNext success
        refine ⟨targetOut, ?_, finalCell, finalReleased⟩
        simpa [targetAtNext] using targetRun
      | some replacementValue =>
        simp only [bind_tc_ok, Aeneas.Std.lift] at success
        have targetNe : componentIndex.val ≠ target := atTarget
        have targetAtNext :
            (back replacementValue).val[target]! =
              current.components.val[target]! := by
          rw [backExact]
          exact List.set_getElem!_ne _ _ _ _ (by omega)
        have targetBoundNext :
            target < (back replacementValue).val.length := by
          simpa [backExact, alloc.vec.Vec.set_val_eq] using targetBound
        have releasedNext :
            ReleasedComponent (back replacementValue).val[target]! := by
          rw [targetAtNext]
          exact targetReleased
        obtain ⟨targetOut, targetRun, finalCell, finalReleased⟩ :=
          loopExposesTargetCell
            ({ current with components := back replacementValue } : RawWeights)
            next currentLog alpha alpha2 alpha3 preparedAlpha preparedAlpha2
            outputLog outputComponents target (by rw [nextValue]; omega)
            targetBoundNext releasedNext success
        refine ⟨targetOut, ?_, finalCell, finalReleased⟩
        simpa [targetAtNext] using targetRun
termination_by current.components.length - componentIndex.val
decreasing_by
  all_goals
    rw [backExact, alloc.vec.Vec.set_length, nextValue]
    omega

/-- The public component traversal maps every released input cell through
the exact component dispatcher and stores that result at the same index. -/
theorem foldAllSuccessExposesComponent
    (weights output : RawWeights) (currentLog : Std.U32)
    (alpha alpha2 alpha3 : RawQM31)
    (preparedAlpha preparedAlpha2 : RawPrepared)
    (target : Nat) (targetBound : target < weights.components.val.length)
    (targetReleased : ReleasedComponent weights.components.val[target]!)
    (success :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_all_components_arity4
          weights currentLog alpha alpha2 alpha3 preparedAlpha preparedAlpha2 =
        .ok output) :
    ∃ componentOut,
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_component_arity4
          weights.components.val[target]! currentLog alpha alpha2 alpha3
            preparedAlpha preparedAlpha2 = .ok (none, componentOut) ∧
      output.components.val[target]! = componentOut ∧
      ReleasedComponent componentOut := by
  unfold
    V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_all_components_arity4
    at success
  generalize loopRun :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_all_components_arity4_loop
        weights currentLog alpha alpha2 alpha3 preparedAlpha preparedAlpha2
          0#usize = loopResult at success
  cases loopResult with
  | fail error => simp at success
  | div => simp at success
  | ok pair =>
    rcases pair with ⟨outputLog, outputComponents⟩
    simp only [bind_tc_ok, Result.ok.injEq] at success
    subst output
    exact loopExposesTargetCell weights 0#usize currentLog alpha alpha2 alpha3
      preparedAlpha preparedAlpha2 outputLog outputComponents target (by norm_num)
      targetBound targetReleased loopRun

/-- A successful public fold exposes all shared challenge-power preparation
calls and the exact same-index component transition. -/
theorem foldSuccessExposesComponent
    (weights output : RawWeights) (alpha : RawQM31)
    (target : Nat) (targetBound : target < weights.components.val.length)
    (targetReleased : ReleasedComponent weights.components.val[target]!)
    (success :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold
          weights alpha = .ok output) :
    ∃ alpha2 alpha3 preparedAlpha preparedAlpha2 componentOut folded,
      V5RelationLinkedGenerated.aspis_core.field.QM31.square alpha = .ok alpha2 ∧
      V5RelationLinkedGenerated.aspis_core.field.PreparedQm31Multiplier.new
          alpha = .ok preparedAlpha ∧
      V5RelationLinkedGenerated.aspis_core.field.PreparedQm31Multiplier.new
          alpha2 = .ok preparedAlpha2 ∧
      V5RelationLinkedGenerated.aspis_core.field.PreparedQm31Multiplier.mul
          preparedAlpha alpha2 = .ok alpha3 ∧
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_all_components_arity4
          weights weights.log_len alpha alpha2 alpha3 preparedAlpha
            preparedAlpha2 = .ok folded ∧
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_component_arity4
          weights.components.val[target]! weights.log_len alpha alpha2 alpha3
            preparedAlpha preparedAlpha2 = .ok (none, componentOut) ∧
      output.components.val[target]! = componentOut ∧
      ReleasedComponent componentOut ∧
      output.log_len = Std.U32.wrapping_sub folded.log_len 2#u32 := by
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold
    at success
  generalize squareRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.square alpha =
        squareResult at success
  cases squareResult with
  | fail error => simp at success
  | div => simp at success
  | ok alpha2 =>
    simp only [bind_tc_ok] at success
    generalize prepareRun :
        V5RelationLinkedGenerated.aspis_core.field.PreparedQm31Multiplier.new
          alpha = prepareResult at success
    cases prepareResult with
    | fail error => simp at success
    | div => simp at success
    | ok preparedAlpha =>
      simp only [bind_tc_ok] at success
      generalize prepare2Run :
          V5RelationLinkedGenerated.aspis_core.field.PreparedQm31Multiplier.new
            alpha2 = prepare2Result at success
      cases prepare2Result with
      | fail error => simp at success
      | div => simp at success
      | ok preparedAlpha2 =>
        simp only [bind_tc_ok] at success
        generalize alpha3Run :
            V5RelationLinkedGenerated.aspis_core.field.PreparedQm31Multiplier.mul
              preparedAlpha alpha2 = alpha3Result at success
        cases alpha3Result with
        | fail error => simp at success
        | div => simp at success
        | ok alpha3 =>
          simp only [bind_tc_ok] at success
          generalize dispatchRun :
              V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_all_components_arity4
                weights weights.log_len alpha alpha2 alpha3 preparedAlpha
                  preparedAlpha2 = dispatchResult at success
          cases dispatchResult with
          | fail error => simp at success
          | div => simp at success
          | ok folded =>
            simp only [bind_tc_ok, Aeneas.Std.lift, Result.ok.injEq] at success
            subst output
            obtain ⟨componentOut, componentRun, outputCell, outputReleased⟩ :=
              foldAllSuccessExposesComponent weights folded weights.log_len alpha
                alpha2 alpha3 preparedAlpha preparedAlpha2 target targetBound
                targetReleased dispatchRun
            refine ⟨alpha2, alpha3, preparedAlpha, preparedAlpha2,
              componentOut, folded, rfl, rfl, prepare2Run,
              alpha3Run, dispatchRun, componentRun, ?_, outputReleased, rfl⟩
            simpa using outputCell

/-- The in-place traversal neither inserts nor removes components. -/
private theorem loopSuccessPreservesComponentLength
    (current : RawWeights) (componentIndex : Std.Usize)
    (currentLog : Std.U32) (alpha alpha2 alpha3 : RawQM31)
    (preparedAlpha preparedAlpha2 : RawPrepared)
    (outputLog : Std.U32) (outputComponents : alloc.vec.Vec Component)
    (success :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_all_components_arity4_loop
          current currentLog alpha alpha2 alpha3 preparedAlpha preparedAlpha2
            componentIndex = .ok (outputLog, outputComponents)) :
    outputComponents.val.length = current.components.val.length := by
  unfold
    V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_all_components_arity4_loop
    at success
  rw [Aeneas.Std.loop.eq_def] at success
  unfold
    V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_all_components_arity4_loop.body
    at success
  simp only at success
  by_cases active : componentIndex < alloc.vec.Vec.len current.components
  · rw [if_pos active] at success
    have activeNat : componentIndex.val < current.components.length := by
      scalar_tac
    obtain ⟨component, back, indexRun, _componentExact, backExact⟩ :=
      generatedVecIndexMutSuccess current.components componentIndex activeNat
    rw [indexRun] at success
    simp only [bind_tc_ok] at success
    generalize dispatchRun :
        V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_component_arity4
          component currentLog alpha alpha2 alpha3 preparedAlpha
            preparedAlpha2 = dispatchResult at success
    cases dispatchResult with
    | fail error => simp at success
    | div => simp at success
    | ok pair =>
      rcases pair with ⟨replacement, componentOut⟩
      cases replacement with
      | none =>
        simp only [bind_tc_ok, Aeneas.Std.lift] at success
        have recurse := loopSuccessPreservesComponentLength
          ({ current with components := back componentOut } : RawWeights)
          (Std.Usize.wrapping_add componentIndex 1#usize) currentLog alpha
          alpha2 alpha3 preparedAlpha preparedAlpha2 outputLog outputComponents
          success
        rw [recurse, backExact, alloc.vec.Vec.set_val_eq, List.length_set]
      | some replacementValue =>
        simp only [bind_tc_ok, Aeneas.Std.lift] at success
        have recurse := loopSuccessPreservesComponentLength
          ({ current with components := back replacementValue } : RawWeights)
          (Std.Usize.wrapping_add componentIndex 1#usize) currentLog alpha
          alpha2 alpha3 preparedAlpha preparedAlpha2 outputLog outputComponents
          success
        rw [recurse, backExact, alloc.vec.Vec.set_val_eq, List.length_set]
  · rw [if_neg active] at success
    simp only [Result.ok.injEq, Prod.mk.injEq] at success
    rcases success with ⟨_, rfl⟩
    rfl
termination_by current.components.length - componentIndex.val
decreasing_by
  all_goals
    rw [backExact, alloc.vec.Vec.set_length]
    have nextValue := wrappingSuccValue current.components componentIndex activeNat
    rw [nextValue]
    omega

/-- The public component traversal preserves the component-vector length. -/
theorem foldAllSuccessPreservesComponentLength
    (weights output : RawWeights) (currentLog : Std.U32)
    (alpha alpha2 alpha3 : RawQM31)
    (preparedAlpha preparedAlpha2 : RawPrepared)
    (success :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_all_components_arity4
          weights currentLog alpha alpha2 alpha3 preparedAlpha preparedAlpha2 =
        .ok output) :
    output.components.val.length = weights.components.val.length := by
  unfold
    V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_all_components_arity4
    at success
  generalize loopRun :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_all_components_arity4_loop
        weights currentLog alpha alpha2 alpha3 preparedAlpha preparedAlpha2
          0#usize = loopResult at success
  cases loopResult with
  | fail error => simp at success
  | div => simp at success
  | ok pair =>
    rcases pair with ⟨outputLog, outputComponents⟩
    simp only [bind_tc_ok, Result.ok.injEq] at success
    subst output
    exact loopSuccessPreservesComponentLength weights 0#usize currentLog alpha
      alpha2 alpha3 preparedAlpha preparedAlpha2 outputLog outputComponents
      loopRun

/-- The public fold changes only the log length after the in-place component
traversal and therefore also preserves the component-vector length. -/
theorem foldSuccessPreservesComponentLength
    (weights output : RawWeights) (alpha : RawQM31)
    (success :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold
          weights alpha = .ok output) :
    output.components.val.length = weights.components.val.length := by
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold
    at success
  generalize squareRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.square alpha =
        squareResult at success
  cases squareResult with
  | fail error => simp at success
  | div => simp at success
  | ok alpha2 =>
    simp only [bind_tc_ok] at success
    generalize prepareRun :
        V5RelationLinkedGenerated.aspis_core.field.PreparedQm31Multiplier.new
          alpha = prepareResult at success
    cases prepareResult with
    | fail error => simp at success
    | div => simp at success
    | ok preparedAlpha =>
      simp only [bind_tc_ok] at success
      generalize prepare2Run :
          V5RelationLinkedGenerated.aspis_core.field.PreparedQm31Multiplier.new
            alpha2 = prepare2Result at success
      cases prepare2Result with
      | fail error => simp at success
      | div => simp at success
      | ok preparedAlpha2 =>
        simp only [bind_tc_ok] at success
        generalize alpha3Run :
            V5RelationLinkedGenerated.aspis_core.field.PreparedQm31Multiplier.mul
              preparedAlpha alpha2 = alpha3Result at success
        cases alpha3Result with
        | fail error => simp at success
        | div => simp at success
        | ok alpha3 =>
          simp only [bind_tc_ok] at success
          generalize dispatchRun :
              V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_all_components_arity4
                weights weights.log_len alpha alpha2 alpha3 preparedAlpha
                  preparedAlpha2 = dispatchResult at success
          cases dispatchResult with
          | fail error => simp at success
          | div => simp at success
          | ok folded =>
            simp only [bind_tc_ok, Aeneas.Std.lift, Result.ok.injEq] at success
            subst output
            exact foldAllSuccessPreservesComponentLength weights folded
              weights.log_len alpha alpha2 alpha3 preparedAlpha preparedAlpha2
              dispatchRun

#print axioms foldAllSuccessExposesComponent
#print axioms foldSuccessExposesComponent
#print axioms foldSuccessPreservesComponentLength

end AspisV5RelationLinkedAccumulatorTraversal
