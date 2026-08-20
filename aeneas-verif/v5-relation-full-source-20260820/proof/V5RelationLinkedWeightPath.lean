import RelationLinked.Funs

/-!
# Production V5 terminal weight route

This file isolates the one helper deliberately left opaque by the complete
production-linked extraction.  The generic `weight_at` fallback is present in
the generated Rust model, but a successful released V5 run reaches `dot` with
`log_len = 2` and an array of exactly four terminal values.  Under those two
facts the generated definition selects its component-specific direct branch,
which contains no call to `weight_at`.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5RelationLinkedWeightPath

open V5RelationLinkedGenerated

abbrev RawQM31 := V5RelationLinkedGenerated.aspis_core.field.QM31
abbrev RawWeights :=
  V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator

private theorem generated_vec_index_mut_success
    {T : Type} (values : alloc.vec.Vec T) (index : Std.Usize)
    (inBounds : index.val < values.length) :
    ∃ value back,
      alloc.vec.Vec.index_mut
          (core.slice.index.SliceIndexUsizeSlice T) values index =
        .ok (value, back) ∧
      back = alloc.vec.Vec.set values index := by
  obtain ⟨pair, run, post⟩ := Aeneas.Std.WP.spec_imp_exists
    (alloc.vec.Vec.index_mut_usize_spec values index inBounds)
  rcases pair with ⟨value, back⟩
  refine ⟨value, back, ?_, post.2⟩
  rw [alloc.vec.Vec.index_mut_slice_index]
  exact run

/-- The generated indexed dispatcher never changes the accumulator's
`log_len`; it updates only the component vector.  This is a success-directed
loop theorem, so it makes no totality claim for malformed or unsupported
component states. -/
theorem fold_all_success_preserves_log_length
    (initialLog : Std.U32)
    (current : RawWeights) (componentIndex : Std.Usize)
    (currentLogLength : current.log_len = initialLog)
    (dispatchLog : Std.U32)
    (alpha alpha2 alpha3 : RawQM31)
    (preparedAlpha preparedAlpha2 :
      V5RelationLinkedGenerated.aspis_core.field.PreparedQm31Multiplier)
    (outputLog : Std.U32)
    (outputComponents : alloc.vec.Vec
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightComponent)
    (success :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_all_components_arity4_loop
          current dispatchLog alpha alpha2 alpha3 preparedAlpha
            preparedAlpha2 componentIndex =
        .ok (outputLog, outputComponents)) :
    outputLog = initialLog := by
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
    have inBounds : componentIndex.val < current.components.length := by
      scalar_tac
    obtain ⟨component, back, indexRun, backExact⟩ :=
      generated_vec_index_mut_success current.components componentIndex inBounds
    rw [indexRun] at success
    simp only [bind_tc_ok] at success
    generalize foldRun :
        V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_component_arity4
          component dispatchLog alpha alpha2 alpha3 preparedAlpha
            preparedAlpha2 = folded at success
    cases folded with
    | fail error => simp at success
    | div => simp at success
    | ok pair =>
      rcases pair with ⟨replacement, componentOut⟩
      cases replacement with
      | none =>
        simp only [bind_tc_ok, Aeneas.Std.lift] at success
        have nextLog :
            ({ current with components := back componentOut } : RawWeights).log_len =
              initialLog := by
          exact currentLogLength
        apply fold_all_success_preserves_log_length initialLog
          ({ current with components := back componentOut } : RawWeights)
          (Std.Usize.wrapping_add componentIndex 1#usize) nextLog dispatchLog
          alpha alpha2 alpha3 preparedAlpha preparedAlpha2 outputLog
          outputComponents success
      | some replacementValue =>
        simp only [bind_tc_ok, Aeneas.Std.lift] at success
        have nextLog :
            ({ current with components := back replacementValue } : RawWeights).log_len =
              initialLog := by
          exact currentLogLength
        apply fold_all_success_preserves_log_length initialLog
          ({ current with components := back replacementValue } : RawWeights)
          (Std.Usize.wrapping_add componentIndex 1#usize) nextLog dispatchLog
          alpha alpha2 alpha3 preparedAlpha preparedAlpha2 outputLog
          outputComponents success
  · rw [if_neg active] at success
    simp only [Result.ok.injEq, Prod.mk.injEq] at success
    exact success.1.symm.trans currentLogLength
termination_by current.components.length - componentIndex.val
decreasing_by
  all_goals
    rw [backExact, alloc.vec.Vec.set_length]
    have noWrap :
        (Std.Usize.wrapping_add componentIndex 1#usize).val =
          componentIndex.val + 1 := by
      rw [Std.Usize.wrapping_add_val_eq]
      have oneValue : (1#usize : Std.Usize).val = 1 := rfl
      rw [oneValue]
      apply Nat.mod_eq_of_lt
      have lengthWithinScalar :
          current.components.length < UScalar.size .Usize := by
        simpa using (alloc.vec.Vec.len current.components).hSize
      omega
    rw [noWrap]
    omega

/-- The public indexed dispatcher returns an accumulator with the same
`log_len` it received. -/
theorem fold_all_wrapper_success_preserves_log_length
    (weights output : RawWeights) (currentLog : Std.U32)
    (alpha alpha2 alpha3 : RawQM31)
    (preparedAlpha preparedAlpha2 :
      V5RelationLinkedGenerated.aspis_core.field.PreparedQm31Multiplier)
    (success :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_all_components_arity4
          weights currentLog alpha alpha2 alpha3 preparedAlpha preparedAlpha2 =
        .ok output) :
    output.log_len = weights.log_len := by
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
    exact fold_all_success_preserves_log_length weights.log_len weights
      0#usize rfl currentLog alpha alpha2 alpha3 preparedAlpha preparedAlpha2
      outputLog outputComponents loopRun

/-- Every successful call to the exact generated production `fold` performs
the one explicit `log_len -= 2` update after its component traversal. -/
theorem fold_success_decrements_log_length
    (weights output : RawWeights) (alpha : RawQM31)
    (success :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold
          weights alpha = .ok output) :
    output.log_len = Std.U32.wrapping_sub weights.log_len 2#u32 := by
  unfold
    V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold
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
            have preserved := fold_all_wrapper_success_preserves_log_length
              weights folded weights.log_len alpha alpha2 alpha3 preparedAlpha
                preparedAlpha2 dispatchRun
            simp only
            rw [preserved]

/-- Four successful production folds starting from the released ten-bit
domain end at `log_len = 2`, independent of the component payloads. -/
theorem four_successful_folds_end_at_log_two
    (weights0 weights1 weights2 weights3 weights4 : RawWeights)
    (alpha0 alpha1 alpha2 alpha3 : RawQM31)
    (initialLog : weights0.log_len = 10#u32)
    (fold0 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold
        weights0 alpha0 = .ok weights1)
    (fold1 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold
        weights1 alpha1 = .ok weights2)
    (fold2 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold
        weights2 alpha2 = .ok weights3)
    (fold3 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold
        weights3 alpha3 = .ok weights4) :
    weights4.log_len = 2#u32 := by
  have log1 := fold_success_decrements_log_length weights0 weights1 alpha0 fold0
  have log2 := fold_success_decrements_log_length weights1 weights2 alpha1 fold1
  have log3 := fold_success_decrements_log_length weights2 weights3 alpha2 fold2
  have log4 := fold_success_decrements_log_length weights3 weights4 alpha3 fold3
  have tenToEight : Std.U32.wrapping_sub 10#u32 2#u32 = 8#u32 := by decide
  have eightToSix : Std.U32.wrapping_sub 8#u32 2#u32 = 6#u32 := by decide
  have sixToFour : Std.U32.wrapping_sub 6#u32 2#u32 = 4#u32 := by decide
  have fourToTwo : Std.U32.wrapping_sub 4#u32 2#u32 = 2#u32 := by decide
  rw [initialLog] at log1
  rw [tenToEight] at log1
  have log1Exact : weights1.log_len = 8#u32 := log1
  rw [log1Exact] at log2
  rw [eightToSix] at log2
  have log2Exact : weights2.log_len = 6#u32 := log2
  rw [log2Exact] at log3
  rw [sixToFour] at log3
  have log3Exact : weights3.log_len = 4#u32 := log3
  rw [log3Exact] at log4
  rw [fourToTwo] at log4
  exact log4

/-- The production dot dispatch is definitionally the direct component loop
at the released terminal shape.  The theorem's proof does not use the opaque
generic `weight_at` fallback. -/
theorem dot_log_two_length_four_uses_direct_components
    (weights : RawWeights) (values : Slice RawQM31)
    (logLength : weights.log_len = 2#u32)
    (valueCount : Slice.len values = 4#usize) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot
        weights values = (do
      let iter ←
        SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter
          Global weights.components
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0
        iter values V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO) := by
  unfold
    V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot
  simp only [logLength, valueCount, if_true]

/-- An array with the released terminal type contributes exactly four values,
so `log_len = 2` is sufficient to force the direct branch at the actual outer
verifier call site. -/
theorem released_terminal_array_uses_direct_components
    (weights : RawWeights) (values : Array RawQM31 4#usize)
    (logLength : weights.log_len = 2#u32) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot
        weights (Array.to_slice values) = (do
      let iter ←
        SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter
          Global weights.components
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0
        iter (Array.to_slice values)
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO) := by
  apply dot_log_two_length_four_uses_direct_components weights
    (Array.to_slice values) logLength
  apply UScalar.eq_of_val_eq
  simp [Slice.len, Array.to_slice, values.property]

#print axioms dot_log_two_length_four_uses_direct_components
#print axioms released_terminal_array_uses_direct_components
#print axioms fold_all_success_preserves_log_length
#print axioms fold_all_wrapper_success_preserves_log_length
#print axioms fold_success_decrements_log_length
#print axioms four_successful_folds_end_at_log_two

end AspisV5RelationLinkedWeightPath
