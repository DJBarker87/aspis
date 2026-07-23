import RuntimeEvaluatorCanonicalCurrent20260722

set_option autoImplicit false

open Aeneas Aeneas.Std Result

namespace ComponentCRuntimeCanonicalGenerated.RuntimeWeightAccumulatorFoldLevel3

open ComponentCRuntimeCanonicalGenerated

abbrev RawQM31 := aspis_core.field.QM31
abbrev RawPrepared := aspis_core.field.PreparedQm31Multiplier
abbrev Accumulator := aspis_core.sumcheck.WeightAccumulator
abbrev Component := aspis_core.sumcheck.WeightComponent

local instance : Inhabited RawQM31 := ⟨aspis_core.field.QM31.ZERO⟩

def realRelationComponents
    (c0 c1 c2 c3 c4 : Component) : alloc.vec.Vec Component :=
  ⟨[c0, c1, c2, c3, c4], by
    scalar_tac⟩

def singletonTensorComponents (component : Component) : alloc.vec.Vec Component :=
  ⟨[component], by scalar_tac⟩

private theorem usize_zero_succ :
    Std.Usize.wrapping_add 0#usize 1#usize = 1#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (1#usize).hSize; scalar_tac)]
  norm_num

private theorem usize_one_succ :
    Std.Usize.wrapping_add 1#usize 1#usize = 2#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (2#usize).hSize; scalar_tac)]
  norm_num

private theorem usize_two_succ :
    Std.Usize.wrapping_add 2#usize 1#usize = 3#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (3#usize).hSize; scalar_tac)]
  norm_num

private theorem usize_three_succ :
    Std.Usize.wrapping_add 3#usize 1#usize = 4#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (4#usize).hSize; scalar_tac)]
  norm_num

private theorem usize_four_succ :
    Std.Usize.wrapping_add 4#usize 1#usize = 5#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (5#usize).hSize; scalar_tac)]
  norm_num

/-- Exact generated traversal of the real relation accumulator's component
order: three Multilinear terms, the deferred grouped-binary mask, then the
Dense terminal covector.  Every primitive receives the same generated
`alpha/alpha2/alpha3` arguments; no replacement or append is possible in this
specialized helper, so the five output constructors retain source order. -/
theorem generated_real_five_component_traversal_exact
    (currentLogLen : Std.U32)
    (alpha alpha2 alpha3 : RawQM31)
    (preparedAlpha preparedAlpha2 : RawPrepared)
    (scale0 scale1 scale2 scale0Out scale1Out scale2Out : RawQM31)
    (point0 point1 point2 point0Out point1Out point2Out :
      alloc.vec.Vec RawQM31)
    (rowGroups : alloc.vec.Vec Std.U8)
    (groupMasks groupMasksOut : alloc.vec.Vec Std.U16)
    (firstAlpha firstAlphaOut : Option RawQM31)
    (groupValues groupValuesOut : alloc.vec.Vec RawQM31)
    (dense denseOut : alloc.vec.Vec RawQM31)
    (hml0 :
      aspis_core.sumcheck.WeightAccumulator.fold_multilinear_arity4
          scale0 point0 alpha alpha2 alpha3 = ok (scale0Out, point0Out))
    (hml1 :
      aspis_core.sumcheck.WeightAccumulator.fold_multilinear_arity4
          scale1 point1 alpha alpha2 alpha3 = ok (scale1Out, point1Out))
    (hml2 :
      aspis_core.sumcheck.WeightAccumulator.fold_multilinear_arity4
          scale2 point2 alpha alpha2 alpha3 = ok (scale2Out, point2Out))
    (hgrouped :
      aspis_core.sumcheck.WeightAccumulator.fold_grouped64_binary_deferred_arity4
          rowGroups groupMasks firstAlpha groupValues currentLogLen alpha
            alpha2 alpha3 =
        ok (rowGroups, groupMasksOut, firstAlphaOut, groupValuesOut))
    (hdense :
      aspis_core.sumcheck.WeightAccumulator.fold_dense_arity4
          dense alpha alpha2 alpha3 = ok denseOut) :
    aspis_core.sumcheck.WeightAccumulator.fold_deferred_relation_arity4_loop
        currentLogLen
        (realRelationComponents
          (.Multilinear scale0 point0)
          (.Multilinear scale1 point1)
          (.Multilinear scale2 point2)
          (.Grouped64x16BinaryDeferred rowGroups groupMasks firstAlpha
            groupValues)
          (.Dense dense))
        alpha alpha2 preparedAlpha preparedAlpha2 alpha3 0#usize =
      ok (realRelationComponents
        (.Multilinear scale0Out point0Out)
        (.Multilinear scale1Out point1Out)
        (.Multilinear scale2Out point2Out)
        (.Grouped64x16BinaryDeferred rowGroups groupMasksOut firstAlphaOut
          groupValuesOut)
        (.Dense denseOut)) := by
  unfold
    aspis_core.sumcheck.WeightAccumulator.fold_deferred_relation_arity4_loop
  rw [loop.eq_1]
  unfold
    aspis_core.sumcheck.WeightAccumulator.fold_deferred_relation_arity4_loop.body
  simp [realRelationComponents, alloc.vec.Vec.index_mut_slice_index,
    alloc.vec.Vec.index_mut_usize, alloc.vec.Vec.index_usize,
    alloc.vec.Vec.set, Std.lift, hml0, hml1, hml2, hgrouped, hdense,
    usize_zero_succ, usize_one_succ, usize_two_succ, usize_three_succ,
    usize_four_succ, loop.eq_1]

/-- The Tensor branch used by the generated circle/line OOD accumulators is
the actual indexed traversal branch and forwards precisely `alpha3` and both
prepared caches to `fold_tensor_arity4`. -/
theorem generated_tensor_single_component_traversal_exact
    (currentLogLen : Std.U32)
    (alpha alpha2 alpha3 scale scaleOut : RawQM31)
    (preparedAlpha preparedAlpha2 : RawPrepared)
    (factors factorsOut : alloc.vec.Vec RawQM31)
    (htensor :
      aspis_core.sumcheck.WeightAccumulator.fold_tensor_arity4
          scale factors alpha3 preparedAlpha preparedAlpha2 =
        ok (scaleOut, factorsOut)) :
    aspis_core.sumcheck.WeightAccumulator.fold_deferred_relation_arity4_loop
        currentLogLen (singletonTensorComponents (.Tensor scale factors)) alpha alpha2
          preparedAlpha preparedAlpha2 alpha3 0#usize =
      ok (singletonTensorComponents (.Tensor scaleOut factorsOut)) := by
  unfold
    aspis_core.sumcheck.WeightAccumulator.fold_deferred_relation_arity4_loop
  rw [loop.eq_1]
  unfold
    aspis_core.sumcheck.WeightAccumulator.fold_deferred_relation_arity4_loop.body
  simp [singletonTensorComponents, alloc.vec.Vec.index_mut_slice_index,
    alloc.vec.Vec.index_mut_usize, alloc.vec.Vec.index_usize,
    alloc.vec.Vec.set, Std.lift, htensor, usize_zero_succ, loop.eq_1]

/-- At log length ten the exact deferred branch stores the first challenge
without touching either schedule vector or the as-yet-empty group values. -/
theorem generated_grouped_deferred_log10_exact
    (rowGroups : alloc.vec.Vec Std.U8)
    (groupMasks : alloc.vec.Vec Std.U16)
    (firstAlpha : Option RawQM31)
    (groupValues : alloc.vec.Vec RawQM31)
    (alpha alpha2 alpha3 : RawQM31) :
    aspis_core.sumcheck.WeightAccumulator.fold_grouped64_binary_deferred_arity4
        rowGroups groupMasks firstAlpha groupValues 10#u32 alpha alpha2 alpha3 =
      ok (rowGroups, groupMasks, some alpha, groupValues) := by
  rfl

/-- At log length eight the branch consumes the stored first challenge,
evaluates the complete low-mask table with the two real challenges, clears the
mask vector and clears `first_alpha`. -/
theorem generated_grouped_deferred_log8_exact
    (rowGroups : alloc.vec.Vec Std.U8)
    (groupMasks clearedMasks : alloc.vec.Vec Std.U16)
    (alpha0 alpha alpha2 alpha3 : RawQM31)
    (groupValues foldedValues : alloc.vec.Vec RawQM31)
    (hfold :
      aspis_core.sumcheck.fold_binary_low_masks
          (alloc.vec.Vec.deref groupMasks) alpha0 alpha = ok foldedValues)
    (hclear : alloc.vec.Vec.clear Global groupMasks = ok clearedMasks) :
    aspis_core.sumcheck.WeightAccumulator.fold_grouped64_binary_deferred_arity4
        rowGroups groupMasks (some alpha0) groupValues 8#u32 alpha alpha2 alpha3 =
      ok (rowGroups, clearedMasks, none, foldedValues) := by
  unfold
    aspis_core.sumcheck.WeightAccumulator.fold_grouped64_binary_deferred_arity4
  change (do
    let groupValuesOut ←
      aspis_core.sumcheck.fold_binary_low_masks
        (alloc.vec.Vec.deref groupMasks) alpha0 alpha
    let cleared ← alloc.vec.Vec.clear Global groupMasks
    ok (rowGroups, cleared, none, groupValuesOut)) = _
  rw [hfold, hclear]
  rfl

/-- A missing first challenge at log length eight is the exact generated
panic result, before any grouped-row transform is attempted. -/
theorem generated_grouped_deferred_log8_missing_alpha_fails
    (rowGroups : alloc.vec.Vec Std.U8)
    (groupMasks : alloc.vec.Vec Std.U16)
    (alpha alpha2 alpha3 : RawQM31)
    (groupValues : alloc.vec.Vec RawQM31) :
    aspis_core.sumcheck.WeightAccumulator.fold_grouped64_binary_deferred_arity4
        rowGroups groupMasks none groupValues 8#u32 alpha alpha2 alpha3 =
      fail Error.panic := by
  rfl

/-- At log length six, the exact generated grouped-row transform is installed
without changing the already-cleared mask/first-alpha fields. -/
theorem generated_grouped_deferred_log6_exact
    (rowGroups foldedGroups : alloc.vec.Vec Std.U8)
    (groupMasks : alloc.vec.Vec Std.U16)
    (firstAlpha : Option RawQM31)
    (groupValues foldedValues : alloc.vec.Vec RawQM31)
    (alpha alpha2 alpha3 : RawQM31)
    (hfold :
      aspis_core.sumcheck.fold_grouped_rows
          (alloc.vec.Vec.deref rowGroups) (alloc.vec.Vec.deref groupValues)
            alpha alpha2 alpha3 = ok (foldedGroups, foldedValues)) :
    aspis_core.sumcheck.WeightAccumulator.fold_grouped64_binary_deferred_arity4
        rowGroups groupMasks firstAlpha groupValues 6#u32 alpha alpha2 alpha3 =
      ok (foldedGroups, groupMasks, firstAlpha, foldedValues) := by
  unfold
    aspis_core.sumcheck.WeightAccumulator.fold_grouped64_binary_deferred_arity4
  change (do
    let (groups, values) ←
      aspis_core.sumcheck.fold_grouped_rows
        (alloc.vec.Vec.deref rowGroups) (alloc.vec.Vec.deref groupValues)
          alpha alpha2 alpha3
    ok (groups, groupMasks, firstAlpha, values)) = _
  rw [hfold]
  rfl

/-- The log-four branch repeats precisely the same grouped-row transform; its
output is the final four-entry deferred representation. -/
theorem generated_grouped_deferred_log4_exact
    (rowGroups foldedGroups : alloc.vec.Vec Std.U8)
    (groupMasks : alloc.vec.Vec Std.U16)
    (firstAlpha : Option RawQM31)
    (groupValues foldedValues : alloc.vec.Vec RawQM31)
    (alpha alpha2 alpha3 : RawQM31)
    (hfold :
      aspis_core.sumcheck.fold_grouped_rows
          (alloc.vec.Vec.deref rowGroups) (alloc.vec.Vec.deref groupValues)
            alpha alpha2 alpha3 = ok (foldedGroups, foldedValues)) :
    aspis_core.sumcheck.WeightAccumulator.fold_grouped64_binary_deferred_arity4
        rowGroups groupMasks firstAlpha groupValues 4#u32 alpha alpha2 alpha3 =
      ok (foldedGroups, groupMasks, firstAlpha, foldedValues) := by
  unfold
    aspis_core.sumcheck.WeightAccumulator.fold_grouped64_binary_deferred_arity4
  change (do
    let (groups, values) ←
      aspis_core.sumcheck.fold_grouped_rows
        (alloc.vec.Vec.deref rowGroups) (alloc.vec.Vec.deref groupValues)
          alpha alpha2 alpha3
    ok (groups, groupMasks, firstAlpha, values)) = _
  rw [hfold]
  rfl

/-- Exact outer call for the real five-component relation sequence.  This is
the source-level composition point for the primitive arithmetic theorems: the
result states the complete component order and the exact log transition. -/
theorem generated_real_five_component_fold_exact
    (currentLogLen : Std.U32)
    (alpha alpha2 alpha3 : RawQM31)
    (preparedAlpha preparedAlpha2 : RawPrepared)
    (scale0 scale1 scale2 scale0Out scale1Out scale2Out : RawQM31)
    (point0 point1 point2 point0Out point1Out point2Out :
      alloc.vec.Vec RawQM31)
    (rowGroups : alloc.vec.Vec Std.U8)
    (groupMasks groupMasksOut : alloc.vec.Vec Std.U16)
    (firstAlpha firstAlphaOut : Option RawQM31)
    (groupValues groupValuesOut dense denseOut : alloc.vec.Vec RawQM31)
    (hsquare : aspis_core.field.QM31.square alpha = ok alpha2)
    (hprepareAlpha :
      aspis_core.field.PreparedQm31Multiplier.new alpha = ok preparedAlpha)
    (hprepareAlpha2 :
      aspis_core.field.PreparedQm31Multiplier.new alpha2 = ok preparedAlpha2)
    (halpha3 :
      aspis_core.field.PreparedQm31Multiplier.mul preparedAlpha alpha2 =
        ok alpha3)
    (hml0 :
      aspis_core.sumcheck.WeightAccumulator.fold_multilinear_arity4
          scale0 point0 alpha alpha2 alpha3 = ok (scale0Out, point0Out))
    (hml1 :
      aspis_core.sumcheck.WeightAccumulator.fold_multilinear_arity4
          scale1 point1 alpha alpha2 alpha3 = ok (scale1Out, point1Out))
    (hml2 :
      aspis_core.sumcheck.WeightAccumulator.fold_multilinear_arity4
          scale2 point2 alpha alpha2 alpha3 = ok (scale2Out, point2Out))
    (hgrouped :
      aspis_core.sumcheck.WeightAccumulator.fold_grouped64_binary_deferred_arity4
          rowGroups groupMasks firstAlpha groupValues currentLogLen alpha
            alpha2 alpha3 =
        ok (rowGroups, groupMasksOut, firstAlphaOut, groupValuesOut))
    (hdense :
      aspis_core.sumcheck.WeightAccumulator.fold_dense_arity4
          dense alpha alpha2 alpha3 = ok denseOut) :
    aspis_core.sumcheck.WeightAccumulator.fold_deferred_relation_arity4
        { log_len := currentLogLen
          components := realRelationComponents
            (.Multilinear scale0 point0)
            (.Multilinear scale1 point1)
            (.Multilinear scale2 point2)
            (.Grouped64x16BinaryDeferred rowGroups groupMasks firstAlpha
              groupValues)
            (.Dense dense) }
        alpha =
      ok {
        log_len := Std.U32.wrapping_sub currentLogLen 2#u32
        components := realRelationComponents
          (.Multilinear scale0Out point0Out)
          (.Multilinear scale1Out point1Out)
          (.Multilinear scale2Out point2Out)
          (.Grouped64x16BinaryDeferred rowGroups groupMasksOut firstAlphaOut
            groupValuesOut)
          (.Dense denseOut) } := by
  unfold aspis_core.sumcheck.WeightAccumulator.fold_deferred_relation_arity4
  rw [hsquare]
  simp only [bind_tc_ok]
  rw [hprepareAlpha]
  simp only [bind_tc_ok]
  rw [hprepareAlpha2]
  simp only [bind_tc_ok]
  rw [halpha3]
  simp only [bind_tc_ok]
  rw [generated_real_five_component_traversal_exact currentLogLen alpha alpha2
    alpha3 preparedAlpha preparedAlpha2 scale0 scale1 scale2 scale0Out
    scale1Out scale2Out point0 point1 point2 point0Out point1Out point2Out
    rowGroups groupMasks groupMasksOut firstAlpha firstAlphaOut groupValues
    groupValuesOut dense denseOut hml0 hml1 hml2 hgrouped hdense]
  rfl

/-- The exact current-source calls made by one successful invocation of the
specialized public relation fold.  In particular, this records the actual
`alpha`, `alpha^2`, prepared-cache and `alpha^3` values passed to the indexed
component traversal, as well as its source `log_len - 2` update. -/
structure GeneratedDeferredFoldStep
    (input : Accumulator) (alpha : RawQM31) (output : Accumulator) where
  alpha2 : RawQM31
  preparedAlpha : RawPrepared
  preparedAlpha2 : RawPrepared
  alpha3 : RawQM31
  componentsOut : alloc.vec.Vec Component
  square_run : aspis_core.field.QM31.square alpha = ok alpha2
  prepare_alpha_run :
    aspis_core.field.PreparedQm31Multiplier.new alpha = ok preparedAlpha
  prepare_alpha2_run :
    aspis_core.field.PreparedQm31Multiplier.new alpha2 = ok preparedAlpha2
  alpha3_run :
    aspis_core.field.PreparedQm31Multiplier.mul preparedAlpha alpha2 =
      ok alpha3
  traversal_run :
    aspis_core.sumcheck.WeightAccumulator.fold_deferred_relation_arity4_loop
        input.log_len input.components alpha alpha2 preparedAlpha
          preparedAlpha2 alpha3 0#usize = ok componentsOut
  output_eq : output = {
    log_len := Std.U32.wrapping_sub input.log_len 2#u32
    components := componentsOut
  }

/-- Success of the actual generated wrapper exposes its whole preprocessing,
indexed component traversal, and log-length transition. -/
def generatedDeferredFoldSuccessWitness
    (input output : Accumulator) (alpha : RawQM31)
    (hrun :
      aspis_core.sumcheck.WeightAccumulator.fold_deferred_relation_arity4
          input alpha = ok output) :
    GeneratedDeferredFoldStep input alpha output := by
  unfold
    aspis_core.sumcheck.WeightAccumulator.fold_deferred_relation_arity4 at hrun
  generalize hsquare : aspis_core.field.QM31.square alpha = squareResult at hrun
  cases squareResult with
  | fail error => simp at hrun
  | div => simp at hrun
  | ok alpha2 =>
    simp only [bind_tc_ok] at hrun
    generalize hprepareAlpha :
        aspis_core.field.PreparedQm31Multiplier.new alpha = prepareAlphaResult
      at hrun
    cases prepareAlphaResult with
    | fail error => simp at hrun
    | div => simp at hrun
    | ok preparedAlpha =>
      simp only [bind_tc_ok] at hrun
      generalize hprepareAlpha2 :
          aspis_core.field.PreparedQm31Multiplier.new alpha2 =
            prepareAlpha2Result at hrun
      cases prepareAlpha2Result with
      | fail error => simp at hrun
      | div => simp at hrun
      | ok preparedAlpha2 =>
        simp only [bind_tc_ok] at hrun
        generalize halpha3 :
            aspis_core.field.PreparedQm31Multiplier.mul preparedAlpha alpha2 =
              alpha3Result at hrun
        cases alpha3Result with
        | fail error => simp at hrun
        | div => simp at hrun
        | ok alpha3 =>
          simp only [bind_tc_ok] at hrun
          generalize htraversal :
              aspis_core.sumcheck.WeightAccumulator.fold_deferred_relation_arity4_loop
                  input.log_len input.components alpha alpha2 preparedAlpha
                    preparedAlpha2 alpha3 0#usize = traversalResult at hrun
          cases traversalResult with
          | fail error => simp at hrun
          | div => simp at hrun
          | ok componentsOut =>
            simp only [bind_tc_ok, Std.lift] at hrun
            cases hrun
            exact {
              alpha2 := alpha2
              preparedAlpha := preparedAlpha
              preparedAlpha2 := preparedAlpha2
              alpha3 := alpha3
              componentsOut := componentsOut
              square_run := hsquare
              prepare_alpha_run := hprepareAlpha
              prepare_alpha2_run := hprepareAlpha2
              alpha3_run := halpha3
              traversal_run := htraversal
              output_eq := rfl
            }

theorem generated_deferred_fold_success_has_exact_step
    (input output : Accumulator) (alpha : RawQM31)
    (hrun :
      aspis_core.sumcheck.WeightAccumulator.fold_deferred_relation_arity4
          input alpha = ok output) :
    Nonempty (GeneratedDeferredFoldStep input alpha output) :=
  ⟨generatedDeferredFoldSuccessWitness input output alpha hrun⟩

/-- The component-traversal failure is returned unchanged by the actual
generated public helper once preprocessing has succeeded. -/
theorem generated_deferred_fold_traversal_failure_propagates
    (input : Accumulator) (alpha alpha2 alpha3 : RawQM31)
    (preparedAlpha preparedAlpha2 : RawPrepared) (error : Error)
    (hsquare : aspis_core.field.QM31.square alpha = ok alpha2)
    (hprepareAlpha :
      aspis_core.field.PreparedQm31Multiplier.new alpha = ok preparedAlpha)
    (hprepareAlpha2 :
      aspis_core.field.PreparedQm31Multiplier.new alpha2 = ok preparedAlpha2)
    (halpha3 :
      aspis_core.field.PreparedQm31Multiplier.mul preparedAlpha alpha2 =
        ok alpha3)
    (htraversal :
      aspis_core.sumcheck.WeightAccumulator.fold_deferred_relation_arity4_loop
          input.log_len input.components alpha alpha2 preparedAlpha
            preparedAlpha2 alpha3 0#usize = fail error) :
    aspis_core.sumcheck.WeightAccumulator.fold_deferred_relation_arity4
        input alpha = fail error := by
  simp [aspis_core.sumcheck.WeightAccumulator.fold_deferred_relation_arity4,
    hsquare, hprepareAlpha, hprepareAlpha2, halpha3, htraversal]

theorem generated_deferred_fold_square_failure_propagates
    (input : Accumulator) (alpha : RawQM31) (error : Error)
    (hsquare : aspis_core.field.QM31.square alpha = fail error) :
    aspis_core.sumcheck.WeightAccumulator.fold_deferred_relation_arity4
        input alpha = fail error := by
  simp [aspis_core.sumcheck.WeightAccumulator.fold_deferred_relation_arity4,
    hsquare]

theorem generated_deferred_fold_prepare_alpha_failure_propagates
    (input : Accumulator) (alpha alpha2 : RawQM31) (error : Error)
    (hsquare : aspis_core.field.QM31.square alpha = ok alpha2)
    (hprepare :
      aspis_core.field.PreparedQm31Multiplier.new alpha = fail error) :
    aspis_core.sumcheck.WeightAccumulator.fold_deferred_relation_arity4
        input alpha = fail error := by
  simp [aspis_core.sumcheck.WeightAccumulator.fold_deferred_relation_arity4,
    hsquare, hprepare]

theorem generated_deferred_fold_prepare_alpha2_failure_propagates
    (input : Accumulator) (alpha alpha2 : RawQM31)
    (preparedAlpha : RawPrepared) (error : Error)
    (hsquare : aspis_core.field.QM31.square alpha = ok alpha2)
    (hprepareAlpha :
      aspis_core.field.PreparedQm31Multiplier.new alpha = ok preparedAlpha)
    (hprepareAlpha2 :
      aspis_core.field.PreparedQm31Multiplier.new alpha2 = fail error) :
    aspis_core.sumcheck.WeightAccumulator.fold_deferred_relation_arity4
        input alpha = fail error := by
  simp [aspis_core.sumcheck.WeightAccumulator.fold_deferred_relation_arity4,
    hsquare, hprepareAlpha, hprepareAlpha2]

theorem generated_deferred_fold_alpha3_failure_propagates
    (input : Accumulator) (alpha alpha2 : RawQM31)
    (preparedAlpha preparedAlpha2 : RawPrepared) (error : Error)
    (hsquare : aspis_core.field.QM31.square alpha = ok alpha2)
    (hprepareAlpha :
      aspis_core.field.PreparedQm31Multiplier.new alpha = ok preparedAlpha)
    (hprepareAlpha2 :
      aspis_core.field.PreparedQm31Multiplier.new alpha2 = ok preparedAlpha2)
    (halpha3 :
      aspis_core.field.PreparedQm31Multiplier.mul preparedAlpha alpha2 =
        fail error) :
    aspis_core.sumcheck.WeightAccumulator.fold_deferred_relation_arity4
        input alpha = fail error := by
  simp [aspis_core.sumcheck.WeightAccumulator.fold_deferred_relation_arity4,
    hsquare, hprepareAlpha, hprepareAlpha2, halpha3]

/-- Exact four-round execution record for the current Component-C relation
accumulator.  `after3` is intentionally retained: it is the live log-4,
Fin-16 state materialized for the fourth relation polynomial. -/
structure GeneratedFourRoundDeferredFold
    (initial : Accumulator) (alphas : Array RawQM31 4#usize)
    (final : Accumulator) where
  after1 : Accumulator
  after2 : Accumulator
  after3 : Accumulator
  step0 : GeneratedDeferredFoldStep initial alphas.val[0]! after1
  step1 : GeneratedDeferredFoldStep after1 alphas.val[1]! after2
  step2 : GeneratedDeferredFoldStep after2 alphas.val[2]! after3
  step3 : GeneratedDeferredFoldStep after3 alphas.val[3]! final
  initial_log_len : initial.log_len = 10#u32
  after1_log_len : after1.log_len = 8#u32
  after2_log_len : after2.log_len = 6#u32
  after3_log_len : after3.log_len = 4#u32
  final_log_len : final.log_len = 2#u32

private theorem wrapping_sub_two_10 :
    Std.U32.wrapping_sub 10#u32 2#u32 = 8#u32 := by decide

private theorem wrapping_sub_two_8 :
    Std.U32.wrapping_sub 8#u32 2#u32 = 6#u32 := by decide

private theorem wrapping_sub_two_6 :
    Std.U32.wrapping_sub 6#u32 2#u32 = 4#u32 := by decide

private theorem wrapping_sub_two_4 :
    Std.U32.wrapping_sub 4#u32 2#u32 = 2#u32 := by decide

/-- Four successful actual calls give the exact log-10/8/6/4/2 transition
and preserve every per-round generated call in an importable witness. -/
def generatedFourRoundDeferredFoldWitness
    (initial after1 after2 after3 final : Accumulator)
    (alphas : Array RawQM31 4#usize)
    (hinitialLog : initial.log_len = 10#u32)
    (hrun0 :
      aspis_core.sumcheck.WeightAccumulator.fold_deferred_relation_arity4
          initial alphas.val[0]! = ok after1)
    (hrun1 :
      aspis_core.sumcheck.WeightAccumulator.fold_deferred_relation_arity4
          after1 alphas.val[1]! = ok after2)
    (hrun2 :
      aspis_core.sumcheck.WeightAccumulator.fold_deferred_relation_arity4
          after2 alphas.val[2]! = ok after3)
    (hrun3 :
      aspis_core.sumcheck.WeightAccumulator.fold_deferred_relation_arity4
          after3 alphas.val[3]! = ok final) :
    GeneratedFourRoundDeferredFold initial alphas final := by
  have hstep0 := generatedDeferredFoldSuccessWitness
    initial after1 alphas.val[0]! hrun0
  have hstep1 := generatedDeferredFoldSuccessWitness
    after1 after2 alphas.val[1]! hrun1
  have hstep2 := generatedDeferredFoldSuccessWitness
    after2 after3 alphas.val[2]! hrun2
  have hstep3 := generatedDeferredFoldSuccessWitness
    after3 final alphas.val[3]! hrun3
  have hlog1 : after1.log_len = 8#u32 := by
    rw [hstep0.output_eq, hinitialLog, wrapping_sub_two_10]
  have hlog2 : after2.log_len = 6#u32 := by
    rw [hstep1.output_eq, hlog1, wrapping_sub_two_8]
  have hlog3 : after3.log_len = 4#u32 := by
    rw [hstep2.output_eq, hlog2, wrapping_sub_two_6]
  have hlog4 : final.log_len = 2#u32 := by
    rw [hstep3.output_eq, hlog3, wrapping_sub_two_4]
  exact {
    after1 := after1
    after2 := after2
    after3 := after3
    step0 := hstep0
    step1 := hstep1
    step2 := hstep2
    step3 := hstep3
    initial_log_len := hinitialLog
    after1_log_len := hlog1
    after2_log_len := hlog2
    after3_log_len := hlog3
    final_log_len := hlog4
  }

theorem generated_four_round_deferred_fold_exact
    (initial after1 after2 after3 final : Accumulator)
    (alphas : Array RawQM31 4#usize)
    (hinitialLog : initial.log_len = 10#u32)
    (hrun0 :
      aspis_core.sumcheck.WeightAccumulator.fold_deferred_relation_arity4
          initial alphas.val[0]! = ok after1)
    (hrun1 :
      aspis_core.sumcheck.WeightAccumulator.fold_deferred_relation_arity4
          after1 alphas.val[1]! = ok after2)
    (hrun2 :
      aspis_core.sumcheck.WeightAccumulator.fold_deferred_relation_arity4
          after2 alphas.val[2]! = ok after3)
    (hrun3 :
      aspis_core.sumcheck.WeightAccumulator.fold_deferred_relation_arity4
          after3 alphas.val[3]! = ok final) :
    Nonempty (GeneratedFourRoundDeferredFold initial alphas final) :=
  ⟨generatedFourRoundDeferredFoldWitness initial after1 after2 after3 final
    alphas hinitialLog hrun0 hrun1 hrun2 hrun3⟩

/-- The retained pre-fourth-fold state really has the complete Fin-16 index
domain required by the released round-3 materialized table. -/
theorem generated_four_round_fin16_state
    (initial : Accumulator) (alphas : Array RawQM31 4#usize)
    (final : Accumulator)
    (trace : GeneratedFourRoundDeferredFold initial alphas final) :
    trace.after3.log_len = 4#u32 ∧
      ∀ index : Fin 16, index.val < 2 ^ trace.after3.log_len.val := by
  constructor
  · exact trace.after3_log_len
  · intro index
    rw [trace.after3_log_len]
    norm_num

#print axioms generated_deferred_fold_success_has_exact_step
#print axioms generated_deferred_fold_traversal_failure_propagates
#print axioms generated_deferred_fold_square_failure_propagates
#print axioms generated_deferred_fold_prepare_alpha_failure_propagates
#print axioms generated_deferred_fold_prepare_alpha2_failure_propagates
#print axioms generated_deferred_fold_alpha3_failure_propagates
#print axioms generated_real_five_component_traversal_exact
#print axioms generated_tensor_single_component_traversal_exact
#print axioms generated_grouped_deferred_log10_exact
#print axioms generated_grouped_deferred_log8_exact
#print axioms generated_grouped_deferred_log8_missing_alpha_fails
#print axioms generated_grouped_deferred_log6_exact
#print axioms generated_grouped_deferred_log4_exact
#print axioms generated_real_five_component_fold_exact
#print axioms generated_four_round_deferred_fold_exact
#print axioms generated_four_round_fin16_state

end ComponentCRuntimeCanonicalGenerated.RuntimeWeightAccumulatorFoldLevel3
