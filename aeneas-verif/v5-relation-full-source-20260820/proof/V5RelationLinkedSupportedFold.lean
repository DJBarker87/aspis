import V5RelationLinkedWeightPath

/-!
# Reachable production weight components

The released relation verifier starts with multilinear, dense, and deferred
grouped-binary components and appends tensor components for the two OOD
observations in each round.  No other `WeightComponent` constructor is
reachable on that path.

This file proves directly on the complete Charon/Aeneas extraction that the
ordinary production dispatcher sends each of those four constructors to the
same component-specific helper, returns no replacement constructor, and
preserves the reachable constructor family on every successful call.
-/

namespace AspisV5RelationLinkedSupportedFold

open Aeneas Aeneas.Std Result

abbrev RawQM31 := V5RelationLinkedGenerated.aspis_core.field.QM31
abbrev RawPrepared :=
  V5RelationLinkedGenerated.aspis_core.field.PreparedQm31Multiplier
abbrev Component :=
  V5RelationLinkedGenerated.aspis_core.sumcheck.WeightComponent

/-- Exactly the component variants used by the released relation path. -/
def ReleasedComponent : Component -> Prop
  | .Multilinear _ _ => True
  | .Tensor _ _ => True
  | .Dense _ => True
  | .Grouped64x16BinaryDeferred _ _ _ _ => True
  | _ => False

theorem fold_component_multilinear_exact
    (scale scaleOut : RawQM31)
    (point pointOut : alloc.vec.Vec RawQM31)
    (currentLog : Std.U32) (alpha alpha2 alpha3 : RawQM31)
    (preparedAlpha preparedAlpha2 : RawPrepared)
    (helperRun :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_multilinear_arity4
          scale point alpha alpha2 alpha3 = .ok (scaleOut, pointOut)) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_component_arity4
        (.Multilinear scale point) currentLog alpha alpha2 alpha3
          preparedAlpha preparedAlpha2 =
      .ok (none, .Multilinear scaleOut pointOut) := by
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_component_arity4,
    helperRun]

theorem fold_component_tensor_exact
    (scale scaleOut : RawQM31)
    (factors factorsOut : alloc.vec.Vec RawQM31)
    (currentLog : Std.U32) (alpha alpha2 alpha3 : RawQM31)
    (preparedAlpha preparedAlpha2 : RawPrepared)
    (helperRun :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_tensor_arity4
          scale factors alpha3 preparedAlpha preparedAlpha2 =
        .ok (scaleOut, factorsOut)) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_component_arity4
        (.Tensor scale factors) currentLog alpha alpha2 alpha3
          preparedAlpha preparedAlpha2 =
      .ok (none, .Tensor scaleOut factorsOut) := by
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_component_arity4,
    helperRun]

theorem fold_component_dense_exact
    (values valuesOut : alloc.vec.Vec RawQM31)
    (currentLog : Std.U32) (alpha alpha2 alpha3 : RawQM31)
    (preparedAlpha preparedAlpha2 : RawPrepared)
    (helperRun :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_dense_arity4
          values alpha alpha2 alpha3 = .ok valuesOut) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_component_arity4
        (.Dense values) currentLog alpha alpha2 alpha3
          preparedAlpha preparedAlpha2 =
      .ok (none, .Dense valuesOut) := by
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_component_arity4,
    helperRun]

theorem fold_component_grouped_deferred_exact
    (rowGroups rowGroupsOut : alloc.vec.Vec Std.U8)
    (groupMasks groupMasksOut : alloc.vec.Vec Std.U16)
    (firstAlpha firstAlphaOut : Option RawQM31)
    (groupValues groupValuesOut : alloc.vec.Vec RawQM31)
    (currentLog : Std.U32) (alpha alpha2 alpha3 : RawQM31)
    (preparedAlpha preparedAlpha2 : RawPrepared)
    (helperRun :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_grouped64_binary_deferred_arity4
          rowGroups groupMasks firstAlpha groupValues currentLog alpha alpha2
            alpha3 =
        .ok (rowGroupsOut, groupMasksOut, firstAlphaOut, groupValuesOut)) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_component_arity4
        (.Grouped64x16BinaryDeferred rowGroups groupMasks firstAlpha groupValues)
          currentLog alpha alpha2 alpha3 preparedAlpha preparedAlpha2 =
      .ok (none, .Grouped64x16BinaryDeferred rowGroupsOut groupMasksOut
        firstAlphaOut groupValuesOut) := by
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_component_arity4,
    helperRun]

/-- A successful generic dispatch on a released component cannot take the
replacement path and its output is again a released component. -/
theorem released_component_success_no_replacement
    (component componentOut : Component)
    (replacement : Option Component)
    (currentLog : Std.U32) (alpha alpha2 alpha3 : RawQM31)
    (preparedAlpha preparedAlpha2 : RawPrepared)
    (released : ReleasedComponent component)
    (success :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_component_arity4
          component currentLog alpha alpha2 alpha3 preparedAlpha preparedAlpha2 =
        .ok (replacement, componentOut)) :
    replacement = none /\ ReleasedComponent componentOut := by
  cases component <;> simp [ReleasedComponent] at released
  case Multilinear scale point =>
    simp only [
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_component_arity4]
      at success
    generalize helperRun :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_multilinear_arity4
          scale point alpha alpha2 alpha3 = helperResult at success
    cases helperResult with
    | fail error => simp at success
    | div => simp at success
    | ok pair =>
      simp only [bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at success
      rcases success with ⟨rfl, rfl⟩
      exact ⟨rfl, trivial⟩
  case Tensor scale factors =>
    simp only [
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_component_arity4]
      at success
    generalize helperRun :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_tensor_arity4
          scale factors alpha3 preparedAlpha preparedAlpha2 = helperResult at success
    cases helperResult with
    | fail error => simp at success
    | div => simp at success
    | ok pair =>
      simp only [bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at success
      rcases success with ⟨rfl, rfl⟩
      exact ⟨rfl, trivial⟩
  case Dense values =>
    simp only [
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_component_arity4]
      at success
    generalize helperRun :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_dense_arity4
          values alpha alpha2 alpha3 = helperResult at success
    cases helperResult with
    | fail error => simp at success
    | div => simp at success
    | ok value =>
      simp only [bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at success
      rcases success with ⟨rfl, rfl⟩
      exact ⟨rfl, trivial⟩
  case Grouped64x16BinaryDeferred rowGroups groupMasks firstAlpha groupValues =>
    simp only [
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_component_arity4]
      at success
    generalize helperRun :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_grouped64_binary_deferred_arity4
          rowGroups groupMasks firstAlpha groupValues currentLog alpha alpha2
            alpha3 = helperResult at success
    cases helperResult with
    | fail error => simp at success
    | div => simp at success
    | ok value =>
      simp only [bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at success
      rcases success with ⟨rfl, rfl⟩
      exact ⟨rfl, trivial⟩

#print axioms fold_component_multilinear_exact
#print axioms fold_component_tensor_exact
#print axioms fold_component_dense_exact
#print axioms fold_component_grouped_deferred_exact
#print axioms released_component_success_no_replacement

end AspisV5RelationLinkedSupportedFold
