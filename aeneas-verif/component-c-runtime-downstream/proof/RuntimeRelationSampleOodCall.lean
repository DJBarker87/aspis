import RuntimeOodWithTableArithmetic

set_option autoImplicit false

open Aeneas Aeneas.Std Result

namespace aspis_prover.ComponentCRuntimeRelationSampleOodCall

open aspis_prover

abbrev RawQM31 := aspis_core.field.QM31
abbrev RuntimeSchedule :=
  v5_mask.component_c_runtime.V5ComponentCRuntimeSchedule
abbrev RuntimeRelation :=
  v5_mask.relation_prover.V5IncrementalRelation
abbrev RuntimeTables :=
  v5_mask.component_c_runtime.V5ComponentCRuntimeRelationTables

/-- A successful generated round-zero sample necessarily executed the actual
circle-OOD-with-table method successfully, at the exact point read from the
runtime schedule. -/
theorem generated_circle_sample_success_has_ood_call
    (schedule : RuntimeSchedule)
    (relation relationOut : RuntimeRelation)
    (tables tablesOut : RuntimeTables)
    (sample : Std.Usize)
    (hrun :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_sample
          schedule relation tables 0#usize sample =
        ok (core.result.Result.Ok (), relationOut, tablesOut)) :
    ∃ point value table,
      Array.index_usize schedule.circle_ood_points sample = ok point ∧
      v5_mask.relation_prover.V5IncrementalRelation.evaluate_circle_ood_with_table
          relation point = ok (core.result.Result.Ok (value, table)) := by
  unfold
    v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_sample
    at hrun
  generalize hpoint :
      Array.index_usize schedule.circle_ood_points sample = pointResult at hrun
  cases pointResult with
  | fail error => simp at hrun
  | div => simp at hrun
  | ok point =>
    simp only [bind_tc_ok] at hrun
    generalize hood :
        v5_mask.relation_prover.V5IncrementalRelation.evaluate_circle_ood_with_table
            relation point = oodResult at hrun
    cases oodResult with
    | fail error => simp at hrun
    | div => simp at hrun
    | ok oodStatus =>
      cases oodStatus with
      | Err oodError =>
        simp [
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          v5_mask.component_c_runtime.V5ComponentCRuntimeError.Insts.CoreConvertFromV5RelationProverError.from]
          at hrun
      | Ok valueAndTable =>
        rcases valueAndTable with ⟨value, table⟩
        exact ⟨point, value, table, rfl, hood⟩

/-- Every successful nonzero-round sample similarly exposes the exact line
point schedule read and successful line-OOD-with-table call. -/
theorem generated_line_sample_success_has_ood_call
    (schedule : RuntimeSchedule)
    (relation relationOut : RuntimeRelation)
    (tables tablesOut : RuntimeTables)
    (round sample : Std.Usize)
    (hround : round ≠ 0#usize)
    (hrun :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_sample
          schedule relation tables round sample =
        ok (core.result.Result.Ok (), relationOut, tablesOut)) :
    ∃ layer layerPoints point value table,
      lift (Std.Usize.wrapping_sub round 1#usize) = ok layer ∧
      Array.index_usize schedule.line_ood_points layer = ok layerPoints ∧
      Array.index_usize layerPoints sample = ok point ∧
      v5_mask.relation_prover.V5IncrementalRelation.evaluate_line_ood_with_table
          relation point = ok (core.result.Result.Ok (value, table)) := by
  unfold
    v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_sample
    at hrun
  simp only [if_neg hround] at hrun
  generalize hlayer :
      lift (Std.Usize.wrapping_sub round 1#usize) = layerResult at hrun
  cases layerResult with
  | fail error => simp at hrun
  | div => simp at hrun
  | ok layer =>
    simp only [bind_tc_ok] at hrun
    generalize hlayerPoints :
        Array.index_usize schedule.line_ood_points layer =
          layerPointsResult at hrun
    cases layerPointsResult with
    | fail error => simp at hrun
    | div => simp at hrun
    | ok layerPoints =>
      simp only [bind_tc_ok] at hrun
      generalize hpoint :
          Array.index_usize layerPoints sample = pointResult at hrun
      cases pointResult with
      | fail error => simp at hrun
      | div => simp at hrun
      | ok point =>
        simp only [bind_tc_ok] at hrun
        generalize hood :
            v5_mask.relation_prover.V5IncrementalRelation.evaluate_line_ood_with_table
                relation point = oodResult at hrun
        cases oodResult with
        | fail error => simp at hrun
        | div => simp at hrun
        | ok oodStatus =>
          cases oodStatus with
          | Err oodError =>
            simp [
              core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              v5_mask.component_c_runtime.V5ComponentCRuntimeError.Insts.CoreConvertFromV5RelationProverError.from]
              at hrun
          | Ok valueAndTable =>
            rcases valueAndTable with ⟨value, table⟩
            exact ⟨layer, layerPoints, point, value, table,
              rfl, hlayerPoints, hpoint, hood⟩

#print axioms generated_circle_sample_success_has_ood_call
#print axioms generated_line_sample_success_has_ood_call

end aspis_prover.ComponentCRuntimeRelationSampleOodCall
