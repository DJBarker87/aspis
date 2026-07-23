import RuntimeRelationSampleStorage

set_option autoImplicit false

open Aeneas Aeneas.Std Result

namespace aspis_prover.ComponentCRuntimeRelationFinishProvenance

open aspis_prover

abbrev RawQM31 := aspis_core.field.QM31
abbrev RuntimeRelation :=
  v5_mask.relation_prover.V5IncrementalRelation
abbrev RuntimeTrace := v5_mask.relation_prover.V5RelationTrace

/-- The source-authentic `finish` routine releases the accumulated OOD and
sumcheck arrays verbatim.  All final consistency checks execute before this
record is returned; none can reindex these two fields. -/
theorem generated_finish_success_preserves_released_arrays
    (relation : RuntimeRelation) (trace : RuntimeTrace)
    (hrun :
      v5_mask.relation_prover.V5IncrementalRelation.finish relation =
        ok (core.result.Result.Ok trace)) :
    trace.ood_values = relation.ood_values ∧
    trace.sumchecks = relation.sumchecks ∧
    trace.running_claims = relation.running_claims ∧
    trace.point_claims = relation.point_claims ∧
    trace.terminal_claim = relation.terminal_claim := by
  unfold v5_mask.relation_prover.V5IncrementalRelation.finish at hrun
  by_cases hround :
      (relation.round != aspis_core.circle_prefix.CANDIDATE_ROUND_COUNT) = true
  · simp [hround] at hrun
  · simp only [hround, Bool.false_eq_true, if_false] at hrun
    by_cases hsamples : (relation.samples != 0#usize) = true
    · simp [hsamples] at hrun
    · simp only [hsamples, Bool.false_eq_true, if_false] at hrun
      generalize hfinalLen :
          aspis_core.circle_prefix.CANDIDATE_FINAL_POLY_LEN = finalLenResult
        at hrun
      cases finalLenResult with
      | fail error => simp at hrun
      | div => simp at hrun
      | ok finalLen =>
        simp only [bind_tc_ok] at hrun
        by_cases hlength : (alloc.vec.Vec.len relation.coefficients != finalLen) = true
        · simp [hlength] at hrun
        · simp only [hlength, Bool.false_eq_true, if_false] at hrun
          generalize hslice :
              alloc.vec.Vec.as_slice Global relation.coefficients = sliceResult
            at hrun
          cases sliceResult with
          | fail error => simp at hrun
          | div => simp at hrun
          | ok coefficientsSlice =>
            simp only [bind_tc_ok] at hrun
            generalize harray :
                core.array.TryFromArrayCopySlice.try_from 4#usize
                    aspis_core.field.QM31.Insts.CoreMarkerCopy coefficientsSlice =
                  arrayResult at hrun
            cases arrayResult with
            | fail error => simp at hrun
            | div => simp at hrun
            | ok arrayStatus =>
              cases arrayStatus with
              | Err arrayError =>
                simp [core.result.Result.map_err,
                  v5_mask.relation_prover.V5IncrementalRelation.finish.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorV5RelationProverError.call_once,
                  v5_mask.relation_prover.V5IncrementalRelation.finish.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorV5RelationProverError.call_once,
                  core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                  core.convert.FromSame.from] at hrun
              | Ok finalCoefficients =>
                simp only [core.result.Result.map_err, bind_tc_ok,
                  core.result.Result.Insts.CoreOpsTry.branch,
                  Std.lift] at hrun
                let finalSlice := Array.to_slice finalCoefficients
                change (do
                    let q ← aspis_core.sumcheck.WeightAccumulator.dot
                      relation.weights finalSlice
                    let b ← core.cmp.PartialEq.ne.trait_default
                      aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 q
                      relation.running_claim
                    if b = true then
                      ok (core.result.Result.Err
                        v5_mask.relation_prover.V5RelationProverError.FoldMismatch)
                    else
                      ok (core.result.Result.Ok {
                        point_claims := relation.point_claims,
                        terminal_claim := relation.terminal_claim,
                        ood_values := relation.ood_values,
                        sumchecks := relation.sumchecks,
                        running_claims := relation.running_claims,
                        final_coefficients := finalCoefficients })) =
                  ok (core.result.Result.Ok trace) at hrun
                generalize hdot :
                    aspis_core.sumcheck.WeightAccumulator.dot
                        relation.weights finalSlice = dotResult at hrun
                cases dotResult with
                | fail error => simp at hrun
                | div => simp at hrun
                | ok dot =>
                  simp only [bind_tc_ok] at hrun
                  generalize hne :
                      core.cmp.PartialEq.ne.trait_default
                          aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
                          dot relation.running_claim = neResult at hrun
                  cases neResult with
                  | fail error => simp at hrun
                  | div => simp at hrun
                  | ok differs =>
                    by_cases hdiffers : differs = true
                    · simp [hdiffers] at hrun
                    · simp only [hdiffers] at hrun
                      cases hrun
                      exact ⟨rfl, rfl, rfl, rfl, rfl⟩

#print axioms generated_finish_success_preserves_released_arrays

/-- Successful `finish` copies the four-element generated coefficient vector
into the public trace's fixed array without reordering or conversion. -/
theorem generated_finish_success_preserves_final_coefficients
    (relation : RuntimeRelation) (trace : RuntimeTrace)
    (hrun :
      v5_mask.relation_prover.V5IncrementalRelation.finish relation =
        ok (core.result.Result.Ok trace)) :
    trace.final_coefficients.val = relation.coefficients.val := by
  unfold v5_mask.relation_prover.V5IncrementalRelation.finish at hrun
  by_cases hround :
      (relation.round != aspis_core.circle_prefix.CANDIDATE_ROUND_COUNT) = true
  · simp [hround] at hrun
  · simp only [hround, Bool.false_eq_true, if_false] at hrun
    by_cases hsamples : (relation.samples != 0#usize) = true
    · simp [hsamples] at hrun
    · simp only [hsamples, Bool.false_eq_true, if_false] at hrun
      generalize hfinalLen :
          aspis_core.circle_prefix.CANDIDATE_FINAL_POLY_LEN = finalLenResult
        at hrun
      cases finalLenResult with
      | fail error => simp at hrun
      | div => simp at hrun
      | ok finalLen =>
        simp only [bind_tc_ok] at hrun
        by_cases hlength :
            (alloc.vec.Vec.len relation.coefficients != finalLen) = true
        · simp [hlength] at hrun
        · simp only [hlength, Bool.false_eq_true, if_false] at hrun
          generalize hslice :
              alloc.vec.Vec.as_slice Global relation.coefficients =
                sliceResult at hrun
          cases sliceResult with
          | fail error => simp at hrun
          | div => simp at hrun
          | ok coefficientsSlice =>
            simp only [bind_tc_ok] at hrun
            have hsliceVal :
                coefficientsSlice.val = relation.coefficients.val := by
              unfold alloc.vec.Vec.as_slice at hslice
              simp only at hslice
              cases hslice
              rfl
            generalize harray :
                core.array.TryFromArrayCopySlice.try_from 4#usize
                    aspis_core.field.QM31.Insts.CoreMarkerCopy
                    coefficientsSlice = arrayResult at hrun
            cases arrayResult with
            | fail error => simp at hrun
            | div => simp at hrun
            | ok arrayStatus =>
              cases arrayStatus with
              | Err arrayError =>
                simp [core.result.Result.map_err,
                  v5_mask.relation_prover.V5IncrementalRelation.finish.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorV5RelationProverError.call_once,
                  core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                  core.convert.FromSame.from] at hrun
              | Ok finalCoefficients =>
                have harrayVal :
                    finalCoefficients.val = coefficientsSlice.val := by
                  unfold core.array.TryFromArrayCopySlice.try_from at harray
                  split at harray
                  · cases harray
                    rfl
                  · simp at harray
                simp only [core.result.Result.map_err, bind_tc_ok,
                  core.result.Result.Insts.CoreOpsTry.branch,
                  Std.lift] at hrun
                let finalSlice := Array.to_slice finalCoefficients
                change (do
                    let q ← aspis_core.sumcheck.WeightAccumulator.dot
                      relation.weights finalSlice
                    let b ← core.cmp.PartialEq.ne.trait_default
                      aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 q
                      relation.running_claim
                    if b = true then
                      ok (core.result.Result.Err
                        v5_mask.relation_prover.V5RelationProverError.FoldMismatch)
                    else
                      ok (core.result.Result.Ok {
                        point_claims := relation.point_claims,
                        terminal_claim := relation.terminal_claim,
                        ood_values := relation.ood_values,
                        sumchecks := relation.sumchecks,
                        running_claims := relation.running_claims,
                        final_coefficients := finalCoefficients })) =
                  ok (core.result.Result.Ok trace) at hrun
                generalize hdot :
                    aspis_core.sumcheck.WeightAccumulator.dot
                        relation.weights finalSlice = dotResult at hrun
                cases dotResult with
                | fail error => simp at hrun
                | div => simp at hrun
                | ok dot =>
                  simp only [bind_tc_ok] at hrun
                  generalize hne :
                      core.cmp.PartialEq.ne.trait_default
                          aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
                          dot relation.running_claim = neResult at hrun
                  cases neResult with
                  | fail error => simp at hrun
                  | div => simp at hrun
                  | ok differs =>
                    by_cases hdiffers : differs = true
                    · simp [hdiffers] at hrun
                    · simp only [hdiffers] at hrun
                      cases hrun
                      exact harrayVal.trans hsliceVal

#print axioms generated_finish_success_preserves_final_coefficients

end aspis_prover.ComponentCRuntimeRelationFinishProvenance
