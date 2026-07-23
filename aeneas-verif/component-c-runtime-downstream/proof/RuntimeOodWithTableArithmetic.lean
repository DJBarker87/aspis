import RuntimeRelationRoundControlFlow

set_option autoImplicit false

open Aeneas Aeneas.Std Result

namespace aspis_prover.ComponentCRuntimeOodWithTableArithmetic

open aspis_prover
open ComponentCRuntimeFoldPrimitiveInstantiation
open ComponentCRuntimeMaterializedRelationArithmetic

abbrev RawQM31 := aspis_core.field.QM31
abbrev RuntimeRelation :=
  v5_mask.relation_prover.V5IncrementalRelation

/-- A successful actual circle-OOD evaluation returns exactly the result of
the generated dense materialized dot against the returned table. -/
theorem generated_circle_ood_success_has_materialized_calls
    (relation : RuntimeRelation)
    (point : aspis_core.circle.SecureCirclePoint)
    (value : RawQM31) (table : alloc.vec.Vec RawQM31)
    (hrun :
      v5_mask.relation_prover.V5IncrementalRelation.evaluate_circle_ood_with_table
          relation point = ok (core.result.Result.Ok (value, table))) :
    ∃ evaluation : aspis_core.sumcheck.WeightAccumulator,
      v5_mask.relation_prover.V5IncrementalRelation.materialize_weights
          evaluation (alloc.vec.Vec.len relation.coefficients) = ok table ∧
      v5_mask.relation_prover.V5IncrementalRelation.materialized_dot
          (alloc.vec.Vec.deref relation.coefficients)
          (alloc.vec.Vec.deref table) = ok value := by
  unfold
    v5_mask.relation_prover.V5IncrementalRelation.evaluate_circle_ood_with_table
    at hrun
  by_cases hround : relation.round != 0#usize
  · simp [hround] at hrun
  · simp only [hround, Bool.false_eq_true, if_false] at hrun
    by_cases hsamples :
        relation.samples >= aspis_core.circle_prefix.CANDIDATE_OOD_SAMPLES
    · simp [hsamples] at hrun
    · simp only [hsamples, if_false] at hrun
      generalize hempty :
          aspis_core.sumcheck.WeightAccumulator.empty
              aspis_core.circle_fri.FIXED_TRACE_LOG_SIZE = emptyResult at hrun
      cases emptyResult with
      | fail error => simp at hrun
      | div => simp at hrun
      | ok emptyWeights =>
        simp only [bind_tc_ok] at hrun
        generalize hadd :
            aspis_core.sumcheck.WeightAccumulator.add_circle_tensor
                emptyWeights aspis_core.field.QM31.ONE point =
              addResult at hrun
        cases addResult with
        | fail error => simp at hrun
        | div => simp at hrun
        | ok addTuple =>
          rcases addTuple with ⟨addStatus, evaluation⟩
          cases addStatus with
          | Err addError =>
            simp [
              core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              v5_mask.relation_prover.V5RelationProverError.Insts.CoreConvertFromTensorWeightError.from]
              at hrun
          | Ok addPayload =>
            rcases addPayload with ⟨⟩
            simp only [bind_tc_ok,
              core.result.Result.Insts.CoreOpsTry.branch] at hrun
            generalize hmaterialize :
                v5_mask.relation_prover.V5IncrementalRelation.materialize_weights
                    evaluation (alloc.vec.Vec.len relation.coefficients) =
                  tableResult at hrun
            cases tableResult with
            | fail error => simp at hrun
            | div => simp at hrun
            | ok actualTable =>
              simp only [bind_tc_ok] at hrun
              generalize hdot :
                  v5_mask.relation_prover.V5IncrementalRelation.materialized_dot
                      (alloc.vec.Vec.deref relation.coefficients)
                      (alloc.vec.Vec.deref actualTable) = dotResult at hrun
              cases dotResult with
              | fail error => simp at hrun
              | div => simp at hrun
              | ok actualValue =>
                cases hrun
                exact ⟨evaluation, hmaterialize, hdot⟩

theorem generated_circle_ood_success_has_materialized_dot
    (relation : RuntimeRelation)
    (point : aspis_core.circle.SecureCirclePoint)
    (value : RawQM31) (table : alloc.vec.Vec RawQM31)
    (hrun :
      v5_mask.relation_prover.V5IncrementalRelation.evaluate_circle_ood_with_table
          relation point = ok (core.result.Result.Ok (value, table))) :
    v5_mask.relation_prover.V5IncrementalRelation.materialized_dot
        (alloc.vec.Vec.deref relation.coefficients)
        (alloc.vec.Vec.deref table) = ok value := by
  rcases generated_circle_ood_success_has_materialized_calls
      relation point value table hrun with ⟨_, _, hdot⟩
  exact hdot

/-- Combining the source-authentic circle-OOD method with the already-proved
dense-dot loop yields the maintained exact-field dot product. -/
theorem generated_circle_ood_success_eq_dotLinear
    (relation : RuntimeRelation)
    (point : aspis_core.circle.SecureCirclePoint)
    (value : RawQM31) (table : alloc.vec.Vec RawQM31)
    (n : Nat)
    (hrun :
      v5_mask.relation_prover.V5IncrementalRelation.evaluate_circle_ood_with_table
          relation point = ok (core.result.Result.Ok (value, table)))
    (hcoefficientLength : relation.coefficients.val.length = n)
    (htableLength : table.val.length = n)
    (hn : n ≤ 1024)
    (hcoefficientsCanonical : RuntimeCanonicalList relation.coefficients.val)
    (htableCanonical : RuntimeCanonicalList table.val) :
    runtimeQM31View value =
      AspisV5ComponentCRelationRowLinearity.dotLinear
        (exactSliceVector n (alloc.vec.Vec.deref table))
        (exactSliceVector n (alloc.vec.Vec.deref relation.coefficients)) := by
  have hdot := generated_circle_ood_success_has_materialized_dot
    relation point value table hrun
  have hcoeffLength :
      (alloc.vec.Vec.deref relation.coefficients).val.length = n :=
    hcoefficientLength
  have hreturnedTableLength :
      (alloc.vec.Vec.deref table).val.length = n := htableLength
  have hlength : relation.coefficients.val.length = table.val.length := by
    omega
  obtain ⟨out, hout, _, hexact⟩ := extracted_materialized_dot_eq_dotLinear
    (alloc.vec.Vec.deref relation.coefficients)
    (alloc.vec.Vec.deref table) hlength (by rw [hcoeffLength]; exact hn)
    hcoefficientsCanonical htableCanonical
  rw [hdot] at hout
  cases hout
  rw [hcoeffLength] at hexact
  exact hexact

/-- The line-OOD path has the same exact dense-dot postcondition.  The proof
also traverses the source-authentic round-to-log arithmetic before reaching
the weight accumulator. -/
theorem generated_line_ood_success_has_materialized_calls
    (relation : RuntimeRelation)
    (point : RawQM31)
    (value : RawQM31) (table : alloc.vec.Vec RawQM31)
    (hrun :
      v5_mask.relation_prover.V5IncrementalRelation.evaluate_line_ood_with_table
          relation point = ok (core.result.Result.Ok (value, table))) :
    ∃ evaluation : aspis_core.sumcheck.WeightAccumulator,
      v5_mask.relation_prover.V5IncrementalRelation.materialize_weights
          evaluation (alloc.vec.Vec.len relation.coefficients) = ok table ∧
      v5_mask.relation_prover.V5IncrementalRelation.materialized_dot
          (alloc.vec.Vec.deref relation.coefficients)
          (alloc.vec.Vec.deref table) = ok value := by
  unfold
    v5_mask.relation_prover.V5IncrementalRelation.evaluate_line_ood_with_table
    at hrun
  by_cases hroundZero : relation.round = 0#usize
  · simp [hroundZero] at hrun
  · simp only [hroundZero, if_false] at hrun
    by_cases hroundHigh :
        relation.round >= aspis_core.circle_prefix.CANDIDATE_ROUND_COUNT
    · simp [hroundHigh] at hrun
    · simp only [hroundHigh, if_false] at hrun
      by_cases hsamples :
          relation.samples >= aspis_core.circle_prefix.CANDIDATE_OOD_SAMPLES
      · simp [hsamples] at hrun
      · simp only [hsamples, if_false] at hrun
        generalize hroundU32 :
            lift (UScalar.cast .U32 relation.round) = roundU32Result at hrun
        cases roundU32Result with
        | fail error => simp at hrun
        | div => simp at hrun
        | ok roundU32 =>
          simp only [bind_tc_ok] at hrun
          generalize htwiceRound :
              lift (Std.U32.wrapping_mul 2#u32 roundU32) =
                twiceRoundResult at hrun
          cases twiceRoundResult with
          | fail error => simp at hrun
          | div => simp at hrun
          | ok twiceRound =>
            simp only [bind_tc_ok] at hrun
            generalize hlogSize :
                lift (Std.U32.wrapping_sub
                    aspis_core.circle_fri.FIXED_TRACE_LOG_SIZE twiceRound) =
                  logSizeResult at hrun
            cases logSizeResult with
            | fail error => simp at hrun
            | div => simp at hrun
            | ok logSize =>
              simp only [bind_tc_ok] at hrun
              generalize hempty :
                  aspis_core.sumcheck.WeightAccumulator.empty logSize =
                    emptyResult at hrun
              cases emptyResult with
              | fail error => simp at hrun
              | div => simp at hrun
              | ok emptyWeights =>
                simp only [bind_tc_ok] at hrun
                generalize hadd :
                    aspis_core.sumcheck.WeightAccumulator.add_line_tensor
                        emptyWeights aspis_core.field.QM31.ONE point =
                      addResult at hrun
                cases addResult with
                | fail error => simp at hrun
                | div => simp at hrun
                | ok addTuple =>
                  rcases addTuple with ⟨addStatus, evaluation⟩
                  cases addStatus with
                  | Err addError =>
                    simp [
                      core.result.Result.Insts.CoreOpsTry.branch,
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                      v5_mask.relation_prover.V5RelationProverError.Insts.CoreConvertFromTensorWeightError.from]
                      at hrun
                  | Ok addPayload =>
                    rcases addPayload with ⟨⟩
                    simp only [bind_tc_ok,
                      core.result.Result.Insts.CoreOpsTry.branch] at hrun
                    generalize hmaterialize :
                        v5_mask.relation_prover.V5IncrementalRelation.materialize_weights
                            evaluation
                            (alloc.vec.Vec.len relation.coefficients) =
                          tableResult at hrun
                    cases tableResult with
                    | fail error => simp at hrun
                    | div => simp at hrun
                    | ok actualTable =>
                      simp only [bind_tc_ok] at hrun
                      generalize hdot :
                          v5_mask.relation_prover.V5IncrementalRelation.materialized_dot
                              (alloc.vec.Vec.deref relation.coefficients)
                              (alloc.vec.Vec.deref actualTable) =
                            dotResult at hrun
                      cases dotResult with
                      | fail error => simp at hrun
                      | div => simp at hrun
                      | ok actualValue =>
                        cases hrun
                        exact ⟨evaluation, hmaterialize, hdot⟩

theorem generated_line_ood_success_has_materialized_dot
    (relation : RuntimeRelation)
    (point value : RawQM31) (table : alloc.vec.Vec RawQM31)
    (hrun :
      v5_mask.relation_prover.V5IncrementalRelation.evaluate_line_ood_with_table
          relation point = ok (core.result.Result.Ok (value, table))) :
    v5_mask.relation_prover.V5IncrementalRelation.materialized_dot
        (alloc.vec.Vec.deref relation.coefficients)
        (alloc.vec.Vec.deref table) = ok value := by
  rcases generated_line_ood_success_has_materialized_calls
      relation point value table hrun with ⟨_, _, hdot⟩
  exact hdot

theorem generated_line_ood_success_eq_dotLinear
    (relation : RuntimeRelation)
    (point value : RawQM31) (table : alloc.vec.Vec RawQM31)
    (n : Nat)
    (hrun :
      v5_mask.relation_prover.V5IncrementalRelation.evaluate_line_ood_with_table
          relation point = ok (core.result.Result.Ok (value, table)))
    (hcoefficientLength : relation.coefficients.val.length = n)
    (htableLength : table.val.length = n)
    (hn : n ≤ 1024)
    (hcoefficientsCanonical : RuntimeCanonicalList relation.coefficients.val)
    (htableCanonical : RuntimeCanonicalList table.val) :
    runtimeQM31View value =
      AspisV5ComponentCRelationRowLinearity.dotLinear
        (exactSliceVector n (alloc.vec.Vec.deref table))
        (exactSliceVector n (alloc.vec.Vec.deref relation.coefficients)) := by
  have hdot := generated_line_ood_success_has_materialized_dot
    relation point value table hrun
  have hcoeffLength :
      (alloc.vec.Vec.deref relation.coefficients).val.length = n :=
    hcoefficientLength
  have hlength : relation.coefficients.val.length = table.val.length := by
    omega
  obtain ⟨out, hout, _, hexact⟩ := extracted_materialized_dot_eq_dotLinear
    (alloc.vec.Vec.deref relation.coefficients)
    (alloc.vec.Vec.deref table) hlength (by rw [hcoeffLength]; exact hn)
    hcoefficientsCanonical htableCanonical
  rw [hdot] at hout
  cases hout
  rw [hcoeffLength] at hexact
  exact hexact

#print axioms generated_circle_ood_success_has_materialized_dot
#print axioms generated_circle_ood_success_eq_dotLinear
#print axioms generated_line_ood_success_has_materialized_dot
#print axioms generated_line_ood_success_eq_dotLinear

end aspis_prover.ComponentCRuntimeOodWithTableArithmetic
