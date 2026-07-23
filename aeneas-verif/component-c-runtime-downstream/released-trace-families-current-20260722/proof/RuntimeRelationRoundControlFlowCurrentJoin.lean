import RuntimePrivateViewControlFlow
import RuntimeMaterializedRelationArithmetic

set_option autoImplicit false

open Aeneas Aeneas.Std Result

namespace aspis_prover.ComponentCRuntimeRelationRoundControlFlow

open aspis_prover

abbrev RawQM31 := aspis_core.field.QM31
abbrev RuntimeSchedule :=
  v5_mask.component_c_runtime.V5ComponentCRuntimeSchedule
abbrev RuntimeRelation :=
  v5_mask.relation_prover.V5IncrementalRelation
abbrev RuntimeTables :=
  v5_mask.component_c_runtime.V5ComponentCRuntimeRelationTables

private theorem generated_array_index_mut_run
    {T : Type*} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize) (hindex : index.val < N.val) :
    Array.index_mut_usize values index =
      ok (values.val[index.val]!, values.set index) := by
  obtain ⟨result, hrun, hpost⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_mut_usize_spec values index (by
      simpa [Array.length_eq] using hindex))
  rcases result with ⟨value, restore⟩
  rcases hpost with ⟨hvalue, hrestore⟩
  have harrayBound : index.val < values.val.length := by
    simpa [Array.length_eq] using hindex
  have hbang : values.val[index.val]! = values.val[index.val] := by
    apply List.getElem!_of_getElem?
    exact List.getElem?_eq_getElem harrayBound
  simpa [hvalue, hrestore, hbang] using hrun

private theorem array_set_get_same
    {T : Type*} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize) (value : T)
    (hindex : index.val < N.val) :
    (values.set index value).val[index.val]! = value := by
  simp only [Array.set_val_eq]
  apply List.set_getElem!_eq
  exact ⟨by simpa [Array.length_eq] using hindex, rfl⟩

/-- Invert a successful source-authentic relation round.  The theorem names
the two OOD sample calls, the coefficient-polynomial/table call, the schedule
alpha read, the coefficient fold, and the exact table setter used by Rust. -/
theorem generated_relation_round_success_decomposes
    (schedule : RuntimeSchedule)
    (relation0 relation4 : RuntimeRelation)
    (tables0 tables4 : RuntimeTables)
    (round : Std.Usize)
    (hrun :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_round
          schedule relation0 tables0 round =
        ok (core.result.Result.Ok (), relation4, tables4)) :
    ∃ relation1 relation2 relation3,
    ∃ tables1 tables2 : RuntimeTables,
    ∃ polynomial : Array RawQM31 7#usize,
    ∃ table : alloc.vec.Vec RawQM31,
    ∃ alpha : RawQM31,
      v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_sample
          schedule relation0 tables0 round 0#usize =
        ok (core.result.Result.Ok (), relation1, tables1) ∧
      v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_sample
          schedule relation1 tables1 round 1#usize =
        ok (core.result.Result.Ok (), relation2, tables2) ∧
      v5_mask.relation_prover.V5IncrementalRelation.polynomial_with_table
          relation2 =
        ok (core.result.Result.Ok (polynomial, table), relation3) ∧
      Array.index_usize schedule.alphas round = ok alpha ∧
      v5_mask.relation_prover.V5IncrementalRelation.fold relation3 alpha =
        ok (core.result.Result.Ok (), relation4) ∧
      round < 4#usize ∧
      tables4.ood = tables2.ood ∧
      tables4.polynomial.val[round.val]! = table := by
  unfold
    v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_round
    at hrun
  generalize hsample0 :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_sample
          schedule relation0 tables0 round 0#usize = sample0Result at hrun
  cases sample0Result with
  | fail error => simp at hrun
  | div => simp at hrun
  | ok sample0Tuple =>
    rcases sample0Tuple with ⟨sample0Status, relation1, tables1⟩
    cases sample0Status with
    | Err sample0Error =>
      simp [
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from] at hrun
    | Ok sample0Payload =>
      rcases sample0Payload with ⟨⟩
      simp only [bind_tc_ok,
        core.result.Result.Insts.CoreOpsTry.branch] at hrun
      generalize hsample1 :
          v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_sample
              schedule relation1 tables1 round 1#usize =
            sample1Result at hrun
      cases sample1Result with
      | fail error => simp at hrun
      | div => simp at hrun
      | ok sample1Tuple =>
        rcases sample1Tuple with ⟨sample1Status, relation2, tables2⟩
        cases sample1Status with
        | Err sample1Error =>
          simp [
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at hrun
        | Ok sample1Payload =>
          rcases sample1Payload with ⟨⟩
          simp only [bind_tc_ok] at hrun
          generalize hpolynomial :
              v5_mask.relation_prover.V5IncrementalRelation.polynomial_with_table
                  relation2 = polynomialResult at hrun
          cases polynomialResult with
          | fail error => simp at hrun
          | div => simp at hrun
          | ok polynomialTuple =>
            rcases polynomialTuple with ⟨polynomialStatus, relation3⟩
            cases polynomialStatus with
            | Err polynomialError =>
              simp [
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                v5_mask.component_c_runtime.V5ComponentCRuntimeError.Insts.CoreConvertFromV5RelationProverError.from]
                at hrun
            | Ok polynomialAndTable =>
              rcases polynomialAndTable with ⟨polynomial, table⟩
              simp only [bind_tc_ok] at hrun
              generalize hvalidate :
                  v5_mask.component_c_runtime.validate_component_c_runtime_relation_table
                      (alloc.vec.Vec.deref table) round 2#u8 =
                    validateResult at hrun
              cases validateResult with
              | fail error => simp at hrun
              | div => simp at hrun
              | ok validateStatus =>
                cases validateStatus with
                | Err validateError =>
                  simp [
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                    core.convert.FromSame.from] at hrun
                | Ok validatePayload =>
                  rcases validatePayload with ⟨⟩
                  simp only [bind_tc_ok] at hrun
                  by_cases hround : round < 4#usize
                  · simp only [massert, hround] at hrun
                    generalize hfirstBorrow :
                        Array.index_mut_usize tables2.polynomial round =
                          firstBorrowResult at hrun
                    cases firstBorrowResult with
                    | fail error => simp at hrun
                    | div => simp at hrun
                    | ok firstBorrow =>
                      rcases firstBorrow with ⟨oldTable, restoreFirst⟩
                      simp only [bind_tc_ok] at hrun
                      let restored := restoreFirst oldTable
                      generalize hsecondBorrow :
                          Array.index_mut_usize restored round =
                            secondBorrowResult at hrun
                      cases secondBorrowResult with
                      | fail error => simp at hrun
                      | div => simp at hrun
                      | ok secondBorrow =>
                        rcases secondBorrow with ⟨oldTableAgain, restoreSecond⟩
                        simp only [bind_tc_ok] at hrun
                        generalize halpha :
                            Array.index_usize schedule.alphas round =
                              alphaResult at hrun
                        cases alphaResult with
                        | fail error => simp at hrun
                        | div => simp at hrun
                        | ok alpha =>
                          simp only [bind_tc_ok] at hrun
                          generalize hfold :
                              v5_mask.relation_prover.V5IncrementalRelation.fold
                                  relation3 alpha = foldResult at hrun
                          cases foldResult with
                          | fail error => simp at hrun
                          | div => simp at hrun
                          | ok foldTuple =>
                            rcases foldTuple with ⟨foldStatus, relationAfter⟩
                            cases foldStatus with
                            | Err foldError =>
                              simp [
                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                v5_mask.component_c_runtime.V5ComponentCRuntimeError.Insts.CoreConvertFromV5RelationProverError.from]
                                at hrun
                            | Ok foldPayload =>
                              rcases foldPayload with ⟨⟩
                              simp only [bind_tc_ok] at hrun
                              cases hrun
                              refine ⟨relation1, relation2, relation3,
                                tables1, tables2, polynomial, table, alpha,
                                rfl, hsample1, hpolynomial, rfl,
                                hfold, hround, rfl, ?_⟩
                              -- The second mutable-array setter writes `table` at
                              -- exactly `round`; no handwritten row permutation is
                              -- introduced here.
                              have hindex : round.val < (4#usize).val := by
                                scalar_tac
                              have hsetter := generated_array_index_mut_run
                                restored round hindex
                              rw [hsetter] at hsecondBorrow
                              cases hsecondBorrow
                              exact array_set_get_same restored round table hindex
                  · simp [massert, hround] at hrun

#print axioms generated_relation_round_success_decomposes

end aspis_prover.ComponentCRuntimeRelationRoundControlFlow
