import RuntimeRoundControlFlowCurrent

set_option autoImplicit false

open Aeneas Aeneas.Std Result

namespace ComponentCRuntimeCanonicalGenerated.RuntimePrivateViewControlFlowCurrent

open ComponentCRuntimeCanonicalGenerated

abbrev RawQM31 := aspis_core.field.QM31
abbrev RuntimeSchedule :=
  v5_mask.component_c_runtime.V5ComponentCRuntimeSchedule
abbrev RuntimeRelation :=
  v5_mask.relation_prover.V5IncrementalRelation
abbrev RuntimeTables :=
  v5_mask.component_c_runtime.V5ComponentCRuntimeRelationTables
abbrev RuntimeLater := Array (alloc.vec.Vec RawQM31) 3#usize
abbrev RuntimeTrace := v5_mask.relation_prover.V5RelationTrace

local instance : Inhabited RawQM31 := ⟨aspis_core.field.QM31.ZERO⟩

/-- A successful execution of the extracted private-view entrypoint contains
the actual four runtime-round calls, followed by the actual relation `finish`
and downstream packer calls.  This theorem is purely a control-flow inversion:
it does not replace any generated arithmetic or serialization routine. -/
theorem generated_private_view_success_decomposes
    (schedule : RuntimeSchedule)
    (coefficients codeword : Slice RawQM31)
    (expectedInactiveClaim : RawQM31)
    (output : alloc.vec.Vec RawQM31)
    (tablesOut : RuntimeTables)
    (hrun :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_private_view_with_tables
          schedule coefficients codeword expectedInactiveClaim =
        ok (core.result.Result.Ok (output, tablesOut))) :
    ∃ relation0 relation1 relation2 relation3 relation4,
    ∃ folded0 folded1 folded2 folded3 folded4 : alloc.vec.Vec RawQM31,
    ∃ later0 later1 later2 later3 later4 : RuntimeLater,
    ∃ tables0 tables1 tables2 tables3 : RuntimeTables,
    ∃ trace : RuntimeTrace,
      v5_mask.component_c_runtime.evaluate_component_c_runtime_round
          schedule relation0 folded0 later0 tables0 0#usize =
        ok (core.result.Result.Ok (), relation1, folded1, later1, tables1) ∧
      v5_mask.component_c_runtime.evaluate_component_c_runtime_round
          schedule relation1 folded1 later1 tables1 1#usize =
        ok (core.result.Result.Ok (), relation2, folded2, later2, tables2) ∧
      v5_mask.component_c_runtime.evaluate_component_c_runtime_round
          schedule relation2 folded2 later2 tables2 2#usize =
        ok (core.result.Result.Ok (), relation3, folded3, later3, tables3) ∧
      v5_mask.component_c_runtime.evaluate_component_c_runtime_round
          schedule relation3 folded3 later3 tables3 3#usize =
        ok (core.result.Result.Ok (), relation4, folded4, later4, tablesOut) ∧
      v5_mask.relation_prover.V5IncrementalRelation.finish relation4 =
        ok (core.result.Result.Ok trace) ∧
      v5_mask.component_c_runtime.pack_component_c_runtime_downstream
          trace.ood_values trace.sumchecks later4 trace.final_coefficients =
        ok (core.result.Result.Ok output) ∧
      later0.val[0]!.val = [] ∧
      later0.val[1]!.val = [] ∧
      later0.val[2]!.val = [] := by
  unfold
    v5_mask.component_c_runtime.evaluate_component_c_runtime_private_view_with_tables
    at hrun
  -- The generated shape checks must both have taken their success branch.
  by_cases hcoeffShape :
      (Slice.len coefficients != v5_mask.component_c.V5_C_ROWS) = true
  · simp [hcoeffShape] at hrun
  · simp only [hcoeffShape, Bool.false_eq_true, if_false] at hrun
    generalize hcodewordLength :
        v5_mask.V5_CODEWORD_LEN = codewordLengthResult at hrun
    cases codewordLengthResult with
    | fail error => simp at hrun
    | div => simp at hrun
    | ok expectedCodewordLength =>
      simp only [bind_tc_ok] at hrun
      by_cases hcodewordShape :
          (Slice.len codeword != expectedCodewordLength) = true
      · simp [hcodewordShape] at hrun
      · simp only [hcodewordShape, Bool.false_eq_true, if_false] at hrun
        generalize hkappa2 :
            aspis_core.field.QM31.square schedule.kappa = kappa2Result at hrun
        cases kappa2Result with
        | fail error => simp at hrun
        | div => simp at hrun
        | ok kappa2 =>
          simp only [bind_tc_ok] at hrun
          generalize hkappa3 :
              aspis_core.field.QM31.mul kappa2 schedule.kappa =
                kappa3Result at hrun
          cases kappa3Result with
          | fail error => simp at hrun
          | div => simp at hrun
          | ok kappa3 =>
            simp only [bind_tc_ok] at hrun
            generalize hcoefficientsVec :
                alloc.slice.Slice.to_vec
                    aspis_core.field.QM31.Insts.CoreCloneClone coefficients =
                  coefficientsVecResult at hrun
            cases coefficientsVecResult with
            | fail error => simp at hrun
            | div => simp at hrun
            | ok coefficientsVec =>
              simp only [bind_tc_ok] at hrun
              generalize hterminalSlice :
                  lift (Array.to_slice schedule.terminal_covector) =
                    terminalSliceResult at hrun
              cases terminalSliceResult with
              | fail error => simp at hrun
              | div => simp at hrun
              | ok terminalSlice =>
                simp only [bind_tc_ok] at hrun
                generalize hrelationNew :
                    v5_mask.relation_prover.V5IncrementalRelation.new
                        coefficientsVec schedule.points
                        (Array.make 3#usize [
                          aspis_core.field.QM31.ONE,
                          schedule.kappa,
                          kappa2])
                        schedule.inactive_masks expectedInactiveClaim
                        terminalSlice kappa3 = relationNewResult at hrun
                cases relationNewResult with
                | fail error => simp at hrun
                | div => simp at hrun
                | ok relationStatus =>
                  cases relationStatus with
                  | Err relationError =>
                    simp [core.result.Result.Insts.CoreOpsTry.branch,
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                      v5_mask.component_c_runtime.V5ComponentCRuntimeError.Insts.CoreConvertFromV5RelationProverError.from]
                      at hrun
                  | Ok relation0 =>
                    simp only [bind_tc_ok,
                      core.result.Result.Insts.CoreOpsTry.branch] at hrun
                    generalize hcodewordVec :
                        alloc.slice.Slice.to_vec
                            aspis_core.field.QM31.Insts.CoreCloneClone codeword =
                          codewordVecResult at hrun
                    cases codewordVecResult with
                    | fail error => simp at hrun
                    | div => simp at hrun
                    | ok folded0 =>
                      simp only [bind_tc_ok] at hrun
                      generalize hlaterSource0 :
                          Array.index_usize schedule.later_fibres 0#usize =
                            laterSource0Result at hrun
                      cases laterSource0Result with
                      | fail error => simp at hrun
                      | div => simp at hrun
                      | ok laterSource0 =>
                        simp only [bind_tc_ok] at hrun
                        generalize hlaterCapacity0 :
                            lift (Std.Usize.wrapping_mul 4#usize
                              (alloc.vec.Vec.len laterSource0)) =
                              laterCapacity0Result at hrun
                        cases laterCapacity0Result with
                        | fail error => simp at hrun
                        | div => simp at hrun
                        | ok laterCapacity0 =>
                          simp only [bind_tc_ok] at hrun
                          generalize hlaterSource1 :
                              Array.index_usize schedule.later_fibres 1#usize =
                                laterSource1Result at hrun
                          cases laterSource1Result with
                          | fail error => simp at hrun
                          | div => simp at hrun
                          | ok laterSource1 =>
                            simp only [bind_tc_ok] at hrun
                            generalize hlaterCapacity1 :
                                lift (Std.Usize.wrapping_mul 4#usize
                                  (alloc.vec.Vec.len laterSource1)) =
                                  laterCapacity1Result at hrun
                            cases laterCapacity1Result with
                            | fail error => simp at hrun
                            | div => simp at hrun
                            | ok laterCapacity1 =>
                              simp only [bind_tc_ok] at hrun
                              generalize hlaterSource2 :
                                  Array.index_usize schedule.later_fibres
                                    2#usize = laterSource2Result at hrun
                              cases laterSource2Result with
                              | fail error => simp at hrun
                              | div => simp at hrun
                              | ok laterSource2 =>
                                simp only [bind_tc_ok] at hrun
                                generalize hlaterCapacity2 :
                                    lift (Std.Usize.wrapping_mul 4#usize
                                      (alloc.vec.Vec.len laterSource2)) =
                                      laterCapacity2Result at hrun
                                cases laterCapacity2Result with
                                | fail error => simp at hrun
                                | div => simp at hrun
                                | ok laterCapacity2 =>
                                  simp only [bind_tc_ok] at hrun
                                  generalize htablesEmpty :
                                      v5_mask.component_c_runtime.V5ComponentCRuntimeRelationTables.empty =
                                        tablesEmptyResult at hrun
                                  cases tablesEmptyResult with
                                  | fail error => simp at hrun
                                  | div => simp at hrun
                                  | ok tables0 =>
                                    simp only [bind_tc_ok] at hrun
                                    generalize hround0 :
                                        v5_mask.component_c_runtime.evaluate_component_c_runtime_round
                                            schedule relation0 folded0
                                            (Array.make 3#usize [
                                              alloc.vec.Vec.with_capacity
                                                aspis_core.field.QM31 laterCapacity0,
                                              alloc.vec.Vec.with_capacity
                                                aspis_core.field.QM31 laterCapacity1,
                                              alloc.vec.Vec.with_capacity
                                                aspis_core.field.QM31 laterCapacity2])
                                            tables0 0#usize = round0Result at hrun
                                    cases round0Result with
                                    | fail error => simp at hrun
                                    | div => simp at hrun
                                    | ok round0Tuple =>
                                      rcases round0Tuple with
                                        ⟨round0Status, relation1, folded1,
                                          later1, tables1⟩
                                      cases round0Status with
                                      | Err round0Error =>
                                        simp [
                                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                          core.convert.FromSame.from] at hrun
                                      | Ok round0Payload =>
                                        rcases round0Payload with ⟨⟩
                                        simp only [bind_tc_ok] at hrun
                                        generalize hround1 :
                                            v5_mask.component_c_runtime.evaluate_component_c_runtime_round
                                                schedule relation1 folded1 later1
                                                tables1 1#usize =
                                              round1Result at hrun
                                        cases round1Result with
                                        | fail error => simp at hrun
                                        | div => simp at hrun
                                        | ok round1Tuple =>
                                          rcases round1Tuple with
                                            ⟨round1Status, relation2, folded2,
                                              later2, tables2⟩
                                          cases round1Status with
                                          | Err round1Error =>
                                            simp [
                                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                              core.convert.FromSame.from] at hrun
                                          | Ok round1Payload =>
                                            rcases round1Payload with ⟨⟩
                                            simp only [bind_tc_ok] at hrun
                                            generalize hround2 :
                                                v5_mask.component_c_runtime.evaluate_component_c_runtime_round
                                                    schedule relation2 folded2 later2
                                                    tables2 2#usize =
                                                  round2Result at hrun
                                            cases round2Result with
                                            | fail error => simp at hrun
                                            | div => simp at hrun
                                            | ok round2Tuple =>
                                              rcases round2Tuple with
                                                ⟨round2Status, relation3, folded3,
                                                  later3, tables3⟩
                                              cases round2Status with
                                              | Err round2Error =>
                                                simp [
                                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                                  core.convert.FromSame.from] at hrun
                                              | Ok round2Payload =>
                                                rcases round2Payload with ⟨⟩
                                                simp only [bind_tc_ok] at hrun
                                                generalize hround3 :
                                                    v5_mask.component_c_runtime.evaluate_component_c_runtime_round
                                                        schedule relation3 folded3
                                                        later3 tables3 3#usize =
                                                      round3Result at hrun
                                                cases round3Result with
                                                | fail error => simp at hrun
                                                | div => simp at hrun
                                                | ok round3Tuple =>
                                                  rcases round3Tuple with
                                                    ⟨round3Status, relation4,
                                                      folded4, later4, tables4⟩
                                                  cases round3Status with
                                                  | Err round3Error =>
                                                    simp [
                                                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                                      core.convert.FromSame.from]
                                                      at hrun
                                                  | Ok round3Payload =>
                                                    rcases round3Payload with ⟨⟩
                                                    simp only [bind_tc_ok] at hrun
                                                    generalize hfinish :
                                                        v5_mask.relation_prover.V5IncrementalRelation.finish
                                                            relation4 =
                                                          finishResult at hrun
                                                    cases finishResult with
                                                    | fail error => simp at hrun
                                                    | div => simp at hrun
                                                    | ok finishStatus =>
                                                      cases finishStatus with
                                                      | Err finishError =>
                                                        simp [
                                                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                                          v5_mask.component_c_runtime.V5ComponentCRuntimeError.Insts.CoreConvertFromV5RelationProverError.from]
                                                          at hrun
                                                      | Ok trace =>
                                                        simp only [bind_tc_ok] at hrun
                                                        generalize hpack :
                                                            v5_mask.component_c_runtime.pack_component_c_runtime_downstream
                                                                trace.ood_values
                                                                trace.sumchecks later4
                                                                trace.final_coefficients =
                                                              packResult at hrun
                                                        cases packResult with
                                                        | fail error => simp at hrun
                                                        | div => simp at hrun
                                                        | ok packStatus =>
                                                          cases packStatus with
                                                          | Err packError =>
                                                            simp [
                                                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                                              core.convert.FromSame.from]
                                                              at hrun
                                                          | Ok packedOutput =>
                                                            cases hrun
                                                            refine ⟨relation0, ?_⟩
                                                            refine ⟨relation1, ?_⟩
                                                            refine ⟨relation2, ?_⟩
                                                            refine ⟨relation3, ?_⟩
                                                            refine ⟨relation4, ?_⟩
                                                            refine ⟨folded0, ?_⟩
                                                            refine ⟨folded1, ?_⟩
                                                            refine ⟨folded2, ?_⟩
                                                            refine ⟨folded3, ?_⟩
                                                            refine ⟨folded4, ?_⟩
                                                            refine ⟨Array.make 3#usize [
                                                              alloc.vec.Vec.with_capacity
                                                                aspis_core.field.QM31 laterCapacity0,
                                                              alloc.vec.Vec.with_capacity
                                                                aspis_core.field.QM31 laterCapacity1,
                                                              alloc.vec.Vec.with_capacity
                                                                aspis_core.field.QM31 laterCapacity2], ?_⟩
                                                            refine ⟨later1, ?_⟩
                                                            refine ⟨later2, ?_⟩
                                                            refine ⟨later3, ?_⟩
                                                            refine ⟨later4, ?_⟩
                                                            refine ⟨tables0, ?_⟩
                                                            refine ⟨tables1, ?_⟩
                                                            refine ⟨tables2, ?_⟩
                                                            refine ⟨tables3, ?_⟩
                                                            refine ⟨trace, ?_⟩
                                                            constructor
                                                            · exact hround0
                                                            constructor
                                                            · exact hround1
                                                            constructor
                                                            · exact hround2
                                                            constructor
                                                            · exact hround3
                                                            constructor
                                                            · exact hfinish
                                                            constructor
                                                            · exact hpack
                                                            · simp [alloc.vec.Vec.with_capacity,
                                                                alloc.vec.Vec.new, Array.make]

/-- The public extracted entrypoint discards only the diagnostic relation
tables.  Every successful public output therefore comes from a successful
execution of the table-returning private implementation on the same inputs. -/
theorem generated_public_success_has_private_tables
    (schedule : RuntimeSchedule)
    (coefficients codeword : Slice RawQM31)
    (expectedInactiveClaim : RawQM31)
    (output : alloc.vec.Vec RawQM31)
    (hrun :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_private_view
          schedule coefficients codeword expectedInactiveClaim =
        ok (core.result.Result.Ok output)) :
    ∃ tables : RuntimeTables,
      v5_mask.component_c_runtime.evaluate_component_c_runtime_private_view_with_tables
          schedule coefficients codeword expectedInactiveClaim =
        ok (core.result.Result.Ok (output, tables)) := by
  unfold
    v5_mask.component_c_runtime.evaluate_component_c_runtime_private_view
    at hrun
  by_cases hcoeffShape :
      (Slice.len coefficients != v5_mask.component_c.V5_C_ROWS) = true
  · simp [hcoeffShape] at hrun
  · simp only [hcoeffShape, Bool.false_eq_true, if_false] at hrun
    generalize hcodewordLength :
        v5_mask.V5_CODEWORD_LEN = codewordLengthResult at hrun
    cases codewordLengthResult with
    | fail error => simp at hrun
    | div => simp at hrun
    | ok expectedCodewordLength =>
      simp only [bind_tc_ok] at hrun
      by_cases hcodewordShape :
          (Slice.len codeword != expectedCodewordLength) = true
      · simp [hcodewordShape] at hrun
      · simp only [hcodewordShape, Bool.false_eq_true, if_false] at hrun
        generalize hprivate :
            v5_mask.component_c_runtime.evaluate_component_c_runtime_private_view_with_tables
                schedule coefficients codeword expectedInactiveClaim =
              privateResult at hrun
        cases privateResult with
        | fail error => simp at hrun
        | div => simp at hrun
        | ok privateStatus =>
          cases privateStatus with
          | Err privateError =>
            simp [
              core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from] at hrun
          | Ok privatePair =>
            rcases privatePair with ⟨privateOutput, tables⟩
            simp only [bind_tc_ok,
              core.result.Result.Insts.CoreOpsTry.branch] at hrun
            cases hrun
            exact ⟨tables, rfl⟩

/-- Public-entrypoint capstone: a successful extracted public execution
contains the same four source-authentic rounds, relation finish, and packer
chain exposed by `generated_private_view_success_decomposes`. -/
theorem generated_public_success_decomposes
    (schedule : RuntimeSchedule)
    (coefficients codeword : Slice RawQM31)
    (expectedInactiveClaim : RawQM31)
    (output : alloc.vec.Vec RawQM31)
    (hrun :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_private_view
          schedule coefficients codeword expectedInactiveClaim =
        ok (core.result.Result.Ok output)) :
    ∃ tables : RuntimeTables,
    ∃ relation0 relation1 relation2 relation3 relation4,
    ∃ folded0 folded1 folded2 folded3 folded4 : alloc.vec.Vec RawQM31,
    ∃ later0 later1 later2 later3 later4 : RuntimeLater,
    ∃ tables0 tables1 tables2 tables3 : RuntimeTables,
    ∃ trace : RuntimeTrace,
      v5_mask.component_c_runtime.evaluate_component_c_runtime_round
          schedule relation0 folded0 later0 tables0 0#usize =
        ok (core.result.Result.Ok (), relation1, folded1, later1, tables1) ∧
      v5_mask.component_c_runtime.evaluate_component_c_runtime_round
          schedule relation1 folded1 later1 tables1 1#usize =
        ok (core.result.Result.Ok (), relation2, folded2, later2, tables2) ∧
      v5_mask.component_c_runtime.evaluate_component_c_runtime_round
          schedule relation2 folded2 later2 tables2 2#usize =
        ok (core.result.Result.Ok (), relation3, folded3, later3, tables3) ∧
      v5_mask.component_c_runtime.evaluate_component_c_runtime_round
          schedule relation3 folded3 later3 tables3 3#usize =
        ok (core.result.Result.Ok (), relation4, folded4, later4, tables) ∧
      v5_mask.relation_prover.V5IncrementalRelation.finish relation4 =
        ok (core.result.Result.Ok trace) ∧
      v5_mask.component_c_runtime.pack_component_c_runtime_downstream
          trace.ood_values trace.sumchecks later4 trace.final_coefficients =
        ok (core.result.Result.Ok output) := by
  obtain ⟨tables, hprivate⟩ :=
    generated_public_success_has_private_tables
      schedule coefficients codeword expectedInactiveClaim output hrun
  rcases generated_private_view_success_decomposes
      schedule coefficients codeword expectedInactiveClaim output tables hprivate with
    ⟨relation0, relation1, relation2, relation3, relation4,
      folded0, folded1, folded2, folded3, folded4,
      later0, later1, later2, later3, later4,
      tables0, tables1, tables2, tables3, trace,
      hround0, hround1, hround2, hround3, hfinish, hpack,
      _hempty0, _hempty1, _hempty2⟩
  exact ⟨tables, relation0, relation1, relation2, relation3, relation4,
    folded0, folded1, folded2, folded3, folded4,
    later0, later1, later2, later3, later4,
    tables0, tables1, tables2, tables3, trace,
    hround0, hround1, hround2, hround3, hfinish, hpack⟩

/-- Strengthened public decomposition retaining the exact empty initial
later-release vectors created by the generated entrypoint. -/
theorem generated_public_success_decomposes_with_empty_later
    (schedule : RuntimeSchedule)
    (coefficients codeword : Slice RawQM31)
    (expectedInactiveClaim : RawQM31)
    (output : alloc.vec.Vec RawQM31)
    (hrun :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_private_view
          schedule coefficients codeword expectedInactiveClaim =
        ok (core.result.Result.Ok output)) :
    ∃ tables : RuntimeTables,
    ∃ relation0 relation1 relation2 relation3 relation4,
    ∃ folded0 folded1 folded2 folded3 folded4 : alloc.vec.Vec RawQM31,
    ∃ later0 later1 later2 later3 later4 : RuntimeLater,
    ∃ tables0 tables1 tables2 tables3 : RuntimeTables,
    ∃ trace : RuntimeTrace,
      v5_mask.component_c_runtime.evaluate_component_c_runtime_round
          schedule relation0 folded0 later0 tables0 0#usize =
        ok (core.result.Result.Ok (), relation1, folded1, later1, tables1) ∧
      v5_mask.component_c_runtime.evaluate_component_c_runtime_round
          schedule relation1 folded1 later1 tables1 1#usize =
        ok (core.result.Result.Ok (), relation2, folded2, later2, tables2) ∧
      v5_mask.component_c_runtime.evaluate_component_c_runtime_round
          schedule relation2 folded2 later2 tables2 2#usize =
        ok (core.result.Result.Ok (), relation3, folded3, later3, tables3) ∧
      v5_mask.component_c_runtime.evaluate_component_c_runtime_round
          schedule relation3 folded3 later3 tables3 3#usize =
        ok (core.result.Result.Ok (), relation4, folded4, later4, tables) ∧
      v5_mask.relation_prover.V5IncrementalRelation.finish relation4 =
        ok (core.result.Result.Ok trace) ∧
      v5_mask.component_c_runtime.pack_component_c_runtime_downstream
          trace.ood_values trace.sumchecks later4 trace.final_coefficients =
        ok (core.result.Result.Ok output) ∧
      later0.val[0]!.val = [] ∧
      later0.val[1]!.val = [] ∧
      later0.val[2]!.val = [] := by
  obtain ⟨tables, hprivate⟩ :=
    generated_public_success_has_private_tables
      schedule coefficients codeword expectedInactiveClaim output hrun
  exact ⟨tables,
    generated_private_view_success_decomposes
      schedule coefficients codeword expectedInactiveClaim output tables hprivate⟩

#print axioms generated_private_view_success_decomposes
#print axioms generated_public_success_has_private_tables
#print axioms generated_public_success_decomposes
#print axioms generated_public_success_decomposes_with_empty_later

end ComponentCRuntimeCanonicalGenerated.RuntimePrivateViewControlFlowCurrent
