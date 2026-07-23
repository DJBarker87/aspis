import RuntimeCodewordMaintainedLayer
import RuntimeCoefficientTowerCorrespondence
import RuntimeLaterFibreCorrespondence

set_option autoImplicit false

open Aeneas Aeneas.Std Result

namespace aspis_prover.ComponentCRuntimeRoundControlFlow

open aspis_prover

abbrev RawQM31 := aspis_core.field.QM31
abbrev RuntimeSchedule :=
  v5_mask.component_c_runtime.V5ComponentCRuntimeSchedule
abbrev RuntimeRelation :=
  v5_mask.relation_prover.V5IncrementalRelation
abbrev RuntimeTables :=
  v5_mask.component_c_runtime.V5ComponentCRuntimeRelationTables
abbrev RuntimeLater := Array (alloc.vec.Vec RawQM31) 3#usize
abbrev RuntimeError :=
  v5_mask.component_c_runtime.V5ComponentCRuntimeError

private theorem array_index_success_bang
    {T : Type*} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize) (value : T)
    (hrun : Array.index_usize values index = ok value) :
    values.val[index.val]! = value := by
  unfold Array.index_usize at hrun
  rw [Array.getElem?_Usize_eq] at hrun
  generalize hget : values.val[index.val]? = result at hrun
  cases result with
  | none => simp at hrun
  | some actual =>
    simp only [Result.ok.injEq] at hrun
    subst actual
    rw [List.getElem!_eq_getElem?_getD, hget]
    rfl

/-- Invert one successful extracted runtime round.  The conclusion exposes the
exact relation-round call, the exact public codeword-fold call, and—when the
round is one of the first three—the exact later-fibre loop.  Thus a later
arithmetic proof cannot silently replace any of those production calls. -/
theorem generated_runtime_round_success_decomposes
    (schedule : RuntimeSchedule)
    (relation relationOut : RuntimeRelation)
    (folded foldedOut : alloc.vec.Vec RawQM31)
    (later laterOut : RuntimeLater)
    (tables tablesOut : RuntimeTables)
    (round : Std.Usize)
    (hrun :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_round
          schedule relation folded later tables round =
        ok (core.result.Result.Ok (), relationOut, foldedOut, laterOut,
          tablesOut)) :
    ∃ relationAfter tablesAfter,
      v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_round
          schedule relation tables round =
        ok (core.result.Result.Ok (), relationAfter, tablesAfter) ∧
      circle_candidate.fold_candidate_codeword_round_for_domain_log
          (alloc.vec.Vec.deref folded)
          schedule.alphas.val[round.val]! round v5_mask.V5_DOMAIN_LOG =
        ok (core.result.Result.Ok foldedOut) ∧
      relationOut = relationAfter ∧
      tablesOut = tablesAfter ∧
      (if round < 3#usize then
        v5_mask.component_c_runtime.evaluate_component_c_runtime_round_loop
            schedule.later_fibres foldedOut later round 0#usize none =
          ok (laterOut, none)
       else laterOut = later) := by
  unfold v5_mask.component_c_runtime.evaluate_component_c_runtime_round at hrun
  generalize hrelationCall :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_round
        schedule relation tables round = relationResult at hrun
  cases relationResult with
  | fail error => simp at hrun
  | div => simp at hrun
  | ok relationTriple =>
    rcases relationTriple with ⟨relationStatus, relationAfter, tablesAfter⟩
    cases relationStatus with
    | Err relationError =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from] at hrun
    | Ok statusPayload =>
      rcases statusPayload with ⟨⟩
      simp only [bind_tc_ok,
        core.result.Result.Insts.CoreOpsTry.branch] at hrun
      generalize halphaRead :
          Array.index_usize schedule.alphas round = alphaResult at hrun
      cases alphaResult with
      | fail error => simp at hrun
      | div => simp at hrun
      | ok alpha =>
        simp only [bind_tc_ok] at hrun
        generalize hfoldCall :
            circle_candidate.fold_candidate_codeword_round_for_domain_log
              (alloc.vec.Vec.deref folded) alpha round v5_mask.V5_DOMAIN_LOG =
              foldResult at hrun
        cases foldResult with
        | fail error => simp at hrun
        | div => simp at hrun
        | ok foldStatus =>
          cases foldStatus with
          | Err foldError =>
            simp [
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              v5_mask.component_c_runtime.V5ComponentCRuntimeError.Insts.CoreConvertFromCircleCandidateError.from]
              at hrun
          | Ok actualFolded =>
            simp only [bind_tc_ok] at hrun
            by_cases hlt : round < 3#usize
            · rw [if_pos hlt] at hrun
              generalize hlaterCall :
                  v5_mask.component_c_runtime.evaluate_component_c_runtime_round_loop
                    schedule.later_fibres actualFolded later round 0#usize none =
                    laterResult at hrun
              cases laterResult with
              | fail error => simp at hrun
              | div => simp at hrun
              | ok laterPair =>
                rcases laterPair with ⟨actualLater, laterError⟩
                cases laterError with
                | some error => simp at hrun
                | none =>
                  cases hrun
                  have halpha :
                      schedule.alphas.val[round.val]! = alpha := by
                    exact array_index_success_bang _ _ _ halphaRead
                  refine ⟨relationOut, tablesOut, rfl, ?_,
                    rfl, rfl, ?_⟩
                  · simpa [halpha] using hfoldCall
                  · rw [if_pos hlt]
                    exact hlaterCall
            · rw [if_neg hlt] at hrun
              cases hrun
              have halpha :
                  schedule.alphas.val[round.val]! = alpha := by
                exact array_index_success_bang _ _ _ halphaRead
              refine ⟨relationOut, tablesOut, rfl, ?_,
                rfl, rfl, ?_⟩
              · simpa [halpha] using hfoldCall
              · rw [if_neg hlt]

#print axioms generated_runtime_round_success_decomposes

end aspis_prover.ComponentCRuntimeRoundControlFlow
