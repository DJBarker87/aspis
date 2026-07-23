import RuntimeRelationRoundControlFlow

set_option autoImplicit false

open Aeneas Aeneas.Std Result

namespace aspis_prover.ComponentCRuntimeRoundDeepControlFlow

open aspis_prover
open ComponentCRuntimeRoundControlFlow
open ComponentCRuntimeRelationRoundControlFlow

abbrev RawQM31 := aspis_core.field.QM31
abbrev RuntimeSchedule :=
  v5_mask.component_c_runtime.V5ComponentCRuntimeSchedule
abbrev RuntimeRelation :=
  v5_mask.relation_prover.V5IncrementalRelation
abbrev RuntimeTables :=
  v5_mask.component_c_runtime.V5ComponentCRuntimeRelationTables
abbrev RuntimeLater := Array (alloc.vec.Vec RawQM31) 3#usize

/-- Compact named form of the fully exposed source-authentic relation-round
control flow. -/
def GeneratedRelationRoundTrace
    (schedule : RuntimeSchedule)
    (relation0 relation4 : RuntimeRelation)
    (tables0 tables4 : RuntimeTables)
    (round : Std.Usize) : Prop :=
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
    tables4.polynomial.val[round.val]! = table

theorem generated_relation_round_success_has_trace
    (schedule : RuntimeSchedule)
    (relation0 relation4 : RuntimeRelation)
    (tables0 tables4 : RuntimeTables)
    (round : Std.Usize)
    (hrun :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_round
          schedule relation0 tables0 round =
        ok (core.result.Result.Ok (), relation4, tables4)) :
    GeneratedRelationRoundTrace schedule relation0 relation4 tables0 tables4
      round :=
  generated_relation_round_success_decomposes
    schedule relation0 relation4 tables0 tables4 round hrun

/-- One successful top-level runtime round is now exposed down through both
wrappers: its two relation OOD samples, polynomial/table production, relation
fold, public codeword fold, and optional later-fibre loop are all the actual
generated calls. -/
theorem generated_runtime_round_success_decomposes_deep
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
    GeneratedRelationRoundTrace schedule relation relationOut tables tablesOut
        round ∧
      circle_candidate.fold_candidate_codeword_round_for_domain_log
          (alloc.vec.Vec.deref folded)
          schedule.alphas.val[round.val]! round v5_mask.V5_DOMAIN_LOG =
        ok (core.result.Result.Ok foldedOut) ∧
      (if round < 3#usize then
        v5_mask.component_c_runtime.evaluate_component_c_runtime_round_loop
            schedule.later_fibres foldedOut later round 0#usize none =
          ok (laterOut, none)
       else laterOut = later) ∧
      v5_mask.component_c_runtime.evaluate_component_c_runtime_round
          schedule relation folded later tables round =
        ok (core.result.Result.Ok (), relationOut, foldedOut, laterOut,
          tablesOut) := by
  obtain ⟨relationAfter, tablesAfter, hrelation, hcodeword,
      hrelationOut, htablesOut, hlater⟩ :=
    generated_runtime_round_success_decomposes
      schedule relation relationOut folded foldedOut later laterOut
      tables tablesOut round hrun
  subst relationAfter
  subst tablesAfter
  exact ⟨generated_relation_round_success_has_trace
      schedule relation relationOut tables tablesOut round hrelation,
    hcodeword, hlater, hrun⟩

def GeneratedRuntimeRoundTrace
    (schedule : RuntimeSchedule)
    (relation relationOut : RuntimeRelation)
    (folded foldedOut : alloc.vec.Vec RawQM31)
    (later laterOut : RuntimeLater)
    (tables tablesOut : RuntimeTables)
    (round : Std.Usize) : Prop :=
  GeneratedRelationRoundTrace schedule relation relationOut tables tablesOut
      round ∧
    circle_candidate.fold_candidate_codeword_round_for_domain_log
        (alloc.vec.Vec.deref folded)
        schedule.alphas.val[round.val]! round v5_mask.V5_DOMAIN_LOG =
      ok (core.result.Result.Ok foldedOut) ∧
    (if round < 3#usize then
      v5_mask.component_c_runtime.evaluate_component_c_runtime_round_loop
          schedule.later_fibres foldedOut later round 0#usize none =
        ok (laterOut, none)
     else laterOut = later) ∧
    v5_mask.component_c_runtime.evaluate_component_c_runtime_round
        schedule relation folded later tables round =
      ok (core.result.Result.Ok (), relationOut, foldedOut, laterOut,
        tablesOut)

/-- The actual public entrypoint contains four consecutive deeply-exposed
rounds, then the exact relation finish and packer. -/
theorem generated_public_success_has_four_deep_rounds
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
    ∃ trace : v5_mask.relation_prover.V5RelationTrace,
      GeneratedRuntimeRoundTrace schedule relation0 relation1
          folded0 folded1 later0 later1 tables0 tables1 0#usize ∧
      GeneratedRuntimeRoundTrace schedule relation1 relation2
          folded1 folded2 later1 later2 tables1 tables2 1#usize ∧
      GeneratedRuntimeRoundTrace schedule relation2 relation3
          folded2 folded3 later2 later3 tables2 tables3 2#usize ∧
      GeneratedRuntimeRoundTrace schedule relation3 relation4
          folded3 folded4 later3 later4 tables3 tables 3#usize ∧
      v5_mask.relation_prover.V5IncrementalRelation.finish relation4 =
        ok (core.result.Result.Ok trace) ∧
      v5_mask.component_c_runtime.pack_component_c_runtime_downstream
          trace.ood_values trace.sumchecks later4 trace.final_coefficients =
        ok (core.result.Result.Ok output) := by
  obtain ⟨tables, relation0, relation1, relation2, relation3, relation4,
      folded0, folded1, folded2, folded3, folded4,
      later0, later1, later2, later3, later4,
      tables0, tables1, tables2, tables3, trace,
      hround0, hround1, hround2, hround3, hfinish, hpack⟩ :=
    ComponentCRuntimePrivateViewControlFlow.generated_public_success_decomposes
      schedule coefficients codeword expectedInactiveClaim output hrun
  refine ⟨tables, relation0, relation1, relation2, relation3, relation4,
    folded0, folded1, folded2, folded3, folded4,
    later0, later1, later2, later3, later4,
    tables0, tables1, tables2, tables3, trace, ?_, ?_, ?_, ?_,
    hfinish, hpack⟩
  · exact generated_runtime_round_success_decomposes_deep
      schedule relation0 relation1 folded0 folded1 later0 later1
      tables0 tables1 0#usize hround0
  · exact generated_runtime_round_success_decomposes_deep
      schedule relation1 relation2 folded1 folded2 later1 later2
      tables1 tables2 1#usize hround1
  · exact generated_runtime_round_success_decomposes_deep
      schedule relation2 relation3 folded2 folded3 later2 later3
      tables2 tables3 2#usize hround2
  · exact generated_runtime_round_success_decomposes_deep
      schedule relation3 relation4 folded3 folded4 later3 later4
      tables3 tables 3#usize hround3

#print axioms generated_relation_round_success_has_trace
#print axioms generated_runtime_round_success_decomposes_deep
#print axioms generated_public_success_has_four_deep_rounds

end aspis_prover.ComponentCRuntimeRoundDeepControlFlow
