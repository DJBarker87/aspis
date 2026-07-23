import RuntimeRoundDeepControlFlow
import RuntimeRelationSampleOodCall

set_option autoImplicit false

open Aeneas Aeneas.Std Result

namespace aspis_prover.ComponentCRuntimeRelationReleasedArithmetic

open aspis_prover
open ComponentCRuntimeFoldPrimitiveInstantiation
open ComponentCRuntimeMaterializedRelationArithmetic
open ComponentCRuntimeRelationRoundControlFlow
open ComponentCRuntimeRelationSampleOodCall
open ComponentCRuntimeOodWithTableArithmetic

abbrev RawQM31 := aspis_core.field.QM31
abbrev RuntimeSchedule :=
  v5_mask.component_c_runtime.V5ComponentCRuntimeSchedule
abbrev RuntimeRelation :=
  v5_mask.relation_prover.V5IncrementalRelation
abbrev RuntimeTables :=
  v5_mask.component_c_runtime.V5ComponentCRuntimeRelationTables

/-- A successful relation round carries a returned polynomial whose exact
semantics are already determined by its returned table.  Canonicality and
length are exposed as the minimal representation side conditions, not folded
into an opaque evaluator premise. -/
theorem generated_relation_round_success_has_polynomial_semantics
    (schedule : RuntimeSchedule)
    (relation0 relation4 : RuntimeRelation)
    (tables0 tables4 : RuntimeTables)
    (round : Std.Usize)
    (hrun :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_round
          schedule relation0 tables0 round =
        ok (core.result.Result.Ok (), relation4, tables4)) :
    ∃ relation2 relation3,
    ∃ polynomial : Array RawQM31 7#usize,
    ∃ table : alloc.vec.Vec RawQM31,
      v5_mask.relation_prover.V5IncrementalRelation.polynomial_with_table
          relation2 =
        ok (core.result.Result.Ok (polynomial, table), relation3) ∧
      tables4.polynomial.val[round.val]! = table ∧
      ∀ n : Nat,
        relation2.coefficients.val.length = 4 * n →
        table.val.length = 4 * n →
        4 * n ≤ 1024 →
        RuntimeCanonicalList relation2.coefficients.val →
        RuntimeCanonicalList table.val →
        RuntimeCanonicalArray polynomial ∧
          ∀ degree : Fin 7,
            exactArrayEntry polynomial degree.val =
              AspisV5ComponentCRelationRowLinearity.polynomialForExtension n
                (exactSliceVector (4 * n) (alloc.vec.Vec.deref table))
                (exactSliceVector (4 * n)
                  (alloc.vec.Vec.deref relation2.coefficients)) degree := by
  obtain ⟨_, relation2, relation3, _, _, polynomial, table, _,
      _, _, hpolynomial, _, _, _, _hoodStored, hstored⟩ :=
    generated_relation_round_success_decomposes
      schedule relation0 relation4 tables0 tables4 round hrun
  refine ⟨relation2, relation3, polynomial, table,
    hpolynomial, hstored, ?_⟩
  intro n hcoeffLength htableLength hbound hcoeffCanonical htableCanonical
  exact polynomial_with_table_success_eq_polynomialForExtension
    n relation2 relation3 polynomial table hpolynomial
    hcoeffLength htableLength hbound hcoeffCanonical htableCanonical

/-- Round-zero sample arithmetic is fully reduced to the returned circle
weight table and the maintained exact-field dot product. -/
theorem generated_circle_sample_success_has_dot_semantics
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
          relation point = ok (core.result.Result.Ok (value, table)) ∧
      ∀ n : Nat,
        relation.coefficients.val.length = n →
        table.val.length = n →
        n ≤ 1024 →
        RuntimeCanonicalList relation.coefficients.val →
        RuntimeCanonicalList table.val →
        runtimeQM31View value =
          AspisV5ComponentCRelationRowLinearity.dotLinear
            (exactSliceVector n (alloc.vec.Vec.deref table))
            (exactSliceVector n
              (alloc.vec.Vec.deref relation.coefficients)) := by
  obtain ⟨point, value, table, hpoint, hood⟩ :=
    generated_circle_sample_success_has_ood_call
      schedule relation relationOut tables tablesOut sample hrun
  refine ⟨point, value, table, hpoint, hood, ?_⟩
  intro n hcoeffLength htableLength hbound hcoeffCanonical htableCanonical
  exact generated_circle_ood_success_eq_dotLinear
    relation point value table n hood hcoeffLength htableLength hbound
    hcoeffCanonical htableCanonical

/-- The same conditional-on-representation result for every nonzero line
round. -/
theorem generated_line_sample_success_has_dot_semantics
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
          relation point = ok (core.result.Result.Ok (value, table)) ∧
      ∀ n : Nat,
        relation.coefficients.val.length = n →
        table.val.length = n →
        n ≤ 1024 →
        RuntimeCanonicalList relation.coefficients.val →
        RuntimeCanonicalList table.val →
        runtimeQM31View value =
          AspisV5ComponentCRelationRowLinearity.dotLinear
            (exactSliceVector n (alloc.vec.Vec.deref table))
            (exactSliceVector n
              (alloc.vec.Vec.deref relation.coefficients)) := by
  obtain ⟨layer, layerPoints, point, value, table,
      hlayer, hlayerPoints, hpoint, hood⟩ :=
    generated_line_sample_success_has_ood_call
      schedule relation relationOut tables tablesOut round sample hround hrun
  refine ⟨layer, layerPoints, point, value, table,
    hlayer, hlayerPoints, hpoint, hood, ?_⟩
  intro n hcoeffLength htableLength hbound hcoeffCanonical htableCanonical
  exact generated_line_ood_success_eq_dotLinear
    relation point value table n hood hcoeffLength htableLength hbound
    hcoeffCanonical htableCanonical

#print axioms generated_relation_round_success_has_polynomial_semantics
#print axioms generated_circle_sample_success_has_dot_semantics
#print axioms generated_line_sample_success_has_dot_semantics

end aspis_prover.ComponentCRuntimeRelationReleasedArithmetic
