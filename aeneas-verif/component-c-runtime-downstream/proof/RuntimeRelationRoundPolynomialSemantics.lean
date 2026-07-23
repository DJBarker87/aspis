import RuntimeRelationRoundTraceProvenance

set_option autoImplicit false

open Aeneas Aeneas.Std Result

namespace aspis_prover.ComponentCRuntimeRelationRoundPolynomialSemantics

open aspis_prover
open ComponentCRuntimeFoldPrimitiveInstantiation
open ComponentCRuntimeMaterializedRelationArithmetic
open ComponentCRuntimeRoundDeepControlFlow
open ComponentCRuntimeRelationRoundTraceProvenance

abbrev RawQM31 := aspis_core.field.QM31
abbrev RuntimeSchedule :=
  v5_mask.component_c_runtime.V5ComponentCRuntimeSchedule
abbrev RuntimeRelation :=
  v5_mask.relation_prover.V5IncrementalRelation
abbrev RuntimeTables :=
  v5_mask.component_c_runtime.V5ComponentCRuntimeRelationTables

structure PolynomialWitness where
  polynomial : Array RawQM31 7#usize
  table : alloc.vec.Vec RawQM31

/-- Exact arithmetic semantics of a generated seven-coefficient relation
message.  The only parameters left are concrete representation properties of
the generated coefficient and materialized-weight vectors. -/
def PolynomialSemantics
    (coefficients : alloc.vec.Vec RawQM31)
    (w : PolynomialWitness) : Prop :=
  ∀ n : Nat,
    coefficients.val.length = 4 * n →
    w.table.val.length = 4 * n →
    4 * n ≤ 1024 →
    RuntimeCanonicalList coefficients.val →
    RuntimeCanonicalList w.table.val →
    RuntimeCanonicalArray w.polynomial ∧
      ∀ degree : Fin 7,
        exactArrayEntry w.polynomial degree.val =
          AspisV5ComponentCRelationRowLinearity.polynomialForExtension n
            (exactSliceVector (4 * n) (alloc.vec.Vec.deref w.table))
            (exactSliceVector (4 * n) (alloc.vec.Vec.deref coefficients))
            degree

/-- The polynomial released by the actual generated circle round is exactly
the maintained relation polynomial for the round's initial coefficient
vector and the actual generated materialized table. -/
theorem generated_circle_round_trace_polynomial_semantics
    (schedule : RuntimeSchedule)
    (relation0 relation4 : RuntimeRelation)
    (tables0 tables4 : RuntimeTables)
    (htrace : GeneratedRelationRoundTrace schedule relation0 relation4
      tables0 tables4 0#usize) :
    ∃ w : PolynomialWitness,
      relation4.sumchecks.val[0]! = w.polynomial ∧
      tables4.polynomial.val[0]! = w.table ∧
      (∃ weights : aspis_core.sumcheck.WeightAccumulator,
        v5_mask.relation_prover.V5IncrementalRelation.materialize_weights
            weights (alloc.vec.Vec.len relation0.coefficients) = ok w.table) ∧
      PolynomialSemantics relation0.coefficients w := by
  rcases generated_circle_round_trace_released_state
      schedule relation0 relation4 tables0 tables4 htrace with
    ⟨_relation1, relation2, relation3, _point0, _point1,
      _value0, _value1, _table0, _table1, polynomial, polynomialTable,
      _hpoint0, _hpoint1, _heval0, _heval1,
      _hcoefficients1, hcoefficients2, hpolynomial, hstored,
      _htable0Stored, _htable1Stored,
      _hood, _hvalue0, _hvalue1, _hsumchecks, hsumcheck,
      _hround, _hsamples⟩
  let w : PolynomialWitness :=
    { polynomial := polynomial, table := polynomialTable }
  have hmaterializeRaw :=
    (polynomial_with_table_success_has_materialized_calls
      relation2 relation3 polynomial polynomialTable hpolynomial).1
  have hmaterialize :
      v5_mask.relation_prover.V5IncrementalRelation.materialize_weights
          relation2.weights (alloc.vec.Vec.len relation0.coefficients) =
        ok polynomialTable := by
    simpa [hcoefficients2] using hmaterializeRaw
  refine ⟨w, hsumcheck, hstored, ⟨relation2.weights, hmaterialize⟩, ?_⟩
  intro n hcoeffLength htableLength hbound hcoeffCanonical htableCanonical
  have hcoeffLength2 : relation2.coefficients.val.length = 4 * n := by
    simpa [hcoefficients2] using hcoeffLength
  have hcoeffCanonical2 : RuntimeCanonicalList relation2.coefficients.val := by
    simpa [hcoefficients2] using hcoeffCanonical
  have h := polynomial_with_table_success_eq_polynomialForExtension
    n relation2 relation3 polynomial polynomialTable hpolynomial
    hcoeffLength2 htableLength hbound hcoeffCanonical2 htableCanonical
  simpa [w, hcoefficients2] using h

/-- Every nonzero generated line round has the same exact released-polynomial
semantics at its actual round slot. -/
theorem generated_line_round_trace_polynomial_semantics
    (schedule : RuntimeSchedule)
    (relation0 relation4 : RuntimeRelation)
    (tables0 tables4 : RuntimeTables)
    (round : Std.Usize)
    (hroundNonzero : round ≠ 0#usize)
    (hroundBound : round.val < 4)
    (hstateRound : relation0.round = round)
    (hstateSamples : relation0.samples = 0#usize)
    (htrace : GeneratedRelationRoundTrace schedule relation0 relation4
      tables0 tables4 round) :
    ∃ w : PolynomialWitness,
      relation4.sumchecks.val[round.val]! = w.polynomial ∧
      tables4.polynomial.val[round.val]! = w.table ∧
      (∃ weights : aspis_core.sumcheck.WeightAccumulator,
        v5_mask.relation_prover.V5IncrementalRelation.materialize_weights
            weights (alloc.vec.Vec.len relation0.coefficients) = ok w.table) ∧
      PolynomialSemantics relation0.coefficients w := by
  rcases generated_line_round_trace_released_state
      schedule relation0 relation4 tables0 tables4 round
      hroundNonzero hroundBound hstateRound hstateSamples htrace with
    ⟨_relation1, relation2, relation3, _layer0, _layer1,
      _layerPoints0, _layerPoints1, _point0, _point1,
      _value0, _value1, _table0, _table1, polynomial, polynomialTable,
      _hlayer0, _hlayer1, _hlayerPoints0, _hlayerPoints1,
      _hpoint0, _hpoint1, _heval0, _heval1,
      _hcoefficients1, hcoefficients2, hpolynomial, hstored,
      _htable0Stored, _htable1Stored,
      _hood, _hvalue0, _hvalue1, _hsumchecks, hsumcheck,
      _hround, _hsamples⟩
  let w : PolynomialWitness :=
    { polynomial := polynomial, table := polynomialTable }
  have hmaterializeRaw :=
    (polynomial_with_table_success_has_materialized_calls
      relation2 relation3 polynomial polynomialTable hpolynomial).1
  have hmaterialize :
      v5_mask.relation_prover.V5IncrementalRelation.materialize_weights
          relation2.weights (alloc.vec.Vec.len relation0.coefficients) =
        ok polynomialTable := by
    simpa [hcoefficients2] using hmaterializeRaw
  refine ⟨w, hsumcheck, hstored, ⟨relation2.weights, hmaterialize⟩, ?_⟩
  intro n hcoeffLength htableLength hbound hcoeffCanonical htableCanonical
  have hcoeffLength2 : relation2.coefficients.val.length = 4 * n := by
    simpa [hcoefficients2] using hcoeffLength
  have hcoeffCanonical2 : RuntimeCanonicalList relation2.coefficients.val := by
    simpa [hcoefficients2] using hcoeffCanonical
  have h := polynomial_with_table_success_eq_polynomialForExtension
    n relation2 relation3 polynomial polynomialTable hpolynomial
    hcoeffLength2 htableLength hbound hcoeffCanonical2 htableCanonical
  simpa [w, hcoefficients2] using h

#print axioms generated_circle_round_trace_polynomial_semantics
#print axioms generated_line_round_trace_polynomial_semantics

end aspis_prover.ComponentCRuntimeRelationRoundPolynomialSemantics
