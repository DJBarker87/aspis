import RuntimeRelationRoundTraceProvenance

set_option autoImplicit false

open Aeneas Aeneas.Std Result

namespace aspis_prover.ComponentCRuntimeRelationRoundOodSemantics

open aspis_prover
open ComponentCRuntimeFoldPrimitiveInstantiation
open ComponentCRuntimeMaterializedRelationArithmetic
open ComponentCRuntimeOodWithTableArithmetic
open ComponentCRuntimeRoundDeepControlFlow
open ComponentCRuntimeRelationRoundTraceProvenance

abbrev RawQM31 := aspis_core.field.QM31
abbrev RuntimeSchedule :=
  v5_mask.component_c_runtime.V5ComponentCRuntimeSchedule
abbrev RuntimeRelation :=
  v5_mask.relation_prover.V5IncrementalRelation
abbrev RuntimeTables :=
  v5_mask.component_c_runtime.V5ComponentCRuntimeRelationTables

structure OodPairWitness where
  value0 : RawQM31
  value1 : RawQM31
  table0 : alloc.vec.Vec RawQM31
  table1 : alloc.vec.Vec RawQM31

/-- Exact arithmetic semantics of one generated OOD pair, parameterized only
by the representation facts which are separately checkable for the returned
Rust vectors. -/
def OodPairDotSemantics
    (coefficients : alloc.vec.Vec RawQM31) (w : OodPairWitness) : Prop :=
  ∀ n : Nat,
    coefficients.val.length = n →
    w.table0.val.length = n →
    w.table1.val.length = n →
    n ≤ 1024 →
    RuntimeCanonicalList coefficients.val →
    RuntimeCanonicalList w.table0.val →
    RuntimeCanonicalList w.table1.val →
    runtimeQM31View w.value0 =
      AspisV5ComponentCRelationRowLinearity.dotLinear
        (exactSliceVector n (alloc.vec.Vec.deref w.table0))
        (exactSliceVector n (alloc.vec.Vec.deref coefficients)) ∧
    runtimeQM31View w.value1 =
      AspisV5ComponentCRelationRowLinearity.dotLinear
        (exactSliceVector n (alloc.vec.Vec.deref w.table1))
        (exactSliceVector n (alloc.vec.Vec.deref coefficients))

/-- Round zero's two actual generated evaluations, as stored in the released
state, are exactly the maintained `dotLinear` map for their returned tables. -/
theorem generated_circle_round_trace_ood_semantics
    (schedule : RuntimeSchedule)
    (relation0 relation4 : RuntimeRelation)
    (tables0 tables4 : RuntimeTables)
    (htrace : GeneratedRelationRoundTrace schedule relation0 relation4
      tables0 tables4 0#usize) :
    ∃ w : OodPairWitness,
      relation4.ood_values.val[0]!.val[0]! = w.value0 ∧
      relation4.ood_values.val[0]!.val[1]! = w.value1 ∧
      tables4.ood.val[0]!.val[0]! = w.table0 ∧
      tables4.ood.val[0]!.val[1]! = w.table1 ∧
      (∃ evaluation0 evaluation1 : aspis_core.sumcheck.WeightAccumulator,
        v5_mask.relation_prover.V5IncrementalRelation.materialize_weights
            evaluation0 (alloc.vec.Vec.len relation0.coefficients) = ok w.table0 ∧
        v5_mask.relation_prover.V5IncrementalRelation.materialize_weights
            evaluation1 (alloc.vec.Vec.len relation0.coefficients) = ok w.table1) ∧
      OodPairDotSemantics relation0.coefficients w := by
  rcases generated_circle_round_trace_released_state
      schedule relation0 relation4 tables0 tables4 htrace with
    ⟨relation1, _relation2, _relation3, _point0, _point1, value0, value1,
      table0, table1, _polynomial, _polynomialTable,
      _hpoint0, _hpoint1, heval0, heval1,
      hcoefficients1, _hcoefficients2,
      _hpolyCall, _hpolyStored,
      htable0Stored, htable1Stored,
      _hood, hvalue0, hvalue1, _hsumchecks, _hpoly,
      _hround, _hsamples⟩
  let w : OodPairWitness :=
    { value0 := value0, value1 := value1, table0 := table0, table1 := table1 }
  rcases generated_circle_ood_success_has_materialized_calls
      relation0 _ value0 table0 heval0 with ⟨evaluation0, hmaterialize0, _⟩
  rcases generated_circle_ood_success_has_materialized_calls
      relation1 _ value1 table1 heval1 with ⟨evaluation1, hmaterialize1, _⟩
  have hmaterialize1' :
      v5_mask.relation_prover.V5IncrementalRelation.materialize_weights
          evaluation1 (alloc.vec.Vec.len relation0.coefficients) = ok table1 := by
    simpa [hcoefficients1] using hmaterialize1
  refine ⟨w, hvalue0, hvalue1, htable0Stored, htable1Stored,
    ⟨evaluation0, evaluation1, hmaterialize0, hmaterialize1'⟩, ?_⟩
  intro n hcoeffLength htable0Length htable1Length hn
    hcoeffCanonical htable0Canonical htable1Canonical
  constructor
  · exact generated_circle_ood_success_eq_dotLinear
      relation0 _ value0 table0 n heval0
      hcoeffLength htable0Length hn hcoeffCanonical htable0Canonical
  · have hcoeffLength1 : relation1.coefficients.val.length = n := by
      rw [hcoefficients1, hcoeffLength]
    have hcoeffCanonical1 : RuntimeCanonicalList relation1.coefficients.val := by
      simpa [hcoefficients1] using hcoeffCanonical
    have h := generated_circle_ood_success_eq_dotLinear
      relation1 _ value1 table1 n heval1
      hcoeffLength1 htable1Length hn hcoeffCanonical1 htable1Canonical
    simpa [hcoefficients1] using h

/-- Every nonzero line round has the identical exact pair semantics. -/
theorem generated_line_round_trace_ood_semantics
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
    ∃ w : OodPairWitness,
      relation4.ood_values.val[round.val]!.val[0]! = w.value0 ∧
      relation4.ood_values.val[round.val]!.val[1]! = w.value1 ∧
      tables4.ood.val[round.val]!.val[0]! = w.table0 ∧
      tables4.ood.val[round.val]!.val[1]! = w.table1 ∧
      (∃ evaluation0 evaluation1 : aspis_core.sumcheck.WeightAccumulator,
        v5_mask.relation_prover.V5IncrementalRelation.materialize_weights
            evaluation0 (alloc.vec.Vec.len relation0.coefficients) = ok w.table0 ∧
        v5_mask.relation_prover.V5IncrementalRelation.materialize_weights
            evaluation1 (alloc.vec.Vec.len relation0.coefficients) = ok w.table1) ∧
      OodPairDotSemantics relation0.coefficients w := by
  rcases generated_line_round_trace_released_state
      schedule relation0 relation4 tables0 tables4 round
      hroundNonzero hroundBound hstateRound hstateSamples htrace with
    ⟨relation1, _relation2, _relation3, _layer0, _layer1,
      _layerPoints0, _layerPoints1, _point0, _point1,
      value0, value1, table0, table1, _polynomial, _polynomialTable,
      _hlayer0, _hlayer1, _hlayerPoints0, _hlayerPoints1,
      _hpoint0, _hpoint1, heval0, heval1,
      hcoefficients1, _hcoefficients2,
      _hpolyCall, _hpolyStored,
      htable0Stored, htable1Stored,
      _hood, hvalue0, hvalue1, _hsumchecks, _hpoly,
      _hround, _hsamples⟩
  let w : OodPairWitness :=
    { value0 := value0, value1 := value1, table0 := table0, table1 := table1 }
  rcases generated_line_ood_success_has_materialized_calls
      relation0 _ value0 table0 heval0 with ⟨evaluation0, hmaterialize0, _⟩
  rcases generated_line_ood_success_has_materialized_calls
      relation1 _ value1 table1 heval1 with ⟨evaluation1, hmaterialize1, _⟩
  have hmaterialize1' :
      v5_mask.relation_prover.V5IncrementalRelation.materialize_weights
          evaluation1 (alloc.vec.Vec.len relation0.coefficients) = ok table1 := by
    simpa [hcoefficients1] using hmaterialize1
  refine ⟨w, hvalue0, hvalue1, htable0Stored, htable1Stored,
    ⟨evaluation0, evaluation1, hmaterialize0, hmaterialize1'⟩, ?_⟩
  intro n hcoeffLength htable0Length htable1Length hn
    hcoeffCanonical htable0Canonical htable1Canonical
  constructor
  · exact generated_line_ood_success_eq_dotLinear
      relation0 _ value0 table0 n heval0
      hcoeffLength htable0Length hn hcoeffCanonical htable0Canonical
  · have hcoeffLength1 : relation1.coefficients.val.length = n := by
      rw [hcoefficients1, hcoeffLength]
    have hcoeffCanonical1 : RuntimeCanonicalList relation1.coefficients.val := by
      simpa [hcoefficients1] using hcoeffCanonical
    have h := generated_line_ood_success_eq_dotLinear
      relation1 _ value1 table1 n heval1
      hcoeffLength1 htable1Length hn hcoeffCanonical1 htable1Canonical
    simpa [hcoefficients1] using h

#print axioms generated_circle_round_trace_ood_semantics
#print axioms generated_line_round_trace_ood_semantics

end aspis_prover.ComponentCRuntimeRelationRoundOodSemantics
