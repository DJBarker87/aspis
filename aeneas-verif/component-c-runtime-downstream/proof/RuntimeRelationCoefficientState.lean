import RuntimeRelationRoundTraceProvenance

set_option autoImplicit false

open Aeneas Aeneas.Std Result

namespace aspis_prover.ComponentCRuntimeRelationCoefficientState

open aspis_prover
open ComponentCRuntimeRelationSampleStorage
open ComponentCRuntimeRelationRoundStateProvenance
open ComponentCRuntimeRoundDeepControlFlow

abbrev RawQM31 := aspis_core.field.QM31
abbrev RuntimeSchedule :=
  v5_mask.component_c_runtime.V5ComponentCRuntimeSchedule
abbrev RuntimeRelation :=
  v5_mask.relation_prover.V5IncrementalRelation
abbrev RuntimeTables :=
  v5_mask.component_c_runtime.V5ComponentCRuntimeRelationTables

/-- One successful generated runtime relation-sample wrapper preserves the
coefficient vector and the round, and advances only the sample cursor.  The
proof follows the actual circle/line branch and its actual add call. -/
theorem generated_relation_sample_preserves_coefficient_state
    (schedule : RuntimeSchedule)
    (relation relationOut : RuntimeRelation)
    (tables tablesOut : RuntimeTables)
    (round sample : Std.Usize)
    (hroundBound : round.val < 4)
    (hstateRound : relation.round = round)
    (hsampleArgBound : sample.val < 2)
    (hsampleBound : relation.samples.val < 2)
    (hrun :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_sample
          schedule relation tables round sample =
        ok (core.result.Result.Ok (), relationOut, tablesOut)) :
    relationOut.coefficients = relation.coefficients ∧
      relationOut.round = relation.round ∧
      relationOut.samples =
        Std.Usize.wrapping_add relation.samples 1#usize := by
  by_cases hroundZero : round = 0#usize
  · rcases generated_circle_sample_success_stores_table
      schedule relation relationOut tables tablesOut round sample
      hroundZero hsampleArgBound hrun with
      ⟨point, value, _table, mix, _hpoint, _hood,
        _hmixRound, _hmix, hadd, _hstored, _hoodUpdate⟩
    have hrelationZero : relation.round = 0#usize := by
      rw [hstateRound, hroundZero]
    rcases generated_add_circle_success_state relation relationOut
      point value mix hrelationZero hsampleBound hadd with
      ⟨_hood, _hvalue, _hsumchecks, hcoefficients,
        hround, hsamples⟩
    exact ⟨hcoefficients, hround, hsamples⟩
  · rcases generated_line_sample_success_stores_table
      schedule relation relationOut tables tablesOut round sample
      hroundZero hroundBound hsampleArgBound hrun with
      ⟨_layer, _layerPoints, point, value, _table, mix,
        _hlayer, _hlayerPoints, _hpoint, _hood,
        _hmixRound, _hmix, hadd, _hstored, _hoodUpdate⟩
    have hrelationNonzero : relation.round ≠ 0#usize := by
      rw [hstateRound]
      exact hroundZero
    have hrelationBound : relation.round.val < 4 := by
      rw [hstateRound]
      exact hroundBound
    rcases generated_add_line_success_state relation relationOut
      point value mix hrelationNonzero hrelationBound hsampleBound hadd with
      ⟨_hood, _hvalue, _hsumchecks, hcoefficients,
        hround, hsamples⟩
    exact ⟨hcoefficients, hround, hsamples⟩

/-- One fully exposed generated relation round applies the source-extracted
natural arity-four coefficient fold to exactly the incoming coefficient
vector and installs its output.  The two OOD samples and polynomial step are
proved coefficient-neutral; no pre-fold equality is assumed. -/
theorem generated_relation_round_trace_exposes_coefficient_fold
    (schedule : RuntimeSchedule)
    (relation relationOut : RuntimeRelation)
    (tables tablesOut : RuntimeTables)
    (round : Std.Usize)
    (hstateRound : relation.round = round)
    (hstateSamples : relation.samples = 0#usize)
    (htrace : GeneratedRelationRoundTrace schedule relation relationOut
      tables tablesOut round) :
    ∃ alpha : RawQM31, ∃ coefficientsAfter : alloc.vec.Vec RawQM31,
      Array.index_usize schedule.alphas round = ok alpha ∧
      circle_candidate.fold_adjacent_natural_arity4
          (alloc.vec.Vec.deref relation.coefficients) alpha =
        ok coefficientsAfter ∧
      relationOut.coefficients = coefficientsAfter := by
  rcases htrace with
    ⟨relation1, relation2, relation3, tables1, tables2,
      polynomial, table, alpha,
      hsample0, hsample1, hpolynomial, halpha, hfold,
      hroundBoundScalar, _hoodStored, _hstored⟩
  have hroundBound : round.val < 4 := by scalar_tac
  have hsample0Bound : relation.samples.val < 2 := by
    rw [hstateSamples]
    norm_num
  rcases generated_relation_sample_preserves_coefficient_state
      schedule relation relation1 tables tables1 round 0#usize
      hroundBound hstateRound (by norm_num) hsample0Bound hsample0 with
    ⟨hcoefficients1, hround1, hsamples1⟩
  have hsamples1Exact : relation1.samples = 1#usize := by
    rw [hsamples1, hstateSamples]
    apply UScalar.val_eq_imp
    rw [Std.Usize.wrapping_add_val_eq]
    rw [Nat.mod_eq_of_lt]
    · norm_num
    · have h := (1#usize).hSize
      scalar_tac
  have hsample1Bound : relation1.samples.val < 2 := by
    rw [hsamples1Exact]
    norm_num
  rcases generated_relation_sample_preserves_coefficient_state
      schedule relation1 relation2 tables1 tables2 round 1#usize
      hroundBound (by rw [hround1, hstateRound])
      (by norm_num) hsample1Bound hsample1 with
    ⟨hcoefficients2, _hround2, _hsamples2⟩
  have hpolyState := generated_polynomial_success_requires_state
    relation2 relation3 polynomial table hpolynomial
  rcases generated_polynomial_success_state relation2 relation3
      polynomial table hpolyState.1 hpolyState.2 hpolynomial with
    ⟨_hsumchecks, _hpolyValue, _hood, hcoefficients3,
      _hround3, _hsamples3⟩
  have hfoldState := generated_fold_success_requires_state
    relation3 relationOut alpha hfold
  rcases generated_fold_success_exposes_coefficients relation3 relationOut
      alpha hfoldState.1 hfoldState.2 hfold with
    ⟨coefficientsAfter, hcoefficientCall, hcoefficientsOut⟩
  have hpreFold : relation3.coefficients = relation.coefficients := by
    rw [hcoefficients3, hcoefficients2, hcoefficients1]
  refine ⟨alpha, coefficientsAfter, halpha, ?_, hcoefficientsOut⟩
  simpa [hpreFold] using hcoefficientCall

#print axioms generated_relation_sample_preserves_coefficient_state
#print axioms generated_relation_round_trace_exposes_coefficient_fold

end aspis_prover.ComponentCRuntimeRelationCoefficientState
