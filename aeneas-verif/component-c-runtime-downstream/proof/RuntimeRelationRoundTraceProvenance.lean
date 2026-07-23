import RuntimeOodStateBounds
import RuntimeRelationRoundStateProvenance
import RuntimeRoundDeepControlFlow

set_option autoImplicit false

open Aeneas Aeneas.Std Result

namespace aspis_prover.ComponentCRuntimeRelationRoundTraceProvenance

open aspis_prover
open ComponentCRuntimeRoundDeepControlFlow
open ComponentCRuntimeRelationSampleStorage
open ComponentCRuntimeRelationRoundStateProvenance

abbrev RawQM31 := aspis_core.field.QM31
abbrev RuntimeSchedule :=
  v5_mask.component_c_runtime.V5ComponentCRuntimeSchedule
abbrev RuntimeRelation :=
  v5_mask.relation_prover.V5IncrementalRelation
abbrev RuntimeTables :=
  v5_mask.component_c_runtime.V5ComponentCRuntimeRelationTables

private theorem wrapping_zero_one :
    Std.Usize.wrapping_add 0#usize 1#usize = 1#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (1#usize).hSize; scalar_tac)]
  norm_num

private theorem wrapping_one_one :
    Std.Usize.wrapping_add 1#usize 1#usize = 2#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (2#usize).hSize; scalar_tac)]
  norm_num

private theorem array_set_get_same
    {T : Type*} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize) (value : T)
    (hindex : index.val < N.val) :
    (values.set index value).val[index.val]! = value := by
  simp only [Array.set_val_eq]
  apply List.set_getElem!_eq
  exact ⟨by simpa [Array.length_eq] using hindex, rfl⟩

private theorem array_set_get_ne
    {T : Type*} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize) (value : T) (other : Nat)
    (hne : other ≠ index.val) :
    (values.set index value).val[other]! = values.val[other]! := by
  simp only [Array.set_val_eq]
  apply List.set_getElem!_ne
  exact Or.inr (Or.inl hne)

private theorem nested_set_get_same
    {T : Type*} [Inhabited T]
    (values : Array (Array T 2#usize) 4#usize)
    (round sample : Std.Usize) (value : T)
    (hround : round.val < 4) (hsample : sample.val < 2) :
    ((values.set round
      (values.val[round.val]!.set sample value)).val[round.val]!).val[
        sample.val]! = value := by
  rw [array_set_get_same values round
    (values.val[round.val]!.set sample value) hround]
  exact array_set_get_same values.val[round.val]! sample value hsample

private theorem nested_second_set_preserves_first
    {T : Type*} [Inhabited T]
    (values : Array (Array T 2#usize) 4#usize)
    (round : Std.Usize) (first second : T)
    (hround : round.val < 4) :
    (((values.set round
        (values.val[round.val]!.set 0#usize first)).set round
      ((values.set round
        (values.val[round.val]!.set 0#usize first)).val[round.val]!.set
          1#usize second)).val[round.val]!).val[0]! = first := by
  let after0 := values.set round
    (values.val[round.val]!.set 0#usize first)
  rw [array_set_get_same after0 round
    (after0.val[round.val]!.set 1#usize second) hround]
  rw [array_set_get_ne after0.val[round.val]! 1#usize second 0 (by norm_num)]
  rw [array_set_get_same values round
    (values.val[round.val]!.set 0#usize first) hround]
  exact array_set_get_same values.val[round.val]! 0#usize first (by norm_num)

/-- A successful generated circle relation round starts from sample zero,
writes exactly the two released OOD values and the seven-coefficient
polynomial, and exits at round one with the sample cursor reset.  This is a
whole-state provenance theorem, not merely a pair of point observations. -/
theorem generated_circle_round_trace_released_state
    (schedule : RuntimeSchedule)
    (relation0 relation4 : RuntimeRelation)
    (tables0 tables4 : RuntimeTables)
    (htrace : GeneratedRelationRoundTrace schedule relation0 relation4
      tables0 tables4 0#usize) :
    ∃ relation1 relation2 relation3 : RuntimeRelation,
    ∃ point0 point1 : aspis_core.circle.SecureCirclePoint,
    ∃ value0 value1 : RawQM31,
    ∃ table0 table1 : alloc.vec.Vec RawQM31,
    ∃ polynomial : Array RawQM31 7#usize,
    ∃ polynomialTable : alloc.vec.Vec RawQM31,
      Array.index_usize schedule.circle_ood_points 0#usize = ok point0 ∧
      Array.index_usize schedule.circle_ood_points 1#usize = ok point1 ∧
      v5_mask.relation_prover.V5IncrementalRelation.evaluate_circle_ood_with_table
          relation0 point0 = ok (core.result.Result.Ok (value0, table0)) ∧
      v5_mask.relation_prover.V5IncrementalRelation.evaluate_circle_ood_with_table
          relation1 point1 = ok (core.result.Result.Ok (value1, table1)) ∧
      relation1.coefficients = relation0.coefficients ∧
      relation2.coefficients = relation0.coefficients ∧
      v5_mask.relation_prover.V5IncrementalRelation.polynomial_with_table
          relation2 =
        ok (core.result.Result.Ok (polynomial, polynomialTable), relation3) ∧
      tables4.polynomial.val[0]! = polynomialTable ∧
      tables4.ood.val[0]!.val[0]! = table0 ∧
      tables4.ood.val[0]!.val[1]! = table1 ∧
      relation4.ood_values =
        (relation0.ood_values.set 0#usize
          (relation0.ood_values.val[0]!.set 0#usize value0)).set 0#usize
            ((relation0.ood_values.set 0#usize
              (relation0.ood_values.val[0]!.set 0#usize value0)).val[0]!.set
                1#usize value1) ∧
      relation4.ood_values.val[0]!.val[0]! = value0 ∧
      relation4.ood_values.val[0]!.val[1]! = value1 ∧
      relation4.sumchecks = relation0.sumchecks.set 0#usize polynomial ∧
      relation4.sumchecks.val[0]! = polynomial ∧
      relation4.round = 1#usize ∧
      relation4.samples = 0#usize := by
  rcases htrace with
    ⟨relation1, relation2, relation3, tables1, tables2,
      polynomial, polynomialTable, alpha,
      hsample0, hsample1, hpolynomial, _halpha, hfold,
      _hroundTrace, hoodStored, hstored⟩
  rcases generated_circle_sample_success_stores_table
      schedule relation0 relation1 tables0 tables1 0#usize 0#usize rfl
      (by norm_num) hsample0 with
    ⟨point0, value0, table0, mix0, hpoint0, hood0,
      _hmixRound0, _hmix0, hadd0, htable0, _htables1Update⟩
  rcases ComponentCRuntimeOodStateBounds.generated_circle_ood_success_state_bounds
      relation0 point0 value0 table0 hood0 with
    ⟨hstateRound, hsample0Bound⟩
  rcases generated_add_circle_success_state relation0 relation1
      point0 value0 mix0 hstateRound hsample0Bound hadd0 with
    ⟨hood1, _hvalue0, hsumchecks1, hcoefficients1, hround1, hsamples1⟩
  have hround1Zero : relation1.round = 0#usize := by
    rw [hround1, hstateRound]
  rcases generated_circle_sample_success_stores_table
      schedule relation1 relation2 tables1 tables2 0#usize 1#usize rfl
      (by norm_num) hsample1 with
    ⟨point1, value1, table1, mix1, hpoint1, hoodSample1,
      _hmixRound1, _hmix1, hadd1, htable1, htables2Update⟩
  rcases ComponentCRuntimeOodStateBounds.generated_circle_ood_success_state_bounds
      relation1 point1 value1 table1 hoodSample1 with
    ⟨_round1FromOod, hsample1Bound⟩
  have hwrap0 :
      (Std.Usize.wrapping_add relation0.samples 1#usize).val =
        relation0.samples.val + 1 := by
    rw [Std.Usize.wrapping_add_val_eq]
    apply Nat.mod_eq_of_lt
    have hthree := (3#usize).hSize
    scalar_tac
  have hstateSamples : relation0.samples = 0#usize := by
    apply UScalar.eq_of_val_eq
    change relation0.samples.val = 0
    have hsamples1Val := congrArg UScalar.val hsamples1
    rw [hwrap0] at hsamples1Val
    omega
  have hsamples1One : relation1.samples = 1#usize := by
    rw [hsamples1, hstateSamples, wrapping_zero_one]
  rcases generated_add_circle_success_state relation1 relation2
      point1 value1 mix1 hround1Zero (by simpa [hsamples1One]) hadd1 with
    ⟨hood2, _hvalue1, hsumchecks2, hcoefficients2, hround2, hsamples2⟩
  have hcoefficients2Initial :
      relation2.coefficients = relation0.coefficients := by
    rw [hcoefficients2, hcoefficients1]
  have hround2Zero : relation2.round = 0#usize := by
    rw [hround2, hround1Zero]
  have hsamples2Two : relation2.samples = 2#usize := by
    rw [hsamples2, hsamples1One, wrapping_one_one]
  rcases generated_polynomial_success_state relation2 relation3 polynomial
      polynomialTable (by rw [hround2Zero]; norm_num) hsamples2Two
      hpolynomial with
    ⟨hsumchecks3, _hpolyValue, hood3, _hcoefficients3,
      hround3, hsamples3⟩
  have hround3Zero : relation3.round = 0#usize := by
    rw [hround3, hround2Zero]
  have hsamples3Two : relation3.samples = 2#usize := by
    rw [hsamples3, hsamples2Two]
  rcases generated_fold_success_preserves_released_arrays relation3 relation4
      alpha (by rw [hround3Zero]; norm_num) hsamples3Two hfold with
    ⟨hood4, hsumchecks4, hround4, hsamples4⟩
  let after0 := relation0.ood_values.set 0#usize
    (relation0.ood_values.val[0]!.set 0#usize value0)
  let after1 := after0.set 0#usize
    (after0.val[0]!.set 1#usize value1)
  have hoodFinal : relation4.ood_values = after1 := by
    rw [hood4, hood3, hood2, hood1, hstateSamples, hsamples1One]
  have htable0Final : tables4.ood.val[0]!.val[0]! = table0 := by
    have houter :
        tables2.ood.val[0]! =
          tables1.ood.val[0]!.set 1#usize table1 := by
      calc
        tables2.ood.val[0]! =
            (tables1.ood.set 0#usize
              (tables1.ood.val[0]!.set 1#usize table1)).val[0]! :=
          congrArg (fun rows => rows.val[0]!) htables2Update
        _ = tables1.ood.val[0]!.set 1#usize table1 :=
          array_set_get_same tables1.ood 0#usize
            (tables1.ood.val[0]!.set 1#usize table1) (by norm_num)
    have hinner :
        (tables1.ood.val[0]!.set 1#usize table1).val[0]! =
          tables1.ood.val[0]!.val[0]! :=
      array_set_get_ne tables1.ood.val[0]! 1#usize table1 0 (by norm_num)
    calc
      tables4.ood.val[0]!.val[0]! = tables2.ood.val[0]!.val[0]! :=
        congrArg (fun rows => rows.val[0]!.val[0]!) hoodStored
      _ = (tables1.ood.val[0]!.set 1#usize table1).val[0]! :=
        congrArg (fun row => row.val[0]!) houter
      _ = tables1.ood.val[0]!.val[0]! := hinner
      _ = table0 := htable0
  have htable1Final : tables4.ood.val[0]!.val[1]! = table1 := by
    rw [hoodStored]
    exact htable1
  refine ⟨relation1, relation2, relation3,
    point0, point1, value0, value1,
    table0, table1, polynomial, polynomialTable,
    hpoint0, hpoint1, hood0, hoodSample1,
    hcoefficients1, hcoefficients2Initial,
    hpolynomial, hstored, htable0Final, htable1Final,
    hoodFinal, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hoodFinal]
    exact nested_second_set_preserves_first relation0.ood_values 0#usize
      value0 value1 (by norm_num)
  · rw [hoodFinal]
    exact nested_set_get_same after0 0#usize 1#usize value1
      (by norm_num) (by norm_num)
  · rw [hsumchecks4, hsumchecks3, hsumchecks2, hsumchecks1,
      hround2Zero]
  · rw [hsumchecks4, hsumchecks3, hsumchecks2, hsumchecks1,
      hround2Zero]
    exact array_set_get_same relation0.sumchecks 0#usize polynomial (by norm_num)
  · rw [hround4, hround3Zero]
    exact wrapping_zero_one
  · exact hsamples4

/-- The same exact state theorem for each nonzero line round. -/
theorem generated_line_round_trace_released_state
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
    ∃ relation1 relation2 relation3 : RuntimeRelation,
    ∃ layer0 layer1 : Std.Usize,
    ∃ layerPoints0 layerPoints1 : Array RawQM31 2#usize,
    ∃ point0 point1 value0 value1 : RawQM31,
    ∃ table0 table1 : alloc.vec.Vec RawQM31,
    ∃ polynomial : Array RawQM31 7#usize,
    ∃ polynomialTable : alloc.vec.Vec RawQM31,
      lift (Std.Usize.wrapping_sub round 1#usize) = ok layer0 ∧
      lift (Std.Usize.wrapping_sub round 1#usize) = ok layer1 ∧
      Array.index_usize schedule.line_ood_points layer0 = ok layerPoints0 ∧
      Array.index_usize schedule.line_ood_points layer1 = ok layerPoints1 ∧
      Array.index_usize layerPoints0 0#usize = ok point0 ∧
      Array.index_usize layerPoints1 1#usize = ok point1 ∧
      v5_mask.relation_prover.V5IncrementalRelation.evaluate_line_ood_with_table
          relation0 point0 = ok (core.result.Result.Ok (value0, table0)) ∧
      v5_mask.relation_prover.V5IncrementalRelation.evaluate_line_ood_with_table
          relation1 point1 = ok (core.result.Result.Ok (value1, table1)) ∧
      relation1.coefficients = relation0.coefficients ∧
      relation2.coefficients = relation0.coefficients ∧
      v5_mask.relation_prover.V5IncrementalRelation.polynomial_with_table
          relation2 =
        ok (core.result.Result.Ok (polynomial, polynomialTable), relation3) ∧
      tables4.polynomial.val[round.val]! = polynomialTable ∧
      tables4.ood.val[round.val]!.val[0]! = table0 ∧
      tables4.ood.val[round.val]!.val[1]! = table1 ∧
      relation4.ood_values =
        (relation0.ood_values.set round
          (relation0.ood_values.val[round.val]!.set 0#usize value0)).set round
            ((relation0.ood_values.set round
              (relation0.ood_values.val[round.val]!.set 0#usize value0)).val[
                round.val]!.set 1#usize value1) ∧
      relation4.ood_values.val[round.val]!.val[0]! = value0 ∧
      relation4.ood_values.val[round.val]!.val[1]! = value1 ∧
      relation4.sumchecks = relation0.sumchecks.set round polynomial ∧
      relation4.sumchecks.val[round.val]! = polynomial ∧
      relation4.round = Std.Usize.wrapping_add round 1#usize ∧
      relation4.samples = 0#usize := by
  rcases htrace with
    ⟨relation1, relation2, relation3, tables1, tables2,
      polynomial, polynomialTable, alpha,
      hsample0, hsample1, hpolynomial, _halpha, hfold,
      _hroundTrace, hoodStored, hstored⟩
  rcases generated_line_sample_success_stores_table
      schedule relation0 relation1 tables0 tables1 round 0#usize
      hroundNonzero hroundBound (by norm_num) hsample0 with
    ⟨layer0, layerPoints0, point0, value0, table0, mix0,
      hlayer0, hlayerPoints0, hpoint0, hoodSample0,
      _hmixRound0, _hmix0, hadd0, htable0, _htables1Update⟩
  rcases generated_add_line_success_state relation0 relation1
      point0 value0 mix0 (by simpa [hstateRound] using hroundNonzero)
      (by simpa [hstateRound] using hroundBound)
      (by simpa [hstateSamples]) hadd0 with
    ⟨hood1, _hvalue0, hsumchecks1, hcoefficients1, hround1, hsamples1⟩
  have hround1Eq : relation1.round = round := by
    rw [hround1, hstateRound]
  have hsamples1One : relation1.samples = 1#usize := by
    rw [hsamples1, hstateSamples, wrapping_zero_one]
  rcases generated_line_sample_success_stores_table
      schedule relation1 relation2 tables1 tables2 round 1#usize
      hroundNonzero hroundBound (by norm_num) hsample1 with
    ⟨layer1, layerPoints1, point1, value1, table1, mix1,
      hlayer1, hlayerPoints1, hpoint1, hoodSample1,
      _hmixRound1, _hmix1, hadd1, htable1, htables2Update⟩
  rcases generated_add_line_success_state relation1 relation2
      point1 value1 mix1 (by simpa [hround1Eq] using hroundNonzero)
      (by simpa [hround1Eq] using hroundBound)
      (by simpa [hsamples1One]) hadd1 with
    ⟨hood2, _hvalue1, hsumchecks2, hcoefficients2, hround2, hsamples2⟩
  have hcoefficients2Initial :
      relation2.coefficients = relation0.coefficients := by
    rw [hcoefficients2, hcoefficients1]
  have hround2Eq : relation2.round = round := by
    rw [hround2, hround1Eq]
  have hsamples2Two : relation2.samples = 2#usize := by
    rw [hsamples2, hsamples1One, wrapping_one_one]
  rcases generated_polynomial_success_state relation2 relation3 polynomial
      polynomialTable (by simpa [hround2Eq] using hroundBound) hsamples2Two
      hpolynomial with
    ⟨hsumchecks3, _hpolyValue, hood3, _hcoefficients3,
      hround3, hsamples3⟩
  have hround3Eq : relation3.round = round := by
    rw [hround3, hround2Eq]
  have hsamples3Two : relation3.samples = 2#usize := by
    rw [hsamples3, hsamples2Two]
  rcases generated_fold_success_preserves_released_arrays relation3 relation4
      alpha (by simpa [hround3Eq] using hroundBound) hsamples3Two hfold with
    ⟨hood4, hsumchecks4, hround4, hsamples4⟩
  let after0 := relation0.ood_values.set round
    (relation0.ood_values.val[round.val]!.set 0#usize value0)
  let after1 := after0.set round
    (after0.val[round.val]!.set 1#usize value1)
  have hoodFinal : relation4.ood_values = after1 := by
    rw [hood4, hood3, hood2, hood1, hstateRound, hstateSamples,
      hround1Eq, hsamples1One]
  have htable0Final :
      tables4.ood.val[round.val]!.val[0]! = table0 := by
    rw [hoodStored, htables2Update]
    rw [array_set_get_same tables1.ood round
      (tables1.ood.val[round.val]!.set 1#usize table1) hroundBound]
    rw [array_set_get_ne tables1.ood.val[round.val]! 1#usize table1 0
      (by norm_num)]
    exact htable0
  have htable1Final :
      tables4.ood.val[round.val]!.val[1]! = table1 := by
    rw [hoodStored]
    exact htable1
  refine ⟨relation1, relation2, relation3,
    layer0, layer1, layerPoints0, layerPoints1,
    point0, point1, value0, value1, table0, table1, polynomial,
    polynomialTable,
    hlayer0, hlayer1, hlayerPoints0, hlayerPoints1, hpoint0, hpoint1,
    hoodSample0, hoodSample1, hcoefficients1, hcoefficients2Initial,
    hpolynomial, hstored, htable0Final, htable1Final,
    hoodFinal, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hoodFinal]
    exact nested_second_set_preserves_first relation0.ood_values round
      value0 value1 hroundBound
  · rw [hoodFinal]
    exact nested_set_get_same after0 round 1#usize value1
      hroundBound (by norm_num)
  · rw [hsumchecks4, hsumchecks3, hsumchecks2, hsumchecks1, hround2Eq]
  · rw [hsumchecks4, hsumchecks3, hsumchecks2, hsumchecks1, hround2Eq]
    exact array_set_get_same relation0.sumchecks round polynomial hroundBound
  · rw [hround4, hround3Eq]
  · exact hsamples4

#print axioms generated_circle_round_trace_released_state
#print axioms generated_line_round_trace_released_state

end aspis_prover.ComponentCRuntimeRelationRoundTraceProvenance
