import RuntimeGeneratedRelationSchedule
import RuntimeFourRoundFinalCoefficients

set_option autoImplicit false

open Aeneas Aeneas.Std Result

namespace aspis_prover.ComponentCRuntimeFourRoundRelationSemantics

open aspis_prover
open ComponentCRuntimeFourRoundFinalCoefficients
open ComponentCRuntimeGeneratedRelationSchedule
open ComponentCRuntimeRelationRoundOodSemantics
open ComponentCRuntimeRelationRoundPolynomialSemantics
open ComponentCRuntimeRelationRoundTraceProvenance
open ComponentCRuntimeRoundDeepControlFlow

abbrev RawQM31 := aspis_core.field.QM31
abbrev RuntimeSchedule :=
  v5_mask.component_c_runtime.V5ComponentCRuntimeSchedule
abbrev RuntimeRelation :=
  v5_mask.relation_prover.V5IncrementalRelation
abbrev RuntimeTables :=
  v5_mask.component_c_runtime.V5ComponentCRuntimeRelationTables

local instance : Inhabited RawQM31 :=
  ComponentCRuntimeLaterFibreProof.instInhabitedQM31_runtimeLaterFibreCorrespondence

private theorem array_set_get_ne
    {T : Type*} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize) (value : T) (other : Nat)
    (hne : other ≠ index.val) :
    (values.set index value).val[other]! = values.val[other]! := by
  simp only [Array.set_val_eq]
  apply List.set_getElem!_ne
  exact Or.inr (Or.inl hne)

private theorem nested_two_set_get_ne
    {T : Type*} [Inhabited T]
    (values : Array (Array T 2#usize) 4#usize)
    (round : Std.Usize) (value0 value1 : T) (other : Nat)
    (hne : other ≠ round.val) :
    ((values.set round
      (values.val[round.val]!.set 0#usize value0)).set round
        ((values.set round
          (values.val[round.val]!.set 0#usize value0)).val[round.val]!.set
            1#usize value1)).val[other]! = values.val[other]! := by
  rw [array_set_get_ne _ round _ other hne]
  exact array_set_get_ne values round _ other hne

/-- A line relation round changes only its own released OOD/polynomial row.
This is derived from the whole-state source trace, not a serializer premise. -/
theorem generated_line_trace_preserves_other_released_row
    (schedule : RuntimeSchedule)
    (relation relationOut : RuntimeRelation)
    (tables tablesOut : RuntimeTables)
    (round : Std.Usize)
    (hroundNonzero : round ≠ 0#usize)
    (hroundBound : round.val < 4)
    (hstateRound : relation.round = round)
    (hstateSamples : relation.samples = 0#usize)
    (htrace : GeneratedRelationRoundTrace schedule relation relationOut
      tables tablesOut round)
    (other : Nat) (hne : other ≠ round.val) :
    relationOut.ood_values.val[other]! = relation.ood_values.val[other]! ∧
      relationOut.sumchecks.val[other]! = relation.sumchecks.val[other]! := by
  rcases generated_line_round_trace_released_state
      schedule relation relationOut tables tablesOut round hroundNonzero
      hroundBound hstateRound hstateSamples htrace with
    ⟨_r1, _r2, _r3, _layer0, _layer1, _layerPoints0, _layerPoints1,
      _point0, _point1, value0, value1, _table0, _table1,
      polynomial, _polynomialTable,
      _hlayer0, _hlayer1, _hlayerPoints0, _hlayerPoints1,
      _hpoint0, _hpoint1, _heval0, _heval1, _hcoeff1, _hcoeff2,
      _hpolynomial, _hstored, _htable0Stored, _htable1Stored,
      hood, _hvalue0, _hvalue1,
      hsumchecks, _hsumcheck, _hround, _hsamples⟩
  constructor
  · rw [hood]
    exact nested_two_set_get_ne relation.ood_values round
      value0 value1 other hne
  · rw [hsumchecks]
    exact array_set_get_ne relation.sumchecks round polynomial other hne

/-- All eight actual OOD values and all four actual polynomial messages are
paired with the exact returned materialized tables that produced them.  The
equalities target the final relation state after proving later rounds preserve
earlier rows. -/
structure FourRoundRelationSemantics
    (relation0 relation1 relation2 relation3 relation4 : RuntimeRelation) where
  tables : FourRoundGeneratedTables
  ood0_match : ∀ sample : Fin 2,
    relation4.ood_values.val[0]!.val[sample.val]! =
      oodPairValue tables.ood0 sample
  ood1_match : ∀ sample : Fin 2,
    relation4.ood_values.val[1]!.val[sample.val]! =
      oodPairValue tables.ood1 sample
  ood2_match : ∀ sample : Fin 2,
    relation4.ood_values.val[2]!.val[sample.val]! =
      oodPairValue tables.ood2 sample
  ood3_match : ∀ sample : Fin 2,
    relation4.ood_values.val[3]!.val[sample.val]! =
      oodPairValue tables.ood3 sample
  polynomial0_match : relation4.sumchecks.val[0]! = tables.polynomial0.polynomial
  polynomial1_match : relation4.sumchecks.val[1]! = tables.polynomial1.polynomial
  polynomial2_match : relation4.sumchecks.val[2]! = tables.polynomial2.polynomial
  polynomial3_match : relation4.sumchecks.val[3]! = tables.polynomial3.polynomial
  ood0_semantics : OodPairDotSemantics relation0.coefficients tables.ood0
  ood1_semantics : OodPairDotSemantics relation1.coefficients tables.ood1
  ood2_semantics : OodPairDotSemantics relation2.coefficients tables.ood2
  ood3_semantics : OodPairDotSemantics relation3.coefficients tables.ood3
  polynomial0_semantics :
    PolynomialSemantics relation0.coefficients tables.polynomial0
  polynomial1_semantics :
    PolynomialSemantics relation1.coefficients tables.polynomial1
  polynomial2_semantics :
    PolynomialSemantics relation2.coefficients tables.polynomial2
  polynomial3_semantics :
    PolynomialSemantics relation3.coefficients tables.polynomial3

/-- Four actual source traces instantiate the complete semantic witness. -/
theorem generated_four_round_relation_semantics
    (schedule : RuntimeSchedule)
    (relation0 relation1 relation2 relation3 relation4 : RuntimeRelation)
    (tables0 tables1 tables2 tables3 tables4 : RuntimeTables)
    (htrace0 : GeneratedRelationRoundTrace schedule relation0 relation1
      tables0 tables1 0#usize)
    (htrace1 : GeneratedRelationRoundTrace schedule relation1 relation2
      tables1 tables2 1#usize)
    (htrace2 : GeneratedRelationRoundTrace schedule relation2 relation3
      tables2 tables3 2#usize)
    (htrace3 : GeneratedRelationRoundTrace schedule relation3 relation4
      tables3 tables4 3#usize) :
    ∃ semantics : FourRoundRelationSemantics
      relation0 relation1 relation2 relation3 relation4, True := by
  have hstate1 := generated_circle_trace_next_state
    schedule relation0 relation1 tables0 tables1 htrace0
  have hstate2Raw := generated_line_trace_next_state
    schedule relation1 relation2 tables1 tables2 1#usize
    (by norm_num) (by norm_num) hstate1.1 hstate1.2 htrace1
  have hstate2 : relation2.round = 2#usize ∧ relation2.samples = 0#usize := by
    have hwrap : Std.Usize.wrapping_add 1#usize 1#usize = 2#usize := by
      apply UScalar.val_eq_imp
      rw [Std.Usize.wrapping_add_val_eq, Nat.mod_eq_of_lt]
      · norm_num
      · have h := (2#usize).hSize
        scalar_tac
    rw [hwrap] at hstate2Raw
    exact hstate2Raw
  have hstate3Raw := generated_line_trace_next_state
    schedule relation2 relation3 tables2 tables3 2#usize
    (by norm_num) (by norm_num) hstate2.1 hstate2.2 htrace2
  have hstate3 : relation3.round = 3#usize ∧ relation3.samples = 0#usize := by
    have hwrap : Std.Usize.wrapping_add 2#usize 1#usize = 3#usize := by
      apply UScalar.val_eq_imp
      rw [Std.Usize.wrapping_add_val_eq, Nat.mod_eq_of_lt]
      · norm_num
      · have h := (3#usize).hSize
        scalar_tac
    rw [hwrap] at hstate3Raw
    exact hstate3Raw
  rcases generated_circle_round_trace_ood_semantics
      schedule relation0 relation1 tables0 tables1 htrace0 with
    ⟨ood0, hood00, hood01, _htable00, _htable01, hoodSem0⟩
  rcases generated_line_round_trace_ood_semantics
      schedule relation1 relation2 tables1 tables2 1#usize
      (by norm_num) (by norm_num) hstate1.1 hstate1.2 htrace1 with
    ⟨ood1, hood10, hood11, _htable10, _htable11, hoodSem1⟩
  rcases generated_line_round_trace_ood_semantics
      schedule relation2 relation3 tables2 tables3 2#usize
      (by norm_num) (by norm_num) hstate2.1 hstate2.2 htrace2 with
    ⟨ood2, hood20, hood21, _htable20, _htable21, hoodSem2⟩
  rcases generated_line_round_trace_ood_semantics
      schedule relation3 relation4 tables3 tables4 3#usize
      (by norm_num) (by norm_num) hstate3.1 hstate3.2 htrace3 with
    ⟨ood3, hood30, hood31, _htable30, _htable31, hoodSem3⟩
  rcases generated_circle_round_trace_polynomial_semantics
      schedule relation0 relation1 tables0 tables1 htrace0 with
    ⟨poly0, hpoly0, _hpolyTable0, hpolySem0⟩
  rcases generated_line_round_trace_polynomial_semantics
      schedule relation1 relation2 tables1 tables2 1#usize
      (by norm_num) (by norm_num) hstate1.1 hstate1.2 htrace1 with
    ⟨poly1, hpoly1, _hpolyTable1, hpolySem1⟩
  rcases generated_line_round_trace_polynomial_semantics
      schedule relation2 relation3 tables2 tables3 2#usize
      (by norm_num) (by norm_num) hstate2.1 hstate2.2 htrace2 with
    ⟨poly2, hpoly2, _hpolyTable2, hpolySem2⟩
  rcases generated_line_round_trace_polynomial_semantics
      schedule relation3 relation4 tables3 tables4 3#usize
      (by norm_num) (by norm_num) hstate3.1 hstate3.2 htrace3 with
    ⟨poly3, hpoly3, _hpolyTable3, hpolySem3⟩
  have hp10 := generated_line_trace_preserves_other_released_row
    schedule relation1 relation2 tables1 tables2 1#usize
    (by norm_num) (by norm_num) hstate1.1 hstate1.2 htrace1 0 (by norm_num)
  have hp20 := generated_line_trace_preserves_other_released_row
    schedule relation2 relation3 tables2 tables3 2#usize
    (by norm_num) (by norm_num) hstate2.1 hstate2.2 htrace2 0 (by norm_num)
  have hp21 := generated_line_trace_preserves_other_released_row
    schedule relation2 relation3 tables2 tables3 2#usize
    (by norm_num) (by norm_num) hstate2.1 hstate2.2 htrace2 1 (by norm_num)
  have hp30 := generated_line_trace_preserves_other_released_row
    schedule relation3 relation4 tables3 tables4 3#usize
    (by norm_num) (by norm_num) hstate3.1 hstate3.2 htrace3 0 (by norm_num)
  have hp31 := generated_line_trace_preserves_other_released_row
    schedule relation3 relation4 tables3 tables4 3#usize
    (by norm_num) (by norm_num) hstate3.1 hstate3.2 htrace3 1 (by norm_num)
  have hp32 := generated_line_trace_preserves_other_released_row
    schedule relation3 relation4 tables3 tables4 3#usize
    (by norm_num) (by norm_num) hstate3.1 hstate3.2 htrace3 2 (by norm_num)
  let generatedTables : FourRoundGeneratedTables := {
    ood0 := ood0, ood1 := ood1, ood2 := ood2, ood3 := ood3,
    polynomial0 := poly0, polynomial1 := poly1,
    polynomial2 := poly2, polynomial3 := poly3 }
  let semantics : FourRoundRelationSemantics
      relation0 relation1 relation2 relation3 relation4 := {
    tables := generatedTables
    ood0_match := by
      intro sample
      rw [hp30.1, hp20.1, hp10.1]
      fin_cases sample
      · exact hood00
      · exact hood01
    ood1_match := by
      intro sample
      rw [hp31.1, hp21.1]
      fin_cases sample
      · exact hood10
      · exact hood11
    ood2_match := by
      intro sample
      rw [hp32.1]
      fin_cases sample
      · exact hood20
      · exact hood21
    ood3_match := by
      intro sample
      fin_cases sample
      · exact hood30
      · exact hood31
    polynomial0_match := by rw [hp30.2, hp20.2, hp10.2]; exact hpoly0
    polynomial1_match := by rw [hp31.2, hp21.2]; exact hpoly1
    polynomial2_match := by rw [hp32.2]; exact hpoly2
    polynomial3_match := hpoly3
    ood0_semantics := hoodSem0
    ood1_semantics := hoodSem1
    ood2_semantics := hoodSem2
    ood3_semantics := hoodSem3
    polynomial0_semantics := hpolySem0
    polynomial1_semantics := hpolySem1
    polynomial2_semantics := hpolySem2
    polynomial3_semantics := hpolySem3 }
  exact ⟨semantics, trivial⟩

#print axioms generated_line_trace_preserves_other_released_row
#print axioms generated_four_round_relation_semantics

end aspis_prover.ComponentCRuntimeFourRoundRelationSemantics
