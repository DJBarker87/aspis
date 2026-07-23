import RuntimePublicPackerCapstone
import RuntimeFourRoundLaterMaintained
import RuntimeFourRoundFinalCoefficients
import RuntimeRelationRoundOodSemantics
import RuntimeRelationRoundPolynomialSemantics
import RuntimeGeneratedRelationSchedule

set_option autoImplicit false

open Aeneas Aeneas.Std Result

namespace aspis_prover.ComponentCRuntimeReleasedTraceFamilies

open aspis_prover
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5ComponentCDownstreamDeployed
open AspisV5ComponentCRelationRowLinearity
open ComponentCRuntimeCoefficientFoldCorrespondence
open ComponentCRuntimeCoefficientTowerCorrespondence
open ComponentCRuntimeFourRoundFinalCoefficients
open ComponentCRuntimeFourRoundLaterMaintained
open ComponentCRuntimeGeneratedRelationSchedule
open ComponentCRuntimeMaterializedRelationArithmetic
open ComponentCRuntimePublicPackerCapstone
open ComponentCRuntimeRelationFinishProvenance
open ComponentCRuntimeRoundDeepControlFlow
open ComponentCRuntimeScheduleProof

abbrev RawQM31 := aspis_core.field.QM31
abbrev BaseField := AspisV5ComponentCQM31TowerExact.M31Exact
abbrev ExtensionField := AspisV5ComponentCQM31TowerExact.QM31Exact
abbrev RuntimeSchedule :=
  v5_mask.component_c_runtime.V5ComponentCRuntimeSchedule
abbrev RuntimeRelation :=
  v5_mask.relation_prover.V5IncrementalRelation
abbrev RuntimeTables :=
  v5_mask.component_c_runtime.V5ComponentCRuntimeRelationTables
abbrev RuntimeLater := Array (alloc.vec.Vec RawQM31) 3#usize
abbrev RuntimeTrace := v5_mask.relation_prover.V5RelationTrace

open ComponentCRuntimeRelationRoundOodSemantics
open ComponentCRuntimeRelationRoundPolynomialSemantics
open ComponentCRuntimeRelationRoundTraceProvenance
open ComponentCRuntimeFoldPrimitiveInstantiation

private theorem list_getElem_bang_irrel
    {T : Type*} (inst1 inst2 : Inhabited T) (values : List T)
    (index : Nat) (hindex : index < values.length) :
    @getElem! (List T) Nat T (fun xs i => i < xs.length)
        List.instGetElem?NatLtLength inst1 values index =
      @getElem! (List T) Nat T (fun xs i => i < xs.length)
        List.instGetElem?NatLtLength inst2 values index := by
  simp [hindex]

private theorem exact_slice_vector_eq_coefficient_view
    (values : Slice RawQM31) (n : Nat)
    (hlength : values.val.length = n) :
    ComponentCRuntimeMaterializedRelationArithmetic.exactSliceVector n values =
      runtimeCoefficientView values n := by
  funext row
  unfold ComponentCRuntimeMaterializedRelationArithmetic.exactSliceVector
    ComponentCRuntimeMaterializedRelationArithmetic.exactSliceEntry
    runtimeCoefficientView
  apply congrArg runtimeQM31View
  apply list_getElem_bang_irrel
  simpa [hlength] using row.isLt

private theorem array3_eq_entries
    {T : Type*} [Inhabited T] (values : Array T 3#usize) :
    values = Array.make 3#usize
      [values.val[0]!, values.val[1]!, values.val[2]!] := by
  rcases values with ⟨values, hlength⟩
  apply Subtype.ext
  simp only [Array.make]
  rcases values with _ | ⟨v0, values⟩
  · simp at hlength
  rcases values with _ | ⟨v1, values⟩
  · simp at hlength
  rcases values with _ | ⟨v2, values⟩
  · simp at hlength
  rcases values with _ | ⟨v3, values⟩
  · rfl
  · simp at hlength

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

private theorem generated_line_trace_preserves_other_released_row
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

/-- The exact generated OOD/polynomial witnesses selected by four authentic
relation traces. -/
structure ReleasedRelationSemantics
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

private theorem generated_released_relation_semantics
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
    Nonempty (ReleasedRelationSemantics
      relation0 relation1 relation2 relation3 relation4) := by
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
  exact ⟨{
    tables := generatedTables
    ood0_match := by
      intro sample
      rw [hp30.1, hp20.1, hp10.1]
      fin_cases sample <;> assumption
    ood1_match := by
      intro sample
      rw [hp31.1, hp21.1]
      fin_cases sample <;> assumption
    ood2_match := by
      intro sample
      rw [hp32.1]
      fin_cases sample <;> assumption
    ood3_match := by intro sample; fin_cases sample <;> assumption
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
    polynomial3_semantics := hpolySem3 }⟩

/-- The finite representation facts for the twelve materialized tables
selected by the four authentic relation traces.  Every length and every
canonicality property is exposed separately; this is not an evaluator
correspondence or a `Faithful` predicate. -/
structure FourRoundGeneratedTableRepresentation
    (tables : FourRoundGeneratedTables) : Prop where
  ood00_length : tables.ood0.table0.val.length = 1024
  ood01_length : tables.ood0.table1.val.length = 1024
  ood10_length : tables.ood1.table0.val.length = 256
  ood11_length : tables.ood1.table1.val.length = 256
  ood20_length : tables.ood2.table0.val.length = 64
  ood21_length : tables.ood2.table1.val.length = 64
  ood30_length : tables.ood3.table0.val.length = 16
  ood31_length : tables.ood3.table1.val.length = 16
  polynomial0_length : tables.polynomial0.table.val.length = 1024
  polynomial1_length : tables.polynomial1.table.val.length = 256
  polynomial2_length : tables.polynomial2.table.val.length = 64
  polynomial3_length : tables.polynomial3.table.val.length = 16
  ood00_canonical :
    ComponentCRuntimeMaterializedRelationArithmetic.RuntimeCanonicalList
      tables.ood0.table0.val
  ood01_canonical :
    ComponentCRuntimeMaterializedRelationArithmetic.RuntimeCanonicalList
      tables.ood0.table1.val
  ood10_canonical :
    ComponentCRuntimeMaterializedRelationArithmetic.RuntimeCanonicalList
      tables.ood1.table0.val
  ood11_canonical :
    ComponentCRuntimeMaterializedRelationArithmetic.RuntimeCanonicalList
      tables.ood1.table1.val
  ood20_canonical :
    ComponentCRuntimeMaterializedRelationArithmetic.RuntimeCanonicalList
      tables.ood2.table0.val
  ood21_canonical :
    ComponentCRuntimeMaterializedRelationArithmetic.RuntimeCanonicalList
      tables.ood2.table1.val
  ood30_canonical :
    ComponentCRuntimeMaterializedRelationArithmetic.RuntimeCanonicalList
      tables.ood3.table0.val
  ood31_canonical :
    ComponentCRuntimeMaterializedRelationArithmetic.RuntimeCanonicalList
      tables.ood3.table1.val
  polynomial0_canonical :
    ComponentCRuntimeMaterializedRelationArithmetic.RuntimeCanonicalList
      tables.polynomial0.table.val
  polynomial1_canonical :
    ComponentCRuntimeMaterializedRelationArithmetic.RuntimeCanonicalList
      tables.polynomial1.table.val
  polynomial2_canonical :
    ComponentCRuntimeMaterializedRelationArithmetic.RuntimeCanonicalList
      tables.polynomial2.table.val
  polynomial3_canonical :
    ComponentCRuntimeMaterializedRelationArithmetic.RuntimeCanonicalList
      tables.polynomial3.table.val

private theorem runtimeCanonicalList_to_materialized
    (values : List RawQM31)
    (h : ComponentCRuntimeCoefficientFoldCorrespondence.RuntimeCanonicalList
      values) :
    ComponentCRuntimeMaterializedRelationArithmetic.RuntimeCanonicalList
      values := by
  exact h

private theorem generated_ood0_table_apply
    (base : DeployedRuntimeSchedule BaseField ExtensionField)
    (tables : FourRoundGeneratedTables) (sample : Fin 2) :
    (decodeRelationSchedule (withGeneratedRelationTables base tables)).ood0
        sample =
      exactSliceVector 1024
        (alloc.vec.Vec.deref (oodPairTable tables.ood0 sample)) := rfl

private theorem generated_ood1_table_apply
    (base : DeployedRuntimeSchedule BaseField ExtensionField)
    (tables : FourRoundGeneratedTables) (sample : Fin 2) :
    (decodeRelationSchedule (withGeneratedRelationTables base tables)).ood1
        sample =
      exactSliceVector 256
        (alloc.vec.Vec.deref (oodPairTable tables.ood1 sample)) := rfl

private theorem generated_ood2_table_apply
    (base : DeployedRuntimeSchedule BaseField ExtensionField)
    (tables : FourRoundGeneratedTables) (sample : Fin 2) :
    (decodeRelationSchedule (withGeneratedRelationTables base tables)).ood2
        sample =
      exactSliceVector 64
        (alloc.vec.Vec.deref (oodPairTable tables.ood2 sample)) := rfl

private theorem generated_ood3_table_apply
    (base : DeployedRuntimeSchedule BaseField ExtensionField)
    (tables : FourRoundGeneratedTables) (sample : Fin 2) :
    (decodeRelationSchedule (withGeneratedRelationTables base tables)).ood3
        sample =
      exactSliceVector 16
        (alloc.vec.Vec.deref (oodPairTable tables.ood3 sample)) := rfl

private theorem generated_polynomial0_table
    (base : DeployedRuntimeSchedule BaseField ExtensionField)
    (tables : FourRoundGeneratedTables) :
    (decodeRelationSchedule (withGeneratedRelationTables base tables)).poly0 =
      exactSliceVector 1024
        (alloc.vec.Vec.deref tables.polynomial0.table) := rfl

private theorem generated_polynomial1_table
    (base : DeployedRuntimeSchedule BaseField ExtensionField)
    (tables : FourRoundGeneratedTables) :
    (decodeRelationSchedule (withGeneratedRelationTables base tables)).poly1 =
      exactSliceVector 256
        (alloc.vec.Vec.deref tables.polynomial1.table) := rfl

private theorem generated_polynomial2_table
    (base : DeployedRuntimeSchedule BaseField ExtensionField)
    (tables : FourRoundGeneratedTables) :
    (decodeRelationSchedule (withGeneratedRelationTables base tables)).poly2 =
      exactSliceVector 64
        (alloc.vec.Vec.deref tables.polynomial2.table) := rfl

private theorem generated_polynomial3_table
    (base : DeployedRuntimeSchedule BaseField ExtensionField)
    (tables : FourRoundGeneratedTables) :
    (decodeRelationSchedule (withGeneratedRelationTables base tables)).poly3 =
      exactSliceVector 16
        (alloc.vec.Vec.deref tables.polynomial3.table) := rfl


/-- The four source-authentic relation traces, their exact generated tables,
and the coefficient tower give all 36 maintained relation coordinates. -/
theorem generated_four_round_relation_rows_match_maintained
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
      tables3 tables4 3#usize)
    (hstateRound0 : relation0.round = 0#usize)
    (hstateSamples0 : relation0.samples = 0#usize)
    (hcoeffLength : relation0.coefficients.val.length = 1024)
    (hcoeffCanonical :
      ComponentCRuntimeCoefficientFoldCorrespondence.RuntimeCanonicalList
        relation0.coefficients.val)
    (halpha0 : runtimeCanonicalQM31 schedule.alphas.val[0]!)
    (halpha1 : runtimeCanonicalQM31 schedule.alphas.val[1]!)
    (halpha2 : runtimeCanonicalQM31 schedule.alphas.val[2]!)
    (halpha3 : runtimeCanonicalQM31 schedule.alphas.val[3]!)
    (base : DeployedRuntimeSchedule BaseField ExtensionField)
    (indices : QueryIndices)
    (hrange : GeneratedLaterFibresInRange indices)
    (c : AspisV5ComponentCConcreteFoldLinearity.Coefficients ExtensionField)
    (hinput : runtimeCoefficientView
      (alloc.vec.Vec.deref relation0.coefficients) 1024 = c)
    (halpha : ∀ round : Fin 4,
      runtimeQM31View schedule.alphas.val[round.val]! = base.alpha round) :
    ∃ semantics : ReleasedRelationSemantics
      relation0 relation1 relation2 relation3 relation4,
      ∀ representation : FourRoundGeneratedTableRepresentation semantics.tables,
        let rt := withGeneratedRelationTables
          (withGeneratedLaterFibres base indices hrange) semantics.tables
        (∀ (round : Fin 4) (sample : Fin 2),
          runtimeQM31View relation4.ood_values.val[round.val]!.val[sample.val]! =
            roundOodRows (decodeRelationSchedule rt) round c sample) ∧
        (∀ (round : Fin 4) (degree : Fin 7),
          runtimeQM31View relation4.sumchecks.val[round.val]!.val[degree.val]! =
            roundPolynomialRows (decodeRelationSchedule rt) round c degree) ∧
        (∀ coefficient : Fin 4,
          runtimeQM31View relation4.coefficients.val[coefficient.val]! =
            finalCoefficientMap (decodeFriSchedule rt) c coefficient) := by
  rcases generated_released_relation_semantics schedule
      relation0 relation1 relation2 relation3 relation4
      tables0 tables1 tables2 tables3 tables4
      htrace0 htrace1 htrace2 htrace3 with ⟨semantics⟩
  refine ⟨semantics, ?_⟩
  intro representation
  dsimp only
  let laterRt := withGeneratedLaterFibres base indices hrange
  let rt := withGeneratedRelationTables laterRt semantics.tables
  have halpha0' : runtimeCanonicalQM31
      (@getElem! (List RawQM31) Nat RawQM31
        (fun xs i => i < xs.length) List.instGetElem?NatLtLength
        ComponentCRuntimeFourRoundFinalCoefficients.instInhabitedRawQM31
        schedule.alphas.val 0) := by
    rw [list_getElem_bang_irrel
      ComponentCRuntimeFourRoundFinalCoefficients.instInhabitedRawQM31
      (inferInstance : Inhabited RawQM31) schedule.alphas.val 0 (by simp)]
    exact halpha0
  have halpha1' : runtimeCanonicalQM31
      (@getElem! (List RawQM31) Nat RawQM31
        (fun xs i => i < xs.length) List.instGetElem?NatLtLength
        ComponentCRuntimeFourRoundFinalCoefficients.instInhabitedRawQM31
        schedule.alphas.val 1) := by
    rw [list_getElem_bang_irrel
      ComponentCRuntimeFourRoundFinalCoefficients.instInhabitedRawQM31
      (inferInstance : Inhabited RawQM31) schedule.alphas.val 1 (by simp)]
    exact halpha1
  have halpha2' : runtimeCanonicalQM31
      (@getElem! (List RawQM31) Nat RawQM31
        (fun xs i => i < xs.length) List.instGetElem?NatLtLength
        ComponentCRuntimeFourRoundFinalCoefficients.instInhabitedRawQM31
        schedule.alphas.val 2) := by
    rw [list_getElem_bang_irrel
      ComponentCRuntimeFourRoundFinalCoefficients.instInhabitedRawQM31
      (inferInstance : Inhabited RawQM31) schedule.alphas.val 2 (by simp)]
    exact halpha2
  have halpha3' : runtimeCanonicalQM31
      (@getElem! (List RawQM31) Nat RawQM31
        (fun xs i => i < xs.length) List.instGetElem?NatLtLength
        ComponentCRuntimeFourRoundFinalCoefficients.instInhabitedRawQM31
        schedule.alphas.val 3) := by
    rw [list_getElem_bang_irrel
      ComponentCRuntimeFourRoundFinalCoefficients.instInhabitedRawQM31
      (inferInstance : Inhabited RawQM31) schedule.alphas.val 3 (by simp)]
    exact halpha3
  have hinputExact :
      exactSliceVector 1024 (alloc.vec.Vec.deref relation0.coefficients) = c := by
    exact (exact_slice_vector_eq_coefficient_view _ 1024 hcoeffLength).trans
      hinput
  have hcoefficients := generated_four_relation_rounds_final_coefficient_map
    schedule relation0 relation1 relation2 relation3 relation4
    tables0 tables1 tables2 tables3 tables4
    htrace0 htrace1 htrace2 htrace3 hstateRound0 hstateSamples0
    hcoeffLength hcoeffCanonical halpha0' halpha1' halpha2' halpha3'
    rt c hinput (fun round => by
      simpa [rt, laterRt, withGeneratedRelationTables,
        withGeneratedLaterFibres] using halpha round)
  have hcoeffCanonical0 :=
    runtimeCanonicalList_to_materialized relation0.coefficients.val
      hcoeffCanonical
  have hcoeffCanonical1 :=
    runtimeCanonicalList_to_materialized relation1.coefficients.val
      hcoefficients.2.2.2.2.1
  have hcoeffCanonical2 :=
    runtimeCanonicalList_to_materialized relation2.coefficients.val
      hcoefficients.2.2.2.2.2.1
  have hcoeffCanonical3 :=
    runtimeCanonicalList_to_materialized relation3.coefficients.val
      hcoefficients.2.2.2.2.2.2.1
  have hood0 : ∀ sample : Fin 2,
      runtimeQM31View (oodPairValue semantics.tables.ood0 sample) =
        dotLinear (exactSliceVector 1024
          (alloc.vec.Vec.deref (oodPairTable semantics.tables.ood0 sample)))
          c := ood_pair_semantics_matches_generated_table
    relation0.coefficients semantics.tables.ood0 1024 c
    semantics.ood0_semantics hcoeffLength
    representation.ood00_length representation.ood01_length (by norm_num)
    hcoeffCanonical0 representation.ood00_canonical
    representation.ood01_canonical hinputExact
  have hood1 : ∀ sample : Fin 2,
      runtimeQM31View (oodPairValue semantics.tables.ood1 sample) =
        dotLinear (exactSliceVector 256
          (alloc.vec.Vec.deref (oodPairTable semantics.tables.ood1 sample)))
          (round1Coefficients (decodeRelationSchedule rt) c) :=
    ood_pair_semantics_matches_generated_table
    relation1.coefficients semantics.tables.ood1 256
    (round1Coefficients (decodeRelationSchedule rt) c)
    semantics.ood1_semantics hcoefficients.1
    representation.ood10_length representation.ood11_length (by norm_num)
    hcoeffCanonical1 representation.ood10_canonical
    representation.ood11_canonical (by
      funext coefficient
      exact hcoefficients.2.2.2.2.2.2.2.2.1 coefficient)
  have hood2 : ∀ sample : Fin 2,
      runtimeQM31View (oodPairValue semantics.tables.ood2 sample) =
        dotLinear (exactSliceVector 64
          (alloc.vec.Vec.deref (oodPairTable semantics.tables.ood2 sample)))
          (round2Coefficients (decodeRelationSchedule rt) c) :=
    ood_pair_semantics_matches_generated_table
    relation2.coefficients semantics.tables.ood2 64
    (round2Coefficients (decodeRelationSchedule rt) c)
    semantics.ood2_semantics hcoefficients.2.1
    representation.ood20_length representation.ood21_length (by norm_num)
    hcoeffCanonical2 representation.ood20_canonical
    representation.ood21_canonical (by
      funext coefficient
      exact hcoefficients.2.2.2.2.2.2.2.2.2.1 coefficient)
  have hood3 : ∀ sample : Fin 2,
      runtimeQM31View (oodPairValue semantics.tables.ood3 sample) =
        dotLinear (exactSliceVector 16
          (alloc.vec.Vec.deref (oodPairTable semantics.tables.ood3 sample)))
          (round3Coefficients (decodeRelationSchedule rt) c) :=
    ood_pair_semantics_matches_generated_table
    relation3.coefficients semantics.tables.ood3 16
    (round3Coefficients (decodeRelationSchedule rt) c)
    semantics.ood3_semantics hcoefficients.2.2.1
    representation.ood30_length representation.ood31_length (by norm_num)
    hcoeffCanonical3 representation.ood30_canonical
    representation.ood31_canonical (by
      funext coefficient
      exact hcoefficients.2.2.2.2.2.2.2.2.2.2.1 coefficient)
  have hpoly0 := polynomial_semantics_matches_generated_table
    relation0.coefficients semantics.tables.polynomial0 256 c
    semantics.polynomial0_semantics (by simpa using hcoeffLength)
    (by simpa using representation.polynomial0_length) (by norm_num)
    hcoeffCanonical0 representation.polynomial0_canonical
    hinputExact
  have hpoly1 := polynomial_semantics_matches_generated_table
    relation1.coefficients semantics.tables.polynomial1 64
    (round1Coefficients (decodeRelationSchedule rt) c)
    semantics.polynomial1_semantics (by simpa using hcoefficients.1)
    (by simpa using representation.polynomial1_length) (by norm_num)
    hcoeffCanonical1 representation.polynomial1_canonical (by
      funext coefficient
      exact hcoefficients.2.2.2.2.2.2.2.2.1 coefficient)
  have hpoly2 := polynomial_semantics_matches_generated_table
    relation2.coefficients semantics.tables.polynomial2 16
    (round2Coefficients (decodeRelationSchedule rt) c)
    semantics.polynomial2_semantics (by simpa using hcoefficients.2.1)
    (by simpa using representation.polynomial2_length) (by norm_num)
    hcoeffCanonical2 representation.polynomial2_canonical (by
      funext coefficient
      exact hcoefficients.2.2.2.2.2.2.2.2.2.1 coefficient)
  have hpoly3 := polynomial_semantics_matches_generated_table
    relation3.coefficients semantics.tables.polynomial3 4
    (round3Coefficients (decodeRelationSchedule rt) c)
    semantics.polynomial3_semantics (by simpa using hcoefficients.2.2.1)
    (by simpa using representation.polynomial3_length) (by norm_num)
    hcoeffCanonical3 representation.polynomial3_canonical (by
      funext coefficient
      exact hcoefficients.2.2.2.2.2.2.2.2.2.2.1 coefficient)
  have hpoly0' : ∀ degree : Fin 7,
      runtimeQM31View semantics.tables.polynomial0.polynomial.val[degree.val]! =
        polynomialForExtension 256
          (exactSliceVector (4 * 256)
            (alloc.vec.Vec.deref semantics.tables.polynomial0.table))
          c degree := by
    intro degree
    rw [list_getElem_bang_irrel
      (inferInstance : Inhabited RawQM31)
      ComponentCRuntimeMaterializedRelationArithmetic.instInhabitedRawQM31
      semantics.tables.polynomial0.polynomial.val degree.val (by simp)]
    exact hpoly0 degree
  have hpoly1' : ∀ degree : Fin 7,
      runtimeQM31View semantics.tables.polynomial1.polynomial.val[degree.val]! =
        polynomialForExtension 64
          (exactSliceVector (4 * 64)
            (alloc.vec.Vec.deref semantics.tables.polynomial1.table))
          (round1Coefficients (decodeRelationSchedule rt) c) degree := by
    intro degree
    rw [list_getElem_bang_irrel
      (inferInstance : Inhabited RawQM31)
      ComponentCRuntimeMaterializedRelationArithmetic.instInhabitedRawQM31
      semantics.tables.polynomial1.polynomial.val degree.val (by simp)]
    exact hpoly1 degree
  have hpoly2' : ∀ degree : Fin 7,
      runtimeQM31View semantics.tables.polynomial2.polynomial.val[degree.val]! =
        polynomialForExtension 16
          (exactSliceVector (4 * 16)
            (alloc.vec.Vec.deref semantics.tables.polynomial2.table))
          (round2Coefficients (decodeRelationSchedule rt) c) degree := by
    intro degree
    rw [list_getElem_bang_irrel
      (inferInstance : Inhabited RawQM31)
      ComponentCRuntimeMaterializedRelationArithmetic.instInhabitedRawQM31
      semantics.tables.polynomial2.polynomial.val degree.val (by simp)]
    exact hpoly2 degree
  have hpoly3' : ∀ degree : Fin 7,
      runtimeQM31View semantics.tables.polynomial3.polynomial.val[degree.val]! =
        polynomialForExtension 4
          (exactSliceVector (4 * 4)
            (alloc.vec.Vec.deref semantics.tables.polynomial3.table))
          (round3Coefficients (decodeRelationSchedule rt) c) degree := by
    intro degree
    rw [list_getElem_bang_irrel
      (inferInstance : Inhabited RawQM31)
      ComponentCRuntimeMaterializedRelationArithmetic.instInhabitedRawQM31
      semantics.tables.polynomial3.polynomial.val degree.val (by simp)]
    exact hpoly3 degree
  have hfinal : ∀ coefficient : Fin 4,
      runtimeQM31View relation4.coefficients.val[coefficient.val]! =
        finalCoefficientMap (decodeFriSchedule rt) c coefficient := by
    intro coefficient
    have hold := hcoefficients.2.2.2.2.2.2.2.2.2.2.2 coefficient
    have hlength := hcoefficients.2.2.2.1
    have hindex : coefficient.val < relation4.coefficients.val.length := by
      rw [hlength]
      exact coefficient.isLt
    rw [list_getElem_bang_irrel
      (inferInstance : Inhabited RawQM31)
      ComponentCRuntimeFourRoundFinalCoefficients.instInhabitedRawQM31
      relation4.coefficients.val coefficient.val hindex]
    exact hold
  refine ⟨?_, ?_, hfinal⟩
  · intro round sample
    have hcases : round.val = 0 ∨ round.val = 1 ∨
        round.val = 2 ∨ round.val = 3 := by omega
    rcases hcases with hround | hround | hround | hround
    · have hr : round = 0 := Fin.eq_of_val_eq hround
      rw [hround, semantics.ood0_match sample, hr]
      simp only [roundOodRows, Matrix.cons_val_zero, ood0Rows,
        LinearMap.pi_apply]
      rw [generated_ood0_table_apply]
      exact hood0 sample
    · have hr : round = 1 := Fin.eq_of_val_eq hround
      rw [hround, semantics.ood1_match sample, hr]
      simp only [roundOodRows, Matrix.cons_val_one, Matrix.cons_val_zero,
        ood1Rows, LinearMap.pi_apply, LinearMap.comp_apply]
      rw [generated_ood1_table_apply]
      exact hood1 sample
    · have hr : round = 2 := Fin.eq_of_val_eq hround
      rw [hround, semantics.ood2_match sample, hr]
      simp only [roundOodRows, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons, ood2Rows, LinearMap.pi_apply,
        LinearMap.comp_apply]
      rw [generated_ood2_table_apply]
      exact hood2 sample
    · have hr : round = 3 := Fin.eq_of_val_eq hround
      rw [hround, semantics.ood3_match sample, hr]
      simp only [roundOodRows, Matrix.cons_val_three, Matrix.tail_cons,
        Matrix.head_cons, ood3Rows, LinearMap.pi_apply,
        LinearMap.comp_apply]
      rw [generated_ood3_table_apply]
      exact hood3 sample
  · intro round degree
    have hcases : round.val = 0 ∨ round.val = 1 ∨
        round.val = 2 ∨ round.val = 3 := by omega
    rcases hcases with hround | hround | hround | hround
    · have hr : round = 0 := Fin.eq_of_val_eq hround
      rw [hround, semantics.polynomial0_match, hr]
      simp only [roundPolynomialRows, Matrix.cons_val_zero,
        polynomial0Rows]
      rw [generated_polynomial0_table]
      exact hpoly0' degree
    · have hr : round = 1 := Fin.eq_of_val_eq hround
      rw [hround, semantics.polynomial1_match, hr]
      simp only [roundPolynomialRows, Matrix.cons_val_one,
        Matrix.cons_val_zero, polynomial1Rows, LinearMap.comp_apply]
      rw [generated_polynomial1_table]
      exact hpoly1' degree
    · have hr : round = 2 := Fin.eq_of_val_eq hround
      rw [hround, semantics.polynomial2_match, hr]
      simp only [roundPolynomialRows, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons, polynomial2Rows, LinearMap.comp_apply]
      rw [generated_polynomial2_table]
      exact hpoly2' degree
    · have hr : round = 3 := Fin.eq_of_val_eq hround
      rw [hround, semantics.polynomial3_match, hr]
      simp only [roundPolynomialRows, Matrix.cons_val_three, Matrix.tail_cons,
        Matrix.head_cons, polynomial3Rows, LinearMap.comp_apply]
      rw [generated_polynomial3_table]
      exact hpoly3' degree

#print axioms generated_four_round_relation_rows_match_maintained

/-- Full source-authentic constructor for the six released families consumed
by the public packer.  The existential table witness is produced by the four
actual relation traces.  Its only remaining inputs are the concrete finite
length/canonicality facts for those returned tables, together with the
pointwise decoded folded-codeword layers already isolated by the codeword
tower proof. -/
theorem generated_four_round_released_trace_families
    (base : DeployedRuntimeSchedule BaseField ExtensionField)
    (indices : QueryIndices)
    (hrange : GeneratedLaterFibresInRange indices)
    (enc : AspisV5ComponentCConcreteFoldLinearity.Coefficients ExtensionField
      →ₗ[ExtensionField] Layer0Word ExtensionField)
    (c : AspisV5ComponentCConcreteFoldLinearity.Coefficients ExtensionField)
    (schedule : RuntimeSchedule)
    (relation0 relation1 relation2 relation3 relation4 : RuntimeRelation)
    (folded0 folded1 folded2 folded3 folded4 : alloc.vec.Vec RawQM31)
    (later0 later1Out later2Out later3Out later4 : RuntimeLater)
    (tables0 tables1 tables2 tables3 tables4 : RuntimeTables)
    (trace : RuntimeTrace)
    (htrace0 : GeneratedRuntimeRoundTrace schedule relation0 relation1
      folded0 folded1 later0 later1Out tables0 tables1 0#usize)
    (htrace1 : GeneratedRuntimeRoundTrace schedule relation1 relation2
      folded1 folded2 later1Out later2Out tables1 tables2 1#usize)
    (htrace2 : GeneratedRuntimeRoundTrace schedule relation2 relation3
      folded2 folded3 later2Out later3Out tables2 tables3 2#usize)
    (htrace3 : GeneratedRuntimeRoundTrace schedule relation3 relation4
      folded3 folded4 later3Out later4 tables3 tables4 3#usize)
    (hfibres0 : schedule.later_fibres.val[0]! = later1 indices)
    (hfibres1 : schedule.later_fibres.val[1]! = later2 indices)
    (hfibres2 : schedule.later_fibres.val[2]! = later3 indices)
    (hempty0 : later0.val[0]!.val = [])
    (hempty1 : later0.val[1]!.val = [])
    (hempty2 : later0.val[2]!.val = [])
    (hread0 : ∀ fibre ∈ (later1 indices).val,
      4 * fibre.val + 4 ≤ folded1.val.length)
    (hread1 : ∀ fibre ∈ (later2 indices).val,
      4 * fibre.val + 4 ≤ folded2.val.length)
    (hread2 : ∀ fibre ∈ (later3 indices).val,
      4 * fibre.val + 4 ≤ folded3.val.length)
    (hcapacity0 : 4 * (later1 indices).val.length ≤ Std.Usize.max)
    (hcapacity1 : 4 * (later2 indices).val.length ≤ Std.Usize.max)
    (hcapacity2 : 4 * (later3 indices).val.length ≤ Std.Usize.max)
    (hcount0 : (later1 indices).length ≤ 18)
    (hcount1 : (later2 indices).length ≤ 18)
    (hcount2 : (later3 indices).length ≤ 18)
    (hfolded1 : ∀ row : Fin layer1Symbols,
      runtimeQM31View folded1.val[row.val]! =
        layer1Map (decodeFriSchedule
          (withGeneratedLaterFibres base indices hrange)) enc c row)
    (hfolded2 : ∀ row : Fin layer2Symbols,
      runtimeQM31View folded2.val[row.val]! =
        layer2Map (decodeFriSchedule
          (withGeneratedLaterFibres base indices hrange)) enc c row)
    (hfolded3 : ∀ row : Fin layer3Symbols,
      runtimeQM31View folded3.val[row.val]! =
        layer3Map (decodeFriSchedule
          (withGeneratedLaterFibres base indices hrange)) enc c row)
    (hstateRound0 : relation0.round = 0#usize)
    (hstateSamples0 : relation0.samples = 0#usize)
    (hcoeffLength : relation0.coefficients.val.length = 1024)
    (hcoeffCanonical :
      ComponentCRuntimeCoefficientFoldCorrespondence.RuntimeCanonicalList
        relation0.coefficients.val)
    (halpha0 : runtimeCanonicalQM31 schedule.alphas.val[0]!)
    (halpha1 : runtimeCanonicalQM31 schedule.alphas.val[1]!)
    (halpha2 : runtimeCanonicalQM31 schedule.alphas.val[2]!)
    (halpha3 : runtimeCanonicalQM31 schedule.alphas.val[3]!)
    (hinput : runtimeCoefficientView
      (alloc.vec.Vec.deref relation0.coefficients) 1024 = c)
    (halpha : ∀ round : Fin 4,
      runtimeQM31View schedule.alphas.val[round.val]! = base.alpha round)
    (hfinish : v5_mask.relation_prover.V5IncrementalRelation.finish relation4 =
      ok (core.result.Result.Ok trace)) :
    ∃ semantics : ReleasedRelationSemantics
      relation0 relation1 relation2 relation3 relation4,
      ∀ representation : FourRoundGeneratedTableRepresentation semantics.tables,
        let rt := withGeneratedRelationTables
          (withGeneratedLaterFibres base indices hrange) semantics.tables
        Nonempty
          (ReleasedTraceFamilies rt enc c runtimeQM31View later4 trace) := by
  rcases generated_four_round_relation_rows_match_maintained
      schedule relation0 relation1 relation2 relation3 relation4
      tables0 tables1 tables2 tables3 tables4
      htrace0.1 htrace1.1 htrace2.1 htrace3.1
      hstateRound0 hstateSamples0 hcoeffLength hcoeffCanonical
      halpha0 halpha1 halpha2 halpha3 base indices hrange c hinput halpha with
    ⟨semantics, hrelation⟩
  refine ⟨semantics, ?_⟩
  intro representation
  dsimp only
  let laterRt := withGeneratedLaterFibres base indices hrange
  let rt := withGeneratedRelationTables laterRt semantics.tables
  have hrelationRows := hrelation representation
  have hlater := generated_four_round_later_release_matches_maintained
    base indices hrange enc c runtimeQM31View schedule
    relation0 relation1 relation2 relation3 relation4
    folded0 folded1 folded2 folded3 folded4
    later0 later1Out later2Out later3Out later4
    tables0 tables1 tables2 tables3 tables4
    htrace0 htrace1 htrace2 htrace3 hfibres0 hfibres1 hfibres2
    hempty0 hempty1 hempty2 hread0 hread1 hread2
    hcapacity0 hcapacity1 hcapacity2 hfolded1 hfolded2 hfolded3
  have hfinishArrays := generated_finish_success_preserves_released_arrays
    relation4 trace hfinish
  have hfinishCoefficients :=
    generated_finish_success_preserves_final_coefficients
      relation4 trace hfinish
  have hrelation4Length : relation4.coefficients.val.length = 4 := by
    rw [← hfinishCoefficients]
    exact trace.final_coefficients.property
  have hrelationForFinish : ∀ coefficient : Fin 4,
      runtimeQM31View
          (@getElem! (List RawQM31) Nat RawQM31
            (fun xs i => i < xs.length) List.instGetElem?NatLtLength
            ComponentCRuntimeFourRoundFinalCoefficients.instInhabitedRawQM31
            relation4.coefficients.val coefficient.val) =
        finalCoefficientMap (decodeFriSchedule rt) c coefficient := by
    intro coefficient
    have hindex : coefficient.val < relation4.coefficients.val.length := by
      rw [hrelation4Length]
      exact coefficient.isLt
    rw [list_getElem_bang_irrel
      ComponentCRuntimeFourRoundFinalCoefficients.instInhabitedRawQM31
      (inferInstance : Inhabited RawQM31)
      relation4.coefficients.val coefficient.val hindex]
    exact hrelationRows.2.2 coefficient
  have hfinalOld := generated_finish_final_coefficients_match_maintained
    relation4 trace rt c hfinish hrelationForFinish
  have hfinal : ∀ coefficient : Fin 4,
      runtimeQM31View trace.final_coefficients.val[coefficient.val]! =
        finalCoefficientMap (decodeFriSchedule rt) c coefficient := by
    intro coefficient
    have hindex : coefficient.val < trace.final_coefficients.val.length := by
      rw [trace.final_coefficients.property]
      exact coefficient.isLt
    rw [list_getElem_bang_irrel
      (inferInstance : Inhabited RawQM31)
      ComponentCRuntimeFourRoundFinalCoefficients.instInhabitedRawQM31
      trace.final_coefficients.val coefficient.val hindex]
    exact hfinalOld coefficient
  have hfri : decodeFriSchedule rt = decodeFriSchedule laterRt := rfl
  dsimp only at hlater
  rcases hlater with
    ⟨_hlaterEq, hlater0LengthOld, hlater1LengthOld,
      hlater2LengthOld, hlater0ReadOld, hlater1ReadOld, hlater2ReadOld⟩
  have hlater0Length : later4.val[0]!.val.length = 4 * rt.later1Count := by
    exact hlater0LengthOld
  have hlater1Length : later4.val[1]!.val.length = 4 * rt.later2Count := by
    exact hlater1LengthOld
  have hlater2Length : later4.val[2]!.val.length = 4 * rt.later3Count := by
    exact hlater2LengthOld
  have hlater0Read : ∀ (index : Fin rt.later1Count) (slot : Fin 4),
      runtimeQM31View
          (later4.val[0]!.val[4 * index.val + slot.val]!) =
        later1ReadMap (decodeFriSchedule rt) enc c (index, slot) := by
    intro index slot
    have hindex : 4 * index.val + slot.val < later4.val[0]!.val.length := by
      rw [hlater0Length]
      omega
    rw [list_getElem_bang_irrel
      (inferInstance : Inhabited RawQM31)
      ComponentCRuntimeLaterFibreProof.instInhabitedQM31_runtimeLaterFibreCorrespondence
      later4.val[0]!.val (4 * index.val + slot.val) hindex]
    rw [hfri]
    exact hlater0ReadOld index slot
  have hlater1Read : ∀ (index : Fin rt.later2Count) (slot : Fin 4),
      runtimeQM31View
          (later4.val[1]!.val[4 * index.val + slot.val]!) =
        later2ReadMap (decodeFriSchedule rt) enc c (index, slot) := by
    intro index slot
    have hindex : 4 * index.val + slot.val < later4.val[1]!.val.length := by
      rw [hlater1Length]
      omega
    rw [list_getElem_bang_irrel
      (inferInstance : Inhabited RawQM31)
      ComponentCRuntimeLaterFibreProof.instInhabitedQM31_runtimeLaterFibreCorrespondence
      later4.val[1]!.val (4 * index.val + slot.val) hindex]
    rw [hfri]
    exact hlater1ReadOld index slot
  have hlater2Read : ∀ (index : Fin rt.later3Count) (slot : Fin 4),
      runtimeQM31View
          (later4.val[2]!.val[4 * index.val + slot.val]!) =
        later3ReadMap (decodeFriSchedule rt) enc c (index, slot) := by
    intro index slot
    have hindex : 4 * index.val + slot.val < later4.val[2]!.val.length := by
      rw [hlater2Length]
      omega
    rw [list_getElem_bang_irrel
      (inferInstance : Inhabited RawQM31)
      ComponentCRuntimeLaterFibreProof.instInhabitedQM31_runtimeLaterFibreCorrespondence
      later4.val[2]!.val (4 * index.val + slot.val) hindex]
    rw [hfri]
    exact hlater2ReadOld index slot
  refine ⟨{
    later0 := later4.val[0]!
    later1 := later4.val[1]!
    later2 := later4.val[2]!
    later_eq := array3_eq_entries later4
    count0 := alloc.vec.Vec.len (later1 indices)
    count1 := alloc.vec.Vec.len (later2 indices)
    count2 := alloc.vec.Vec.len (later3 indices)
    count0_exact := ?_
    count1_exact := ?_
    count2_exact := ?_
    count0_bound := ?_
    count1_bound := ?_
    count2_bound := ?_
    later0_length := hlater0Length
    later1_length := hlater1Length
    later2_length := hlater2Length
    ood := ?_
    polynomial := ?_
    later0_read := hlater0Read
    later1_read := hlater1Read
    later2_read := hlater2Read
    final_read := hfinal }⟩
  · rfl
  · rfl
  · rfl
  · simpa [alloc.vec.Vec.len] using hcount0
  · simpa [alloc.vec.Vec.len] using hcount1
  · simpa [alloc.vec.Vec.len] using hcount2
  · intro round sample
    rw [hfinishArrays.1]
    exact hrelationRows.1 round sample
  · intro round degree
    rw [hfinishArrays.2.1]
    exact hrelationRows.2.1 round degree

#print axioms generated_four_round_released_trace_families

end aspis_prover.ComponentCRuntimeReleasedTraceFamilies
