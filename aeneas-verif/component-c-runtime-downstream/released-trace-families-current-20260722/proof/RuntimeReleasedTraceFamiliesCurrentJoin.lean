import RuntimePublicPackerCapstone
import RuntimeFourRoundLaterMaintained
import RuntimeFourRoundFinalCoefficients
import RuntimeRelationRoundOodSemantics
import RuntimeRelationRoundPolynomialSemantics
import RuntimeGeneratedRelationSchedule
import RuntimeMaintainedRoundSelectors
import RuntimeReleasedTraceFamiliesSourceJoin
import RuntimeRelationTableCanonicalityCurrentJoin

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
open ComponentCRuntimeRoundControlFlow
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
open ComponentCRuntimeReleasedTraceFamiliesSourceJoin

private theorem validatorCanonicalQM31_to_materialized
    (value : RawQM31)
    (hcanonical :
      RuntimeRelationTableCanonicality.RuntimeCanonicalQM31 value) :
    runtimeCanonicalQM31 value := by
  have hP : aspis_core.field.P = 2147483647#u32 := by
    unfold aspis_core.field.P
    rfl
  unfold RuntimeRelationTableCanonicality.RuntimeCanonicalQM31 at hcanonical
  rw [hP] at hcanonical
  simpa [RuntimeRelationTableCanonicality.RuntimeCanonicalQM31,
    runtimeCanonicalQM31, runtimeCanonicalCM31, runtimeCanonicalM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    AspisAeneasCM31Multiplicative.m31Modulus] using hcanonical

private theorem validatorCanonicalList_to_materialized
    (values : List RawQM31)
    (hcanonical :
      RuntimeRelationTableCanonicality.RuntimeCanonicalList values) :
    ComponentCRuntimeMaterializedRelationArithmetic.RuntimeCanonicalList
      values := by
  induction values with
  | nil => simp [ComponentCRuntimeMaterializedRelationArithmetic.RuntimeCanonicalList]
  | cons head tail ih =>
      have hhead :
          RuntimeRelationTableCanonicality.RuntimeCanonicalQM31 head := by
        exact hcanonical 0 (by simp)
      have htail :
          RuntimeRelationTableCanonicality.RuntimeCanonicalList tail := by
        intro index hindex
        have hnext := hcanonical (index + 1) (by simp; omega)
        simpa using hnext
      unfold ComponentCRuntimeMaterializedRelationArithmetic.RuntimeCanonicalList
      intro value hvalue
      simp only [List.mem_cons] at hvalue
      rcases hvalue with rfl | hvalue
      · exact validatorCanonicalQM31_to_materialized _ hhead
      · exact ih htail value hvalue

private theorem generated_runtime_trace_relation_round_call
    (schedule : RuntimeSchedule)
    (relation relationOut : RuntimeRelation)
    (folded foldedOut : alloc.vec.Vec RawQM31)
    (later laterOut : RuntimeLater)
    (tables tablesOut : RuntimeTables)
    (round : Std.Usize)
    (htrace : GeneratedRuntimeRoundTrace schedule relation relationOut
      folded foldedOut later laterOut tables tablesOut round) :
    v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_round
        schedule relation tables round =
      ok (core.result.Result.Ok (), relationOut, tablesOut) := by
  obtain ⟨relationAfter, tablesAfter, hrelation, _hcodeword,
      hrelationOut, htablesOut, _hlater⟩ :=
    generated_runtime_round_success_decomposes schedule relation relationOut
      folded foldedOut later laterOut tables tablesOut round htrace.2.2.2
  subst relationAfter
  subst tablesAfter
  exact hrelation

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

private theorem dotLinear_result_transport_both
    {K : Type*} [Field K] {n : Nat} {x : K}
    {sourceWeights targetWeights sourceCoefficients targetCoefficients :
      Fin n → K}
    (hx : x = dotLinear sourceWeights sourceCoefficients)
    (hweights : targetWeights = sourceWeights)
    (hcoefficients : sourceCoefficients = targetCoefficients) :
    x = dotLinear targetWeights targetCoefficients := by
  calc
    x = dotLinear sourceWeights sourceCoefficients := hx
    _ = dotLinear targetWeights sourceCoefficients :=
      congrArg (fun weights => dotLinear weights sourceCoefficients)
        hweights.symm
    _ = dotLinear targetWeights targetCoefficients :=
      congrArg (dotLinear targetWeights) hcoefficients

private theorem polynomial_result_transport
    {K : Type*} [Field K] {n : Nat} {x : K}
    (weights : Fin (4 * n) → K)
    {sourceCoefficients targetCoefficients : Fin (4 * n) → K}
    (degree : Fin 7)
    (hx : x = polynomialForExtension n weights sourceCoefficients degree)
    (hcoefficients : sourceCoefficients = targetCoefficients) :
    x = polynomialForExtension n weights targetCoefficients degree :=
  hx.trans (congrArg
    (fun coefficients => polynomialForExtension n weights coefficients degree)
    hcoefficients)

private theorem ood0_result_to_round
    {K : Type*} [Field K] {x : K} (rt : FixedRelationSchedule K)
    (c : AspisV5ComponentCConcreteFoldLinearity.Coefficients K)
    (sample : Fin 2) (hx : x = dotLinear (rt.ood0 sample) c) :
    x = roundOodRows rt 0 c sample :=
  hx.trans (roundOodRows_zero_scalar rt c sample).symm

private theorem ood1_result_to_round
    {K : Type*} [Field K] {x : K} (rt : FixedRelationSchedule K)
    (c : AspisV5ComponentCConcreteFoldLinearity.Coefficients K)
    (sample : Fin 2)
    (hx : x = dotLinear (rt.ood1 sample) (round1Coefficients rt c)) :
    x = roundOodRows rt 1 c sample :=
  hx.trans (roundOodRows_one rt c sample).symm

private theorem ood2_result_to_round
    {K : Type*} [Field K] {x : K} (rt : FixedRelationSchedule K)
    (c : AspisV5ComponentCConcreteFoldLinearity.Coefficients K)
    (sample : Fin 2)
    (hx : x = dotLinear (rt.ood2 sample) (round2Coefficients rt c)) :
    x = roundOodRows rt 2 c sample :=
  hx.trans (roundOodRows_two rt c sample).symm

private theorem ood3_result_to_round
    {K : Type*} [Field K] {x : K} (rt : FixedRelationSchedule K)
    (c : AspisV5ComponentCConcreteFoldLinearity.Coefficients K)
    (sample : Fin 2)
    (hx : x = dotLinear (rt.ood3 sample) (round3Coefficients rt c)) :
    x = roundOodRows rt 3 c sample :=
  hx.trans (roundOodRows_three rt c sample).symm

private theorem ood0_source_to_round
    {K : Type*} [Field K] {x : K} (rt : FixedRelationSchedule K)
    (c : AspisV5ComponentCConcreteFoldLinearity.Coefficients K)
    (sample : Fin 2) {sourceWeights sourceCoefficients : Fin 1024 → K}
    (hx : x = dotLinear sourceWeights sourceCoefficients)
    (hweights : rt.ood0 sample = sourceWeights)
    (hcoefficients : sourceCoefficients = c) :
    x = roundOodRows rt 0 c sample :=
  ood0_result_to_round rt c sample
    (dotLinear_result_transport_both hx hweights hcoefficients)

private theorem ood1_source_to_round
    {K : Type*} [Field K] {x : K} (rt : FixedRelationSchedule K)
    (c : AspisV5ComponentCConcreteFoldLinearity.Coefficients K)
    (sample : Fin 2) {sourceWeights sourceCoefficients : Fin 256 → K}
    (hx : x = dotLinear sourceWeights sourceCoefficients)
    (hweights : rt.ood1 sample = sourceWeights)
    (hcoefficients : sourceCoefficients = round1Coefficients rt c) :
    x = roundOodRows rt 1 c sample :=
  ood1_result_to_round rt c sample
    (dotLinear_result_transport_both hx hweights hcoefficients)

private theorem ood2_source_to_round
    {K : Type*} [Field K] {x : K} (rt : FixedRelationSchedule K)
    (c : AspisV5ComponentCConcreteFoldLinearity.Coefficients K)
    (sample : Fin 2) {sourceWeights sourceCoefficients : Fin 64 → K}
    (hx : x = dotLinear sourceWeights sourceCoefficients)
    (hweights : rt.ood2 sample = sourceWeights)
    (hcoefficients : sourceCoefficients = round2Coefficients rt c) :
    x = roundOodRows rt 2 c sample :=
  ood2_result_to_round rt c sample
    (dotLinear_result_transport_both hx hweights hcoefficients)

private theorem ood3_source_to_round
    {K : Type*} [Field K] {x : K} (rt : FixedRelationSchedule K)
    (c : AspisV5ComponentCConcreteFoldLinearity.Coefficients K)
    (sample : Fin 2) {sourceWeights sourceCoefficients : Fin 16 → K}
    (hx : x = dotLinear sourceWeights sourceCoefficients)
    (hweights : rt.ood3 sample = sourceWeights)
    (hcoefficients : sourceCoefficients = round3Coefficients rt c) :
    x = roundOodRows rt 3 c sample :=
  ood3_result_to_round rt c sample
    (dotLinear_result_transport_both hx hweights hcoefficients)

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
  ood00_materialize : ∃ weights : aspis_core.sumcheck.WeightAccumulator,
    v5_mask.relation_prover.V5IncrementalRelation.materialize_weights weights
      (alloc.vec.Vec.len relation0.coefficients) = ok tables.ood0.table0
  ood01_materialize : ∃ weights : aspis_core.sumcheck.WeightAccumulator,
    v5_mask.relation_prover.V5IncrementalRelation.materialize_weights weights
      (alloc.vec.Vec.len relation0.coefficients) = ok tables.ood0.table1
  ood10_materialize : ∃ weights : aspis_core.sumcheck.WeightAccumulator,
    v5_mask.relation_prover.V5IncrementalRelation.materialize_weights weights
      (alloc.vec.Vec.len relation1.coefficients) = ok tables.ood1.table0
  ood11_materialize : ∃ weights : aspis_core.sumcheck.WeightAccumulator,
    v5_mask.relation_prover.V5IncrementalRelation.materialize_weights weights
      (alloc.vec.Vec.len relation1.coefficients) = ok tables.ood1.table1
  ood20_materialize : ∃ weights : aspis_core.sumcheck.WeightAccumulator,
    v5_mask.relation_prover.V5IncrementalRelation.materialize_weights weights
      (alloc.vec.Vec.len relation2.coefficients) = ok tables.ood2.table0
  ood21_materialize : ∃ weights : aspis_core.sumcheck.WeightAccumulator,
    v5_mask.relation_prover.V5IncrementalRelation.materialize_weights weights
      (alloc.vec.Vec.len relation2.coefficients) = ok tables.ood2.table1
  ood30_materialize : ∃ weights : aspis_core.sumcheck.WeightAccumulator,
    v5_mask.relation_prover.V5IncrementalRelation.materialize_weights weights
      (alloc.vec.Vec.len relation3.coefficients) = ok tables.ood3.table0
  ood31_materialize : ∃ weights : aspis_core.sumcheck.WeightAccumulator,
    v5_mask.relation_prover.V5IncrementalRelation.materialize_weights weights
      (alloc.vec.Vec.len relation3.coefficients) = ok tables.ood3.table1
  polynomial0_materialize : ∃ weights : aspis_core.sumcheck.WeightAccumulator,
    v5_mask.relation_prover.V5IncrementalRelation.materialize_weights weights
      (alloc.vec.Vec.len relation0.coefficients) = ok tables.polynomial0.table
  polynomial1_materialize : ∃ weights : aspis_core.sumcheck.WeightAccumulator,
    v5_mask.relation_prover.V5IncrementalRelation.materialize_weights weights
      (alloc.vec.Vec.len relation1.coefficients) = ok tables.polynomial1.table
  polynomial2_materialize : ∃ weights : aspis_core.sumcheck.WeightAccumulator,
    v5_mask.relation_prover.V5IncrementalRelation.materialize_weights weights
      (alloc.vec.Vec.len relation2.coefficients) = ok tables.polynomial2.table
  polynomial3_materialize : ∃ weights : aspis_core.sumcheck.WeightAccumulator,
    v5_mask.relation_prover.V5IncrementalRelation.materialize_weights weights
      (alloc.vec.Vec.len relation3.coefficients) = ok tables.polynomial3.table
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
      tables3 tables4 3#usize)
    (hrun0 :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_round
          schedule relation0 tables0 0#usize =
        ok (core.result.Result.Ok (), relation1, tables1))
    (hrun1 :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_round
          schedule relation1 tables1 1#usize =
        ok (core.result.Result.Ok (), relation2, tables2))
    (hrun2 :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_round
          schedule relation2 tables2 2#usize =
        ok (core.result.Result.Ok (), relation3, tables3))
    (hrun3 :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_round
          schedule relation3 tables3 3#usize =
        ok (core.result.Result.Ok (), relation4, tables4)) :
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
    ⟨ood0, hood00, hood01, htable00, htable01, hoodCalls0, hoodSem0⟩
  rcases generated_line_round_trace_ood_semantics
      schedule relation1 relation2 tables1 tables2 1#usize
      (by norm_num) (by norm_num) hstate1.1 hstate1.2 htrace1 with
    ⟨ood1, hood10, hood11, htable10, htable11, hoodCalls1, hoodSem1⟩
  rcases generated_line_round_trace_ood_semantics
      schedule relation2 relation3 tables2 tables3 2#usize
      (by norm_num) (by norm_num) hstate2.1 hstate2.2 htrace2 with
    ⟨ood2, hood20, hood21, htable20, htable21, hoodCalls2, hoodSem2⟩
  rcases generated_line_round_trace_ood_semantics
      schedule relation3 relation4 tables3 tables4 3#usize
      (by norm_num) (by norm_num) hstate3.1 hstate3.2 htrace3 with
    ⟨ood3, hood30, hood31, htable30, htable31, hoodCalls3, hoodSem3⟩
  rcases generated_circle_round_trace_polynomial_semantics
      schedule relation0 relation1 tables0 tables1 htrace0 with
    ⟨poly0, hpoly0, hpolyTable0, hpolyCall0, hpolySem0⟩
  rcases generated_line_round_trace_polynomial_semantics
      schedule relation1 relation2 tables1 tables2 1#usize
      (by norm_num) (by norm_num) hstate1.1 hstate1.2 htrace1 with
    ⟨poly1, hpoly1, hpolyTable1, hpolyCall1, hpolySem1⟩
  rcases generated_line_round_trace_polynomial_semantics
      schedule relation2 relation3 tables2 tables3 2#usize
      (by norm_num) (by norm_num) hstate2.1 hstate2.2 htrace2 with
    ⟨poly2, hpoly2, hpolyTable2, hpolyCall2, hpolySem2⟩
  rcases generated_line_round_trace_polynomial_semantics
      schedule relation3 relation4 tables3 tables4 3#usize
      (by norm_num) (by norm_num) hstate3.1 hstate3.2 htrace3 with
    ⟨poly3, hpoly3, hpolyTable3, hpolyCall3, hpolySem3⟩
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
  rcases hoodCalls0 with ⟨weights00, weights01, hmaterialize00, hmaterialize01⟩
  rcases hoodCalls1 with ⟨weights10, weights11, hmaterialize10, hmaterialize11⟩
  rcases hoodCalls2 with ⟨weights20, weights21, hmaterialize20, hmaterialize21⟩
  rcases hoodCalls3 with ⟨weights30, weights31, hmaterialize30, hmaterialize31⟩
  have hoodCanonical0 :=
    RuntimeRelationTableCanonicality.generated_round_success_stores_canonical_ood
      schedule relation0 relation1 tables0 tables1 0#usize hrun0
  have hoodCanonical1 :=
    RuntimeRelationTableCanonicality.generated_round_success_stores_canonical_ood
      schedule relation1 relation2 tables1 tables2 1#usize hrun1
  have hoodCanonical2 :=
    RuntimeRelationTableCanonicality.generated_round_success_stores_canonical_ood
      schedule relation2 relation3 tables2 tables3 2#usize hrun2
  have hoodCanonical3 :=
    RuntimeRelationTableCanonicality.generated_round_success_stores_canonical_ood
      schedule relation3 relation4 tables3 tables4 3#usize hrun3
  have hpolyCanonical0 :=
    RuntimeRelationTableCanonicality.generated_round_success_stores_canonical_polynomial
      schedule relation0 relation1 tables0 tables1 0#usize hrun0
  have hpolyCanonical1 :=
    RuntimeRelationTableCanonicality.generated_round_success_stores_canonical_polynomial
      schedule relation1 relation2 tables1 tables2 1#usize hrun1
  have hpolyCanonical2 :=
    RuntimeRelationTableCanonicality.generated_round_success_stores_canonical_polynomial
      schedule relation2 relation3 tables2 tables3 2#usize hrun2
  have hpolyCanonical3 :=
    RuntimeRelationTableCanonicality.generated_round_success_stores_canonical_polynomial
      schedule relation3 relation4 tables3 tables4 3#usize hrun3
  have hood00Canonical := validatorCanonicalList_to_materialized ood0.table0.val
    (by rw [← htable00]; exact hoodCanonical0 0)
  have hood01Canonical := validatorCanonicalList_to_materialized ood0.table1.val
    (by rw [← htable01]; exact hoodCanonical0 1)
  have hood10Canonical := validatorCanonicalList_to_materialized ood1.table0.val
    (by rw [← htable10]; exact hoodCanonical1 0)
  have hood11Canonical := validatorCanonicalList_to_materialized ood1.table1.val
    (by rw [← htable11]; exact hoodCanonical1 1)
  have hood20Canonical := validatorCanonicalList_to_materialized ood2.table0.val
    (by rw [← htable20]; exact hoodCanonical2 0)
  have hood21Canonical := validatorCanonicalList_to_materialized ood2.table1.val
    (by rw [← htable21]; exact hoodCanonical2 1)
  have hood30Canonical := validatorCanonicalList_to_materialized ood3.table0.val
    (by rw [← htable30]; exact hoodCanonical3 0)
  have hood31Canonical := validatorCanonicalList_to_materialized ood3.table1.val
    (by rw [← htable31]; exact hoodCanonical3 1)
  have hpoly0Canonical := validatorCanonicalList_to_materialized poly0.table.val
    (by rw [← hpolyTable0]; exact hpolyCanonical0)
  have hpoly1Canonical := validatorCanonicalList_to_materialized poly1.table.val
    (by rw [← hpolyTable1]; exact hpolyCanonical1)
  have hpoly2Canonical := validatorCanonicalList_to_materialized poly2.table.val
    (by rw [← hpolyTable2]; exact hpolyCanonical2)
  have hpoly3Canonical := validatorCanonicalList_to_materialized poly3.table.val
    (by rw [← hpolyTable3]; exact hpolyCanonical3)
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
    polynomial3_semantics := hpolySem3
    ood00_materialize := ⟨weights00, hmaterialize00⟩
    ood01_materialize := ⟨weights01, hmaterialize01⟩
    ood10_materialize := ⟨weights10, hmaterialize10⟩
    ood11_materialize := ⟨weights11, hmaterialize11⟩
    ood20_materialize := ⟨weights20, hmaterialize20⟩
    ood21_materialize := ⟨weights21, hmaterialize21⟩
    ood30_materialize := ⟨weights30, hmaterialize30⟩
    ood31_materialize := ⟨weights31, hmaterialize31⟩
    polynomial0_materialize := hpolyCall0
    polynomial1_materialize := hpolyCall1
    polynomial2_materialize := hpolyCall2
    polynomial3_materialize := hpolyCall3
    ood00_canonical := hood00Canonical
    ood01_canonical := hood01Canonical
    ood10_canonical := hood10Canonical
    ood11_canonical := hood11Canonical
    ood20_canonical := hood20Canonical
    ood21_canonical := hood21Canonical
    ood30_canonical := hood30Canonical
    ood31_canonical := hood31Canonical
    polynomial0_canonical := hpoly0Canonical
    polynomial1_canonical := hpoly1Canonical
    polynomial2_canonical := hpoly2Canonical
    polynomial3_canonical := hpoly3Canonical }⟩

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

private theorem generated_materialized_table_length
    (coefficients table : alloc.vec.Vec RawQM31)
    (weights : aspis_core.sumcheck.WeightAccumulator)
    (n : Nat)
    (hcoefficients : coefficients.val.length = n)
    (hbound : n ≤ 1024)
    (hrun :
      v5_mask.relation_prover.V5IncrementalRelation.materialize_weights
          weights (alloc.vec.Vec.len coefficients) = ok table) :
    table.val.length = n := by
  have hlength := generated_materialize_weights_success_length
    weights (alloc.vec.Vec.len coefficients) table (by
      simpa [alloc.vec.Vec.len, hcoefficients] using hbound) hrun
  simpa [alloc.vec.Vec.len, hcoefficients] using hlength

/-- Source-shaped OOD facts retained without forcing the concrete QM31 tower
to normalize the maintained round selector inside the large four-round proof.
`ReleasedTraceFamilies.ood` performs that last selector step generically. -/
structure ReleasedRelationOodSources
    (rt : DeployedRuntimeSchedule BaseField ExtensionField)
    (c : AspisV5ComponentCConcreteFoldLinearity.Coefficients ExtensionField)
    (relation : RuntimeRelation) where
  ood0_source : ∀ sample : Fin 2,
    ∃ value : ExtensionField, ∃ weights : Fin 1024 → ExtensionField,
      ∃ coefficients : Fin 1024 → ExtensionField,
        runtimeQM31View relation.ood_values.val[0]!.val[sample.val]! = value ∧
          value = maintainedSourceDot weights coefficients ∧
          (decodeRelationSchedule rt).ood0 sample = weights ∧
          coefficients = c
  ood1_source : ∀ sample : Fin 2,
    ∃ value : ExtensionField, ∃ weights : Fin 256 → ExtensionField,
      ∃ coefficients : Fin 256 → ExtensionField,
        runtimeQM31View relation.ood_values.val[1]!.val[sample.val]! = value ∧
          value = maintainedSourceDot weights coefficients ∧
          (decodeRelationSchedule rt).ood1 sample = weights ∧
          coefficients = round1Coefficients (decodeRelationSchedule rt) c
  ood2_source : ∀ sample : Fin 2,
    ∃ value : ExtensionField, ∃ weights : Fin 64 → ExtensionField,
      ∃ coefficients : Fin 64 → ExtensionField,
        runtimeQM31View relation.ood_values.val[2]!.val[sample.val]! = value ∧
          value = maintainedSourceDot weights coefficients ∧
          (decodeRelationSchedule rt).ood2 sample = weights ∧
          coefficients = round2Coefficients (decodeRelationSchedule rt) c
  ood3_source : ∀ sample : Fin 2,
    ∃ value : ExtensionField, ∃ weights : Fin 16 → ExtensionField,
      ∃ coefficients : Fin 16 → ExtensionField,
        runtimeQM31View relation.ood_values.val[3]!.val[sample.val]! = value ∧
          value = maintainedSourceDot weights coefficients ∧
          (decodeRelationSchedule rt).ood3 sample = weights ∧
          coefficients = round3Coefficients (decodeRelationSchedule rt) c

structure ReleasedRelationPolynomialSources
    (rt : DeployedRuntimeSchedule BaseField ExtensionField)
    (c : AspisV5ComponentCConcreteFoldLinearity.Coefficients ExtensionField)
    (relation : RuntimeRelation) where
  polynomial0_source : ∀ degree : Fin 7,
    ∃ value : ExtensionField, ∃ weights : Fin 1024 → ExtensionField,
      ∃ coefficients : Fin 1024 → ExtensionField,
        runtimeQM31View relation.sumchecks.val[0]!.val[degree.val]! = value ∧
          value = maintainedSourcePolynomial 256 weights coefficients degree ∧
          (decodeRelationSchedule rt).poly0 = weights ∧
          coefficients = c
  polynomial1_source : ∀ degree : Fin 7,
    ∃ value : ExtensionField, ∃ weights : Fin 256 → ExtensionField,
      ∃ coefficients : Fin 256 → ExtensionField,
        runtimeQM31View relation.sumchecks.val[1]!.val[degree.val]! = value ∧
          value = maintainedSourcePolynomial 64 weights coefficients degree ∧
          (decodeRelationSchedule rt).poly1 = weights ∧
          coefficients = round1Coefficients (decodeRelationSchedule rt) c
  polynomial2_source : ∀ degree : Fin 7,
    ∃ value : ExtensionField, ∃ weights : Fin 64 → ExtensionField,
      ∃ coefficients : Fin 64 → ExtensionField,
        runtimeQM31View relation.sumchecks.val[2]!.val[degree.val]! = value ∧
          value = maintainedSourcePolynomial 16 weights coefficients degree ∧
          (decodeRelationSchedule rt).poly2 = weights ∧
          coefficients = round2Coefficients (decodeRelationSchedule rt) c
  polynomial3_source : ∀ degree : Fin 7,
    ∃ value : ExtensionField, ∃ weights : Fin 16 → ExtensionField,
      ∃ coefficients : Fin 16 → ExtensionField,
        runtimeQM31View relation.sumchecks.val[3]!.val[degree.val]! = value ∧
          value = maintainedSourcePolynomial 4 weights coefficients degree ∧
          (decodeRelationSchedule rt).poly3 = weights ∧
          coefficients = round3Coefficients (decodeRelationSchedule rt) c

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

private theorem four_round_ood_rows_match
    {K : Type*} [Field K]
    (rt : FixedRelationSchedule K)
    (relation0 relation1 relation2 relation3 relation4 : RuntimeRelation)
    (semantics : ReleasedRelationSemantics
      relation0 relation1 relation2 relation3 relation4)
    (view : RawQM31 → K)
    (c : AspisV5ComponentCConcreteFoldLinearity.Coefficients K)
    (hround0 : ∀ sample : Fin 2,
      view (oodPairValue semantics.tables.ood0 sample) =
        roundOodRows rt 0 c sample)
    (hround1 : ∀ sample : Fin 2,
      view (oodPairValue semantics.tables.ood1 sample) =
        roundOodRows rt 1 c sample)
    (hround2 : ∀ sample : Fin 2,
      view (oodPairValue semantics.tables.ood2 sample) =
        roundOodRows rt 2 c sample)
    (hround3 : ∀ sample : Fin 2,
      view (oodPairValue semantics.tables.ood3 sample) =
        roundOodRows rt 3 c sample) :
    ∀ (round : Fin 4) (sample : Fin 2),
      view relation4.ood_values.val[round.val]!.val[sample.val]! =
        roundOodRows rt round c sample := by
  intro round sample
  have hcases : round.val = 0 ∨ round.val = 1 ∨
      round.val = 2 ∨ round.val = 3 := by omega
  rcases hcases with hround | hround | hround | hround
  · have hr : round = 0 := Fin.eq_of_val_eq hround
    rw [hround, semantics.ood0_match sample, hr]
    exact hround0 sample
  · have hr : round = 1 := Fin.eq_of_val_eq hround
    rw [hround, semantics.ood1_match sample, hr]
    exact hround1 sample
  · have hr : round = 2 := Fin.eq_of_val_eq hround
    rw [hround, semantics.ood2_match sample, hr]
    exact hround2 sample
  · have hr : round = 3 := Fin.eq_of_val_eq hround
    rw [hround, semantics.ood3_match sample, hr]
    exact hround3 sample


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
    (hrun0 :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_round
          schedule relation0 tables0 0#usize =
        ok (core.result.Result.Ok (), relation1, tables1))
    (hrun1 :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_round
          schedule relation1 tables1 1#usize =
        ok (core.result.Result.Ok (), relation2, tables2))
    (hrun2 :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_round
          schedule relation2 tables2 2#usize =
        ok (core.result.Result.Ok (), relation3, tables3))
    (hrun3 :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_relation_round
          schedule relation3 tables3 3#usize =
        ok (core.result.Result.Ok (), relation4, tables4))
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
      let rt := withGeneratedRelationTables
        (withGeneratedLaterFibres base indices hrange) semantics.tables
      ReleasedRelationOodSources rt c relation4 ∧
      ReleasedRelationPolynomialSources rt c relation4 ∧
      (∀ coefficient : Fin 4,
        runtimeQM31View relation4.coefficients.val[coefficient.val]! =
          finalCoefficientMap (decodeFriSchedule rt) c coefficient) := by
  rcases generated_released_relation_semantics schedule
      relation0 relation1 relation2 relation3 relation4
      tables0 tables1 tables2 tables3 tables4
      htrace0 htrace1 htrace2 htrace3 hrun0 hrun1 hrun2 hrun3 with ⟨semantics⟩
  refine ⟨semantics, ?_⟩
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
      simpa [rt, laterRt,
        ComponentCRuntimeReleasedTraceFamiliesSourceJoin.withGeneratedRelationTables,
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
  have hcoefficients1Exact :
      exactSliceVector 256 (alloc.vec.Vec.deref relation1.coefficients) =
        round1Coefficients (decodeRelationSchedule rt) c := by
    funext coefficient
    exact hcoefficients.2.2.2.2.2.2.2.2.1 coefficient
  have hcoefficients2Exact :
      exactSliceVector 64 (alloc.vec.Vec.deref relation2.coefficients) =
        round2Coefficients (decodeRelationSchedule rt) c := by
    funext coefficient
    exact hcoefficients.2.2.2.2.2.2.2.2.2.1 coefficient
  have hcoefficients3Exact :
      exactSliceVector 16 (alloc.vec.Vec.deref relation3.coefficients) =
        round3Coefficients (decodeRelationSchedule rt) c := by
    funext coefficient
    exact hcoefficients.2.2.2.2.2.2.2.2.2.2.1 coefficient
  have hood00Length : semantics.tables.ood0.table0.val.length = 1024 := by
    rcases semantics.ood00_materialize with ⟨weights, hrun⟩
    exact generated_materialized_table_length relation0.coefficients
      semantics.tables.ood0.table0 weights 1024 hcoeffLength (by norm_num) hrun
  have hood01Length : semantics.tables.ood0.table1.val.length = 1024 := by
    rcases semantics.ood01_materialize with ⟨weights, hrun⟩
    exact generated_materialized_table_length relation0.coefficients
      semantics.tables.ood0.table1 weights 1024 hcoeffLength (by norm_num) hrun
  have hood10Length : semantics.tables.ood1.table0.val.length = 256 := by
    rcases semantics.ood10_materialize with ⟨weights, hrun⟩
    exact generated_materialized_table_length relation1.coefficients
      semantics.tables.ood1.table0 weights 256 hcoefficients.1 (by norm_num) hrun
  have hood11Length : semantics.tables.ood1.table1.val.length = 256 := by
    rcases semantics.ood11_materialize with ⟨weights, hrun⟩
    exact generated_materialized_table_length relation1.coefficients
      semantics.tables.ood1.table1 weights 256 hcoefficients.1 (by norm_num) hrun
  have hood20Length : semantics.tables.ood2.table0.val.length = 64 := by
    rcases semantics.ood20_materialize with ⟨weights, hrun⟩
    exact generated_materialized_table_length relation2.coefficients
      semantics.tables.ood2.table0 weights 64 hcoefficients.2.1 (by norm_num) hrun
  have hood21Length : semantics.tables.ood2.table1.val.length = 64 := by
    rcases semantics.ood21_materialize with ⟨weights, hrun⟩
    exact generated_materialized_table_length relation2.coefficients
      semantics.tables.ood2.table1 weights 64 hcoefficients.2.1 (by norm_num) hrun
  have hood30Length : semantics.tables.ood3.table0.val.length = 16 := by
    rcases semantics.ood30_materialize with ⟨weights, hrun⟩
    exact generated_materialized_table_length relation3.coefficients
      semantics.tables.ood3.table0 weights 16 hcoefficients.2.2.1 (by norm_num) hrun
  have hood31Length : semantics.tables.ood3.table1.val.length = 16 := by
    rcases semantics.ood31_materialize with ⟨weights, hrun⟩
    exact generated_materialized_table_length relation3.coefficients
      semantics.tables.ood3.table1 weights 16 hcoefficients.2.2.1 (by norm_num) hrun
  have hpoly0Length : semantics.tables.polynomial0.table.val.length = 1024 := by
    rcases semantics.polynomial0_materialize with ⟨weights, hrun⟩
    exact generated_materialized_table_length relation0.coefficients
      semantics.tables.polynomial0.table weights 1024 hcoeffLength (by norm_num) hrun
  have hpoly1Length : semantics.tables.polynomial1.table.val.length = 256 := by
    rcases semantics.polynomial1_materialize with ⟨weights, hrun⟩
    exact generated_materialized_table_length relation1.coefficients
      semantics.tables.polynomial1.table weights 256 hcoefficients.1 (by norm_num) hrun
  have hpoly2Length : semantics.tables.polynomial2.table.val.length = 64 := by
    rcases semantics.polynomial2_materialize with ⟨weights, hrun⟩
    exact generated_materialized_table_length relation2.coefficients
      semantics.tables.polynomial2.table weights 64 hcoefficients.2.1 (by norm_num) hrun
  have hpoly3Length : semantics.tables.polynomial3.table.val.length = 16 := by
    rcases semantics.polynomial3_materialize with ⟨weights, hrun⟩
    exact generated_materialized_table_length relation3.coefficients
      semantics.tables.polynomial3.table weights 16 hcoefficients.2.2.1 (by norm_num) hrun
  have representation :
      FourRoundGeneratedTableRepresentation semantics.tables := {
    ood00_length := hood00Length
    ood01_length := hood01Length
    ood10_length := hood10Length
    ood11_length := hood11Length
    ood20_length := hood20Length
    ood21_length := hood21Length
    ood30_length := hood30Length
    ood31_length := hood31Length
    polynomial0_length := hpoly0Length
    polynomial1_length := hpoly1Length
    polynomial2_length := hpoly2Length
    polynomial3_length := hpoly3Length
    ood00_canonical := semantics.ood00_canonical
    ood01_canonical := semantics.ood01_canonical
    ood10_canonical := semantics.ood10_canonical
    ood11_canonical := semantics.ood11_canonical
    ood20_canonical := semantics.ood20_canonical
    ood21_canonical := semantics.ood21_canonical
    ood30_canonical := semantics.ood30_canonical
    ood31_canonical := semantics.ood31_canonical
    polynomial0_canonical := semantics.polynomial0_canonical
    polynomial1_canonical := semantics.polynomial1_canonical
    polynomial2_canonical := semantics.polynomial2_canonical
    polynomial3_canonical := semantics.polynomial3_canonical }
  have hood0Source := ood_pair_semantics_matches_generated_table
      relation0.coefficients semantics.tables.ood0 1024
      (exactSliceVector 1024 (alloc.vec.Vec.deref relation0.coefficients))
      semantics.ood0_semantics hcoeffLength
      representation.ood00_length representation.ood01_length (by norm_num)
      hcoeffCanonical0 representation.ood00_canonical
      representation.ood01_canonical rfl
  have hood1Source := ood_pair_semantics_matches_generated_table
      relation1.coefficients semantics.tables.ood1 256
      (exactSliceVector 256 (alloc.vec.Vec.deref relation1.coefficients))
      semantics.ood1_semantics hcoefficients.1
      representation.ood10_length representation.ood11_length (by norm_num)
      hcoeffCanonical1 representation.ood10_canonical
      representation.ood11_canonical rfl
  have hood2Source := ood_pair_semantics_matches_generated_table
      relation2.coefficients semantics.tables.ood2 64
      (exactSliceVector 64 (alloc.vec.Vec.deref relation2.coefficients))
      semantics.ood2_semantics hcoefficients.2.1
      representation.ood20_length representation.ood21_length (by norm_num)
      hcoeffCanonical2 representation.ood20_canonical
      representation.ood21_canonical rfl
  have hood3Source := ood_pair_semantics_matches_generated_table
      relation3.coefficients semantics.tables.ood3 16
      (exactSliceVector 16 (alloc.vec.Vec.deref relation3.coefficients))
      semantics.ood3_semantics hcoefficients.2.2.1
      representation.ood30_length representation.ood31_length (by norm_num)
      hcoeffCanonical3 representation.ood30_canonical
      representation.ood31_canonical rfl
  have hpoly0Source := polynomial_semantics_matches_generated_table
    relation0.coefficients semantics.tables.polynomial0 256
    (exactSliceVector 1024 (alloc.vec.Vec.deref relation0.coefficients))
    semantics.polynomial0_semantics (by simpa using hcoeffLength)
    (by simpa using representation.polynomial0_length) (by norm_num)
    hcoeffCanonical0 representation.polynomial0_canonical
    rfl
  have hpoly1Source := polynomial_semantics_matches_generated_table
    relation1.coefficients semantics.tables.polynomial1 64
    (exactSliceVector 256 (alloc.vec.Vec.deref relation1.coefficients))
    semantics.polynomial1_semantics (by simpa using hcoefficients.1)
    (by simpa using representation.polynomial1_length) (by norm_num)
    hcoeffCanonical1 representation.polynomial1_canonical rfl
  have hpoly2Source := polynomial_semantics_matches_generated_table
    relation2.coefficients semantics.tables.polynomial2 16
    (exactSliceVector 64 (alloc.vec.Vec.deref relation2.coefficients))
    semantics.polynomial2_semantics (by simpa using hcoefficients.2.1)
    (by simpa using representation.polynomial2_length) (by norm_num)
    hcoeffCanonical2 representation.polynomial2_canonical rfl
  have hpoly3Source := polynomial_semantics_matches_generated_table
    relation3.coefficients semantics.tables.polynomial3 4
    (exactSliceVector 16 (alloc.vec.Vec.deref relation3.coefficients))
    semantics.polynomial3_semantics (by simpa using hcoefficients.2.2.1)
    (by simpa using representation.polynomial3_length) (by norm_num)
    hcoeffCanonical3 representation.polynomial3_canonical rfl
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
  · refine {
      ood0_source := ?_
      ood1_source := ?_
      ood2_source := ?_
      ood3_source := ?_ }
    · intro sample
      have hvalue := (congrArg runtimeQM31View
        (semantics.ood0_match sample)).trans (hood0Source sample)
      refine ⟨_, _, _, hvalue, rfl, ?_, hinputExact⟩
      · exact generated_ood0_table_apply laterRt semantics.tables sample
    · intro sample
      have hvalue := (congrArg runtimeQM31View
        (semantics.ood1_match sample)).trans (hood1Source sample)
      refine ⟨_, _, _, hvalue, rfl, ?_, hcoefficients1Exact⟩
      · exact generated_ood1_table_apply laterRt semantics.tables sample
    · intro sample
      have hvalue := (congrArg runtimeQM31View
        (semantics.ood2_match sample)).trans (hood2Source sample)
      refine ⟨_, _, _, hvalue, rfl, ?_, hcoefficients2Exact⟩
      · exact generated_ood2_table_apply laterRt semantics.tables sample
    · intro sample
      have hvalue := (congrArg runtimeQM31View
        (semantics.ood3_match sample)).trans (hood3Source sample)
      refine ⟨_, _, _, hvalue, rfl, ?_, hcoefficients3Exact⟩
      · exact generated_ood3_table_apply laterRt semantics.tables sample
  · refine {
      polynomial0_source := ?_
      polynomial1_source := ?_
      polynomial2_source := ?_
      polynomial3_source := ?_ }
    · intro degree
      have hvalue := hpoly0Source degree
      rw [← semantics.polynomial0_match] at hvalue
      refine ⟨_, _, _, ?_, rfl,
        generated_polynomial0_table laterRt semantics.tables, hinputExact⟩
      rw [list_getElem_bang_irrel
        (inferInstance : Inhabited RawQM31)
        ComponentCRuntimeMaterializedRelationArithmetic.instInhabitedRawQM31
        relation4.sumchecks.val[0]!.val degree.val (by simp)]
      exact hvalue
    · intro degree
      have hvalue := hpoly1Source degree
      rw [← semantics.polynomial1_match] at hvalue
      refine ⟨_, _, _, ?_, rfl,
        generated_polynomial1_table laterRt semantics.tables,
        hcoefficients1Exact⟩
      rw [list_getElem_bang_irrel
        (inferInstance : Inhabited RawQM31)
        ComponentCRuntimeMaterializedRelationArithmetic.instInhabitedRawQM31
        relation4.sumchecks.val[1]!.val degree.val (by simp)]
      exact hvalue
    · intro degree
      have hvalue := hpoly2Source degree
      rw [← semantics.polynomial2_match] at hvalue
      refine ⟨_, _, _, ?_, rfl,
        generated_polynomial2_table laterRt semantics.tables,
        hcoefficients2Exact⟩
      rw [list_getElem_bang_irrel
        (inferInstance : Inhabited RawQM31)
        ComponentCRuntimeMaterializedRelationArithmetic.instInhabitedRawQM31
        relation4.sumchecks.val[2]!.val degree.val (by simp)]
      exact hvalue
    · intro degree
      have hvalue := hpoly3Source degree
      rw [← semantics.polynomial3_match] at hvalue
      refine ⟨_, _, _, ?_, rfl,
        generated_polynomial3_table laterRt semantics.tables,
        hcoefficients3Exact⟩
      rw [list_getElem_bang_irrel
        (inferInstance : Inhabited RawQM31)
        ComponentCRuntimeMaterializedRelationArithmetic.instInhabitedRawQM31
        relation4.sumchecks.val[3]!.val degree.val (by simp)]
      exact hvalue

#print axioms generated_four_round_relation_rows_match_maintained

/-- Full source-authentic constructor for the six released families consumed
by the public packer.  The existential table witness, its exact lengths, and
its raw canonicality proof are all produced from the four actual runtime
rounds. -/
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
      let rt := withGeneratedRelationTables
        (withGeneratedLaterFibres base indices hrange) semantics.tables
      Nonempty
        (ReleasedTraceFamilies rt enc c runtimeQM31View later4 trace) := by
  rcases generated_four_round_relation_rows_match_maintained
      schedule relation0 relation1 relation2 relation3 relation4
      tables0 tables1 tables2 tables3 tables4
      htrace0.1 htrace1.1 htrace2.1 htrace3.1
      (generated_runtime_trace_relation_round_call schedule relation0 relation1
        folded0 folded1 later0 later1Out tables0 tables1 0#usize htrace0)
      (generated_runtime_trace_relation_round_call schedule relation1 relation2
        folded1 folded2 later1Out later2Out tables1 tables2 1#usize htrace1)
      (generated_runtime_trace_relation_round_call schedule relation2 relation3
        folded2 folded3 later2Out later3Out tables2 tables3 2#usize htrace2)
      (generated_runtime_trace_relation_round_call schedule relation3 relation4
        folded3 folded4 later3Out later4 tables3 tables4 3#usize htrace3)
      hstateRound0 hstateSamples0 hcoeffLength hcoeffCanonical
      halpha0 halpha1 halpha2 halpha3 base indices hrange c hinput halpha with
    ⟨semantics, hrelation⟩
  refine ⟨semantics, ?_⟩
  dsimp only
  let laterRt := withGeneratedLaterFibres base indices hrange
  let rt := withGeneratedRelationTables laterRt semantics.tables
  have hrelationRows := hrelation
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
  cases hfri
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
    ood0_source := ?_
    ood1_source := ?_
    ood2_source := ?_
    ood3_source := ?_
    polynomial0_source := ?_
    polynomial1_source := ?_
    polynomial2_source := ?_
    polynomial3_source := ?_
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
  · intro sample
    rcases hrelationRows.1.ood0_source sample with
      ⟨value, weights, coefficients, hstored, hevaluated,
        hweights, hcoefficients⟩
    refine ⟨value, weights, coefficients, ?_, hevaluated,
      hweights, hcoefficients⟩
    rw [hfinishArrays.1]
    exact hstored
  · intro sample
    rcases hrelationRows.1.ood1_source sample with
      ⟨value, weights, coefficients, hstored, hevaluated,
        hweights, hcoefficients⟩
    refine ⟨value, weights, coefficients, ?_, hevaluated,
      hweights, hcoefficients⟩
    rw [hfinishArrays.1]
    exact hstored
  · intro sample
    rcases hrelationRows.1.ood2_source sample with
      ⟨value, weights, coefficients, hstored, hevaluated,
        hweights, hcoefficients⟩
    refine ⟨value, weights, coefficients, ?_, hevaluated,
      hweights, hcoefficients⟩
    rw [hfinishArrays.1]
    exact hstored
  · intro sample
    rcases hrelationRows.1.ood3_source sample with
      ⟨value, weights, coefficients, hstored, hevaluated,
        hweights, hcoefficients⟩
    refine ⟨value, weights, coefficients, ?_, hevaluated,
      hweights, hcoefficients⟩
    rw [hfinishArrays.1]
    exact hstored
  · intro degree
    rcases hrelationRows.2.1.polynomial0_source degree with
      ⟨value, weights, coefficients, hstored, hevaluated,
        hweights, hcoefficients⟩
    refine ⟨value, weights, coefficients, ?_, hevaluated,
      hweights, hcoefficients⟩
    rw [hfinishArrays.2.1]
    exact hstored
  · intro degree
    rcases hrelationRows.2.1.polynomial1_source degree with
      ⟨value, weights, coefficients, hstored, hevaluated,
        hweights, hcoefficients⟩
    refine ⟨value, weights, coefficients, ?_, hevaluated,
      hweights, hcoefficients⟩
    rw [hfinishArrays.2.1]
    exact hstored
  · intro degree
    rcases hrelationRows.2.1.polynomial2_source degree with
      ⟨value, weights, coefficients, hstored, hevaluated,
        hweights, hcoefficients⟩
    refine ⟨value, weights, coefficients, ?_, hevaluated,
      hweights, hcoefficients⟩
    rw [hfinishArrays.2.1]
    exact hstored
  · intro degree
    rcases hrelationRows.2.1.polynomial3_source degree with
      ⟨value, weights, coefficients, hstored, hevaluated,
        hweights, hcoefficients⟩
    refine ⟨value, weights, coefficients, ?_, hevaluated,
      hweights, hcoefficients⟩
    rw [hfinishArrays.2.1]
    exact hstored

#print axioms generated_four_round_released_trace_families

/-- One authentic successful public Component-C run together with the finite
schedule/input facts consumed by the maintained decoder.  All execution
fields are equalities for the extracted Rust entrypoint, its four actual
runtime rounds, finish, and public packer. -/
structure GeneratedPublicRun where
  base : DeployedRuntimeSchedule BaseField ExtensionField
  indices : QueryIndices
  hrange : GeneratedLaterFibresInRange indices
  enc : AspisV5ComponentCConcreteFoldLinearity.Coefficients ExtensionField
    →ₗ[ExtensionField] Layer0Word ExtensionField
  c : AspisV5ComponentCConcreteFoldLinearity.Coefficients ExtensionField
  schedule : RuntimeSchedule
  coefficients : Slice RawQM31
  codeword : Slice RawQM31
  expectedInactiveClaim : RawQM31
  output : alloc.vec.Vec RawQM31
  public_success :
    v5_mask.component_c_runtime.evaluate_component_c_runtime_private_view
        schedule coefficients codeword expectedInactiveClaim =
      ok (core.result.Result.Ok output)
  relation0 : RuntimeRelation
  relation1 : RuntimeRelation
  relation2 : RuntimeRelation
  relation3 : RuntimeRelation
  relation4 : RuntimeRelation
  folded0 : alloc.vec.Vec RawQM31
  folded1 : alloc.vec.Vec RawQM31
  folded2 : alloc.vec.Vec RawQM31
  folded3 : alloc.vec.Vec RawQM31
  folded4 : alloc.vec.Vec RawQM31
  later0 : RuntimeLater
  later1Out : RuntimeLater
  later2Out : RuntimeLater
  later3Out : RuntimeLater
  later4 : RuntimeLater
  tables0 : RuntimeTables
  tables1 : RuntimeTables
  tables2 : RuntimeTables
  tables3 : RuntimeTables
  tables4 : RuntimeTables
  trace : RuntimeTrace
  htrace0 : GeneratedRuntimeRoundTrace schedule relation0 relation1
    folded0 folded1 later0 later1Out tables0 tables1 0#usize
  htrace1 : GeneratedRuntimeRoundTrace schedule relation1 relation2
    folded1 folded2 later1Out later2Out tables1 tables2 1#usize
  htrace2 : GeneratedRuntimeRoundTrace schedule relation2 relation3
    folded2 folded3 later2Out later3Out tables2 tables3 2#usize
  htrace3 : GeneratedRuntimeRoundTrace schedule relation3 relation4
    folded3 folded4 later3Out later4 tables3 tables4 3#usize
  hfinish : v5_mask.relation_prover.V5IncrementalRelation.finish relation4 =
    ok (core.result.Result.Ok trace)
  hpack :
    v5_mask.component_c_runtime.pack_component_c_runtime_downstream
        trace.ood_values trace.sumchecks later4 trace.final_coefficients =
      ok (core.result.Result.Ok output)
  hfibres0 : schedule.later_fibres.val[0]! = later1 indices
  hfibres1 : schedule.later_fibres.val[1]! = later2 indices
  hfibres2 : schedule.later_fibres.val[2]! = later3 indices
  hempty0 : later0.val[0]!.val = []
  hempty1 : later0.val[1]!.val = []
  hempty2 : later0.val[2]!.val = []
  hread0 : ∀ fibre ∈ (later1 indices).val,
    4 * fibre.val + 4 ≤ folded1.val.length
  hread1 : ∀ fibre ∈ (later2 indices).val,
    4 * fibre.val + 4 ≤ folded2.val.length
  hread2 : ∀ fibre ∈ (later3 indices).val,
    4 * fibre.val + 4 ≤ folded3.val.length
  hcapacity0 : 4 * (later1 indices).val.length ≤ Std.Usize.max
  hcapacity1 : 4 * (later2 indices).val.length ≤ Std.Usize.max
  hcapacity2 : 4 * (later3 indices).val.length ≤ Std.Usize.max
  hcount0 : (later1 indices).length ≤ 18
  hcount1 : (later2 indices).length ≤ 18
  hcount2 : (later3 indices).length ≤ 18
  hfolded1 : ∀ row : Fin layer1Symbols,
    runtimeQM31View folded1.val[row.val]! =
      layer1Map (decodeFriSchedule
        (withGeneratedLaterFibres base indices hrange)) enc c row
  hfolded2 : ∀ row : Fin layer2Symbols,
    runtimeQM31View folded2.val[row.val]! =
      layer2Map (decodeFriSchedule
        (withGeneratedLaterFibres base indices hrange)) enc c row
  hfolded3 : ∀ row : Fin layer3Symbols,
    runtimeQM31View folded3.val[row.val]! =
      layer3Map (decodeFriSchedule
        (withGeneratedLaterFibres base indices hrange)) enc c row
  hstateRound0 : relation0.round = 0#usize
  hstateSamples0 : relation0.samples = 0#usize
  hcoeffLength : relation0.coefficients.val.length = 1024
  hcoeffCanonical :
    ComponentCRuntimeCoefficientFoldCorrespondence.RuntimeCanonicalList
      relation0.coefficients.val
  halpha0 : runtimeCanonicalQM31 schedule.alphas.val[0]!
  halpha1 : runtimeCanonicalQM31 schedule.alphas.val[1]!
  halpha2 : runtimeCanonicalQM31 schedule.alphas.val[2]!
  halpha3 : runtimeCanonicalQM31 schedule.alphas.val[3]!
  hinput : runtimeCoefficientView
    (alloc.vec.Vec.deref relation0.coefficients) 1024 = c
  halpha : ∀ round : Fin 4,
    runtimeQM31View schedule.alphas.val[round.val]! = base.alpha round

/-- Public-output claim for an actual extracted Component-C run. -/
def GeneratedPublicOutputMatchesDeployed (run : GeneratedPublicRun) : Prop :=
  ∃ semantics : ReleasedRelationSemantics run.relation0 run.relation1
      run.relation2 run.relation3 run.relation4,
    let rt := withGeneratedRelationTables
      (withGeneratedLaterFibres run.base run.indices run.hrange) semantics.tables
    run.output.val.length = fRows (decodeFriSchedule rt) ∧
      ∀ row : Fin (fRows (decodeFriSchedule rt)),
        runtimeQM31View run.output.val[row.val]! =
          deployedEvaluate rt run.enc run.c row

/-- The actual public evaluator, its four extracted runtime rounds, finish,
and packer return exactly the maintained deployed Component-C output. -/
theorem generated_public_run_output_matches_deployed
    (run : GeneratedPublicRun) :
    GeneratedPublicOutputMatchesDeployed run := by
  rcases generated_four_round_released_trace_families
      run.base run.indices run.hrange run.enc run.c run.schedule
      run.relation0 run.relation1 run.relation2 run.relation3 run.relation4
      run.folded0 run.folded1 run.folded2 run.folded3 run.folded4
      run.later0 run.later1Out run.later2Out run.later3Out run.later4
      run.tables0 run.tables1 run.tables2 run.tables3 run.tables4 run.trace
      run.htrace0 run.htrace1 run.htrace2 run.htrace3
      run.hfibres0 run.hfibres1 run.hfibres2
      run.hempty0 run.hempty1 run.hempty2
      run.hread0 run.hread1 run.hread2
      run.hcapacity0 run.hcapacity1 run.hcapacity2
      run.hcount0 run.hcount1 run.hcount2
      run.hfolded1 run.hfolded2 run.hfolded3
      run.hstateRound0 run.hstateSamples0 run.hcoeffLength
      run.hcoeffCanonical run.halpha0 run.halpha1 run.halpha2 run.halpha3
      run.hinput run.halpha run.hfinish with ⟨semantics, hfamilies⟩
  refine ⟨semantics, ?_⟩
  dsimp only
  rcases hfamilies with ⟨families⟩
  exact concrete_released_trace_families_output_matches_deployed
    (withGeneratedRelationTables
      (withGeneratedLaterFibres run.base run.indices run.hrange)
      semantics.tables)
    run.enc run.c runtimeQM31View run.later4 run.trace run.output families
    run.hpack

#print axioms generated_public_run_output_matches_deployed

end aspis_prover.ComponentCRuntimeReleasedTraceFamilies
