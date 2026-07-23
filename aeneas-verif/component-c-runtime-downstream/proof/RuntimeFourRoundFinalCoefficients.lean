import RuntimeRelationCoefficientState
import RuntimeCoefficientTowerCorrespondence
import RuntimeRelationFinishProvenance
import AspisFormal.V5ComponentCDownstreamDeployed

set_option autoImplicit false

open Aeneas Aeneas.Std Result

namespace aspis_prover.ComponentCRuntimeFourRoundFinalCoefficients

open aspis_prover
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5ComponentCDownstreamDeployed
open ComponentCRuntimeCoefficientFoldCorrespondence
open ComponentCRuntimeCoefficientTowerCorrespondence
open ComponentCRuntimeFoldPrimitiveInstantiation
open ComponentCRuntimeRelationCoefficientState
open ComponentCRuntimeRelationFinishProvenance
open ComponentCRuntimeRelationRoundTraceProvenance
open ComponentCRuntimeRoundDeepControlFlow

abbrev RawQM31 := aspis_core.field.QM31
abbrev ExtensionField := AspisV5ComponentCQM31TowerExact.QM31Exact
abbrev RuntimeSchedule :=
  v5_mask.component_c_runtime.V5ComponentCRuntimeSchedule
abbrev RuntimeRelation :=
  v5_mask.relation_prover.V5IncrementalRelation
abbrev RuntimeTables :=
  v5_mask.component_c_runtime.V5ComponentCRuntimeRelationTables

local instance : Inhabited RawQM31 :=
  ComponentCRuntimeCoefficientTowerCorrespondence.instInhabitedRawQM31

private theorem wrapping_zero_one :
    Std.Usize.wrapping_add 0#usize 1#usize = 1#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq, Nat.mod_eq_of_lt]
  · norm_num
  · have h := (1#usize).hSize
    scalar_tac

private theorem wrapping_one_one :
    Std.Usize.wrapping_add 1#usize 1#usize = 2#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq, Nat.mod_eq_of_lt]
  · norm_num
  · have h := (2#usize).hSize
    scalar_tac

private theorem wrapping_two_one :
    Std.Usize.wrapping_add 2#usize 1#usize = 3#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq, Nat.mod_eq_of_lt]
  · norm_num
  · have h := (3#usize).hSize
    scalar_tac

theorem generated_circle_trace_next_state
    (schedule : RuntimeSchedule)
    (relation relationOut : RuntimeRelation)
    (tables tablesOut : RuntimeTables)
    (htrace : GeneratedRelationRoundTrace schedule relation relationOut
      tables tablesOut 0#usize) :
    relationOut.round = 1#usize ∧ relationOut.samples = 0#usize := by
  rcases generated_circle_round_trace_released_state
      schedule relation relationOut tables tablesOut htrace with
    ⟨_r1, _r2, _r3, _point0, _point1, _value0, _value1,
      _table0, _table1, _polynomial, _polynomialTable,
      _hpoint0, _hpoint1, _heval0, _heval1, _hcoeff1, _hcoeff2,
      _hpolynomial, _hstored, _htable0Stored, _htable1Stored,
      _hood, _hvalue0, _hvalue1,
      _hsumchecks, _hsumcheck, hround, hsamples⟩
  exact ⟨hround, hsamples⟩

theorem generated_line_trace_next_state
    (schedule : RuntimeSchedule)
    (relation relationOut : RuntimeRelation)
    (tables tablesOut : RuntimeTables)
    (round : Std.Usize)
    (hroundNonzero : round ≠ 0#usize)
    (hroundBound : round.val < 4)
    (hstateRound : relation.round = round)
    (hstateSamples : relation.samples = 0#usize)
    (htrace : GeneratedRelationRoundTrace schedule relation relationOut
      tables tablesOut round) :
    relationOut.round = Std.Usize.wrapping_add round 1#usize ∧
      relationOut.samples = 0#usize := by
  rcases generated_line_round_trace_released_state
      schedule relation relationOut tables tablesOut round
      hroundNonzero hroundBound hstateRound hstateSamples htrace with
    ⟨_r1, _r2, _r3, _layer0, _layer1, _layerPoints0, _layerPoints1,
      _point0, _point1, _value0, _value1, _table0, _table1,
      _polynomial, _polynomialTable,
      _hlayer0, _hlayer1, _hlayerPoints0, _hlayerPoints1,
      _hpoint0, _hpoint1, _heval0, _heval1, _hcoeff1, _hcoeff2,
      _hpolynomial, _hstored, _htable0Stored, _htable1Stored,
      _hood, _hvalue0, _hvalue1,
      _hsumchecks, _hsumcheck, hround, hsamples⟩
  simpa [hstateRound] using And.intro hround hsamples

#print axioms generated_circle_trace_next_state
#print axioms generated_line_trace_next_state

private theorem finalCoefficientMap_apply_generic
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (schedule : FixedSchedule F K) (c : Coefficients K)
    (coefficient : Fin 4) :
    finalCoefficientMap schedule c coefficient =
      coefficientFoldLayer 4 (schedule.alpha 3)
        (coefficientFoldLayer 16 (schedule.alpha 2)
          (coefficientFoldLayer 64 (schedule.alpha 1)
            (coefficientFoldLayer 256 (schedule.alpha 0) c))) coefficient :=
  rfl

private theorem fourCoefficientFolds_congr
    {K : Type*} [Field K]
    (alpha beta : Fin 4 → K)
    (values other : Coefficients K)
    (halpha : alpha = beta) (hvalues : values = other)
    (coefficient : Fin 4) :
    coefficientFoldLayer 4 (alpha 3)
        (coefficientFoldLayer 16 (alpha 2)
          (coefficientFoldLayer 64 (alpha 1)
            (coefficientFoldLayer 256 (alpha 0) values))) coefficient =
      coefficientFoldLayer 4 (beta 3)
        (coefficientFoldLayer 16 (beta 2)
          (coefficientFoldLayer 64 (beta 1)
            (coefficientFoldLayer 256 (beta 0) other))) coefficient := by
  subst beta
  subst other
  rfl

private theorem fourCoefficientFolds_congr_scalars
    {K : Type*} [Field K]
    (alpha0 alpha1 alpha2 alpha3 beta0 beta1 beta2 beta3 : K)
    (values other : Coefficients K)
    (halpha0 : alpha0 = beta0) (halpha1 : alpha1 = beta1)
    (halpha2 : alpha2 = beta2) (halpha3 : alpha3 = beta3)
    (hvalues : values = other) (coefficient : Fin 4) :
    coefficientFoldLayer 4 alpha3
        (coefficientFoldLayer 16 alpha2
          (coefficientFoldLayer 64 alpha1
            (coefficientFoldLayer 256 alpha0 values))) coefficient =
      coefficientFoldLayer 4 beta3
        (coefficientFoldLayer 16 beta2
          (coefficientFoldLayer 64 beta1
            (coefficientFoldLayer 256 beta0 other))) coefficient := by
  subst beta0
  subst beta1
  subst beta2
  subst beta3
  subst other
  rfl

private theorem oneCoefficientFold_congr
    {K : Type*} [Field K]
    (alpha beta : K) (values other : Coefficients K)
    (halpha : alpha = beta) (hvalues : values = other)
    (coefficient : Fin 256) :
    coefficientFoldLayer 256 alpha values coefficient =
      coefficientFoldLayer 256 beta other coefficient := by
  subst beta
  subst other
  rfl

private theorem twoCoefficientFolds_congr
    {K : Type*} [Field K]
    (alpha0 alpha1 beta0 beta1 : K)
    (values other : Coefficients K)
    (halpha0 : alpha0 = beta0) (halpha1 : alpha1 = beta1)
    (hvalues : values = other) (coefficient : Fin 64) :
    coefficientFoldLayer 64 alpha1
        (coefficientFoldLayer 256 alpha0 values) coefficient =
      coefficientFoldLayer 64 beta1
        (coefficientFoldLayer 256 beta0 other) coefficient := by
  subst beta0
  subst beta1
  subst other
  rfl

private theorem threeCoefficientFolds_congr
    {K : Type*} [Field K]
    (alpha0 alpha1 alpha2 beta0 beta1 beta2 : K)
    (values other : Coefficients K)
    (halpha0 : alpha0 = beta0) (halpha1 : alpha1 = beta1)
    (halpha2 : alpha2 = beta2) (hvalues : values = other)
    (coefficient : Fin 16) :
    coefficientFoldLayer 16 alpha2
        (coefficientFoldLayer 64 alpha1
          (coefficientFoldLayer 256 alpha0 values)) coefficient =
      coefficientFoldLayer 16 beta2
        (coefficientFoldLayer 64 beta1
          (coefficientFoldLayer 256 beta0 other)) coefficient := by
  subst beta0
  subst beta1
  subst beta2
  subst other
  rfl

private theorem round1Coefficients_apply_generic
    {K : Type*} [Field K]
    (schedule : AspisV5ComponentCRelationRowLinearity.FixedRelationSchedule K)
    (c : Coefficients K)
    (coefficient : Fin 256) :
    AspisV5ComponentCRelationRowLinearity.round1Coefficients
        schedule c coefficient =
      coefficientFoldLayer 256 (schedule.alpha 0) c coefficient := rfl

private theorem round2Coefficients_apply_generic
    {K : Type*} [Field K]
    (schedule : AspisV5ComponentCRelationRowLinearity.FixedRelationSchedule K)
    (c : Coefficients K)
    (coefficient : Fin 64) :
    AspisV5ComponentCRelationRowLinearity.round2Coefficients
        schedule c coefficient =
      coefficientFoldLayer 64 (schedule.alpha 1)
        (coefficientFoldLayer 256 (schedule.alpha 0) c) coefficient := rfl

private theorem round3Coefficients_apply_generic
    {K : Type*} [Field K]
    (schedule : AspisV5ComponentCRelationRowLinearity.FixedRelationSchedule K)
    (c : Coefficients K)
    (coefficient : Fin 16) :
    AspisV5ComponentCRelationRowLinearity.round3Coefficients
        schedule c coefficient =
      coefficientFoldLayer 16 (schedule.alpha 2)
        (coefficientFoldLayer 64 (schedule.alpha 1)
          (coefficientFoldLayer 256 (schedule.alpha 0) c)) coefficient := rfl

/-- The coefficient vector carried by four actual generated relation rounds
is exactly the maintained `1024 → 256 → 64 → 16 → 4` natural-basis
map.  This composes the real per-round fold calls rather than an independent
model-side tower. -/
theorem generated_four_relation_rounds_final_coefficient_map
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
    (hcoeffCanonical : RuntimeCanonicalList relation0.coefficients.val)
    (halpha0 : runtimeCanonicalQM31 schedule.alphas.val[0]!)
    (halpha1 : runtimeCanonicalQM31 schedule.alphas.val[1]!)
    (halpha2 : runtimeCanonicalQM31 schedule.alphas.val[2]!)
    (halpha3 : runtimeCanonicalQM31 schedule.alphas.val[3]!)
    (rt : DeployedRuntimeSchedule
      AspisV5ComponentCQM31TowerExact.M31Exact ExtensionField)
    (c : Coefficients ExtensionField)
    (hinput : runtimeCoefficientView
      (alloc.vec.Vec.deref relation0.coefficients) 1024 = c)
    (halpha : ∀ round : Fin 4,
      runtimeQM31View schedule.alphas.val[round.val]! = rt.alpha round) :
    relation1.coefficients.val.length = 256 ∧
      relation2.coefficients.val.length = 64 ∧
      relation3.coefficients.val.length = 16 ∧
      relation4.coefficients.val.length = 4 ∧
      RuntimeCanonicalList relation1.coefficients.val ∧
      RuntimeCanonicalList relation2.coefficients.val ∧
      RuntimeCanonicalList relation3.coefficients.val ∧
      RuntimeCanonicalList relation4.coefficients.val ∧
      (∀ coefficient : Fin 256,
        runtimeQM31View relation1.coefficients.val[coefficient.val]! =
          AspisV5ComponentCRelationRowLinearity.round1Coefficients
            (decodeRelationSchedule rt) c coefficient) ∧
      (∀ coefficient : Fin 64,
        runtimeQM31View relation2.coefficients.val[coefficient.val]! =
          AspisV5ComponentCRelationRowLinearity.round2Coefficients
            (decodeRelationSchedule rt) c coefficient) ∧
      (∀ coefficient : Fin 16,
        runtimeQM31View relation3.coefficients.val[coefficient.val]! =
          AspisV5ComponentCRelationRowLinearity.round3Coefficients
            (decodeRelationSchedule rt) c coefficient) ∧
      ∀ coefficient : Fin 4,
        runtimeQM31View relation4.coefficients.val[coefficient.val]! =
          finalCoefficientMap (decodeFriSchedule rt) c coefficient := by
  have hstate1 := generated_circle_trace_next_state schedule relation0 relation1
    tables0 tables1 htrace0
  have hstate2Raw := generated_line_trace_next_state schedule relation1 relation2
    tables1 tables2 1#usize (by norm_num) (by norm_num)
    hstate1.1 hstate1.2 htrace1
  have hstate2 : relation2.round = 2#usize ∧
      relation2.samples = 0#usize := by
    rw [wrapping_one_one] at hstate2Raw
    exact hstate2Raw
  have hstate3Raw := generated_line_trace_next_state schedule relation2 relation3
    tables2 tables3 2#usize (by norm_num) (by norm_num)
    hstate2.1 hstate2.2 htrace2
  have hstate3 : relation3.round = 3#usize ∧
      relation3.samples = 0#usize := by
    rw [wrapping_two_one] at hstate3Raw
    exact hstate3Raw
  rcases generated_relation_round_trace_exposes_coefficient_fold
      schedule relation0 relation1 tables0 tables1 0#usize
      hstateRound0 hstateSamples0 htrace0 with
    ⟨alpha0, coefficients1, halphaCall0, hcall0, hcoefficients1⟩
  rcases generated_relation_round_trace_exposes_coefficient_fold
      schedule relation1 relation2 tables1 tables2 1#usize
      hstate1.1 hstate1.2 htrace1 with
    ⟨alpha1, coefficients2, halphaCall1, hcall1, hcoefficients2⟩
  rcases generated_relation_round_trace_exposes_coefficient_fold
      schedule relation2 relation3 tables2 tables3 2#usize
      hstate2.1 hstate2.2 htrace2 with
    ⟨alpha2, coefficients3, halphaCall2, hcall2, hcoefficients3⟩
  rcases generated_relation_round_trace_exposes_coefficient_fold
      schedule relation3 relation4 tables3 tables4 3#usize
      hstate3.1 hstate3.2 htrace3 with
    ⟨alpha3, coefficients4, halphaCall3, hcall3, hcoefficients4⟩
  have halpha0Eq : alpha0 = schedule.alphas.val[0]! := by
    have hindex : Array.index_usize schedule.alphas 0#usize =
        ok schedule.alphas.val[0]! := by simp [Array.index_usize]
    rw [hindex] at halphaCall0
    simpa using halphaCall0.symm
  have halpha1Eq : alpha1 = schedule.alphas.val[1]! := by
    have hindex : Array.index_usize schedule.alphas 1#usize =
        ok schedule.alphas.val[1]! := by simp [Array.index_usize]
    rw [hindex] at halphaCall1
    simpa using halphaCall1.symm
  have halpha2Eq : alpha2 = schedule.alphas.val[2]! := by
    have hindex : Array.index_usize schedule.alphas 2#usize =
        ok schedule.alphas.val[2]! := by simp [Array.index_usize]
    rw [hindex] at halphaCall2
    simpa using halphaCall2.symm
  have halpha3Eq : alpha3 = schedule.alphas.val[3]! := by
    have hindex : Array.index_usize schedule.alphas 3#usize =
        ok schedule.alphas.val[3]! := by simp [Array.index_usize]
    rw [hindex] at halphaCall3
    simpa using halphaCall3.symm
  subst alpha0
  subst alpha1
  subst alpha2
  subst alpha3
  rcases generated_four_round_coefficient_tower
      (alloc.vec.Vec.deref relation0.coefficients)
      schedule.alphas.val[0]! schedule.alphas.val[1]!
      schedule.alphas.val[2]! schedule.alphas.val[3]!
      hcoeffLength hcoeffCanonical halpha0 halpha1 halpha2 halpha3 with
    ⟨values1, values2, values3, values4,
      hrun1, hrun2, hrun3, hrun4,
      hlen1, hlen2, hlen3, hlen4,
      hcan1, hcan2, hcan3, hcan4,
      hexact1, hexact2, hexact3, hexact4⟩
  rw [hcall0] at hrun1
  have hvalues1 : values1 = coefficients1 := by simpa using hrun1.symm
  subst values1
  rw [hcoefficients1] at hcall1
  rw [hcall1] at hrun2
  have hvalues2 : values2 = coefficients2 := by simpa using hrun2.symm
  subst values2
  rw [hcoefficients2] at hcall2
  rw [hcall2] at hrun3
  have hvalues3 : values3 = coefficients3 := by simpa using hrun3.symm
  subst values3
  rw [hcoefficients3] at hcall3
  rw [hcall3] at hrun4
  have hvalues4 : values4 = coefficients4 := by simpa using hrun4.symm
  subst values4
  have hfinalLength : relation4.coefficients.val.length = 4 := by
    simpa only [hcoefficients4] using hlen4
  have hlength1 : relation1.coefficients.val.length = 256 := by
    simpa only [hcoefficients1] using hlen1
  have hlength2 : relation2.coefficients.val.length = 64 := by
    simpa only [hcoefficients2] using hlen2
  have hlength3 : relation3.coefficients.val.length = 16 := by
    simpa only [hcoefficients3] using hlen3
  have hcanonical1 : RuntimeCanonicalList relation1.coefficients.val := by
    simpa only [hcoefficients1] using hcan1
  have hcanonical2 : RuntimeCanonicalList relation2.coefficients.val := by
    simpa only [hcoefficients2] using hcan2
  have hcanonical3 : RuntimeCanonicalList relation3.coefficients.val := by
    simpa only [hcoefficients3] using hcan3
  have hcanonical4 : RuntimeCanonicalList relation4.coefficients.val := by
    simpa only [hcoefficients4] using hcan4
  have hactualAlpha0 :
      runtimeQM31View schedule.alphas.val[0]! = rt.alpha 0 := by
    simpa using halpha (0 : Fin 4)
  have hactualAlpha1 :
      runtimeQM31View schedule.alphas.val[1]! = rt.alpha 1 := by
    simpa using halpha (1 : Fin 4)
  have hactualAlpha2 :
      runtimeQM31View schedule.alphas.val[2]! = rt.alpha 2 := by
    simpa using halpha (2 : Fin 4)
  have hactualAlpha3 :
      runtimeQM31View schedule.alphas.val[3]! = rt.alpha 3 := by
    simpa using halpha (3 : Fin 4)
  refine ⟨hlength1, hlength2, hlength3, hfinalLength,
    hcanonical1, hcanonical2, hcanonical3, hcanonical4,
    ?_, ?_, ?_, ?_⟩
  · intro coefficient
    have hrelationValue :
        runtimeQM31View relation1.coefficients.val[coefficient.val]! =
          runtimeQM31View coefficients1.val[coefficient.val]! := by
      rw [hcoefficients1]
    rw [hrelationValue, hexact1 coefficient]
    have htower := oneCoefficientFold_congr
      (runtimeQM31View schedule.alphas.val[0]!) (rt.alpha 0)
      (runtimeCoefficientView
        (alloc.vec.Vec.deref relation0.coefficients) 1024) c
      hactualAlpha0 hinput coefficient
    exact htower.trans
      (round1Coefficients_apply_generic
        (decodeRelationSchedule rt) c coefficient).symm
  · intro coefficient
    have hrelationValue :
        runtimeQM31View relation2.coefficients.val[coefficient.val]! =
          runtimeQM31View coefficients2.val[coefficient.val]! := by
      rw [hcoefficients2]
    rw [hrelationValue, hexact2 coefficient]
    have htower := twoCoefficientFolds_congr
      (runtimeQM31View schedule.alphas.val[0]!)
      (runtimeQM31View schedule.alphas.val[1]!)
      (rt.alpha 0) (rt.alpha 1)
      (runtimeCoefficientView
        (alloc.vec.Vec.deref relation0.coefficients) 1024) c
      hactualAlpha0 hactualAlpha1 hinput coefficient
    exact htower.trans
      (round2Coefficients_apply_generic
        (decodeRelationSchedule rt) c coefficient).symm
  · intro coefficient
    have hrelationValue :
        runtimeQM31View relation3.coefficients.val[coefficient.val]! =
          runtimeQM31View coefficients3.val[coefficient.val]! := by
      rw [hcoefficients3]
    rw [hrelationValue, hexact3 coefficient]
    have htower := threeCoefficientFolds_congr
      (runtimeQM31View schedule.alphas.val[0]!)
      (runtimeQM31View schedule.alphas.val[1]!)
      (runtimeQM31View schedule.alphas.val[2]!)
      (rt.alpha 0) (rt.alpha 1) (rt.alpha 2)
      (runtimeCoefficientView
        (alloc.vec.Vec.deref relation0.coefficients) 1024) c
      hactualAlpha0 hactualAlpha1 hactualAlpha2 hinput coefficient
    exact htower.trans
      (round3Coefficients_apply_generic
        (decodeRelationSchedule rt) c coefficient).symm
  intro coefficient
  have hfinalValue :
      runtimeQM31View relation4.coefficients.val[coefficient.val]! =
        runtimeQM31View coefficients4.val[coefficient.val]! := by
    rw [hcoefficients4]
  rw [hfinalValue, hexact4 coefficient]
  have htower := fourCoefficientFolds_congr_scalars
    (runtimeQM31View schedule.alphas.val[0]!)
    (runtimeQM31View schedule.alphas.val[1]!)
    (runtimeQM31View schedule.alphas.val[2]!)
    (runtimeQM31View schedule.alphas.val[3]!)
    (rt.alpha 0) (rt.alpha 1) (rt.alpha 2) (rt.alpha 3)
    (runtimeCoefficientView
      (alloc.vec.Vec.deref relation0.coefficients) 1024) c
    hactualAlpha0 hactualAlpha1 hactualAlpha2 hactualAlpha3 hinput coefficient
  have hfinalDef := finalCoefficientMap_apply_generic
    (decodeFriSchedule rt) c coefficient
  exact htower.trans hfinalDef.symm

#print axioms generated_four_relation_rounds_final_coefficient_map

/-- The public trace returned by the actual generated `finish` call carries
the same maintained four final coefficients established for the relation
state. -/
theorem generated_finish_final_coefficients_match_maintained
    (relation : RuntimeRelation)
    (trace : v5_mask.relation_prover.V5RelationTrace)
    (rt : DeployedRuntimeSchedule
      AspisV5ComponentCQM31TowerExact.M31Exact ExtensionField)
    (c : Coefficients ExtensionField)
    (hfinish :
      v5_mask.relation_prover.V5IncrementalRelation.finish relation =
        ok (core.result.Result.Ok trace))
    (hrelation : ∀ coefficient : Fin 4,
      runtimeQM31View relation.coefficients.val[coefficient.val]! =
        finalCoefficientMap (decodeFriSchedule rt) c coefficient) :
    ∀ coefficient : Fin 4,
      runtimeQM31View trace.final_coefficients.val[coefficient.val]! =
        finalCoefficientMap (decodeFriSchedule rt) c coefficient := by
  have hfinal := generated_finish_success_preserves_final_coefficients
    relation trace hfinish
  intro coefficient
  rw [hfinal]
  exact hrelation coefficient

#print axioms generated_finish_final_coefficients_match_maintained

end aspis_prover.ComponentCRuntimeFourRoundFinalCoefficients
