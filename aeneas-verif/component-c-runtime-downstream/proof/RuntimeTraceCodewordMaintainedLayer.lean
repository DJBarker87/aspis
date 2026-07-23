import RuntimeFourRoundLaterRelease
import RuntimeCodewordMaintainedLayer
import AspisFormal.V5ComponentCDownstreamDeployed

set_option autoImplicit false

open Aeneas Aeneas.Std Result

namespace aspis_prover.ComponentCRuntimeTraceCodewordMaintainedLayer

open aspis_prover
open ComponentCRuntimeFoldPrimitiveInstantiation
open ComponentCRuntimeRoundDeepControlFlow
open ComponentCRuntimeCodewordFoldCorrespondence
open ComponentCRuntimeCodewordMaintainedLayer
open AspisV5ComponentCConcreteFoldLinearity

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

local instance : Inhabited RawQM31 :=
  ComponentCRuntimeCodewordMaintainedLayer.instInhabitedRawQM31

private theorem decoded_layer1Map_apply
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (rt : AspisV5ComponentCDownstreamDeployed.DeployedRuntimeSchedule F K)
    (enc : Coefficients K →ₗ[K] Layer0Word K)
    (c : Coefficients K) (row : Fin 131072) :
    layer1Map (AspisV5ComponentCDownstreamDeployed.decodeFriSchedule rt)
        enc c row =
      circleFoldLayer 131072 (rt.alpha 0) rt.circleInv2x rt.circleInv2y
        (enc c) row := rfl

private theorem decoded_layer2Map_apply
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (rt : AspisV5ComponentCDownstreamDeployed.DeployedRuntimeSchedule F K)
    (enc : Coefficients K →ₗ[K] Layer0Word K)
    (c : Coefficients K) (row : Fin 32768) :
    layer2Map (AspisV5ComponentCDownstreamDeployed.decodeFriSchedule rt)
        enc c row =
      lineFoldLayer 32768 (rt.alpha 1) rt.line1Inverse
        (layer1Map
          (AspisV5ComponentCDownstreamDeployed.decodeFriSchedule rt)
          enc c) row := rfl

private theorem decoded_layer3Map_apply
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (rt : AspisV5ComponentCDownstreamDeployed.DeployedRuntimeSchedule F K)
    (enc : Coefficients K →ₗ[K] Layer0Word K)
    (c : Coefficients K) (row : Fin 8192) :
    layer3Map (AspisV5ComponentCDownstreamDeployed.decodeFriSchedule rt)
        enc c row =
      lineFoldLayer 8192 (rt.alpha 2) rt.line2Inverse
        (layer2Map
          (AspisV5ComponentCDownstreamDeployed.decodeFriSchedule rt)
          enc c) row := rfl

/-- The four folded vectors reached by the actual public runtime-round trace
are the same vectors produced by the maintained fold-tower correspondence.
This eliminates a potential "proved tower, different execution" gap by using
the four generated call equalities and result injectivity. -/
theorem generated_runtime_trace_has_maintained_codeword_tower
    (schedule : RuntimeSchedule)
    (relation0 relation1 relation2 relation3 relation4 : RuntimeRelation)
    (folded0 folded1 folded2 folded3 folded4 : alloc.vec.Vec RawQM31)
    (later0 later1 later2 later3 later4 : RuntimeLater)
    (tables0 tables1 tables2 tables3 tables4 : RuntimeTables)
    (htrace0 : GeneratedRuntimeRoundTrace schedule relation0 relation1
      folded0 folded1 later0 later1 tables0 tables1 0#usize)
    (htrace1 : GeneratedRuntimeRoundTrace schedule relation1 relation2
      folded1 folded2 later1 later2 tables1 tables2 1#usize)
    (htrace2 : GeneratedRuntimeRoundTrace schedule relation2 relation3
      folded2 folded3 later2 later3 tables2 tables3 2#usize)
    (htrace3 : GeneratedRuntimeRoundTrace schedule relation3 relation4
      folded3 folded4 later3 later4 tables3 tables4 3#usize)
    (len0 len1 len2 len3 : Std.Usize)
    (hcallLen0 :
      circle_candidate.candidate_layer_len_for_domain_log
          v5_mask.V5_DOMAIN_LOG 0#usize =
        ok (core.result.Result.Ok len0))
    (hcallLen1 :
      circle_candidate.candidate_layer_len_for_domain_log
          v5_mask.V5_DOMAIN_LOG 1#usize =
        ok (core.result.Result.Ok len1))
    (hcallLen2 :
      circle_candidate.candidate_layer_len_for_domain_log
          v5_mask.V5_DOMAIN_LOG 2#usize =
        ok (core.result.Result.Ok len2))
    (hcallLen3 :
      circle_candidate.candidate_layer_len_for_domain_log
          v5_mask.V5_DOMAIN_LOG 3#usize =
        ok (core.result.Result.Ok len3))
    (hlen0 : len0.val = 524288)
    (hlen1 : len1.val = 131072)
    (hlen2 : len2.val = 32768)
    (hlen3 : len3.val = 8192)
    (hfolded0Length : folded0.val.length = 524288)
    (hfolded0Canonical : RuntimeCanonicalList folded0.val)
    (halpha0 : runtimeCanonicalQM31 schedule.alphas.val[0]!)
    (halpha1 : runtimeCanonicalQM31 schedule.alphas.val[1]!)
    (halpha2 : runtimeCanonicalQM31 schedule.alphas.val[2]!)
    (halpha3 : runtimeCanonicalQM31 schedule.alphas.val[3]!)
    (circleInv2x circleInv2y : Fin 131072 → BaseField)
    (line1Inverse : Fin 32768 → Fin 3 → BaseField)
    (line2Inverse : Fin 8192 → Fin 3 → BaseField)
    (line3Inverse : Fin 2048 → Fin 3 → BaseField)
    (hcircle : GeneratedCircleCoordinateSchedule
      v5_mask.V5_DOMAIN_LOG 131072 circleInv2x circleInv2y)
    (hline1 : GeneratedLineCoordinateSchedule
      v5_mask.V5_DOMAIN_LOG 1#u8 32768 line1Inverse)
    (hline2 : GeneratedLineCoordinateSchedule
      v5_mask.V5_DOMAIN_LOG 2#u8 8192 line2Inverse)
    (hline3 : GeneratedLineCoordinateSchedule
      v5_mask.V5_DOMAIN_LOG 3#u8 2048 line3Inverse) :
    folded1.val.length = 131072 ∧
    folded2.val.length = 32768 ∧
    folded3.val.length = 8192 ∧
    folded4.val.length = 2048 ∧
    RuntimeCanonicalList folded1.val ∧
    RuntimeCanonicalList folded2.val ∧
    RuntimeCanonicalList folded3.val ∧
    RuntimeCanonicalList folded4.val ∧
    (∀ fibre : Fin 131072,
      runtimeQM31View folded1.val[fibre.val]! =
        circleFoldLayer 131072
          (runtimeQM31View schedule.alphas.val[0]!)
          circleInv2x circleInv2y
          (runtimeInputView (alloc.vec.Vec.deref folded0) 131072) fibre) ∧
    (∀ fibre : Fin 32768,
      runtimeQM31View folded2.val[fibre.val]! =
        lineFoldLayer 32768
          (runtimeQM31View schedule.alphas.val[1]!) line1Inverse
          (runtimeInputView (alloc.vec.Vec.deref folded1) 32768) fibre) ∧
    (∀ fibre : Fin 8192,
      runtimeQM31View folded3.val[fibre.val]! =
        lineFoldLayer 8192
          (runtimeQM31View schedule.alphas.val[2]!) line2Inverse
          (runtimeInputView (alloc.vec.Vec.deref folded2) 8192) fibre) ∧
    ∀ fibre : Fin 2048,
      runtimeQM31View folded4.val[fibre.val]! =
        lineFoldLayer 2048
          (runtimeQM31View schedule.alphas.val[3]!) line3Inverse
          (runtimeInputView (alloc.vec.Vec.deref folded3) 2048) fibre := by
  obtain ⟨values1, values2, values3, values4,
      hrun0, hrun1, hrun2, hrun3,
      hlength1, hlength2, hlength3, hlength4,
      hcanonical1, hcanonical2, hcanonical3, hcanonical4,
      hexact1, hexact2, hexact3, hexact4⟩ :=
    generated_four_round_codeword_tower
      (alloc.vec.Vec.deref folded0)
      schedule.alphas.val[0]! schedule.alphas.val[1]!
      schedule.alphas.val[2]! schedule.alphas.val[3]!
      v5_mask.V5_DOMAIN_LOG len0 len1 len2 len3
      hcallLen0 hcallLen1 hcallLen2 hcallLen3
      hlen0 hlen1 hlen2 hlen3 hfolded0Length hfolded0Canonical
      halpha0 halpha1 halpha2 halpha3
      circleInv2x circleInv2y line1Inverse line2Inverse line3Inverse
      hcircle hline1 hline2 hline3
  have hactual0 :
      circle_candidate.fold_candidate_codeword_round_for_domain_log
          (alloc.vec.Vec.deref folded0) schedule.alphas.val[0]!
          0#usize v5_mask.V5_DOMAIN_LOG =
        ok (core.result.Result.Ok folded1) := by
    simpa using htrace0.2.1
  rw [hrun0] at hactual0
  have hvalues1 : values1 = folded1 := by simpa using hactual0
  subst values1
  have hactual1 :
      circle_candidate.fold_candidate_codeword_round_for_domain_log
          (alloc.vec.Vec.deref folded1) schedule.alphas.val[1]!
          1#usize v5_mask.V5_DOMAIN_LOG =
        ok (core.result.Result.Ok folded2) := by
    simpa using htrace1.2.1
  rw [hrun1] at hactual1
  have hvalues2 : values2 = folded2 := by simpa using hactual1
  subst values2
  have hactual2 :
      circle_candidate.fold_candidate_codeword_round_for_domain_log
          (alloc.vec.Vec.deref folded2) schedule.alphas.val[2]!
          2#usize v5_mask.V5_DOMAIN_LOG =
        ok (core.result.Result.Ok folded3) := by
    simpa using htrace2.2.1
  rw [hrun2] at hactual2
  have hvalues3 : values3 = folded3 := by simpa using hactual2
  subst values3
  have hactual3 :
      circle_candidate.fold_candidate_codeword_round_for_domain_log
          (alloc.vec.Vec.deref folded3) schedule.alphas.val[3]!
          3#usize v5_mask.V5_DOMAIN_LOG =
        ok (core.result.Result.Ok folded4) := by
    simpa using htrace3.2.1
  rw [hrun3] at hactual3
  have hvalues4 : values4 = folded4 := by simpa using hactual3
  subst values4
  exact ⟨hlength1, hlength2, hlength3, hlength4,
    hcanonical1, hcanonical2, hcanonical3, hcanonical4,
    hexact1, hexact2, hexact3, hexact4⟩

#print axioms generated_runtime_trace_has_maintained_codeword_tower

/-- Pure adapter from the exact decoded runtime tower to the maintained fixed
four-layer maps.  It requires only the initial encoded-word equality and the
four scalar challenge equalities; fold ordering and recursion are inherited
from the source-authentic tower theorem above. -/
theorem decoded_runtime_tower_eq_fixed_layers
    (schedule : RuntimeSchedule)
    (rt : AspisV5ComponentCDownstreamDeployed.DeployedRuntimeSchedule
      BaseField ExtensionField)
    (enc : Coefficients ExtensionField →ₗ[ExtensionField]
      Layer0Word ExtensionField)
    (c : Coefficients ExtensionField)
    (folded0 folded1 folded2 folded3 : alloc.vec.Vec RawQM31)
    (hinput : runtimeInputView (alloc.vec.Vec.deref folded0) 131072 = enc c)
    (halpha : ∀ round : Fin 4,
      runtimeQM31View schedule.alphas.val[round.val]! = rt.alpha round)
    (hexact1 : ∀ fibre : Fin 131072,
      runtimeQM31View folded1.val[fibre.val]! =
        circleFoldLayer 131072
          (runtimeQM31View schedule.alphas.val[0]!)
          rt.circleInv2x rt.circleInv2y
          (runtimeInputView (alloc.vec.Vec.deref folded0) 131072) fibre)
    (hexact2 : ∀ fibre : Fin 32768,
      runtimeQM31View folded2.val[fibre.val]! =
        lineFoldLayer 32768
          (runtimeQM31View schedule.alphas.val[1]!) rt.line1Inverse
          (runtimeInputView (alloc.vec.Vec.deref folded1) 32768) fibre)
    (hexact3 : ∀ fibre : Fin 8192,
      runtimeQM31View folded3.val[fibre.val]! =
        lineFoldLayer 8192
          (runtimeQM31View schedule.alphas.val[2]!) rt.line2Inverse
          (runtimeInputView (alloc.vec.Vec.deref folded2) 8192) fibre) :
    (∀ row : Fin 131072,
      runtimeQM31View folded1.val[row.val]! =
        layer1Map
          (AspisV5ComponentCDownstreamDeployed.decodeFriSchedule rt)
          enc c row) ∧
    (∀ row : Fin 32768,
      runtimeQM31View folded2.val[row.val]! =
        layer2Map
          (AspisV5ComponentCDownstreamDeployed.decodeFriSchedule rt)
          enc c row) ∧
    ∀ row : Fin 8192,
      runtimeQM31View folded3.val[row.val]! =
        layer3Map
          (AspisV5ComponentCDownstreamDeployed.decodeFriSchedule rt)
          enc c row := by
  have hLayer1 : ∀ row : Fin 131072,
      runtimeQM31View folded1.val[row.val]! =
        layer1Map
          (AspisV5ComponentCDownstreamDeployed.decodeFriSchedule rt)
          enc c row := by
    have halpha0Nat :
        runtimeQM31View schedule.alphas.val[0]! = rt.alpha 0 := by
      simpa using halpha 0
    intro row
    rw [hexact1 row, halpha0Nat]
    rw [decoded_layer1Map_apply]
    rw [hinput]
  have hLayer1Function :
      runtimeInputView (alloc.vec.Vec.deref folded1) 32768 =
        layer1Map
          (AspisV5ComponentCDownstreamDeployed.decodeFriSchedule rt)
          enc c := by
    funext row
    exact hLayer1 row
  have hLayer2 : ∀ row : Fin 32768,
      runtimeQM31View folded2.val[row.val]! =
        layer2Map
          (AspisV5ComponentCDownstreamDeployed.decodeFriSchedule rt)
          enc c row := by
    have halpha1Nat :
        runtimeQM31View schedule.alphas.val[1]! = rt.alpha 1 := by
      simpa using halpha 1
    intro row
    rw [hexact2 row, halpha1Nat]
    rw [decoded_layer2Map_apply]
    rw [hLayer1Function]
  have hLayer2Function :
      runtimeInputView (alloc.vec.Vec.deref folded2) 8192 =
        layer2Map
          (AspisV5ComponentCDownstreamDeployed.decodeFriSchedule rt)
          enc c := by
    funext row
    exact hLayer2 row
  have hLayer3 : ∀ row : Fin 8192,
      runtimeQM31View folded3.val[row.val]! =
        layer3Map
          (AspisV5ComponentCDownstreamDeployed.decodeFriSchedule rt)
          enc c row := by
    have halpha2Nat :
        runtimeQM31View schedule.alphas.val[2]! = rt.alpha 2 := by
      simpa using halpha 2
    intro row
    rw [hexact3 row, halpha2Nat]
    rw [decoded_layer3Map_apply]
    rw [hLayer2Function]
  exact ⟨hLayer1, hLayer2, hLayer3⟩

#print axioms decoded_runtime_tower_eq_fixed_layers

end aspis_prover.ComponentCRuntimeTraceCodewordMaintainedLayer
