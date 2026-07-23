import RuntimeCodewordFoldCorrespondence

set_option autoImplicit false

open Aeneas Aeneas.Std Result

namespace aspis_prover.ComponentCRuntimeCodewordMaintainedLayer

open aspis_prover
open ComponentCRuntimeFoldPrimitiveInstantiation
open ComponentCRuntimeCodewordFoldCorrespondence
open AspisV5ComponentCConcreteFoldLinearity

abbrev RawQM31 := aspis_core.field.QM31
abbrev RawM31 := aspis_core.field.M31
abbrev BaseField := AspisV5ComponentCQM31TowerExact.M31Exact
abbrev ExtensionField := AspisV5ComponentCQM31TowerExact.QM31Exact

local instance : Inhabited RawQM31 := ⟨aspis_core.field.QM31.ZERO⟩

private theorem list_getElemBang_mem
    (values : List RawQM31) (index : Nat) (hindex : index < values.length) :
    values[index]! ∈ values := by
  have heq : values[index]! = values[index] := by
    apply List.getElem!_of_getElem?
    simp [hindex]
  rw [heq]
  exact List.getElem_mem hindex

/-- The exact decoded view of one generated input codeword. -/
def runtimeInputView (values : Slice RawQM31) (n : Nat) :
    Fin (4 * n) → ExtensionField :=
  fun row => runtimeQM31View values.val[row.val]!

/-- The generated base-field representation embeds into the maintained tower
by the ordinary algebra map. -/
theorem runtimeM31View_eq_algebraMap (value : RawM31) :
    runtimeM31View value =
      algebraMap BaseField ExtensionField (value.val : BaseField) := by
  rfl

/-- Exact, granular interface for the public circle-coordinate generator and
its two inverse computations.  This is not an evaluator-faithfulness premise:
every executable call and every decoded scalar is named separately. -/
def GeneratedCircleCoordinateSchedule
    (domainLog : Std.U32) (n : Nat)
    (inv2x inv2y : Fin n → BaseField) : Prop :=
  ∀ (fibre : Fin n) (rawFibre : Std.Usize),
    rawFibre.val = fibre.val →
    ∃ point rawInv2x rawInv2y,
      aspis_core.circle_fri.circle_fiber_point_for_domain_log
          domainLog rawFibre = ok (core.result.Result.Ok point) ∧
      aspis_core.circle_fri.inverse_double point.y
          aspis_core.circle_fri.FoldDenominator.CircleY =
        ok (core.result.Result.Ok rawInv2y) ∧
      aspis_core.circle_fri.inverse_double point.x
          aspis_core.circle_fri.FoldDenominator.CircleX =
        ok (core.result.Result.Ok rawInv2x) ∧
      runtimeCanonicalM31 rawInv2x ∧
      runtimeCanonicalM31 rawInv2y ∧
      (rawInv2x.val : BaseField) = inv2x fibre ∧
      (rawInv2y.val : BaseField) = inv2y fibre

/-- Exact, granular interface for the public line-coordinate generator and
its three inverse computations. -/
def GeneratedLineCoordinateSchedule
    (domainLog : Std.U32) (layer : Std.U8) (n : Nat)
    (inverse : Fin n → Fin 3 → BaseField) : Prop :=
  ∀ (fibre : Fin n) (rawFibre : Std.Usize),
    rawFibre.val = fibre.val →
    ∃ coordinates rawInv0 rawInv1 rawInv2,
      aspis_core.circle_fri.line_fold_coordinates_for_circle
          domainLog layer rawFibre =
        ok (core.result.Result.Ok coordinates) ∧
      aspis_core.circle_fri.inverse_double coordinates.first_pair_x
          aspis_core.circle_fri.FoldDenominator.LineFirstPairX =
        ok (core.result.Result.Ok rawInv0) ∧
      aspis_core.circle_fri.inverse_double coordinates.second_pair_x
          aspis_core.circle_fri.FoldDenominator.LineSecondPairX =
        ok (core.result.Result.Ok rawInv1) ∧
      aspis_core.circle_fri.inverse_double coordinates.second_fold_x
          aspis_core.circle_fri.FoldDenominator.LineSecondFoldX =
        ok (core.result.Result.Ok rawInv2) ∧
      runtimeCanonicalM31 rawInv0 ∧
      runtimeCanonicalM31 rawInv1 ∧
      runtimeCanonicalM31 rawInv2 ∧
      (rawInv0.val : BaseField) = inverse fibre 0 ∧
      (rawInv1.val : BaseField) = inverse fibre 1 ∧
      (rawInv2.val : BaseField) = inverse fibre 2

private theorem orderedFour_runtimeInputView
    (values : Slice RawQM31) (n : Nat) (fibre : Fin n) :
    ComponentCRuntimeFoldPrimitiveReduction.orderedFour
        (runtimeQM31View values.val[4 * fibre.val]!)
        (runtimeQM31View values.val[4 * fibre.val + 1]!)
        (runtimeQM31View values.val[4 * fibre.val + 2]!)
        (runtimeQM31View values.val[4 * fibre.val + 3]!) =
      fun slot => runtimeInputView values n (childIndex fibre slot) := by
  funext slot
  fin_cases slot <;>
    rfl

/-- The actual generated public circle round equals the maintained full layer
map, conditional only on the explicit coordinate/inverse call table above. -/
theorem generated_public_circle_round_equals_maintained
    (values : Slice RawQM31) (alpha : RawQM31)
    (domainLog : Std.U32) (n : Nat) (layerLen : Std.Usize)
    (inv2x inv2y : Fin n → BaseField)
    (hlayerCall :
      circle_candidate.candidate_layer_len_for_domain_log domainLog 0#usize =
        ok (core.result.Result.Ok layerLen))
    (hlayerLen : layerLen.val = 4 * n)
    (hvaluesLength : values.val.length = 4 * n)
    (hn : n ≤ 131072)
    (hvaluesCanonical : RuntimeCanonicalList values.val)
    (halpha : runtimeCanonicalQM31 alpha)
    (hcoordinates : GeneratedCircleCoordinateSchedule
      domainLog n inv2x inv2y) :
    ∃ out,
      circle_candidate.fold_candidate_codeword_round_for_domain_log
          values alpha 0#usize domainLog = ok (core.result.Result.Ok out) ∧
      out.val.length = n ∧
      RuntimeCanonicalList out.val ∧
      ∀ fibre : Fin n,
        runtimeQM31View out.val[fibre.val]! =
          circleFoldLayer n (runtimeQM31View alpha) inv2x inv2y
            (runtimeInputView values n) fibre := by
  let expected : Fin n → ExtensionField := fun fibre =>
    circleFoldLayer n (runtimeQM31View alpha) inv2x inv2y
      (runtimeInputView values n) fibre
  have hcontract : GeneratedFibreFoldContract
      values alpha 0#usize domainLog n expected := by
    intro fibre rawFibre hfibre
    obtain ⟨point, rawInv2x, rawInv2y, hpoint, hinvY, hinvX,
      hcanX, hcanY, hviewX, hviewY⟩ :=
      hcoordinates fibre rawFibre hfibre
    obtain ⟨out, hrun, hcanonical, hexact⟩ :=
      generated_circle_fibre_fold_exact
        values.val[4 * fibre.val]!
        values.val[4 * fibre.val + 1]!
        values.val[4 * fibre.val + 2]!
        values.val[4 * fibre.val + 3]!
        alpha domainLog rawFibre point rawInv2x rawInv2y
        (hvaluesCanonical _ (list_getElemBang_mem _ _ (by omega)))
        (hvaluesCanonical _ (list_getElemBang_mem _ _ (by omega)))
        (hvaluesCanonical _ (list_getElemBang_mem _ _ (by omega)))
        (hvaluesCanonical _ (list_getElemBang_mem _ _ (by omega)))
        halpha hcanX hcanY hpoint hinvY hinvX
    refine ⟨out, hrun, hcanonical, ?_⟩
    rw [hexact, runtimeM31View_eq_algebraMap,
      runtimeM31View_eq_algebraMap, hviewX, hviewY,
      orderedFour_runtimeInputView]
    unfold expected
    rw [circleFoldLayer_apply]
  obtain ⟨out, hrun, hlength, hcanonical, hexact⟩ :=
    extracted_codeword_fold_public_exact values alpha 0#usize domainLog
      n layerLen (by norm_num) hlayerCall hlayerLen hvaluesLength hn
      hvaluesCanonical expected hcontract
  exact ⟨out, hrun, hlength, hcanonical, fun fibre =>
    hexact fibre.val fibre.isLt⟩

/-- The actual generated public line round equals the maintained full layer
map for an arbitrary deployed later round. -/
theorem generated_public_line_round_equals_maintained
    (values : Slice RawQM31) (alpha : RawQM31)
    (round : Std.Usize) (layer : Std.U8)
    (domainLog : Std.U32) (n : Nat) (layerLen : Std.Usize)
    (inverse : Fin n → Fin 3 → BaseField)
    (hroundLow : 0 < round.val) (hroundHigh : round.val < 4)
    (hlayerCast : UScalar.cast .U8 round = layer)
    (hlayerCall :
      circle_candidate.candidate_layer_len_for_domain_log domainLog round =
        ok (core.result.Result.Ok layerLen))
    (hlayerLen : layerLen.val = 4 * n)
    (hvaluesLength : values.val.length = 4 * n)
    (hn : n ≤ 131072)
    (hvaluesCanonical : RuntimeCanonicalList values.val)
    (halpha : runtimeCanonicalQM31 alpha)
    (hcoordinates : GeneratedLineCoordinateSchedule
      domainLog layer n inverse) :
    ∃ out,
      circle_candidate.fold_candidate_codeword_round_for_domain_log
          values alpha round domainLog = ok (core.result.Result.Ok out) ∧
      out.val.length = n ∧
      RuntimeCanonicalList out.val ∧
      ∀ fibre : Fin n,
        runtimeQM31View out.val[fibre.val]! =
          lineFoldLayer n (runtimeQM31View alpha) inverse
            (runtimeInputView values n) fibre := by
  have hroundNe : round ≠ 0#usize := by
    intro h
    have := congrArg UScalar.val h
    norm_num at this
    omega
  let expected : Fin n → ExtensionField := fun fibre =>
    lineFoldLayer n (runtimeQM31View alpha) inverse
      (runtimeInputView values n) fibre
  have hcontract : GeneratedFibreFoldContract
      values alpha round domainLog n expected := by
    intro fibre rawFibre hfibre
    obtain ⟨coordinates, rawInv0, rawInv1, rawInv2,
      hcoordinatesCall, hinv0, hinv1, hinv2,
      hcan0, hcan1, hcan2, hview0, hview1, hview2⟩ :=
      hcoordinates fibre rawFibre hfibre
    obtain ⟨out, hrun, hcanonical, hexact⟩ :=
      generated_line_fibre_fold_exact
        values.val[4 * fibre.val]!
        values.val[4 * fibre.val + 1]!
        values.val[4 * fibre.val + 2]!
        values.val[4 * fibre.val + 3]!
        alpha domainLog layer rawFibre coordinates rawInv0 rawInv1 rawInv2
        (hvaluesCanonical _ (list_getElemBang_mem _ _ (by omega)))
        (hvaluesCanonical _ (list_getElemBang_mem _ _ (by omega)))
        (hvaluesCanonical _ (list_getElemBang_mem _ _ (by omega)))
        (hvaluesCanonical _ (list_getElemBang_mem _ _ (by omega)))
        halpha hcan0 hcan1 hcan2 hcoordinatesCall hinv0 hinv1 hinv2
    refine ⟨out, ?_, hcanonical, ?_⟩
    · unfold generatedFibreCall
      rw [if_neg hroundNe]
      simp only [Std.lift, bind_tc_ok, hlayerCast]
      exact hrun
    · rw [hexact, runtimeM31View_eq_algebraMap,
        runtimeM31View_eq_algebraMap, runtimeM31View_eq_algebraMap,
        hview0, hview1, hview2, orderedFour_runtimeInputView]
      unfold expected
      rw [lineFoldLayer_apply]
  obtain ⟨out, hrun, hlength, hcanonical, hexact⟩ :=
    extracted_codeword_fold_public_exact values alpha round domainLog
      n layerLen hroundHigh hlayerCall hlayerLen hvaluesLength hn
      hvaluesCanonical expected hcontract
  exact ⟨out, hrun, hlength, hcanonical, fun fibre =>
    hexact fibre.val fibre.isLt⟩

/-- Four source-authentic codeword rounds in the exact deployed size tower.
The result deliberately retains each intermediate Rust vector and each public
call equation, so later-release proofs can read the same vectors rather than a
reconstructed mathematical substitute. -/
theorem generated_four_round_codeword_tower
    (values0 : Slice RawQM31)
    (alpha0 alpha1 alpha2 alpha3 : RawQM31)
    (domainLog : Std.U32)
    (len0 len1 len2 len3 : Std.Usize)
    (hcallLen0 :
      circle_candidate.candidate_layer_len_for_domain_log domainLog 0#usize =
        ok (core.result.Result.Ok len0))
    (hcallLen1 :
      circle_candidate.candidate_layer_len_for_domain_log domainLog 1#usize =
        ok (core.result.Result.Ok len1))
    (hcallLen2 :
      circle_candidate.candidate_layer_len_for_domain_log domainLog 2#usize =
        ok (core.result.Result.Ok len2))
    (hcallLen3 :
      circle_candidate.candidate_layer_len_for_domain_log domainLog 3#usize =
        ok (core.result.Result.Ok len3))
    (hlen0 : len0.val = 524288)
    (hlen1 : len1.val = 131072)
    (hlen2 : len2.val = 32768)
    (hlen3 : len3.val = 8192)
    (hvalues0Length : values0.val.length = 524288)
    (hvalues0Canonical : RuntimeCanonicalList values0.val)
    (halpha0 : runtimeCanonicalQM31 alpha0)
    (halpha1 : runtimeCanonicalQM31 alpha1)
    (halpha2 : runtimeCanonicalQM31 alpha2)
    (halpha3 : runtimeCanonicalQM31 alpha3)
    (circleInv2x circleInv2y : Fin 131072 → BaseField)
    (line1Inverse : Fin 32768 → Fin 3 → BaseField)
    (line2Inverse : Fin 8192 → Fin 3 → BaseField)
    (line3Inverse : Fin 2048 → Fin 3 → BaseField)
    (hcircle : GeneratedCircleCoordinateSchedule
      domainLog 131072 circleInv2x circleInv2y)
    (hline1 : GeneratedLineCoordinateSchedule
      domainLog 1#u8 32768 line1Inverse)
    (hline2 : GeneratedLineCoordinateSchedule
      domainLog 2#u8 8192 line2Inverse)
    (hline3 : GeneratedLineCoordinateSchedule
      domainLog 3#u8 2048 line3Inverse) :
    ∃ values1 values2 values3 values4,
      circle_candidate.fold_candidate_codeword_round_for_domain_log
          values0 alpha0 0#usize domainLog =
        ok (core.result.Result.Ok values1) ∧
      circle_candidate.fold_candidate_codeword_round_for_domain_log
          (alloc.vec.Vec.deref values1) alpha1 1#usize domainLog =
        ok (core.result.Result.Ok values2) ∧
      circle_candidate.fold_candidate_codeword_round_for_domain_log
          (alloc.vec.Vec.deref values2) alpha2 2#usize domainLog =
        ok (core.result.Result.Ok values3) ∧
      circle_candidate.fold_candidate_codeword_round_for_domain_log
          (alloc.vec.Vec.deref values3) alpha3 3#usize domainLog =
        ok (core.result.Result.Ok values4) ∧
      values1.val.length = 131072 ∧
      values2.val.length = 32768 ∧
      values3.val.length = 8192 ∧
      values4.val.length = 2048 ∧
      RuntimeCanonicalList values1.val ∧
      RuntimeCanonicalList values2.val ∧
      RuntimeCanonicalList values3.val ∧
      RuntimeCanonicalList values4.val ∧
      (∀ fibre : Fin 131072,
        runtimeQM31View values1.val[fibre.val]! =
          circleFoldLayer 131072 (runtimeQM31View alpha0)
            circleInv2x circleInv2y (runtimeInputView values0 131072) fibre) ∧
      (∀ fibre : Fin 32768,
        runtimeQM31View values2.val[fibre.val]! =
          lineFoldLayer 32768 (runtimeQM31View alpha1) line1Inverse
            (runtimeInputView (alloc.vec.Vec.deref values1) 32768) fibre) ∧
      (∀ fibre : Fin 8192,
        runtimeQM31View values3.val[fibre.val]! =
          lineFoldLayer 8192 (runtimeQM31View alpha2) line2Inverse
            (runtimeInputView (alloc.vec.Vec.deref values2) 8192) fibre) ∧
      ∀ fibre : Fin 2048,
        runtimeQM31View values4.val[fibre.val]! =
          lineFoldLayer 2048 (runtimeQM31View alpha3) line3Inverse
            (runtimeInputView (alloc.vec.Vec.deref values3) 2048) fibre := by
  obtain ⟨values1, run1, length1, canonical1, exact1⟩ :=
    generated_public_circle_round_equals_maintained values0 alpha0 domainLog
      131072 len0 circleInv2x circleInv2y hcallLen0 (by omega)
      (by omega) (by norm_num) hvalues0Canonical halpha0 hcircle
  have cast1 : UScalar.cast .U8 (1#usize : Std.Usize) = 1#u8 := by
    apply UScalar.eq_of_val_eq
    rw [UScalar.cast_val_eq]
    norm_num [UScalar.size]
  have inputLength1 :
      (alloc.vec.Vec.deref values1).val.length = 4 * 32768 := by
    change values1.val.length = 4 * 32768
    omega
  obtain ⟨values2, run2, length2, canonical2, exact2⟩ :=
    generated_public_line_round_equals_maintained
      (alloc.vec.Vec.deref values1) alpha1 1#usize 1#u8 domainLog
      32768 len1 line1Inverse (by norm_num) (by norm_num) cast1 hcallLen1
      (by omega) inputLength1 (by norm_num)
      canonical1 halpha1 hline1
  have cast2 : UScalar.cast .U8 (2#usize : Std.Usize) = 2#u8 := by
    apply UScalar.eq_of_val_eq
    rw [UScalar.cast_val_eq]
    norm_num [UScalar.size]
  have inputLength2 :
      (alloc.vec.Vec.deref values2).val.length = 4 * 8192 := by
    change values2.val.length = 4 * 8192
    omega
  obtain ⟨values3, run3, length3, canonical3, exact3⟩ :=
    generated_public_line_round_equals_maintained
      (alloc.vec.Vec.deref values2) alpha2 2#usize 2#u8 domainLog
      8192 len2 line2Inverse (by norm_num) (by norm_num) cast2 hcallLen2
      (by omega) inputLength2 (by norm_num)
      canonical2 halpha2 hline2
  have cast3 : UScalar.cast .U8 (3#usize : Std.Usize) = 3#u8 := by
    apply UScalar.eq_of_val_eq
    rw [UScalar.cast_val_eq]
    norm_num [UScalar.size]
  have inputLength3 :
      (alloc.vec.Vec.deref values3).val.length = 4 * 2048 := by
    change values3.val.length = 4 * 2048
    omega
  obtain ⟨values4, run4, length4, canonical4, exact4⟩ :=
    generated_public_line_round_equals_maintained
      (alloc.vec.Vec.deref values3) alpha3 3#usize 3#u8 domainLog
      2048 len3 line3Inverse (by norm_num) (by norm_num) cast3 hcallLen3
      (by omega) inputLength3 (by norm_num)
      canonical3 halpha3 hline3
  exact ⟨values1, values2, values3, values4,
    run1, run2, run3, run4,
    length1, length2, length3, length4,
    canonical1, canonical2, canonical3, canonical4,
    exact1, exact2, exact3, exact4⟩

#print axioms runtimeM31View_eq_algebraMap
#print axioms generated_public_circle_round_equals_maintained
#print axioms generated_public_line_round_equals_maintained
#print axioms generated_four_round_codeword_tower

end aspis_prover.ComponentCRuntimeCodewordMaintainedLayer
