import Coordinates.Funs
import V5FriCoordinateFieldSemantics

set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 16000

/-!
# Exact denominator construction in the extracted V5 coordinate helper

These proofs follow the translated loops which build the flat denominator
array before batch inversion.  They establish the source order and the exact
field value in every slot.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5FriCoordinateDenominatorLoops

open AspisV5FriCoordinateFieldSemantics
open AspisCircleGroupOrder

namespace Coordinate
open V5FriCoordinateAdapter

abbrev M31 := aspis_core.field.M31
abbrev M31Vec := alloc.vec.Vec M31
abbrev Point := aspis_core.circle_fri.BaseCirclePoint
abbrev PointVec := alloc.vec.Vec Point
abbrev Kind := aspis_core.circle_fri.FoldDenominator

end Coordinate

instance : Inhabited Coordinate.M31 := ⟨0#u32⟩
instance : Inhabited Coordinate.Point :=
  ⟨{ x := 0#u32, y := 0#u32 }⟩

private theorem getElemBang_eq_getElem {T : Type*} [Inhabited T]
    (values : List T) (index : Nat) (hindex : index < values.length) :
    values[index]! = values[index] := by
  apply List.getElem!_of_getElem?
  simp [hindex]

private theorem wrapping_add_one_exact (index : Std.Usize)
    (hindex : index.val < Std.Usize.max) :
    (Std.Usize.wrapping_add index 1#usize).val = index.val + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  apply Nat.mod_eq_of_lt
  have hone : (1#usize : Std.Usize).val = 1 := rfl
  rw [hone, UScalar.size_UScalarTyUsize]
  have hsize := Usize.size_scalarTac_eq
  omega

def CanonicalM31Vec (values : Coordinate.M31Vec) : Prop :=
  ∀ value, value ∈ values.val → canonicalM31 value

def CanonicalPoints (points : Coordinate.PointVec) : Prop :=
  ∀ index, index < points.val.length →
    pointCanonical points.val[index]!

private theorem extend_pair_exact
    (values : Coordinate.M31Vec) (left right : Coordinate.M31)
    (hcapacity : values.val.length + 2 ≤ Std.Usize.max) :
    ∃ output : Coordinate.M31Vec,
      alloc.vec.Vec.extend_from_slice
          V5FriCoordinateAdapter.aspis_core.field.M31.Insts.CoreCloneClone
          values
          (Array.to_slice (Array.make 2#usize [left, right])) = .ok output ∧
      output.val = values.val ++ [left, right] := by
  let slice : Slice Coordinate.M31 :=
    Array.to_slice (Array.make 2#usize [left, right])
  have hslice : slice.val = [left, right] := by
    rfl
  have hclone : Slice.clone
      V5FriCoordinateAdapter.aspis_core.field.M31.Insts.CoreCloneClone.clone
      slice ⦃ cloned => slice = cloned ⦄ := by
    apply Slice.clone_spec
    intro value hvalue
    unfold V5FriCoordinateAdapter.aspis_core.field.M31.Insts.CoreCloneClone.clone
    rfl
  obtain ⟨cloned, hcloneRun, hcloned⟩ :=
    Aeneas.Std.WP.spec_imp_exists hclone
  subst cloned
  let output : Coordinate.M31Vec :=
    ⟨values.val ++ slice.val, by
      rw [List.length_append, hslice]
      simpa using hcapacity⟩
  refine ⟨output, ?_, ?_⟩
  · change alloc.vec.Vec.extend_from_slice
        V5FriCoordinateAdapter.aspis_core.field.M31.Insts.CoreCloneClone
        values slice = .ok output
    unfold alloc.vec.Vec.extend_from_slice
    have hlength : values.length + slice.length ≤ Std.Usize.max := by
      simpa [alloc.vec.Vec.length, Slice.length, hslice] using hcapacity
    rw [dif_pos hlength]
    simp only [hcloneRun]
    rfl
  · simp [output, hslice]

private def CircleInvariant
    (points : Coordinate.PointVec)
    (state : Coordinate.M31Vec × Option Coordinate.Kind × Std.Usize) :
    Prop :=
  state.2.2.val ≤ points.val.length ∧
  state.1.val.length = 2 * state.2.2.val ∧
  CanonicalM31Vec state.1 ∧
  state.2.1 = none ∧
  ∀ index, index < state.2.2.val →
    m31Value state.1.val[2 * index]! =
        2 * m31Value points.val[index]!.x ∧
    m31Value state.1.val[2 * index + 1]! =
        2 * m31Value points.val[index]!.y

def CirclePost
    (points : Coordinate.PointVec)
    (out : Coordinate.M31Vec × Option Coordinate.Kind) : Prop :=
  out.1.val.length = 2 * points.val.length ∧
  CanonicalM31Vec out.1 ∧
  out.2 = none ∧
  ∀ index, index < points.val.length →
    m31Value out.1.val[2 * index]! =
        2 * m31Value points.val[index]!.x ∧
    m31Value out.1.val[2 * index + 1]! =
        2 * m31Value points.val[index]!.y

/-- The source circle loop appends exactly `2*x, 2*y` for each selected
circle point and retains `none` for the zero marker when all denominators are
nonzero. -/
theorem circle_denominator_loop_exact
    (points : Coordinate.PointVec) (output : Coordinate.M31Vec)
    (hpoints : CanonicalPoints points) (houtput : output.val = [])
    (hpointCountFits : 2 * points.val.length ≤ Std.Usize.max)
    (hnonzero : ∀ index, index < points.val.length →
      2 * m31Value points.val[index]!.x ≠ 0 ∧
      2 * m31Value points.val[index]!.y ≠ 0) :
    V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop0
        points output none 0#usize
      ⦃ out => CirclePost points out ⦄ := by
  unfold
    V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop0
  apply loop.spec_decr_nat
    (fun state => points.val.length - state.2.2.val)
    (CircleInvariant points)
    (CirclePost points)
  · rintro ⟨current, currentZero, ordinal⟩ hstate
    rcases hstate with
      ⟨hordinalLe, hlength, hcanonical, hzero, hvalues⟩
    simp only at hordinalLe hlength hcanonical hzero hvalues
    unfold
      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop0.body
    by_cases hactive : ordinal.val < points.val.length
    · have hcondition : ordinal < alloc.vec.Vec.len points := by
        simpa [UScalar.lt_equiv] using hactive
      have hpointSpec := alloc.vec.Vec.index_usize_spec points ordinal hactive
      obtain ⟨point, hpointRun, hpointValue⟩ :=
        Aeneas.Std.WP.spec_imp_exists hpointSpec
      have hpointBang : point = points.val[ordinal.val]! := by
        rw [hpointValue,
          getElemBang_eq_getElem points.val ordinal.val hactive]
      have hpointCanonical : pointCanonical point := by
        rw [hpointBang]
        exact hpoints ordinal.val hactive
      obtain ⟨x, hxRun, hxCanonical, hxValue⟩ :=
        double_produces_canonical point.x hpointCanonical.1
      obtain ⟨y, hyRun, hyCanonical, hyValue⟩ :=
        double_produces_canonical point.y hpointCanonical.2
      have hxyNonzero := hnonzero ordinal.val hactive
      have hxNonzero : m31Value x ≠ 0 := by
        rw [hxValue, hpointBang]
        exact hxyNonzero.1
      have hyNonzero : m31Value y ≠ 0 := by
        rw [hyValue, hpointBang]
        exact hxyNonzero.2
      have hxZeroRun := is_zero_false x hxNonzero
      have hyZeroRun := is_zero_false y hyNonzero
      have hcapacity : current.val.length + 2 ≤ Std.Usize.max := by
        rw [hlength]
        omega
      obtain ⟨next, hnextRun, hnextValue⟩ :=
        extend_pair_exact current x y hcapacity
      have hordinalSmall : ordinal.val < Std.Usize.max := by
        have hpointsMax : points.val.length ≤ Std.Usize.max := points.property
        omega
      let ordinalOne := Std.Usize.wrapping_add ordinal 1#usize
      have hordinalOne : ordinalOne.val = ordinal.val + 1 := by
        unfold ordinalOne
        exact wrapping_add_one_exact ordinal hordinalSmall
      simp only [if_pos hcondition]
      rw [alloc.vec.Vec.index_slice_index, hpointRun]
      simp only [bind_tc_ok]
      rw [hxRun]
      simp only [bind_tc_ok]
      rw [hyRun]
      simp only [bind_tc_ok]
      rw [hxZeroRun]
      simp only [bind_tc_ok, Bool.false_eq_true, if_false]
      rw [hyZeroRun]
      simp only [bind_tc_ok, Bool.false_eq_true, if_false, Std.lift]
      rw [hzero, hnextRun]
      simp only [bind_tc_ok, WP.spec_ok]
      change CircleInvariant points (next, none, ordinalOne) ∧
        points.val.length - ordinalOne.val <
          points.val.length - ordinal.val
      refine ⟨?_, by rw [hordinalOne]; omega⟩
      unfold CircleInvariant
      simp only
      have hnextLength : next.val.length = 2 * ordinalOne.val := by
        rw [hnextValue, List.length_append, hlength, hordinalOne]
        simp
        omega
      have hnextCanonical : CanonicalM31Vec next := by
        intro value hvalue
        rw [hnextValue] at hvalue
        rcases List.mem_append.mp hvalue with hvalue | hvalue
        · exact hcanonical value hvalue
        · have hxy : value = x ∨ value = y := by
            simpa only [List.mem_cons, List.not_mem_nil, or_false] using hvalue
          rcases hxy with rfl | rfl
          · exact hxCanonical
          · exact hyCanonical
      refine ⟨by rw [hordinalOne]; omega, hnextLength,
        hnextCanonical, True.intro, ?_⟩
      intro index hindex
      by_cases hold : index < ordinal.val
      · have holdPair := hvalues index hold
        have hleftBound : 2 * index < current.val.length := by omega
        have hrightBound : 2 * index + 1 < current.val.length := by omega
        have hleftNext :
            next.val[2 * index]! = current.val[2 * index]! := by
          have hnextBang :
              next.val[2 * index]! =
                (current.val ++ [x, y])[2 * index]! :=
            congrArg (fun values => values[2 * index]!) hnextValue
          rw [hnextBang]
          have happBound : 2 * index <
              (current.val ++ [x, y]).length := by
            simp only [List.length_append, List.length_cons, List.length_nil]
            omega
          rw [getElemBang_eq_getElem _ _ happBound,
            List.getElem_append_left hleftBound]
          rw [← getElemBang_eq_getElem current.val _ hleftBound]
        have hrightNext :
            next.val[2 * index + 1]! = current.val[2 * index + 1]! := by
          have hnextBang :
              next.val[2 * index + 1]! =
                (current.val ++ [x, y])[2 * index + 1]! :=
            congrArg (fun values => values[2 * index + 1]!) hnextValue
          rw [hnextBang]
          have happBound : 2 * index + 1 <
              (current.val ++ [x, y]).length := by
            simp only [List.length_append, List.length_cons, List.length_nil]
            omega
          rw [getElemBang_eq_getElem _ _ happBound,
            List.getElem_append_left hrightBound]
          rw [← getElemBang_eq_getElem current.val _ hrightBound]
        rw [hleftNext, hrightNext]
        exact holdPair
      · have hnew : index = ordinal.val := by
          rw [hordinalOne] at hindex
          omega
        subst index
        have hxAt : next.val[2 * ordinal.val]! = x := by
          have hslot : 2 * ordinal.val = current.val.length := hlength.symm
          rw [hslot]
          have hnextBang :
              next.val[current.val.length]! =
                (current.val ++ [x, y])[current.val.length]! :=
            congrArg (fun values => values[current.val.length]!) hnextValue
          rw [hnextBang]
          simp
        have hyAt : next.val[2 * ordinal.val + 1]! = y := by
          have hslot : 2 * ordinal.val + 1 = current.val.length + 1 := by
            rw [hlength]
          rw [hslot]
          have hnextBang :
              next.val[current.val.length + 1]! =
                (current.val ++ [x, y])[current.val.length + 1]! :=
            congrArg (fun values => values[current.val.length + 1]!) hnextValue
          rw [hnextBang]
          simp
        rw [hxAt, hyAt, hxValue, hyValue, hpointBang]
        exact ⟨rfl, rfl⟩
    · have hdone : ordinal.val = points.val.length := by omega
      have hcondition : ¬ ordinal < alloc.vec.Vec.len points := by
        simpa [UScalar.lt_equiv] using hactive
      simp only [if_neg hcondition, WP.spec_ok]
      rw [hdone] at hlength hvalues
      exact ⟨hlength, hcanonical, hzero, hvalues⟩
  · unfold CircleInvariant CanonicalM31Vec
    simp only
    refine ⟨by simp, ?_, ?_, True.intro, ?_⟩
    · simpa [houtput]
    · intro value hvalue
      simp [houtput] at hvalue
    · intro index hindex
      norm_num at hindex

private def CoordinateInvariant
    (initial : Coordinate.M31Vec) (coordinates : Array Coordinate.M31 3#usize)
    (state : Coordinate.M31Vec × Option Coordinate.Kind × Std.Usize) : Prop :=
  state.2.2.val ≤ 3 ∧
  state.1.val = initial.val ++ coordinates.val.take state.2.2.val ∧
  CanonicalM31Vec state.1 ∧
  state.2.1 = none

private def CoordinatePost
    (initial : Coordinate.M31Vec) (coordinates : Array Coordinate.M31 3#usize)
    (out : Coordinate.M31Vec × Option Coordinate.Kind) : Prop :=
  out.1.val = initial.val ++ coordinates.val ∧
  CanonicalM31Vec out.1 ∧
  out.2 = none

/-- The extracted three-coordinate inner loop appends all three entries in
source order.  On the accepted path its zero marker stays empty. -/
theorem coordinate_denominator_loop_exact
    (initial : Coordinate.M31Vec)
    (coordinates : Array Coordinate.M31 3#usize)
    (kinds : Array Coordinate.Kind 3#usize)
    (hinitial : CanonicalM31Vec initial)
    (hcoordinates : ∀ index, index < 3 →
      canonicalM31 coordinates.val[index]!)
    (hnonzero : ∀ index, index < 3 →
      m31Value coordinates.val[index]! ≠ 0)
    (hcapacity : initial.val.length + 3 ≤ Std.Usize.max) :
    V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop1_loop0_loop0
        initial none coordinates kinds 0#usize
      ⦃ out => CoordinatePost initial coordinates out ⦄ := by
  unfold
    V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop1_loop0_loop0
  apply loop.spec_decr_nat
    (fun state => 3 - state.2.2.val)
    (CoordinateInvariant initial coordinates)
    (CoordinatePost initial coordinates)
  · rintro ⟨current, currentZero, ordinal⟩ hstate
    rcases hstate with
      ⟨hordinalLe, hcurrentValue, hcurrentCanonical, hzero⟩
    simp only at hordinalLe hcurrentValue hcurrentCanonical hzero
    unfold
      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop1_loop0_loop0.body
    by_cases hactive : ordinal.val < 3
    · have hcondition : ordinal < 3#usize := by
        simpa [UScalar.lt_equiv] using hactive
      obtain ⟨coordinate, hcoordinateRun, hcoordinateValue⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (Array.index_usize_spec coordinates ordinal (by
            simpa [Array.length_eq] using hactive))
      obtain ⟨kind, hkindRun, _hkindValue⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (Array.index_usize_spec kinds ordinal (by
            simpa [Array.length_eq] using hactive))
      have hcoordinateBang :
          coordinate = coordinates.val[ordinal.val]! := by
        rw [hcoordinateValue,
          getElemBang_eq_getElem coordinates.val ordinal.val (by
            simpa [Array.length_eq] using hactive)]
      have hcoordinateCanonical : canonicalM31 coordinate := by
        rw [hcoordinateBang]
        exact hcoordinates ordinal.val hactive
      have hcoordinateNonzero : m31Value coordinate ≠ 0 := by
        rw [hcoordinateBang]
        exact hnonzero ordinal.val hactive
      have hzeroRun := is_zero_false coordinate hcoordinateNonzero
      have hcurrentLength :
          current.val.length = initial.val.length + ordinal.val := by
        rw [hcurrentValue, List.length_append, List.length_take,
          coordinates.property]
        have hthree : (3#usize : Std.Usize).val = 3 := rfl
        rw [hthree]
        omega
      have hroom : current.val.length < Std.Usize.max := by
        rw [hcurrentLength]
        omega
      obtain ⟨next, hpushRun, hnextValue⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (alloc.vec.Vec.push_spec current coordinate hroom)
      have hordinalSmall : ordinal.val < Std.Usize.max := by
        have hmax : 3 < Std.Usize.max := by
          rcases Usize.cMax_bound_concrete with ⟨hmax, _⟩
          omega
        omega
      let ordinalOne := Std.Usize.wrapping_add ordinal 1#usize
      have hordinalOne : ordinalOne.val = ordinal.val + 1 := by
        unfold ordinalOne
        exact wrapping_add_one_exact ordinal hordinalSmall
      simp only [if_pos hcondition]
      rw [hcoordinateRun]
      simp only [bind_tc_ok]
      rw [hkindRun]
      simp only [bind_tc_ok]
      rw [hzeroRun]
      simp only [bind_tc_ok, Bool.false_eq_true, if_false]
      rw [hzero, hpushRun]
      simp only [bind_tc_ok, Std.lift, WP.spec_ok]
      change CoordinateInvariant initial coordinates (next, none, ordinalOne) ∧
        3 - ordinalOne.val < 3 - ordinal.val
      refine ⟨?_, by rw [hordinalOne]; omega⟩
      unfold CoordinateInvariant
      simp only
      have hnextExact :
          next.val = initial.val ++ coordinates.val.take ordinalOne.val := by
        rw [hnextValue, hcurrentValue, hordinalOne, List.take_add_one]
        have hget : coordinates.val[ordinal.val]? = some coordinate := by
          rw [List.getElem?_eq_getElem (by
            simpa [Array.length_eq] using hactive)]
          exact congrArg some hcoordinateValue.symm
        simp [hget]
      have hnextCanonical : CanonicalM31Vec next := by
        intro value hvalue
        rw [hnextValue] at hvalue
        rcases List.mem_append.mp hvalue with hvalue | hvalue
        · exact hcurrentCanonical value hvalue
        · have hvalueEq : value = coordinate := by simpa using hvalue
          rw [hvalueEq]
          exact hcoordinateCanonical
      exact ⟨by rw [hordinalOne]; omega, hnextExact,
        hnextCanonical, True.intro⟩
    · have hdone : ordinal.val = 3 := by omega
      have hcondition : ¬ ordinal < 3#usize := by
        simpa [UScalar.lt_equiv] using hactive
      simp only [if_neg hcondition, WP.spec_ok]
      unfold CoordinatePost
      simp only
      rw [hdone] at hcurrentValue
      have hcoordinatesLength : coordinates.val.length = 3 := by
        simpa using coordinates.property
      have htake : coordinates.val.take 3 = coordinates.val := by
        calc
          coordinates.val.take 3 =
              coordinates.val.take coordinates.val.length :=
            congrArg coordinates.val.take hcoordinatesLength.symm
          _ = coordinates.val := List.take_length
      exact ⟨hcurrentValue.trans
        (congrArg (fun tail => initial.val ++ tail) htake),
        hcurrentCanonical, hzero⟩
  · unfold CoordinateInvariant CanonicalM31Vec
    simp only
    refine ⟨by norm_num, ?_, hinitial, True.intro⟩
    simp

#print axioms extend_pair_exact
#print axioms circle_denominator_loop_exact
#print axioms coordinate_denominator_loop_exact

end AspisV5FriCoordinateDenominatorLoops
