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

private theorem getElemBang_append_left {T : Type*} [Inhabited T]
    (head tail : List T) (index : Nat) (hindex : index < head.length) :
    (head ++ tail)[index]! = head[index]! := by
  have happ : index < (head ++ tail).length := by
    simp only [List.length_append]
    omega
  rw [getElemBang_eq_getElem _ _ happ,
    List.getElem_append_left hindex,
    ← getElemBang_eq_getElem head index hindex]

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

private def LinePointInvariant
    (initial : Coordinate.M31Vec) (points : Coordinate.PointVec)
    (state : Coordinate.M31Vec × Option Coordinate.Kind × Std.Usize) : Prop :=
  state.2.2.val ≤ points.val.length ∧
  state.1.val.length = initial.val.length + 3 * state.2.2.val ∧
  CanonicalM31Vec state.1 ∧
  state.2.1 = none ∧
  (∀ index, index < initial.val.length →
    state.1.val[index]! = initial.val[index]!) ∧
  ∀ index, index < state.2.2.val →
    m31Value state.1.val[initial.val.length + 3 * index]! =
        2 * m31Value points.val[index]!.x ∧
    m31Value state.1.val[initial.val.length + 3 * index + 1]! =
        2 * m31Value points.val[index]!.y ∧
    m31Value state.1.val[initial.val.length + 3 * index + 2]! =
        2 * (2 * m31Value points.val[index]!.x ^ 2 - 1)

def LinePointPost
    (initial : Coordinate.M31Vec) (points : Coordinate.PointVec)
    (out : Coordinate.M31Vec × Option Coordinate.Kind) : Prop :=
  out.1.val.length = initial.val.length + 3 * points.val.length ∧
  CanonicalM31Vec out.1 ∧
  out.2 = none ∧
  (∀ index, index < initial.val.length →
    out.1.val[index]! = initial.val[index]!) ∧
  ∀ index, index < points.val.length →
    m31Value out.1.val[initial.val.length + 3 * index]! =
        2 * m31Value points.val[index]!.x ∧
    m31Value out.1.val[initial.val.length + 3 * index + 1]! =
        2 * m31Value points.val[index]!.y ∧
    m31Value out.1.val[initial.val.length + 3 * index + 2]! =
        2 * (2 * m31Value points.val[index]!.x ^ 2 - 1)

/-- For every point of one later FRI layer, the translated Rust appends the
three denominators `2*x`, `2*y`, and `2*(2*x^2-1)` in that order. -/
theorem line_point_denominator_loop_exact
    (initial : Coordinate.M31Vec) (points : Coordinate.PointVec)
    (hinitial : CanonicalM31Vec initial)
    (hpoints : CanonicalPoints points)
    (hcapacity : initial.val.length + 3 * points.val.length ≤
      Std.Usize.max)
    (hnonzero : ∀ index, index < points.val.length →
      2 * m31Value points.val[index]!.x ≠ 0 ∧
      2 * m31Value points.val[index]!.y ≠ 0 ∧
      2 * (2 * m31Value points.val[index]!.x ^ 2 - 1) ≠ 0) :
    V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop1_loop0
        initial none points 0#usize
      ⦃ out => LinePointPost initial points out ⦄ := by
  unfold
    V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop1_loop0
  apply loop.spec_decr_nat
    (fun state => points.val.length - state.2.2.val)
    (LinePointInvariant initial points)
    (LinePointPost initial points)
  · rintro ⟨current, currentZero, ordinal⟩ hstate
    rcases hstate with
      ⟨hordinalLe, hlength, hcanonical, hzero, hprefix, hvalues⟩
    simp only at hordinalLe hlength hcanonical hzero hprefix hvalues
    unfold
      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop1_loop0.body
    by_cases hactive : ordinal.val < points.val.length
    · have hcondition : ordinal < alloc.vec.Vec.len points := by
        simpa [UScalar.lt_equiv] using hactive
      obtain ⟨point, hpointRun, hpointValue⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (alloc.vec.Vec.index_usize_spec points ordinal hactive)
      have hpointBang : point = points.val[ordinal.val]! := by
        rw [hpointValue,
          getElemBang_eq_getElem points.val ordinal.val hactive]
      have hpointCanonical : pointCanonical point := by
        rw [hpointBang]
        exact hpoints ordinal.val hactive
      obtain ⟨first, hfirstRun, hfirstCanonical, hfirstValue⟩ :=
        double_produces_canonical point.x hpointCanonical.1
      obtain ⟨second, hsecondRun, hsecondCanonical, hsecondValue⟩ :=
        double_produces_canonical point.y hpointCanonical.2
      obtain ⟨foldX, hfoldXRun, hfoldXCanonical, hfoldXValue⟩ :=
        double_x_produces_canonical point.x hpointCanonical.1
      obtain ⟨third, hthirdRun, hthirdCanonical, hthirdValue⟩ :=
        double_produces_canonical foldX hfoldXCanonical
      let coordinates : Array Coordinate.M31 3#usize :=
        Array.make 3#usize [first, second, third]
      let kinds : Array Coordinate.Kind 3#usize :=
        Array.make 3#usize [
          V5FriCoordinateAdapter.aspis_core.circle_fri.FoldDenominator.LineFirstPairX,
          V5FriCoordinateAdapter.aspis_core.circle_fri.FoldDenominator.LineSecondPairX,
          V5FriCoordinateAdapter.aspis_core.circle_fri.FoldDenominator.LineSecondFoldX]
      have hcoordinatesValue : coordinates.val = [first, second, third] := rfl
      have hcoord0 : coordinates.val[0]! = first := by
        rw [hcoordinatesValue]
        rfl
      have hcoord1 : coordinates.val[1]! = second := by
        rw [hcoordinatesValue]
        rfl
      have hcoord2 : coordinates.val[2]! = third := by
        rw [hcoordinatesValue]
        rfl
      have hcoordinateCanonical : ∀ index, index < 3 →
          canonicalM31 coordinates.val[index]! := by
        intro index hindex
        interval_cases index
        · rw [hcoord0]
          exact hfirstCanonical
        · rw [hcoord1]
          exact hsecondCanonical
        · rw [hcoord2]
          exact hthirdCanonical
      have hpointNonzero := hnonzero ordinal.val hactive
      have hcoordinateNonzero : ∀ index, index < 3 →
          m31Value coordinates.val[index]! ≠ 0 := by
        intro index hindex
        interval_cases index
        · rw [hcoord0, hfirstValue, hpointBang]
          exact hpointNonzero.1
        · rw [hcoord1, hsecondValue, hpointBang]
          exact hpointNonzero.2.1
        · rw [hcoord2, hthirdValue, hfoldXValue, hpointBang]
          exact hpointNonzero.2.2
      have hinnerCapacity : current.val.length + 3 ≤ Std.Usize.max := by
        rw [hlength]
        omega
      obtain ⟨⟨next, nextZero⟩, hinnerRun, hinnerPost⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (coordinate_denominator_loop_exact current coordinates kinds
            hcanonical hcoordinateCanonical hcoordinateNonzero
            hinnerCapacity)
      rcases hinnerPost with
        ⟨hnextValue, hnextCanonical, hnextZero⟩
      simp only at hnextValue hnextCanonical hnextZero
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
      rw [hfirstRun]
      simp only [bind_tc_ok]
      rw [hsecondRun]
      simp only [bind_tc_ok]
      rw [hfoldXRun]
      simp only [bind_tc_ok]
      rw [hthirdRun]
      simp only [bind_tc_ok]
      have hinnerRun' :
          V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop1_loop0_loop0
            current currentZero
            (Array.make 3#usize [first, second, third])
            (Array.make 3#usize [
              V5FriCoordinateAdapter.aspis_core.circle_fri.FoldDenominator.LineFirstPairX,
              V5FriCoordinateAdapter.aspis_core.circle_fri.FoldDenominator.LineSecondPairX,
              V5FriCoordinateAdapter.aspis_core.circle_fri.FoldDenominator.LineSecondFoldX])
            0#usize = .ok (next, nextZero) := by
        rw [hzero]
        simpa [coordinates, kinds] using hinnerRun
      rw [hinnerRun']
      simp only [bind_tc_ok, Std.lift, WP.spec_ok]
      rw [hnextZero]
      change LinePointInvariant initial points (next, none, ordinalOne) ∧
        points.val.length - ordinalOne.val <
          points.val.length - ordinal.val
      refine ⟨?_, by rw [hordinalOne]; omega⟩
      unfold LinePointInvariant
      simp only
      have hnextLength :
          next.val.length = initial.val.length + 3 * ordinalOne.val := by
        rw [hnextValue, List.length_append, hcoordinatesValue, hlength,
          hordinalOne]
        simp
        omega
      have hnextPrefix : ∀ index, index < initial.val.length →
          next.val[index]! = initial.val[index]! := by
        intro index hindex
        have hcurrentBound : index < current.val.length := by omega
        have hnextAt : next.val[index]! = current.val[index]! := by
          have hnextBang :=
            congrArg (fun values => values[index]!) hnextValue
          rw [hnextBang]
          exact getElemBang_append_left _ _ _ hcurrentBound
        rw [hnextAt]
        exact hprefix index hindex
      refine ⟨by rw [hordinalOne]; omega, hnextLength,
        hnextCanonical, True.intro, hnextPrefix, ?_⟩
      intro index hindex
      by_cases hold : index < ordinal.val
      · have holdValues := hvalues index hold
        have hslot0 : initial.val.length + 3 * index < current.val.length := by
          omega
        have hslot1 : initial.val.length + 3 * index + 1 < current.val.length := by
          omega
        have hslot2 : initial.val.length + 3 * index + 2 < current.val.length := by
          omega
        have hsame (slot : Nat) (hslot : slot < current.val.length) :
            next.val[slot]! = current.val[slot]! := by
          have hnextBang := congrArg (fun values => values[slot]!) hnextValue
          rw [hnextBang]
          exact getElemBang_append_left _ _ _ hslot
        rw [hsame _ hslot0, hsame _ hslot1, hsame _ hslot2]
        exact holdValues
      · have hnew : index = ordinal.val := by
          rw [hordinalOne] at hindex
          omega
        subst index
        have hslot : initial.val.length + 3 * ordinal.val =
            current.val.length := by omega
        have hfirstAt : next.val[current.val.length]! = first := by
          have hnextBang := congrArg
            (fun values => values[current.val.length]!) hnextValue
          rw [hnextBang, hcoordinatesValue]
          simp
        have hsecondAt : next.val[current.val.length + 1]! = second := by
          have hnextBang := congrArg
            (fun values => values[current.val.length + 1]!) hnextValue
          rw [hnextBang, hcoordinatesValue]
          simp
        have hthirdAt : next.val[current.val.length + 2]! = third := by
          have hnextBang := congrArg
            (fun values => values[current.val.length + 2]!) hnextValue
          rw [hnextBang, hcoordinatesValue]
          simp
        rw [hslot, hfirstAt, hsecondAt, hthirdAt,
          hfirstValue, hsecondValue, hthirdValue, hfoldXValue, hpointBang]
        exact ⟨rfl, rfl, rfl⟩
    · have hdone : ordinal.val = points.val.length := by omega
      have hcondition : ¬ ordinal < alloc.vec.Vec.len points := by
        simpa [UScalar.lt_equiv] using hactive
      simp only [if_neg hcondition, WP.spec_ok]
      rw [hdone] at hlength hvalues
      exact ⟨hlength, hcanonical, hzero, hprefix, hvalues⟩
  · unfold LinePointInvariant
    simp only
    refine ⟨by norm_num, ?_, hinitial, True.intro,
      (fun _ _ => True.intro), ?_⟩
    · norm_num
    · intro index hindex
      norm_num at hindex

def ThreeLineLayerPost
    (initial : Coordinate.M31Vec)
    (line1 line2 line3 : Coordinate.PointVec)
    (out : Coordinate.M31Vec × Option Coordinate.Kind) : Prop :=
  ∃ after1 after2 : Coordinate.M31Vec,
    LinePointPost initial line1 (after1, none) ∧
    LinePointPost after1 line2 (after2, none) ∧
    LinePointPost after2 line3 out

/-- The combined three-layer postcondition retains the initial prefix and
places every later denominator at its exact production offset. -/
theorem threeLineLayerPost_exact_values
    (initial lineValues : Coordinate.M31Vec)
    (line1 line2 line3 : Coordinate.PointVec)
    (hpost : ThreeLineLayerPost initial line1 line2 line3
      (lineValues, none)) :
    lineValues.val.length = initial.val.length +
        3 * line1.val.length + 3 * line2.val.length +
        3 * line3.val.length ∧
    (∀ index, index < initial.val.length →
      lineValues.val[index]! = initial.val[index]!) ∧
    (∀ index, index < line1.val.length →
      m31Value lineValues.val[initial.val.length + 3 * index]! =
          2 * m31Value line1.val[index]!.x ∧
      m31Value lineValues.val[initial.val.length + 3 * index + 1]! =
          2 * m31Value line1.val[index]!.y ∧
      m31Value lineValues.val[initial.val.length + 3 * index + 2]! =
          2 * (2 * m31Value line1.val[index]!.x ^ 2 - 1)) ∧
    (∀ index, index < line2.val.length →
      m31Value lineValues.val[
          initial.val.length + 3 * line1.val.length + 3 * index]! =
          2 * m31Value line2.val[index]!.x ∧
      m31Value lineValues.val[
          initial.val.length + 3 * line1.val.length + 3 * index + 1]! =
          2 * m31Value line2.val[index]!.y ∧
      m31Value lineValues.val[
          initial.val.length + 3 * line1.val.length + 3 * index + 2]! =
          2 * (2 * m31Value line2.val[index]!.x ^ 2 - 1)) ∧
    (∀ index, index < line3.val.length →
      m31Value lineValues.val[
          initial.val.length + 3 * line1.val.length +
            3 * line2.val.length + 3 * index]! =
          2 * m31Value line3.val[index]!.x ∧
      m31Value lineValues.val[
          initial.val.length + 3 * line1.val.length +
            3 * line2.val.length + 3 * index + 1]! =
          2 * m31Value line3.val[index]!.y ∧
      m31Value lineValues.val[
          initial.val.length + 3 * line1.val.length +
            3 * line2.val.length + 3 * index + 2]! =
          2 * (2 * m31Value line3.val[index]!.x ^ 2 - 1)) := by
  unfold ThreeLineLayerPost at hpost
  rcases hpost with ⟨after1, after2, hpost1, hpost2, hpost3⟩
  unfold LinePointPost at hpost1 hpost2 hpost3
  have hlen1 := hpost1.1
  have hprefix1 := hpost1.2.2.2.1
  have hvalues1 := hpost1.2.2.2.2
  have hlen2 := hpost2.1
  have hprefix2 := hpost2.2.2.2.1
  have hvalues2 := hpost2.2.2.2.2
  have hlen3 := hpost3.1
  have hprefix3 := hpost3.2.2.2.1
  have hvalues3 := hpost3.2.2.2.2
  simp only at hlen1 hprefix1 hvalues1 hlen2 hprefix2 hvalues2 hlen3 hprefix3 hvalues3
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · intro index hindex
    rw [hprefix3 index (by omega), hprefix2 index (by omega),
      hprefix1 index hindex]
  · intro index hindex
    have hslot0 : initial.val.length + 3 * index < after1.val.length := by
      omega
    have hslot1 : initial.val.length + 3 * index + 1 <
        after1.val.length := by omega
    have hslot2 : initial.val.length + 3 * index + 2 <
        after1.val.length := by omega
    have hvalues := hvalues1 index hindex
    rw [hprefix3 _ (by omega), hprefix2 _ hslot0,
      hprefix3 _ (by omega), hprefix2 _ hslot1,
      hprefix3 _ (by omega), hprefix2 _ hslot2]
    exact hvalues
  · intro index hindex
    have hslot0 : after1.val.length + 3 * index < after2.val.length := by
      omega
    have hslot1 : after1.val.length + 3 * index + 1 <
        after2.val.length := by omega
    have hslot2 : after1.val.length + 3 * index + 2 <
        after2.val.length := by omega
    have hvalues := hvalues2 index hindex
    rw [show initial.val.length + 3 * line1.val.length =
        after1.val.length by omega,
      hprefix3 _ hslot0, hprefix3 _ hslot1, hprefix3 _ hslot2]
    exact hvalues
  · intro index hindex
    have hvalues := hvalues3 index hindex
    rw [show initial.val.length + 3 * line1.val.length +
        3 * line2.val.length = after2.val.length by omega]
    exact hvalues

/-- The fixed three-layer translated loop runs the later FRI layers in the
source order: first layer, second layer, then third layer. -/
theorem three_line_layer_denominator_loop_exact
    (initial : Coordinate.M31Vec)
    (line1 line2 line3 : Coordinate.PointVec)
    (hinitial : CanonicalM31Vec initial)
    (hline1 : CanonicalPoints line1)
    (hline2 : CanonicalPoints line2)
    (hline3 : CanonicalPoints line3)
    (hcapacity : initial.val.length +
        3 * (line1.val.length + line2.val.length + line3.val.length) ≤
      Std.Usize.max)
    (hnonzero1 : ∀ index, index < line1.val.length →
      2 * m31Value line1.val[index]!.x ≠ 0 ∧
      2 * m31Value line1.val[index]!.y ≠ 0 ∧
      2 * (2 * m31Value line1.val[index]!.x ^ 2 - 1) ≠ 0)
    (hnonzero2 : ∀ index, index < line2.val.length →
      2 * m31Value line2.val[index]!.x ≠ 0 ∧
      2 * m31Value line2.val[index]!.y ≠ 0 ∧
      2 * (2 * m31Value line2.val[index]!.x ^ 2 - 1) ≠ 0)
    (hnonzero3 : ∀ index, index < line3.val.length →
      2 * m31Value line3.val[index]!.x ≠ 0 ∧
      2 * m31Value line3.val[index]!.y ≠ 0 ∧
      2 * (2 * m31Value line3.val[index]!.x ^ 2 - 1) ≠ 0) :
    V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop1
        line1 line2 line3 initial none 0#usize
      ⦃ out => ThreeLineLayerPost initial line1 line2 line3 out ⦄ := by
  have hcap1 : initial.val.length + 3 * line1.val.length ≤
      Std.Usize.max := by omega
  obtain ⟨⟨after1, zero1⟩, hrun1, hpost1⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (line_point_denominator_loop_exact initial line1 hinitial hline1
        hcap1 hnonzero1)
  rcases hpost1 with
    ⟨hlen1, hcanonical1, hzero1, hprefix1, hvalues1⟩
  simp only at hlen1 hcanonical1 hzero1 hprefix1 hvalues1
  have hcap2 : after1.val.length + 3 * line2.val.length ≤
      Std.Usize.max := by rw [hlen1]; omega
  obtain ⟨⟨after2, zero2⟩, hrun2, hpost2⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (line_point_denominator_loop_exact after1 line2 hcanonical1 hline2
        hcap2 hnonzero2)
  rcases hpost2 with
    ⟨hlen2, hcanonical2, hzero2, hprefix2, hvalues2⟩
  simp only at hlen2 hcanonical2 hzero2 hprefix2 hvalues2
  have hcap3 : after2.val.length + 3 * line3.val.length ≤
      Std.Usize.max := by rw [hlen2, hlen1]; omega
  obtain ⟨⟨after3, zero3⟩, hrun3, hpost3⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (line_point_denominator_loop_exact after2 line3 hcanonical2 hline3
        hcap3 hnonzero3)
  rcases hpost3 with
    ⟨hlen3, hcanonical3, hzero3, hprefix3, hvalues3⟩
  simp only at hlen3 hcanonical3 hzero3 hprefix3 hvalues3
  have hrun1' := hrun1
  have hrun2' := hrun2
  have hrun3' := hrun3
  rw [hzero1] at hrun1'
  rw [hzero2] at hrun2'
  rw [hzero3] at hrun3'
  have hmax3 : 3 < Std.Usize.max := by
    rcases Usize.cMax_bound_concrete with ⟨hmax, _⟩
    omega
  have hwrap0 : Std.Usize.wrapping_add 0#usize 1#usize = 1#usize := by
    apply UScalar.eq_of_val_eq
    change (Std.Usize.wrapping_add 0#usize 1#usize).val = 1
    exact wrapping_add_one_exact 0#usize (by
      change 0 < Std.Usize.max
      omega)
  have hwrap1 : Std.Usize.wrapping_add 1#usize 1#usize = 2#usize := by
    apply UScalar.eq_of_val_eq
    change (Std.Usize.wrapping_add 1#usize 1#usize).val = 2
    exact wrapping_add_one_exact 1#usize (by
      change 1 < Std.Usize.max
      omega)
  have hwrap2 : Std.Usize.wrapping_add 2#usize 1#usize = 3#usize := by
    apply UScalar.eq_of_val_eq
    change (Std.Usize.wrapping_add 2#usize 1#usize).val = 3
    exact wrapping_add_one_exact 2#usize (by
      change 2 < Std.Usize.max
      omega)
  unfold
    V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop1
  rw [loop.eq_def]
  unfold
    V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop1.body
  norm_num [UScalar.lt_equiv]
  rw [hrun1']
  simp only [bind_tc_ok, Std.lift, hwrap0]
  rw [loop.eq_def]
  norm_num [UScalar.lt_equiv]
  rw [hrun2']
  simp only [bind_tc_ok, Std.lift, hwrap1]
  rw [loop.eq_def]
  norm_num [UScalar.lt_equiv]
  rw [hrun3']
  simp only [bind_tc_ok, Std.lift, hwrap2]
  rw [loop.eq_def]
  norm_num [UScalar.lt_equiv, WP.spec_ok]
  unfold ThreeLineLayerPost
  exact ⟨after1, after2,
    ⟨hlen1, hcanonical1, rfl, hprefix1, hvalues1⟩,
    ⟨hlen2, hcanonical2, rfl, hprefix2, hvalues2⟩,
    hlen3, hcanonical3, rfl, hprefix3, hvalues3⟩

#print axioms extend_pair_exact
#print axioms circle_denominator_loop_exact
#print axioms coordinate_denominator_loop_exact
#print axioms line_point_denominator_loop_exact
#print axioms three_line_layer_denominator_loop_exact

end AspisV5FriCoordinateDenominatorLoops
