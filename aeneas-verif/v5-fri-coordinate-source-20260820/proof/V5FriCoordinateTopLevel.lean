import Coordinates.Funs
import V5FriCoordinateDenominatorLoops
import V5FriCoordinateInverseLoops
import V5FriCoordinateOutputLoops
import V5FriCoordinatePointLoops

set_option autoImplicit false
set_option maxHeartbeats 20000000
set_option maxRecDepth 24000

/-!
# The accepted path of the extracted V5 FRI coordinate function

This file joins the already proved denominator, batch-inversion, and output
loops at the actual extracted Rust entry point.  Point selection is supplied
through the exact results of the two extracted point helpers; the separate
point-loop proof discharges those results for the released query schedule.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5FriCoordinateTopLevel

open AspisCircleGroupOrder
open AspisV5FriCoordinateFieldSemantics
open AspisV5FriCoordinateDenominatorLoops
open AspisV5FriCoordinateInverseLoops
open AspisV5FriCoordinateOutputLoops
open AspisV5FriCoordinatePointLoops

namespace Coordinate
open V5FriCoordinateAdapter

abbrev M31 := aspis_core.field.M31
abbrev M31Vec := alloc.vec.Vec M31
abbrev Point := aspis_core.circle_fri.BaseCirclePoint
abbrev PointVec := alloc.vec.Vec Point
abbrev Output := aspis_core.circle_fri.DerivedCircleQueryFoldInverses

end Coordinate

instance : Inhabited Coordinate.M31 := ⟨0#u32⟩
instance : Inhabited Coordinate.Point :=
  ⟨{ x := 0#u32, y := 0#u32 }⟩

private theorem getElemBang_eq_getElem {T : Type*} [Inhabited T]
    (values : List T) (index : Nat) (hindex : index < values.length) :
    values[index]! = values[index] := by
  apply List.getElem!_of_getElem?
  simp [hindex]

theorem canonicalVec_of_members
    (values : Coordinate.M31Vec)
    (hvalues : AspisV5FriCoordinateDenominatorLoops.CanonicalM31Vec values) :
    AspisV5FriCoordinateInverseLoops.CanonicalVec values := by
  intro index hindex
  apply hvalues
  rw [getElemBang_eq_getElem values.val index hindex]
  exact List.getElem_mem hindex

/-- The exact circle-loop postcondition also records that every produced
denominator is nonzero. -/
theorem circlePost_nonzero
    (points : Coordinate.PointVec) (values : Coordinate.M31Vec)
    (hpost : CirclePost points (values, none))
    (hnonzero : ∀ index, index < points.val.length →
      2 * m31Value points.val[index]!.x ≠ 0 ∧
      2 * m31Value points.val[index]!.y ≠ 0) :
    NonzeroVec values := by
  rcases hpost with ⟨hlength, _hcanonical, _hkind, hvalues⟩
  intro index hindex
  rw [hlength] at hindex
  have hhalf : index / 2 < points.val.length := by
    omega
  have hrem : index % 2 < 2 := Nat.mod_lt _ (by omega)
  have hpoint := hnonzero (index / 2) hhalf
  have hsource := hvalues (index / 2) hhalf
  interval_cases hcase : index % 2
  · have hslot : index = 2 * (index / 2) := by omega
    rw [hslot, hsource.1]
    exact hpoint.1
  · have hslot : index = 2 * (index / 2) + 1 := by omega
    rw [hslot, hsource.2]
    exact hpoint.2

/-- Appending one later-layer point list preserves nonzero earlier entries
and adds exactly three nonzero entries per point. -/
theorem linePointPost_nonzero
    (initial pointsValues : Coordinate.M31Vec)
    (points : Coordinate.PointVec)
    (hpost : LinePointPost initial points (pointsValues, none))
    (hinitial : NonzeroVec initial)
    (hnonzero : ∀ index, index < points.val.length →
      2 * m31Value points.val[index]!.x ≠ 0 ∧
      2 * m31Value points.val[index]!.y ≠ 0 ∧
      2 * (2 * m31Value points.val[index]!.x ^ 2 - 1) ≠ 0) :
    NonzeroVec pointsValues := by
  rcases hpost with
    ⟨hlength, _hcanonical, _hkind, hprefix, hvalues⟩
  intro index hindex
  rw [hlength] at hindex
  by_cases hbefore : index < initial.val.length
  · rw [hprefix index hbefore]
    exact hinitial index hbefore
  · let relative := index - initial.val.length
    have hpointIndex : relative / 3 < points.val.length := by
      dsimp [relative]
      omega
    have hrem : relative % 3 < 3 := Nat.mod_lt _ (by omega)
    have hpoint := hnonzero (relative / 3) hpointIndex
    have hsource := hvalues (relative / 3) hpointIndex
    interval_cases hcase : relative % 3
    · have hslot : index = initial.val.length + 3 * (relative / 3) := by
        dsimp [relative] at hcase ⊢
        omega
      rw [hslot, hsource.1]
      exact hpoint.1
    · have hslot : index = initial.val.length + 3 * (relative / 3) + 1 := by
        dsimp [relative] at hcase ⊢
        omega
      rw [hslot, hsource.2.1]
      exact hpoint.2.1
    · have hslot : index = initial.val.length + 3 * (relative / 3) + 2 := by
        dsimp [relative] at hcase ⊢
        omega
      rw [hslot, hsource.2.2]
      exact hpoint.2.2

/-- The fixed three later-layer calls preserve nonzeroness from the initial
circle denominators through the complete flat array. -/
theorem threeLinePost_nonzero
    (line1 line2 line3 : Coordinate.PointVec)
    (initialValues finalValues : Coordinate.M31Vec)
    (hpost : ThreeLineLayerPost initialValues line1 line2 line3
      (finalValues, none))
    (hinitial : NonzeroVec initialValues)
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
    NonzeroVec finalValues := by
  rcases hpost with ⟨after1, after2, hpost1, hpost2, hpost3⟩
  have hnonzeroAfter1 := linePointPost_nonzero initialValues after1 line1
    hpost1 hinitial hnonzero1
  have hnonzeroAfter2 := linePointPost_nonzero after1 after2 line2
    hpost2 hnonzeroAfter1 hnonzero2
  exact linePointPost_nonzero after2 finalValues line3 hpost3
    hnonzeroAfter2 hnonzero3

private theorem vec_is_empty_false
    (values : Coordinate.M31Vec) (hnonempty : 0 < values.val.length) :
    alloc.vec.Vec.is_empty Global values = .ok false := by
  unfold alloc.vec.Vec.is_empty
  simp only
  have hne : values.val ≠ [] := by
    intro hempty
    rw [hempty] at hnonempty
    simp at hnonempty
  simp [hne]

private theorem slice_first_nonempty
    (values : Coordinate.M31Vec) (hnonempty : 0 < values.val.length) :
    core.slice.Slice.first (alloc.vec.Vec.deref values) =
      .ok (some values.val[0]!) := by
  cases hvalues : values.val with
  | nil => simp [hvalues] at hnonempty
  | cons head tail =>
      simp [core.slice.Slice.first, alloc.vec.Vec.deref, hvalues]

/-! ## Point-helper results needed by the top-level function -/

/-- Pointwise mathematical meaning immediately gives the canonical raw-field
condition needed by the denominator loops. -/
theorem canonicalPoints_of_represents
    (points : Coordinate.PointVec) (expected : Nat → C)
    (hpoints : ∀ index, index < points.val.length →
      Represents points.val[index]! (expected index)) :
    CanonicalPoints points := by
  intro index hindex
  exact (hpoints index hindex).1

/-- The selected-point proof supplies both the exact output length and all
canonicality obligations used later by the extracted top-level proof. -/
theorem selectedPointsPost_length_and_canonical
    (fibers : Slice Std.U32) (points : Coordinate.PointVec)
    (hpost : SelectedPointsPost fibers points) :
    points.val.length = fibers.val.length ∧ CanonicalPoints points := by
  refine ⟨hpost.1, ?_⟩
  apply canonicalPoints_of_represents points
    (fun ordinal => selectedExpectedPoint fibers.val[ordinal]!)
  intro ordinal hordinal
  apply hpost.2 ordinal
  simpa [hpost.1] using hordinal

/-- A deterministic mathematical description of one parent list.  It says
that any authenticated child which maps to a requested parent produces the
same expected parent point.  This is the small, reusable condition discharged
by the released circle/line-domain identities. -/
def ParentExpectedCompatible
    (childIndices parentIndices : Slice Std.U32)
    (childExpected parentExpected : Nat → C)
    (doublings : Std.U8) : Prop :=
  ∀ (childOrdinal parentOrdinal : Nat),
    childOrdinal < childIndices.val.length →
    parentOrdinal < parentIndices.val.length →
    childIndices.val[childOrdinal]!.val / 4 =
        parentIndices.val[parentOrdinal]!.val →
    parentTransform doublings (childExpected childOrdinal)
        childIndices.val[childOrdinal]! = parentExpected parentOrdinal

/-- A successful translated parent helper has the requested deterministic
meaning whenever the released index relation satisfies
`ParentExpectedCompatible`. -/
theorem parent_success_exact_expected
    (childIndices : Slice Std.U32) (childPoints : Slice Coordinate.Point)
    (parentIndices : Slice Std.U32) (doublings : Std.U8)
    (childExpected parentExpected : Nat → C)
    (output : Coordinate.PointVec)
    (hchildren : ∀ ordinal, ordinal < childPoints.val.length →
      Represents childPoints.val[ordinal]! (childExpected ordinal))
    (hcompatible : ParentExpectedCompatible childIndices parentIndices
      childExpected parentExpected doublings)
    (hrun :
      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_parent_line_points
          childIndices childPoints parentIndices doublings =
        .ok (output, true)) :
    output.val.length = parentIndices.val.length ∧
      ∀ ordinal, ordinal < output.val.length →
        Represents output.val[ordinal]! (parentExpected ordinal) := by
  have hpost := derive_parent_line_points_success childIndices childPoints
    parentIndices doublings childExpected output hchildren hrun
  refine ⟨hpost.1, ?_⟩
  intro ordinal hordinal
  have hparent : ordinal < parentIndices.val.length := by
    simpa [hpost.1] using hordinal
  rcases hpost.2 ordinal hparent with
    ⟨childOrdinal, hchild, hmapped, hrepresents⟩
  have heq := hcompatible childOrdinal ordinal hchild hparent hmapped
  rw [heq] at hrepresents
  exact hrepresents

/-- Mathematical nonzero coordinate facts transfer directly to the raw
points returned by the translated helper. -/
theorem circle_nonzero_of_represents
    (points : Coordinate.PointVec) (expected : Nat → C)
    (hpoints : ∀ index, index < points.val.length →
      Represents points.val[index]! (expected index))
    (hnonzero : ∀ index, index < points.val.length →
      2 * (expected index).1.1 ≠ 0 ∧
      2 * (expected index).1.2 ≠ 0) :
    ∀ index, index < points.val.length →
      2 * m31Value points.val[index]!.x ≠ 0 ∧
      2 * m31Value points.val[index]!.y ≠ 0 := by
  intro index hindex
  have hmeaning := (hpoints index hindex).2
  have hexpected := hnonzero index hindex
  change
    2 * AspisV5FriCoordinateFieldSemantics.m31Value
          points.val[index]!.x ≠ 0 ∧
      2 * AspisV5FriCoordinateFieldSemantics.m31Value
          points.val[index]!.y ≠ 0
  rw [show AspisV5FriCoordinateFieldSemantics.m31Value
          points.val[index]!.x = (expected index).1.1 by
        exact congrArg Prod.fst hmeaning,
      show AspisV5FriCoordinateFieldSemantics.m31Value
          points.val[index]!.y = (expected index).1.2 by
        exact congrArg Prod.snd hmeaning]
  exact hexpected

theorem line_nonzero_of_represents
    (points : Coordinate.PointVec) (expected : Nat → C)
    (hpoints : ∀ index, index < points.val.length →
      Represents points.val[index]! (expected index))
    (hnonzero : ∀ index, index < points.val.length →
      2 * (expected index).1.1 ≠ 0 ∧
      2 * (expected index).1.2 ≠ 0 ∧
      2 * (2 * (expected index).1.1 ^ 2 - 1) ≠ 0) :
    ∀ index, index < points.val.length →
      2 * m31Value points.val[index]!.x ≠ 0 ∧
      2 * m31Value points.val[index]!.y ≠ 0 ∧
      2 * (2 * m31Value points.val[index]!.x ^ 2 - 1) ≠ 0 := by
  intro index hindex
  have hmeaning := (hpoints index hindex).2
  have hexpected := hnonzero index hindex
  change
    2 * AspisV5FriCoordinateFieldSemantics.m31Value
          points.val[index]!.x ≠ 0 ∧
      2 * AspisV5FriCoordinateFieldSemantics.m31Value
          points.val[index]!.y ≠ 0 ∧
      2 * (2 * AspisV5FriCoordinateFieldSemantics.m31Value
          points.val[index]!.x ^ 2 - 1) ≠ 0
  rw [show AspisV5FriCoordinateFieldSemantics.m31Value
          points.val[index]!.x = (expected index).1.1 by
        exact congrArg Prod.fst hmeaning,
      show AspisV5FriCoordinateFieldSemantics.m31Value
          points.val[index]!.y = (expected index).1.2 by
        exact congrArg Prod.snd hmeaning]
  exact hexpected

/-- Once the extracted point helpers have returned the stated valid point
lists, the complete accepted branch of the extracted Rust coordinate function
runs successfully.  The result contains the exact inverse of every denominator
and the exact source output layout. -/
theorem extracted_accepted_path_exact
    (layer0 line1 line2 line3 : Slice Std.U32)
    (circlePoints line1Points line2Points line3Points : Coordinate.PointVec)
    (hcircleCall :
      V5FriCoordinateAdapter.aspis_core.circle_fri.selected_circle_fiber_points_shared
          19#u32 layer0 = .ok (circlePoints, true))
    (hline1Call :
      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_parent_line_points
          layer0 (alloc.vec.Vec.deref circlePoints) line1 1#u8 =
        .ok (line1Points, true))
    (hline2Call :
      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_parent_line_points
          line1 (alloc.vec.Vec.deref line1Points) line2 2#u8 =
        .ok (line2Points, true))
    (hline3Call :
      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_parent_line_points
          line2 (alloc.vec.Vec.deref line2Points) line3 2#u8 =
        .ok (line3Points, true))
    (hcircleLength : circlePoints.val.length = layer0.val.length)
    (hline1Length : line1Points.val.length = line1.val.length)
    (hline2Length : line2Points.val.length = line2.val.length)
    (hline3Length : line3Points.val.length = line3.val.length)
    (hcircleCanonical : CanonicalPoints circlePoints)
    (hline1Canonical : CanonicalPoints line1Points)
    (hline2Canonical : CanonicalPoints line2Points)
    (hline3Canonical : CanonicalPoints line3Points)
    (hcircleNonempty : 0 < circlePoints.val.length)
    (hcapacity : 2 * circlePoints.val.length +
        3 * (line1Points.val.length + line2Points.val.length +
          line3Points.val.length) ≤ Std.Usize.max)
    (hcircleNonzero : ∀ index, index < circlePoints.val.length →
      2 * m31Value circlePoints.val[index]!.x ≠ 0 ∧
      2 * m31Value circlePoints.val[index]!.y ≠ 0)
    (hline1Nonzero : ∀ index, index < line1Points.val.length →
      2 * m31Value line1Points.val[index]!.x ≠ 0 ∧
      2 * m31Value line1Points.val[index]!.y ≠ 0 ∧
      2 * (2 * m31Value line1Points.val[index]!.x ^ 2 - 1) ≠ 0)
    (hline2Nonzero : ∀ index, index < line2Points.val.length →
      2 * m31Value line2Points.val[index]!.x ≠ 0 ∧
      2 * m31Value line2Points.val[index]!.y ≠ 0 ∧
      2 * (2 * m31Value line2Points.val[index]!.x ^ 2 - 1) ≠ 0)
    (hline3Nonzero : ∀ index, index < line3Points.val.length →
      2 * m31Value line3Points.val[index]!.x ≠ 0 ∧
      2 * m31Value line3Points.val[index]!.y ≠ 0 ∧
      2 * (2 * m31Value line3Points.val[index]!.x ^ 2 - 1) ≠ 0) :
    ∃ circleDenominators denominators flat output,
      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle
          19#u32 layer0 line1 line2 line3 =
        .ok (.Ok output) ∧
      CirclePost circlePoints (circleDenominators, none) ∧
      ThreeLineLayerPost circleDenominators line1Points line2Points line3Points
        (denominators, none) ∧
      BatchInverseEvidence denominators flat ∧
      AcceptedOutputEvidence layer0 line1 line2 line3 flat line3Points
        output := by
  let emptyDenominators : Coordinate.M31Vec :=
    alloc.vec.Vec.new Coordinate.M31
  have hemptyDenominators : emptyDenominators.val = [] := rfl
  have hcircleCapacity : 2 * circlePoints.val.length ≤ Std.Usize.max := by
    omega
  obtain ⟨⟨circleDenominators, circleZero⟩, hcircleRun,
      hcirclePost⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (circle_denominator_loop_exact circlePoints emptyDenominators
        hcircleCanonical hemptyDenominators hcircleCapacity hcircleNonzero)
  have hcirclePostSaved := hcirclePost
  rcases hcirclePost with
    ⟨hcircleDenominatorLength, hcircleDenominatorCanonical,
      hcircleZero, hcircleValues⟩
  simp only at hcircleDenominatorLength hcircleDenominatorCanonical
  simp only at hcircleZero hcircleValues
  rw [hcircleZero] at hcircleRun hcirclePostSaved
  have hlaterCapacity : circleDenominators.val.length +
      3 * (line1Points.val.length + line2Points.val.length +
        line3Points.val.length) ≤ Std.Usize.max := by
    rw [hcircleDenominatorLength]
    exact hcapacity
  obtain ⟨⟨denominators, finalZero⟩, hlaterRun, hlaterPost⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (three_line_layer_denominator_loop_exact circleDenominators
        line1Points line2Points line3Points hcircleDenominatorCanonical
        hline1Canonical hline2Canonical hline3Canonical hlaterCapacity
        hline1Nonzero hline2Nonzero hline3Nonzero)
  have hlaterPostSaved := hlaterPost
  rcases hlaterPost with ⟨after1, after2, hafter1, hafter2, hafter3⟩
  have hfinalZero := hafter3.2.2.1
  change finalZero = none at hfinalZero
  rw [hfinalZero] at hlaterRun hlaterPostSaved
  have hdenominatorLength : denominators.val.length =
      2 * layer0.val.length + 3 * line1.val.length +
        3 * line2.val.length + 3 * line3.val.length := by
    rw [hafter3.1, hafter2.1, hafter1.1,
      hcircleDenominatorLength, hcircleLength, hline1Length,
      hline2Length, hline3Length]
  have hdenominatorCanonical :
      AspisV5FriCoordinateInverseLoops.CanonicalVec denominators :=
    canonicalVec_of_members denominators hafter3.2.1
  have hcircleNonzeroVec : NonzeroVec circleDenominators :=
    circlePost_nonzero circlePoints circleDenominators
      hcirclePostSaved hcircleNonzero
  have hdenominatorNonzero : NonzeroVec denominators :=
    threeLinePost_nonzero line1Points line2Points line3Points
      circleDenominators denominators hlaterPostSaved hcircleNonzeroVec
      hline1Nonzero hline2Nonzero hline3Nonzero
  have hdenominatorNonempty : 0 < denominators.val.length := by
    rw [hdenominatorLength, ← hcircleLength]
    omega
  obtain ⟨initialFlat, hinitialFlatRun, hinitialFlatValue,
      hinitialFlatLength⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (alloc.vec.from_elem_spec
        V5FriCoordinateAdapter.aspis_core.field.M31.Insts.CoreCloneClone
        V5FriCoordinateAdapter.aspis_core.field.M31.ZERO
        (alloc.vec.Vec.len denominators) (by rfl))
  have hzeroCanonical :
      canonicalM31 V5FriCoordinateAdapter.aspis_core.field.M31.ZERO := by
    norm_num [canonicalM31,
      AspisV5FriArithmeticSemantics.canonicalM31,
      AspisAeneasCM31Multiplicative.CanonicalRawM31,
      V5FriCoordinateAdapter.aspis_core.field.M31.ZERO]
  have hinitialFlatCanonical :
      AspisV5FriCoordinateInverseLoops.CanonicalVec initialFlat := by
    intro index hindex
    rw [hinitialFlatValue] at hindex ⊢
    rw [getElemBang_eq_getElem _ _ hindex]
    simpa using hzeroCanonical
  obtain ⟨forward, accumulator, accumulatorInverse, flat,
      hforwardRun, hinverseRun, hbackwardRun, hcheckRun, hbatchEvidence⟩ :=
    batch_inverse_pipeline_exact denominators initialFlat
      hdenominatorCanonical hdenominatorNonzero hdenominatorNonempty
      (by simpa using hinitialFlatLength) hinitialFlatCanonical
  obtain ⟨cursor0, circleOutput, cursor1, later0, cursor2, later1Output,
      later2, finalX, hcircleOutputRun, hlater0Run, hlater1Run,
      hlater2Run, hfinalXRun, houtputEvidence⟩ :=
    accepted_output_calls_exact layer0 line1 line2 line3 flat line3Points
      (by
        calc
          flat.val.length = denominators.val.length := hbatchEvidence.1
          _ = 2 * layer0.val.length + 3 * line1.val.length +
              3 * line2.val.length + 3 * line3.val.length :=
            hdenominatorLength)
      (fun index hindex => (hline3Canonical index hindex).1)
  let output : Coordinate.Output :=
    { circle := circleOutput,
      later := Array.make 3#usize [later0, later1Output, later2],
      final_x := finalX }
  have hnotEmpty := vec_is_empty_false denominators hdenominatorNonempty
  have hfirstDenominator :=
    slice_first_nonempty denominators hdenominatorNonempty
  have hfirstFlat : core.slice.Slice.first (alloc.vec.Vec.deref flat) =
      .ok (some flat.val[0]!) := by
    apply slice_first_nonempty
    rw [hbatchEvidence.1]
    exact hdenominatorNonempty
  have hcircleRunSource :
      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop0
          circlePoints (alloc.vec.Vec.new Coordinate.M31) none 0#usize =
        .ok (circleDenominators, none) := by
    simpa [emptyDenominators] using hcircleRun
  have hnotEqualRun :
      core.cmp.PartialEq.ne.trait_default
          V5FriCoordinateAdapter.aspis_core.field.M31.Insts.CoreCmpPartialEqM31
          V5FriCoordinateAdapter.aspis_core.field.M31.ONE
          V5FriCoordinateAdapter.aspis_core.field.M31.ONE = .ok false := by
    simp [core.cmp.PartialEq.ne.trait_default,
      core.cmp.PartialEq.ne.default,
      V5FriCoordinateAdapter.aspis_core.field.M31.Insts.CoreCmpPartialEqM31,
      V5FriCoordinateAdapter.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq]
  have hcircleOrderMinusOne :
      Std.U32.wrapping_sub 31#u32 1#u32 = 30#u32 := by
    decide
  have hcircleOutputRunSource :
      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop29
          layer0 flat 0#usize
          (alloc.vec.Vec.new (Array Coordinate.M31 2#usize)) 0#usize =
        .ok (cursor0, circleOutput) := by
    simpa only [alloc.vec.Vec.with_capacity] using hcircleOutputRun
  have hlater0RunSource :
      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop30
          line1 flat cursor0
          (alloc.vec.Vec.new (Array Coordinate.M31 3#usize)) 0#usize =
        .ok (cursor1, later0) := by
    simpa only [alloc.vec.Vec.with_capacity] using hlater0Run
  have hlater1RunSource :
      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop31
          line2 flat cursor1
          (alloc.vec.Vec.new (Array Coordinate.M31 3#usize)) 0#usize =
        .ok (cursor2, later1Output) := by
    simpa only [alloc.vec.Vec.with_capacity] using hlater1Run
  have hlater2RunSource :
      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop32
          line3 flat cursor2
          (alloc.vec.Vec.new (Array Coordinate.M31 3#usize)) 0#usize =
        .ok later2 := by
    simpa only [alloc.vec.Vec.with_capacity] using hlater2Run
  have hfinalXRunSource :
      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop33
          line3Points (alloc.vec.Vec.new Coordinate.M31) 0#usize =
        .ok finalX := by
    simpa only [alloc.vec.Vec.with_capacity] using hfinalXRun
  have hmain :
      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle
          19#u32 layer0 line1 line2 line3 = .ok (.Ok output) := by
    unfold
      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle
    norm_num [aspis_core.params.CIRCLE_LOG_ORDER,
      Std.lift, UScalar.lt_equiv, hcircleOrderMinusOne,
      UScalar.size, U32.size, U32.numBits]
    rw [hcircleCall]
    simp only [bind_tc_ok, if_true]
    rw [hline1Call]
    simp only [bind_tc_ok, if_true]
    rw [hline2Call]
    simp only [bind_tc_ok, if_true]
    rw [hline3Call]
    simp only [bind_tc_ok, if_true]
    simp only [alloc.vec.Vec.with_capacity]
    rw [hcircleRunSource]
    simp only [bind_tc_ok]
    rw [hlaterRun]
    simp only [bind_tc_ok]
    rw [hinitialFlatRun]
    simp only [bind_tc_ok]
    rw [hnotEmpty]
    simp only [bind_tc_ok, Bool.false_eq_true, if_false]
    rw [hforwardRun]
    simp only [bind_tc_ok]
    rw [hinverseRun]
    simp only [bind_tc_ok]
    rw [hbackwardRun]
    simp only [bind_tc_ok]
    rw [hfirstDenominator]
    simp only [bind_tc_ok]
    rw [hfirstFlat]
    simp only [bind_tc_ok]
    rw [hcheckRun]
    simp only [bind_tc_ok]
    rw [hnotEqualRun]
    simp only [bind_tc_ok, Bool.false_eq_true, if_false]
    rw [hcircleOutputRunSource]
    simp only [bind_tc_ok]
    rw [hlater0RunSource]
    simp only [bind_tc_ok]
    rw [hlater1RunSource]
    simp only [bind_tc_ok]
    rw [hlater2RunSource]
    simp only [bind_tc_ok]
    rw [hfinalXRunSource]
    simp [output]
  refine ⟨circleDenominators, denominators, flat, output, ?_,
    hcirclePostSaved, hlaterPostSaved, hbatchEvidence, ?_⟩
  · exact hmain
  · exact houtputEvidence

#print axioms circlePost_nonzero
#print axioms linePointPost_nonzero
#print axioms threeLinePost_nonzero
#print axioms extracted_accepted_path_exact

end AspisV5FriCoordinateTopLevel
