import V5CoordinateProductionAcceptedProof

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 24000

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V5CoordinateProductionReleasedProof

open V5CoordinateProductionTailProof
open V5CoordinateProductionAcceptedProof
open V5CoordinateProductionFullProof
open V5CoordinateSelectedProductionProof
open AspisV5FriCoordinateReleasedPointConnection
open AspisV5FriCoordinateFieldSemantics
open AspisCircleGroupOrder

namespace Source
open V5CoordinateSelectedProductionSource

abbrev Point := circle_fri.BaseCirclePoint
abbrev PointVec := alloc.vec.Vec Point
abbrev M31 := field.M31
abbrev M31Vec := alloc.vec.Vec M31
abbrev Output := circle_fri.DerivedCircleQueryFoldInverses
end Source

namespace Adapter
open V5FriCoordinateAdapter

abbrev Point := aspis_core.circle_fri.BaseCirclePoint
abbrev PointVec := alloc.vec.Vec Point
abbrev M31 := aspis_core.field.M31
abbrev M31Vec := alloc.vec.Vec M31
abbrev Output := aspis_core.circle_fri.DerivedCircleQueryFoldInverses
end Adapter

instance : Inhabited Source.Point := ⟨{ x := 0#u32, y := 0#u32 }⟩

private theorem getElemBang_eq_getElem {T : Type*} [Inhabited T]
    (values : List T) (index : Nat) (hindex : index < values.length) :
    values[index]! = values[index] := by
  apply List.getElem!_of_getElem?
  simp [hindex]

def toAdapterOutput (output : Source.Output) : Adapter.Output where
  circle := output.circle
  later := output.later
  final_x := output.final_x

@[simp] theorem toAdapterPointVec_length (points : Source.PointVec) :
    (toAdapterPointVec points).val.length = points.val.length := by
  simp [toAdapterPointVec]

theorem toAdapterPointVec_getBang (points : Source.PointVec)
    (index : Nat) (hindex : index < points.val.length) :
    (toAdapterPointVec points).val[index]! =
      toAdapterPoint points.val[index]! := by
  have hmapped : index < (points.val.map toAdapterPoint).length := by
    simpa using hindex
  change (points.val.map toAdapterPoint)[index]! =
    toAdapterPoint points.val[index]!
  rw [getElemBang_eq_getElem _ _ hmapped,
    getElemBang_eq_getElem _ _ hindex]
  simp

theorem sourceReleasedPoints_to_adapter
    (layer0 line1 line2 line3 : Slice Std.U32)
    (circlePoints line1Points line2Points line3Points : Source.PointVec)
    (hpoints : SourceReleasedPointListsEvidence layer0 line1 line2 line3
      circlePoints line1Points line2Points line3Points) :
    ReleasedPointListsEvidence layer0 line1 line2 line3
      (toAdapterPointVec circlePoints) (toAdapterPointVec line1Points)
      (toAdapterPointVec line2Points) (toAdapterPointVec line3Points) := by
  refine {
    circleLength := by simpa using hpoints.circleLength
    line1Length := by simpa using hpoints.line1Length
    line2Length := by simpa using hpoints.line2Length
    line3Length := by simpa using hpoints.line3Length
    circle := ?_
    line1 := ?_
    line2 := ?_
    line3 := ?_ }
  · intro index hindex
    have hsourceIndex : index < circlePoints.val.length := by simpa using hindex
    rw [toAdapterPointVec_getBang circlePoints index hsourceIndex]
    exact hpoints.circle index hsourceIndex
  · intro index hindex
    have hsourceIndex : index < line1Points.val.length := by simpa using hindex
    rw [toAdapterPointVec_getBang line1Points index hsourceIndex]
    exact hpoints.line1 index hsourceIndex
  · intro index hindex
    have hsourceIndex : index < line2Points.val.length := by simpa using hindex
    rw [toAdapterPointVec_getBang line2Points index hsourceIndex]
    exact hpoints.line2 index hsourceIndex
  · intro index hindex
    have hsourceIndex : index < line3Points.val.length := by simpa using hindex
    rw [toAdapterPointVec_getBang line3Points index hsourceIndex]
    exact hpoints.line3 index hsourceIndex

theorem sourceCirclePost_to_adapter
    (points : Source.PointVec) (values : Source.M31Vec)
    (hpost : SourceCirclePost points values) :
    AspisV5FriCoordinateDenominatorLoops.CirclePost
      (toAdapterPointVec points) (values, none) := by
  rcases hpost with ⟨hlength, hcanonical, hvalues⟩
  refine ⟨by simpa using hlength, hcanonical, rfl, ?_⟩
  intro index hindex
  have hsourceIndex : index < points.val.length := by simpa using hindex
  have hvalue := hvalues index hsourceIndex
  rw [toAdapterPointVec_getBang points index hsourceIndex]
  exact hvalue

theorem sourceLinePost_to_adapter
    (initial output : Source.M31Vec) (points : Source.PointVec)
    (hpost : SourceLinePointPost initial points (output, none)) :
    AspisV5FriCoordinateDenominatorLoops.LinePointPost initial
      (toAdapterPointVec points) (output, none) := by
  rcases hpost with
    ⟨hlength, hcanonical, _hnone, hprefix, hvalues⟩
  refine ⟨by simpa using hlength, hcanonical, rfl, hprefix, ?_⟩
  intro index hindex
  have hsourceIndex : index < points.val.length := by simpa using hindex
  have hvalue := hvalues index hsourceIndex
  rw [toAdapterPointVec_getBang points index hsourceIndex]
  exact hvalue

theorem sourceBatchInverse_to_adapter
    (denominators flat : Source.M31Vec)
    (hpost : SourceBatchInverseEvidence denominators
      (alloc.vec.Vec.deref flat)) :
    AspisV5FriCoordinateInverseLoops.BatchInverseEvidence denominators flat := by
  rcases hpost with ⟨hlength, hcanonical, hvalues⟩
  refine ⟨hlength, ?_, hvalues⟩
  intro index hindex
  exact hcanonical index hindex

theorem sourceFinalXPost_to_adapter
    (points : Source.PointVec) (output : Source.M31Vec)
    (hpost : SourceFinalXPost points output) :
    AspisV5FriCoordinateOutputLoops.FinalXPost
      (toAdapterPointVec points) output := by
  rcases hpost with ⟨hlength, hcanonical, hvalues⟩
  refine ⟨by simpa using hlength, hcanonical, ?_⟩
  intro index hindex
  have hsourceIndex : index < points.val.length := by simpa using hindex
  have hvalue := hvalues index hsourceIndex
  rw [toAdapterPointVec_getBang points index hsourceIndex]
  simpa [SourceFinalXFormula,
    AspisV5FriCoordinateOutputLoops.finalXFormula,
    toAdapterPoint] using hvalue

theorem sourceOutputEvidence_to_adapter
    (layer0 line1 line2 line3 : Slice Std.U32)
    (flat : Source.M31Vec) (line3Points : Source.PointVec)
    (output : Source.Output)
    (hpost : SourceOutputEvidence layer0 line1 line2 line3 flat
      line3Points output) :
    AspisV5FriCoordinateOutputLoops.AcceptedOutputEvidence
      layer0 line1 line2 line3 flat (toAdapterPointVec line3Points)
      (toAdapterOutput output) := by
  rcases hpost with
    ⟨hcircle, later0, later1, later2, hlater, hlater0, hlater1,
      hlater2, hfinal⟩
  exact ⟨hcircle, later0, later1, later2, hlater, hlater0, hlater1,
    hlater2, sourceFinalXPost_to_adapter line3Points output.final_x hfinal⟩

def AdapterPathEvidence
    (layer0 line1 line2 line3 : Slice Std.U32)
    (circlePoints line1Points line2Points line3Points : Source.PointVec)
    (output : Source.Output) : Prop :=
  ∃ circleDenominators after1 after2 denominators flat : Source.M31Vec,
    ReleasedPointListsEvidence layer0 line1 line2 line3
      (toAdapterPointVec circlePoints) (toAdapterPointVec line1Points)
      (toAdapterPointVec line2Points) (toAdapterPointVec line3Points) ∧
    AspisV5FriCoordinateDenominatorLoops.CirclePost
      (toAdapterPointVec circlePoints) (circleDenominators, none) ∧
    AspisV5FriCoordinateDenominatorLoops.LinePointPost
      circleDenominators (toAdapterPointVec line1Points) (after1, none) ∧
    AspisV5FriCoordinateDenominatorLoops.LinePointPost
      after1 (toAdapterPointVec line2Points) (after2, none) ∧
    AspisV5FriCoordinateDenominatorLoops.LinePointPost
      after2 (toAdapterPointVec line3Points) (denominators, none) ∧
    AspisV5FriCoordinateInverseLoops.BatchInverseEvidence denominators flat ∧
    AspisV5FriCoordinateOutputLoops.AcceptedOutputEvidence
      layer0 line1 line2 line3 flat (toAdapterPointVec line3Points)
      (toAdapterOutput output)

theorem sourceAcceptedPath_to_adapterPath
    (layer0 line1 line2 line3 : Slice Std.U32)
    (circlePoints line1Points line2Points line3Points : Source.PointVec)
    (output : Source.Output)
    (hpoints : SourceReleasedPointListsEvidence layer0 line1 line2 line3
      circlePoints line1Points line2Points line3Points)
    (hpath : SourceAcceptedPathEvidence layer0 line1 line2 line3
      circlePoints line1Points line2Points line3Points output) :
    AdapterPathEvidence layer0 line1 line2 line3 circlePoints line1Points
      line2Points line3Points output := by
  rcases hpath with
    ⟨circleDenominators, after1, after2, denominators, flat,
      hcircle, hline1, hline2, hline3, hinverses, houtput⟩
  exact ⟨circleDenominators, after1, after2, denominators, flat,
    sourceReleasedPoints_to_adapter layer0 line1 line2 line3
      circlePoints line1Points line2Points line3Points hpoints
    , sourceCirclePost_to_adapter circlePoints circleDenominators
      hcircle
    , sourceLinePost_to_adapter circleDenominators after1
      line1Points hline1
    , sourceLinePost_to_adapter after1 after2 line2Points hline2
    , sourceLinePost_to_adapter after2 denominators line3Points
      hline3
    , sourceBatchInverse_to_adapter denominators flat hinverses
    , sourceOutputEvidence_to_adapter layer0 line1 line2 line3
      flat line3Points output houtput⟩

/-- The exact production-source path has the released mathematical meaning at
every returned coordinate.  This theorem talks about the actual source output;
no equality to the older duplicate adapter implementation is assumed. -/
theorem adapterPath_released_coordinates_exact
    (layer0 line1 line2 line3 : Slice Std.U32)
    (circlePoints line1Points line2Points line3Points : Source.PointVec)
    (output : Source.Output)
    (hline3 : IndicesBelow line3 2048)
    (path : AdapterPathEvidence layer0 line1 line2 line3 circlePoints
      line1Points line2Points line3Points output) :
    ReleasedCoordinateOutputEvidence layer0 line1 line2 line3
      (toAdapterOutput output) := by
  rcases path with
    ⟨circleDenominators, after1, after2, denominators, flat,
      hpointsAdapter, hcircle, hline1Post, hline2Post, hline3Post,
      hinverses, houtputLayout⟩
  have hlines : AspisV5FriCoordinateDenominatorLoops.ThreeLineLayerPost
      circleDenominators (toAdapterPointVec line1Points)
      (toAdapterPointVec line2Points) (toAdapterPointVec line3Points)
      (denominators, none) :=
    ⟨after1, after2, hline1Post, hline2Post,
      hline3Post⟩
  have hlineValues :=
    AspisV5FriCoordinateDenominatorLoops.threeLineLayerPost_exact_values
      circleDenominators denominators
      (toAdapterPointVec line1Points) (toAdapterPointVec line2Points)
      (toAdapterPointVec line3Points) hlines
  have hcircleLength : circleDenominators.val.length ≤
      denominators.val.length := by
    rcases hlineValues with ⟨hlength, _⟩
    omega
  have hcircleExact := accepted_output_circle_exact
    layer0 line1 line2 line3
    (toAdapterPointVec circlePoints) (toAdapterPointVec line1Points)
    (toAdapterPointVec line2Points) (toAdapterPointVec line3Points)
    circleDenominators denominators flat
    (toAdapterOutput output) hpointsAdapter hcircle hinverses
    hcircleLength hlineValues.2.1 houtputLayout
  have hline1Exact := accepted_output_line1_exact
    layer0 line1 line2 line3
    (toAdapterPointVec circlePoints) (toAdapterPointVec line1Points)
    (toAdapterPointVec line2Points) (toAdapterPointVec line3Points)
    circleDenominators denominators flat
    (toAdapterOutput output) hpointsAdapter hcircle hlines hinverses
    houtputLayout
  have hline2Exact := accepted_output_line2_exact
    layer0 line1 line2 line3
    (toAdapterPointVec circlePoints) (toAdapterPointVec line1Points)
    (toAdapterPointVec line2Points) (toAdapterPointVec line3Points)
    circleDenominators denominators flat
    (toAdapterOutput output) hpointsAdapter hcircle hlines hinverses
    houtputLayout
  have hline3Exact := accepted_output_line3_exact
    layer0 line1 line2 line3
    (toAdapterPointVec circlePoints) (toAdapterPointVec line1Points)
    (toAdapterPointVec line2Points) (toAdapterPointVec line3Points)
    circleDenominators denominators flat
    (toAdapterOutput output) hpointsAdapter hcircle hlines hinverses
    houtputLayout
  have hfinalExact := accepted_output_final_x_exact
    layer0 line1 line2 line3
    (toAdapterPointVec circlePoints) (toAdapterPointVec line1Points)
    (toAdapterPointVec line2Points) (toAdapterPointVec line3Points)
    flat (toAdapterOutput output) hline3 hpointsAdapter
    houtputLayout
  have hflatLength : flat.val.length =
      2 * layer0.val.length + 3 * line1.val.length +
        3 * line2.val.length + 3 * line3.val.length := by
    calc
      flat.val.length = denominators.val.length := hinverses.1
      _ = circleDenominators.val.length +
          3 * (toAdapterPointVec line1Points).val.length +
          3 * (toAdapterPointVec line2Points).val.length +
          3 * (toAdapterPointVec line3Points).val.length := hlineValues.1
      _ = 2 * layer0.val.length + 3 * line1.val.length +
          3 * line2.val.length + 3 * line3.val.length := by
        rw [hcircle.1, hpointsAdapter.circleLength,
          hpointsAdapter.line1Length, hpointsAdapter.line2Length,
          hpointsAdapter.line3Length]
  have hflatCanonical := hinverses.2.1
  obtain ⟨later0, later1, later2, hlater, hlater0, hlater1, hlater2,
      hfinalPost⟩ := houtputLayout.2
  have hlater0Out : (toAdapterOutput output).later.val[0]! = later0 := by
    rw [hlater]
    rfl
  have hlater1Out : (toAdapterOutput output).later.val[1]! = later1 := by
    rw [hlater]
    rfl
  have hlater2Out : (toAdapterOutput output).later.val[2]! = later2 := by
    rw [hlater]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfinalExact⟩
  · intro ordinal hord
    constructor
    · rw [houtputLayout.1,
        AspisV5FriCoordinateOutputLoops.pairOutput_get_zero flat 0
          layer0.val.length ordinal hord]
      apply hflatCanonical
      rw [hflatLength]
      omega
    · rw [houtputLayout.1,
        AspisV5FriCoordinateOutputLoops.pairOutput_get_one flat 0
          layer0.val.length ordinal hord]
      apply hflatCanonical
      rw [hflatLength]
      omega
  · intro ordinal hord slot
    rw [hlater0Out, hlater0]
    fin_cases slot
    · rw [AspisV5FriCoordinateOutputLoops.tripleOutput_get_zero flat
        (2 * layer0.val.length) line1.val.length ordinal hord]
      apply hflatCanonical
      rw [hflatLength]
      omega
    · rw [AspisV5FriCoordinateOutputLoops.tripleOutput_get_one flat
        (2 * layer0.val.length) line1.val.length ordinal hord]
      apply hflatCanonical
      rw [hflatLength]
      omega
    · rw [AspisV5FriCoordinateOutputLoops.tripleOutput_get_two flat
        (2 * layer0.val.length) line1.val.length ordinal hord]
      apply hflatCanonical
      rw [hflatLength]
      omega
  · intro ordinal hord slot
    rw [hlater1Out, hlater1]
    fin_cases slot
    · rw [AspisV5FriCoordinateOutputLoops.tripleOutput_get_zero flat
        (2 * layer0.val.length + 3 * line1.val.length)
          line2.val.length ordinal hord]
      apply hflatCanonical
      rw [hflatLength]
      omega
    · rw [AspisV5FriCoordinateOutputLoops.tripleOutput_get_one flat
        (2 * layer0.val.length + 3 * line1.val.length)
          line2.val.length ordinal hord]
      apply hflatCanonical
      rw [hflatLength]
      omega
    · rw [AspisV5FriCoordinateOutputLoops.tripleOutput_get_two flat
        (2 * layer0.val.length + 3 * line1.val.length)
          line2.val.length ordinal hord]
      apply hflatCanonical
      rw [hflatLength]
      omega
  · intro ordinal hord slot
    rw [hlater2Out, hlater2]
    fin_cases slot
    · rw [AspisV5FriCoordinateOutputLoops.tripleOutput_get_zero flat
        (2 * layer0.val.length + 3 * line1.val.length +
          3 * line2.val.length) line3.val.length ordinal hord]
      apply hflatCanonical
      rw [hflatLength]
      omega
    · rw [AspisV5FriCoordinateOutputLoops.tripleOutput_get_one flat
        (2 * layer0.val.length + 3 * line1.val.length +
          3 * line2.val.length) line3.val.length ordinal hord]
      apply hflatCanonical
      rw [hflatLength]
      omega
    · rw [AspisV5FriCoordinateOutputLoops.tripleOutput_get_two flat
        (2 * layer0.val.length + 3 * line1.val.length +
          3 * line2.val.length) line3.val.length ordinal hord]
      apply hflatCanonical
      rw [hflatLength]
      omega
  · intro ordinal hord
    apply hfinalPost.2.1 ordinal
    rw [hfinalPost.1, hpointsAdapter.line3Length]
    exact hord
  · intro ordinal hord
    have h := hcircleExact ordinal hord
    have hcoordinates := releasedCircleExpected_coordinates layer0 ordinal
    simpa only [hcoordinates.1, hcoordinates.2] using h
  · intro ordinal hord slot
    have h := hline1Exact ordinal hord
    have hcoordinates := releasedLine1Expected_coordinates line1 ordinal
    fin_cases slot
    · exact h.1.trans (congrArg Inv.inv (congrArg (2 * ·)
        hcoordinates.1))
    · exact h.2.1.trans (congrArg Inv.inv (congrArg (2 * ·)
        hcoordinates.2.1))
    · exact h.2.2.trans (congrArg Inv.inv (congrArg (2 * ·)
        hcoordinates.2.2))
  · intro ordinal hord slot
    have h := hline2Exact ordinal hord
    have hcoordinates := releasedLine2Expected_coordinates line2 ordinal
    fin_cases slot
    · exact h.1.trans (congrArg Inv.inv (congrArg (2 * ·)
        hcoordinates.1))
    · exact h.2.1.trans (congrArg Inv.inv (congrArg (2 * ·)
        hcoordinates.2.1))
    · exact h.2.2.trans (congrArg Inv.inv (congrArg (2 * ·)
        hcoordinates.2.2))
  · intro ordinal hord slot
    have h := hline3Exact ordinal hord
    have hcoordinates := releasedLine3Expected_coordinates line3 ordinal
    fin_cases slot
    · exact h.1.trans (congrArg Inv.inv (congrArg (2 * ·)
        hcoordinates.1))
    · exact h.2.1.trans (congrArg Inv.inv (congrArg (2 * ·)
        hcoordinates.2.1))
    · exact h.2.2.trans (congrArg Inv.inv (congrArg (2 * ·)
        hcoordinates.2.2))

#print axioms sourceAcceptedPath_to_adapterPath
#print axioms adapterPath_released_coordinates_exact

end V5CoordinateProductionReleasedProof
