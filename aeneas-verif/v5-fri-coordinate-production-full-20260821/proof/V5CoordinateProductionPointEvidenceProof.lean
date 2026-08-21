import V5CoordinateProductionTailProof

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V5CoordinateProductionPointEvidenceProof

open V5CoordinateProductionTailProof
open V5CoordinateProductionFullProof
open V5CoordinateSelectedProductionProof
open AspisV5FriCoordinateFieldSemantics
open AspisCircleGroupOrder
open AspisV5FriCoordinateReleasedPointConnection
open V5CoordinateSelectedProductionSource

abbrev Point := V5CoordinateProductionTailProof.Point
abbrev PointVec := V5CoordinateProductionTailProof.PointVec

private theorem sourceRepresents_coordinates
    (point : Point) (expected : AspisCircleGroupOrder.C)
    (hrep : SourceRepresents point expected) :
    m31Value point.x = expected.1.1 ∧
      m31Value point.y = expected.1.2 := by
  constructor
  · exact congrArg Prod.fst hrep.2
  · exact congrArg Prod.snd hrep.2

/-- All field-domain facts needed by the four production denominator loops.
The point lists come from the already-proved released point construction; this
stage only turns those representations into the exact canonicality and
nonzero facts consumed by the generated Rust loops. -/
structure SourceReleasedPointArithmeticEvidence
    (circlePoints line1Points line2Points line3Points : PointVec) : Prop where
  circleCanonical : SourceCanonicalPoints circlePoints
  line1Canonical : SourceCanonicalPoints line1Points
  line2Canonical : SourceCanonicalPoints line2Points
  line3Canonical : SourceCanonicalPoints line3Points
  circleNonzero : ∀ index, index < circlePoints.val.length →
    2 * m31Value circlePoints.val[index]!.x ≠ 0 ∧
    2 * m31Value circlePoints.val[index]!.y ≠ 0
  line1Nonzero : ∀ index, index < line1Points.val.length →
    2 * m31Value line1Points.val[index]!.x ≠ 0 ∧
    2 * m31Value line1Points.val[index]!.y ≠ 0 ∧
    2 * (2 * m31Value line1Points.val[index]!.x ^ 2 - 1) ≠ 0
  line2Nonzero : ∀ index, index < line2Points.val.length →
    2 * m31Value line2Points.val[index]!.x ≠ 0 ∧
    2 * m31Value line2Points.val[index]!.y ≠ 0 ∧
    2 * (2 * m31Value line2Points.val[index]!.x ^ 2 - 1) ≠ 0
  line3Nonzero : ∀ index, index < line3Points.val.length →
    2 * m31Value line3Points.val[index]!.x ≠ 0 ∧
    2 * m31Value line3Points.val[index]!.y ≠ 0 ∧
    2 * (2 * m31Value line3Points.val[index]!.x ^ 2 - 1) ≠ 0

theorem source_released_point_arithmetic_evidence
    (layer0 line1 line2 line3 : Slice Std.U32)
    (circlePoints line1Points line2Points line3Points : PointVec)
    (hlayer0 : IndicesBelow layer0 131072)
    (hline1 : IndicesBelow line1 32768)
    (hline2 : IndicesBelow line2 8192)
    (hline3 : IndicesBelow line3 2048)
    (hpoints : SourceReleasedPointListsEvidence layer0 line1 line2 line3
      circlePoints line1Points line2Points line3Points) :
    SourceReleasedPointArithmeticEvidence circlePoints line1Points
      line2Points line3Points := by
  refine {
    circleCanonical := ?_
    line1Canonical := ?_
    line2Canonical := ?_
    line3Canonical := ?_
    circleNonzero := ?_
    line1Nonzero := ?_
    line2Nonzero := ?_
    line3Nonzero := ?_ }
  · intro index hindex
    exact (hpoints.circle index hindex).1
  · intro index hindex
    exact (hpoints.line1 index hindex).1
  · intro index hindex
    exact (hpoints.line2 index hindex).1
  · intro index hindex
    exact (hpoints.line3 index hindex).1
  · intro index hindex
    have hreleased := releasedCircleExpected_nonzero layer0 hlayer0 index
      (by simpa [hpoints.circleLength] using hindex)
    have hcoordinates := sourceRepresents_coordinates
      circlePoints.val[index]! (ReleasedCircleExpected layer0 index)
      (hpoints.circle index hindex)
    rw [hcoordinates.1, hcoordinates.2]
    exact hreleased
  · intro index hindex
    have hreleased := releasedLine1Expected_nonzero line1 hline1 index
      (by simpa [hpoints.line1Length] using hindex)
    have hcoordinates := sourceRepresents_coordinates
      line1Points.val[index]! (ReleasedLine1Expected line1 index)
      (hpoints.line1 index hindex)
    rw [hcoordinates.1, hcoordinates.2]
    exact hreleased
  · intro index hindex
    have hreleased := releasedLine2Expected_nonzero line2 hline2 index
      (by simpa [hpoints.line2Length] using hindex)
    have hcoordinates := sourceRepresents_coordinates
      line2Points.val[index]! (ReleasedLine2Expected line2 index)
      (hpoints.line2 index hindex)
    rw [hcoordinates.1, hcoordinates.2]
    exact hreleased
  · intro index hindex
    have hreleased := releasedLine3Expected_nonzero line3 hline3 index
      (by simpa [hpoints.line3Length] using hindex)
    have hcoordinates := sourceRepresents_coordinates
      line3Points.val[index]! (ReleasedLine3Expected line3 index)
      (hpoints.line3 index hindex)
    rw [hcoordinates.1, hcoordinates.2]
    exact hreleased

#print axioms source_released_point_arithmetic_evidence

end V5CoordinateProductionPointEvidenceProof
