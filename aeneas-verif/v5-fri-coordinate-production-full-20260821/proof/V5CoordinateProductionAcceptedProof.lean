import V5CoordinateProductionDenominatorPathProof

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V5CoordinateProductionAcceptedProof

open V5CoordinateProductionTailProof
open V5CoordinateProductionPointEvidenceProof
open V5CoordinateProductionDenominatorPathProof
open V5CoordinateProductionFullProof
open V5CoordinateSelectedProductionProof
open AspisV5FriCoordinateFieldSemantics
open AspisV5FriCoordinateReleasedPointConnection
open V5CoordinateSelectedProductionSource

abbrev M31 := V5CoordinateProductionTailProof.M31
abbrev M31Vec := V5CoordinateProductionTailProof.M31Vec
abbrev PointVec := V5CoordinateProductionTailProof.PointVec
abbrev Output := V5CoordinateProductionTailProof.Output

def SourceAcceptedPathEvidence
    (layer0 line1 line2 line3 : Slice Std.U32)
    (circlePoints line1Points line2Points line3Points : PointVec)
    (output : Output) : Prop :=
  ∃ circleDenominators after1 after2 denominators flat : M31Vec,
    SourceCirclePost circlePoints circleDenominators ∧
    SourceLinePointPost circleDenominators line1Points (after1, none) ∧
    SourceLinePointPost after1 line2Points (after2, none) ∧
    SourceLinePointPost after2 line3Points (denominators, none) ∧
    SourceTerminalEvidence layer0 line1 line2 line3 denominators flat
      line3Points output

/-- Exact inner path for one accepted domain-19 production coordinate call.
The proof composes the separately checked released-point arithmetic facts, all
four source denominator loops, and the terminal batch/output call.  It has no
implementation-equality premise. -/
theorem source_accepted_inner_path_exact
    (layer0 line1 line2 line3 : Slice Std.U32)
    (later : Array (Slice Std.U32) 3#usize)
    (inverseFn : M31 → M31)
    (circlePoints line1Points line2Points line3Points : PointVec)
    (denominatorCount : Std.Usize) (output : Output)
    (hlayer0 : IndicesBelow layer0 131072)
    (hline1 : IndicesBelow line1 32768)
    (hline2 : IndicesBelow line2 8192)
    (hline3 : IndicesBelow line3 2048)
    (hpoints : SourceReleasedPointListsEvidence layer0 line1 line2 line3
      circlePoints line1Points line2Points line3Points)
    (hlater0 : Array.index_usize later 0#usize = .ok line1)
    (hlater1 : Array.index_usize later 1#usize = .ok line2)
    (hlater2 : Array.index_usize later 2#usize = .ok line3)
    (hcircleNonempty : 0 < layer0.val.length)
    (hcapacity : 2 * layer0.val.length +
      3 * (line1.val.length + line2.val.length + line3.val.length) ≤
        Std.Usize.max)
    (hloop :
      V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0
          { slice := alloc.vec.Vec.deref circlePoints, i := 0 }
          layer0 later inverseFn line1Points line2Points line3Points
          denominatorCount
          (alloc.vec.Vec.with_capacity M31 denominatorCount) =
        .ok (.Ok output)) :
    SourceAcceptedPathEvidence layer0 line1 line2 line3 circlePoints
      line1Points line2Points line3Points output := by
  have harithmetic :=
    source_released_point_arithmetic_evidence layer0 line1 line2 line3
      circlePoints line1Points line2Points line3Points hlayer0 hline1 hline2
      hline3 hpoints
  obtain ⟨circleDenominators, after1, after2, denominators,
      hcirclePost, hline1Post, hline2Post, hline3Post, hterminalRun⟩ :=
    source_accepted_denominator_path_exact layer0 line1 line2 line3 later
      inverseFn circlePoints line1Points line2Points line3Points
      denominatorCount output hpoints harithmetic hcapacity hloop
  have hdenominatorReleasedLength : denominators.val.length =
      2 * layer0.val.length + 3 * line1.val.length +
        3 * line2.val.length + 3 * line3.val.length := by
    rw [hline3Post.1, hline2Post.1, hline1Post.1, hcirclePost.1,
      hpoints.circleLength, hpoints.line1Length, hpoints.line2Length,
      hpoints.line3Length]
  obtain ⟨flat, hterminalEvidence⟩ := source_terminal_success_exact
    layer0 line1 line2 line3 later inverseFn line1Points line2Points
    line3Points denominatorCount denominators output hlater0 hlater1 hlater2
    (by rw [hdenominatorReleasedLength]; omega) hdenominatorReleasedLength
    (fun index hindex => (harithmetic.line3Canonical index hindex).1)
    hterminalRun
  exact ⟨circleDenominators, after1, after2, denominators, flat,
    hcirclePost, hline1Post, hline2Post, hline3Post, hterminalEvidence⟩

#print axioms source_accepted_inner_path_exact

end V5CoordinateProductionAcceptedProof
