import V5CoordinateProductionPointEvidenceProof

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V5CoordinateProductionDenominatorPathProof

open V5CoordinateProductionTailProof
open V5CoordinateProductionPointEvidenceProof
open V5CoordinateProductionFullProof
open V5CoordinateSelectedProductionProof
open AspisV5FriCoordinateFieldSemantics
open AspisV5FriCoordinateReleasedPointConnection
open V5CoordinateSelectedProductionSource

abbrev M31 := V5CoordinateProductionTailProof.M31
abbrev M31Vec := V5CoordinateProductionTailProof.M31Vec
abbrev PointVec := V5CoordinateProductionTailProof.PointVec
abbrev Output := V5CoordinateProductionTailProof.Output

/-- Evidence after the circle-prefix loop and all three fixed line loops have
run on an accepted production execution.  Besides the mathematical poststates,
the structure retains the exact accepted source call at the terminal iterator,
which is the only input the final batch/output stage needs. -/
def SourceAcceptedDenominatorPathEvidence
    (layer0 : Slice Std.U32) (later : Array (Slice Std.U32) 3#usize)
    (inverseFn : M31 → M31)
    (line1Points line2Points line3Points : PointVec)
    (denominatorCount : Std.Usize) (output : Output)
    (circlePoints : PointVec) : Prop :=
  ∃ circleDenominators after1 after2 denominators : M31Vec,
    SourceCirclePost circlePoints circleDenominators ∧
    SourceLinePointPost circleDenominators line1Points (after1, none) ∧
    SourceLinePointPost after1 line2Points (after2, none) ∧
    SourceLinePointPost after2 line3Points (denominators, none) ∧
    V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0
      (sourcePointVecIterAt line1Points line2Points line3Points 3)
      layer0 later inverseFn line3Points denominatorCount denominators =
        .ok (.Ok output)

theorem source_accepted_denominator_path_exact
    (layer0 line1 line2 line3 : Slice Std.U32)
    (later : Array (Slice Std.U32) 3#usize)
    (inverseFn : M31 → M31)
    (circlePoints line1Points line2Points line3Points : PointVec)
    (denominatorCount : Std.Usize) (output : Output)
    (hpoints : SourceReleasedPointListsEvidence layer0 line1 line2 line3
      circlePoints line1Points line2Points line3Points)
    (harithmetic : SourceReleasedPointArithmeticEvidence circlePoints
      line1Points line2Points line3Points)
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
    SourceAcceptedDenominatorPathEvidence layer0 later inverseFn line1Points
      line2Points line3Points denominatorCount output circlePoints := by
  obtain ⟨circleDenominators, hcirclePost, hcircleAccepted⟩ :=
    source_circle_prefix_from_empty_accepted circlePoints layer0 later
      inverseFn line1Points line2Points line3Points denominatorCount
      harithmetic.circleCanonical harithmetic.circleNonzero
      (by rw [hpoints.circleLength]; omega)
  rcases hcirclePost with
    ⟨hcircleLength, hcircleValuesCanonical, hcircleValues⟩
  have hline1Capacity : circleDenominators.val.length +
      3 * line1Points.val.length ≤ Std.Usize.max := by
    rw [hcircleLength, hpoints.circleLength, hpoints.line1Length]
    omega
  obtain ⟨line1Out, hline1Run, hline1Post⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (source_line_point_denominator_loop_exact circleDenominators
        line1Points hcircleValuesCanonical harithmetic.line1Canonical
        hline1Capacity harithmetic.line1Nonzero)
  rcases line1Out with ⟨after1, pending1⟩
  rcases hline1Post with
    ⟨hafter1Length, hafter1Canonical, hpending1, hafter1Prefix,
      hafter1Values⟩
  change pending1 = none at hpending1
  subst pending1
  have hline2Capacity : after1.val.length +
      3 * line2Points.val.length ≤ Std.Usize.max := by
    rw [hafter1Length, hcircleLength, hpoints.circleLength,
      hpoints.line1Length, hpoints.line2Length]
    omega
  obtain ⟨line2Out, hline2Run, hline2Post⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (source_line_point_denominator_loop_exact after1 line2Points
        hafter1Canonical harithmetic.line2Canonical hline2Capacity
        harithmetic.line2Nonzero)
  rcases line2Out with ⟨after2, pending2⟩
  rcases hline2Post with
    ⟨hafter2Length, hafter2Canonical, hpending2, hafter2Prefix,
      hafter2Values⟩
  change pending2 = none at hpending2
  subst pending2
  have hline3Capacity : after2.val.length +
      3 * line3Points.val.length ≤ Std.Usize.max := by
    rw [hafter2Length, hafter1Length, hcircleLength,
      hpoints.circleLength, hpoints.line1Length, hpoints.line2Length,
      hpoints.line3Length]
    omega
  obtain ⟨line3Out, hline3Run, hline3Post⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (source_line_point_denominator_loop_exact after2 line3Points
        hafter2Canonical harithmetic.line3Canonical hline3Capacity
        harithmetic.line3Nonzero)
  rcases line3Out with ⟨denominators, pending3⟩
  rcases hline3Post with
    ⟨hdenominatorLength, hdenominatorCanonical, hpending3,
      hdenominatorPrefix, hdenominatorValues⟩
  change pending3 = none at hpending3
  subst pending3
  have houterAccepted :
      V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0
          ⟨Array.make 3#usize [line1Points, line2Points, line3Points], 0⟩
          layer0 later inverseFn line3Points denominatorCount
          circleDenominators = .ok (.Ok output) :=
    hcircleAccepted (.Ok output) hloop
  have houterIteratorEq :
      (⟨Array.make 3#usize [line1Points, line2Points, line3Points], 0⟩ :
        core.array.iter.IntoIter PointVec 3#usize) =
      sourcePointVecIterAt line1Points line2Points line3Points 0 := by
    unfold sourcePointVecIterAt sourcePointVecTriple
    congr 1
  have houterAccepted' :
      V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0
          (sourcePointVecIterAt line1Points line2Points line3Points 0)
          layer0 later inverseFn line3Points denominatorCount
          circleDenominators = .ok (.Ok output) := by
    rw [← houterIteratorEq]
    exact houterAccepted
  have hterminalRun :
      V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0
          (sourcePointVecIterAt line1Points line2Points line3Points 3)
          layer0 later inverseFn line3Points denominatorCount denominators =
        .ok (.Ok output) :=
    source_three_line_outer_accepted layer0 later inverseFn line1Points
      line2Points line3Points denominatorCount circleDenominators after1
      after2 denominators (.Ok output) hline1Run hline2Run hline3Run
      houterAccepted'
  exact ⟨circleDenominators, after1, after2, denominators,
    ⟨hcircleLength, hcircleValuesCanonical, hcircleValues⟩,
    ⟨hafter1Length, hafter1Canonical, rfl, hafter1Prefix,
      hafter1Values⟩,
    ⟨hafter2Length, hafter2Canonical, rfl, hafter2Prefix,
      hafter2Values⟩,
    ⟨hdenominatorLength, hdenominatorCanonical, rfl,
      hdenominatorPrefix, hdenominatorValues⟩,
    hterminalRun⟩

#print axioms source_accepted_denominator_path_exact

end V5CoordinateProductionDenominatorPathProof
