import V5CoordinateProductionReleasedProof

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000
set_option linter.unusedSimpArgs false

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V5CoordinateProductionTopCallProof

open V5CoordinateProductionTailProof
open V5CoordinateProductionAcceptedProof
open V5CoordinateProductionReleasedProof
open V5CoordinateProductionFullProof
open V5CoordinateSelectedProductionProof
open V5CoordinateSelectedProductionSource
open AspisV5FriCoordinateReleasedPointConnection

abbrev M31 := V5CoordinateProductionTailProof.M31
abbrev Output := V5CoordinateProductionTailProof.Output
abbrev PointVec := V5CoordinateProductionTailProof.PointVec

/-- An accepted call to the actual generated production entry point exposes
the four successful point-helper calls and the exact accepted inner-loop call.
This is control-flow inversion of the generated source, not an assumed
implementation equality. -/
theorem source_accepted_full_call_decomposes
    (layer0 line1 line2 line3 : Slice Std.U32)
    (later : Array (Slice Std.U32) 3#usize)
    (inverseFn : M31 → M31) (output : Output)
    (hlater0 : Array.index_usize later 0#usize = .ok line1)
    (hlater1 : Array.index_usize later 1#usize = .ok line2)
    (hlater2 : Array.index_usize later 2#usize = .ok line3)
    (hrun :
      V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle
        19#u32 layer0 later inverseFn = .ok (.Ok output)) :
    ∃ circlePoints line1Points line2Points line3Points : PointVec,
      ∃ denominatorCount : Std.Usize,
      V5CoordinateSelectedProductionSource.circle_fri.selected_circle_fiber_points_shared
          19#u32 layer0 = .ok (.Ok circlePoints) ∧
      V5CoordinateSelectedProductionSource.circle_fri.derive_parent_line_points
          layer0 (alloc.vec.Vec.deref circlePoints) line1 1#u8 =
        .ok (.Ok line1Points) ∧
      V5CoordinateSelectedProductionSource.circle_fri.derive_parent_line_points
          line1 (alloc.vec.Vec.deref line1Points) line2 2#u8 =
        .ok (.Ok line2Points) ∧
      V5CoordinateSelectedProductionSource.circle_fri.derive_parent_line_points
          line2 (alloc.vec.Vec.deref line2Points) line3 2#u8 =
        .ok (.Ok line3Points) ∧
      V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0
          { slice := alloc.vec.Vec.deref circlePoints, i := 0 }
          layer0 later inverseFn line1Points line2Points line3Points
          denominatorCount (alloc.vec.Vec.with_capacity M31 denominatorCount) =
        .ok (.Ok output) := by
  unfold
    V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle
    at hrun
  have horder :
      (V5CoordinateSelectedProductionSource.params.CIRCLE_LOG_ORDER - 1#u32 :
        Result Std.U32) = .ok 30#u32 := by
    unfold V5CoordinateSelectedProductionSource.params.CIRCLE_LOG_ORDER
    rfl
  rw [horder] at hrun
  norm_num [V5CoordinateSelectedProductionSource.params.CIRCLE_LOG_ORDER,
    Std.lift, UScalar.lt_equiv, UScalar.size, U32.size, U32.numBits,
    Bind.bind, Aeneas.Std.bind]
    at hrun
  generalize hcircleCall :
      V5CoordinateSelectedProductionSource.circle_fri.selected_circle_fiber_points_shared
        19#u32 layer0 = circleResult at hrun
  cases circleResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
  | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
  | ok circleInner =>
    cases circleInner with
    | Err error =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame, core.convert.FromSame.from,
        Bind.bind, Aeneas.Std.bind] at hrun
    | Ok circlePoints =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
        at hrun
      rw [hlater0] at hrun
      simp only [bind_tc_ok] at hrun
      generalize hline1Call :
          V5CoordinateSelectedProductionSource.circle_fri.derive_parent_line_points
            layer0 (alloc.vec.Vec.deref circlePoints) line1 1#u8 =
              line1Result at hrun
      cases line1Result with
      | fail error => simp at hrun
      | div => simp at hrun
      | ok line1Inner =>
        cases line1Inner with
        | Err error =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame, core.convert.FromSame.from] at hrun
        | Ok line1Points =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
            at hrun
          rw [hlater1] at hrun
          simp only [bind_tc_ok] at hrun
          generalize hline2Call :
              V5CoordinateSelectedProductionSource.circle_fri.derive_parent_line_points
                line1 (alloc.vec.Vec.deref line1Points) line2 2#u8 =
                  line2Result at hrun
          cases line2Result with
          | fail error => simp at hrun
          | div => simp at hrun
          | ok line2Inner =>
            cases line2Inner with
            | Err error =>
              simp [core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame, core.convert.FromSame.from] at hrun
            | Ok line2Points =>
              simp only [core.result.Result.Insts.CoreOpsTry.branch,
                bind_tc_ok] at hrun
              rw [hlater2] at hrun
              simp only [bind_tc_ok] at hrun
              generalize hline3Call :
                  V5CoordinateSelectedProductionSource.circle_fri.derive_parent_line_points
                    line2 (alloc.vec.Vec.deref line2Points) line3 2#u8 =
                      line3Result at hrun
              cases line3Result with
              | fail error => simp at hrun
              | div => simp at hrun
              | ok line3Inner =>
                cases line3Inner with
                | Err error =>
                  simp [core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                    core.convert.FromSame, core.convert.FromSame.from] at hrun
                | Ok line3Points =>
                  simp only [core.result.Result.Insts.CoreOpsTry.branch,
                    bind_tc_ok] at hrun
                  generalize hcapacityCall :
                      core.option.Option.and_then
                        V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeOptionUsize
                        (Slice.len layer0 |>.checked_mul 2#usize) later =
                          capacityResult at hrun
                  cases capacityResult with
                  | fail error => simp at hrun
                  | div => simp at hrun
                  | ok capacityOption =>
                    cases capacityOption with
                    | none =>
                      simp [core.option.Option.ok_or,
                        core.result.Result.Insts.CoreOpsTry.branch,
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                        core.convert.FromSame, core.convert.FromSame.from]
                        at hrun
                    | some denominatorCount =>
                      simp only [core.option.Option.ok_or,
                        core.result.Result.Insts.CoreOpsTry.branch,
                        bind_tc_ok,
                        V5CoordinateSelectedProductionSource.SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter]
                        at hrun
                      exact ⟨circlePoints, line1Points, line2Points,
                        line3Points, denominatorCount, rfl, hline1Call,
                        hline2Call, hline3Call, hrun⟩

/-- End-to-end coordinate meaning for the actual generated production entry
point.  Every returned table entry has the released circle/line-coordinate
meaning. -/
theorem source_accepted_full_call_released_coordinates
    (layer0 line1 line2 line3 : Slice Std.U32)
    (later : Array (Slice Std.U32) 3#usize)
    (inverseFn : M31 → M31) (output : Output)
    (hlater0 : Array.index_usize later 0#usize = .ok line1)
    (hlater1 : Array.index_usize later 1#usize = .ok line2)
    (hlater2 : Array.index_usize later 2#usize = .ok line3)
    (hlayer0 : IndicesBelow layer0 131072)
    (hline1 : IndicesBelow line1 32768)
    (hline2 : IndicesBelow line2 8192)
    (hline3 : IndicesBelow line3 2048)
    (hcircleNonempty : 0 < layer0.val.length)
    (hcapacity : 2 * layer0.val.length +
      3 * (line1.val.length + line2.val.length + line3.val.length) ≤
        Std.Usize.max)
    (hrun :
      V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle
        19#u32 layer0 later inverseFn = .ok (.Ok output)) :
    ReleasedCoordinateOutputEvidence layer0 line1 line2 line3
      (V5CoordinateProductionReleasedProof.toAdapterOutput output) := by
  obtain ⟨circlePoints, line1Points, line2Points, line3Points,
      denominatorCount, hcircleCall, hline1Call, hline2Call, hline3Call,
      hloop⟩ := source_accepted_full_call_decomposes layer0 line1 line2 line3
    later inverseFn output hlater0 hlater1 hlater2 hrun
  have hpoints := source_accepted_point_helpers_represent_released
    layer0 line1 line2 line3 circlePoints line1Points line2Points line3Points
    hlayer0 hline1 hline2 hline3 hcircleCall hline1Call hline2Call hline3Call
  have hpath := source_accepted_inner_path_exact layer0 line1 line2 line3
    later inverseFn circlePoints line1Points line2Points line3Points
    denominatorCount output hlayer0 hline1 hline2 hline3 hpoints hlater0
    hlater1 hlater2 hcircleNonempty hcapacity hloop
  have hadapter := sourceAcceptedPath_to_adapterPath layer0 line1 line2 line3
    circlePoints line1Points line2Points line3Points output hpoints hpath
  exact adapterPath_released_coordinates_exact layer0 line1 line2 line3
    circlePoints line1Points line2Points line3Points output hline3 hadapter

#print axioms source_accepted_full_call_decomposes
#print axioms source_accepted_full_call_released_coordinates

end V5CoordinateProductionTopCallProof
