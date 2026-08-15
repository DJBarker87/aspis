import V5MerkleDeployedSource.Funs

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V5MerkleGeneratedDriverInversion

open V5MerkleDeployedSource

abbrev Digest := Array Std.U8 32#usize
abbrev Opening :=
  state_only_private_openings.StateOnlyPrivateOpening
abbrev HashBuffer := alloc.vec.Vec Digest
abbrev QueryIndices :=
  aspis_core.circle_line_merkle.CircleLineQueryIndices
abbrev Topology := merkle.Radix4BinaryCapTopology

theorem bind_eq_ok_iff {A B : Type} (x : Result A) (f : A → Result B)
    (y : B) :
    Bind.bind x f = .ok y ↔ ∃ value, x = .ok value ∧ f value = .ok y := by
  cases x <;> simp [Bind.bind, Aeneas.Std.bind]

/-- Every value returned by the generated five-section driver, together with
the exact five helper calls and their threaded remainders and scratch buffers.
The fifth scratch result is included even though the Rust caller discards it. -/
structure GeneratedFiveSectionTrace
    (roots : private_openings.V5PrivateOpeningRoots)
    (queries : Slice Std.U32) (proofBytes : Slice Std.U8)
    (verified : private_openings.VerifiedV5PrivateOpenings)
    (remainder : Slice Std.U8) where
  layer0Leaves : Std.Usize
  indices : QueryIndices
  rootsArray : Array Digest 5#usize
  tags : Array Std.U8 5#usize
  topology : Topology
  root0 : Digest
  root1 : Digest
  root2 : Digest
  root3 : Digest
  root4 : Digest
  depth0 : Std.U32
  depth1 : Std.U32
  depth2 : Std.U32
  depth3 : Std.U32
  depth4 : Std.U32
  tag0 : Std.U8
  tag1 : Std.U8
  tag2 : Std.U8
  tag3 : Std.U8
  tag4 : Std.U8
  width0 : Std.Usize
  width1 : Std.Usize
  width2 : Std.Usize
  width3 : Std.Usize
  width4 : Std.Usize
  queryArray0 : alloc.vec.Vec Std.U32
  queryArray1 : alloc.vec.Vec Std.U32
  queryArray2 : alloc.vec.Vec Std.U32
  opening0 : Opening
  opening1 : Opening
  opening2 : Opening
  opening3 : Opening
  opening4 : Opening
  remainder0 : Slice Std.U8
  remainder1 : Slice Std.U8
  remainder2 : Slice Std.U8
  remainder3 : Slice Std.U8
  remainder4 : Slice Std.U8
  level1 : HashBuffer
  next1 : HashBuffer
  level2 : HashBuffer
  next2 : HashBuffer
  level3 : HashBuffer
  next3 : HashBuffer
  level4 : HashBuffer
  next4 : HashBuffer
  level5 : HashBuffer
  next5 : HashBuffer
  bytesConsumed : Std.Usize
  layer0Leaves_eq :
    private_openings.V5_PRIVATE_LAYER0_LEAVES = .ok layer0Leaves
  indices_eq :
    aspis_core.circle_line_merkle.derive_circle_line_query_indices_for_count
      queries layer0Leaves = .ok (.Ok indices)
  roots_eq : roots.as_array = .ok rootsArray
  tags_eq : private_openings.V5_PRIVATE_TREE_TAGS = .ok tags
  root0_eq : Array.index_usize rootsArray 0#usize = .ok root0
  root1_eq : Array.index_usize rootsArray 1#usize = .ok root1
  root2_eq : Array.index_usize rootsArray 2#usize = .ok root2
  root3_eq : Array.index_usize rootsArray 3#usize = .ok root3
  root4_eq : Array.index_usize rootsArray 4#usize = .ok root4
  depth0_eq : Array.index_usize private_openings.V5_PRIVATE_DEPTHS 0#usize = .ok depth0
  depth1_eq : Array.index_usize private_openings.V5_PRIVATE_DEPTHS 1#usize = .ok depth1
  depth2_eq : Array.index_usize private_openings.V5_PRIVATE_DEPTHS 2#usize = .ok depth2
  depth3_eq : Array.index_usize private_openings.V5_PRIVATE_DEPTHS 3#usize = .ok depth3
  depth4_eq : Array.index_usize private_openings.V5_PRIVATE_DEPTHS 4#usize = .ok depth4
  tag0_eq : Array.index_usize tags 0#usize = .ok tag0
  tag1_eq : Array.index_usize tags 1#usize = .ok tag1
  tag2_eq : Array.index_usize tags 2#usize = .ok tag2
  tag3_eq : Array.index_usize tags 3#usize = .ok tag3
  tag4_eq : Array.index_usize tags 4#usize = .ok tag4
  width0_eq : Array.index_usize private_openings.V5_PRIVATE_VALUE_WIDTHS 0#usize = .ok width0
  width1_eq : Array.index_usize private_openings.V5_PRIVATE_VALUE_WIDTHS 1#usize = .ok width1
  width2_eq : Array.index_usize private_openings.V5_PRIVATE_VALUE_WIDTHS 2#usize = .ok width2
  width3_eq : Array.index_usize private_openings.V5_PRIVATE_VALUE_WIDTHS 3#usize = .ok width3
  width4_eq : Array.index_usize private_openings.V5_PRIVATE_VALUE_WIDTHS 4#usize = .ok width4
  queryArray0_eq : Array.index_usize indices.later 0#usize = .ok queryArray0
  queryArray1_eq : Array.index_usize indices.later 1#usize = .ok queryArray1
  queryArray2_eq : Array.index_usize indices.later 2#usize = .ok queryArray2
  topology_eq :
    merkle.Radix4BinaryCapTopology.new
      depth0 (alloc.vec.Vec.deref indices.layer0) = .ok (some topology)
  call0 :
    state_only_private_openings.verify_state_only_private_opening_from_proof_with_topology
      root0 depth0 tag0 width0
      (alloc.vec.Vec.deref indices.layer0) proofBytes topology 0#usize
      (alloc.vec.Vec.with_capacity Digest (alloc.vec.Vec.len indices.layer0))
      (alloc.vec.Vec.with_capacity Digest (alloc.vec.Vec.len indices.layer0)) =
        .ok (.Ok (opening0, remainder0), level1, next1)
  call1 :
    state_only_private_openings.verify_state_only_private_opening_from_proof_with_topology
      root1 depth1 tag1 width1
      (alloc.vec.Vec.deref indices.layer0) remainder0 topology 0#usize
      level1 next1 = .ok (.Ok (opening1, remainder1), level2, next2)
  call2 :
    state_only_private_openings.verify_state_only_private_opening_from_proof_with_topology
      root2 depth2 tag2 width2
      (alloc.vec.Vec.deref queryArray0) remainder1 topology 1#usize
      level2 next2 = .ok (.Ok (opening2, remainder2), level3, next3)
  call3 :
    state_only_private_openings.verify_state_only_private_opening_from_proof_with_topology
      root3 depth3 tag3 width3
      (alloc.vec.Vec.deref queryArray1) remainder2 topology 2#usize
      level3 next3 = .ok (.Ok (opening3, remainder3), level4, next4)
  call4 :
    state_only_private_openings.verify_state_only_private_opening_from_proof_with_topology
      root4 depth4 tag4 width4
      (alloc.vec.Vec.deref queryArray2) remainder3 topology 3#usize
      level4 next4 = .ok (.Ok (opening4, remainder4), level5, next5)
  bytesConsumed_eq :
    bytesConsumed =
      Std.Usize.wrapping_sub (Slice.len proofBytes) (Slice.len remainder4)
  verified_eq : verified = {
    c1 := opening0
    c2 := opening1
    later := Array.make 3#usize [opening2, opening3, opening4]
    indices := indices
    bytes_consumed := bytesConsumed }
  remainder_eq : remainder = remainder4

theorem generated_from_proof_success_yields_five_section_trace
    (roots : private_openings.V5PrivateOpeningRoots)
    (queries : Slice Std.U32) (proofBytes remainder : Slice Std.U8)
    (verified : private_openings.VerifiedV5PrivateOpenings)
    (hsuccess :
      private_openings.verify_v5_private_openings_from_proof
        roots queries proofBytes = .ok (.Ok (verified, remainder))) :
    Nonempty (GeneratedFiveSectionTrace roots queries proofBytes verified remainder) := by
  unfold private_openings.verify_v5_private_openings_from_proof at hsuccess
  rw [bind_eq_ok_iff] at hsuccess
  rcases hsuccess with ⟨layer0Leaves, hlayer0Leaves, hsuccess⟩
  rw [bind_eq_ok_iff] at hsuccess
  rcases hsuccess with ⟨queryResult, hqueryResult, hsuccess⟩
  cases queryResult with
  | Err queryError =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        private_openings.V5PrivateOpeningError.Insts.CoreConvertFromCircleLineMerkleError.from]
        at hsuccess
  | Ok indices =>
      simp [core.result.Result.Insts.CoreOpsTry.branch] at hsuccess
      rw [bind_eq_ok_iff] at hsuccess
      rcases hsuccess with ⟨rootsArray, hroots, hsuccess⟩
      rw [bind_eq_ok_iff] at hsuccess
      rcases hsuccess with ⟨depth0, hdepth0, hsuccess⟩
      rw [bind_eq_ok_iff] at hsuccess
      rcases hsuccess with ⟨topologyOption, htopologyOption, hsuccess⟩
      cases topologyOption with
      | none =>
          simp [core.option.Option.ok_or,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
            at hsuccess
      | some topology =>
          simp [core.option.Option.ok_or,
            core.result.Result.Insts.CoreOpsTry.branch] at hsuccess
          rw [bind_eq_ok_iff] at hsuccess
          rcases hsuccess with ⟨root0, hroot0, hsuccess⟩
          rw [bind_eq_ok_iff] at hsuccess
          rcases hsuccess with ⟨tags, htags, hsuccess⟩
          rw [bind_eq_ok_iff] at hsuccess
          rcases hsuccess with ⟨tag0, htag0, hsuccess⟩
          rw [bind_eq_ok_iff] at hsuccess
          rcases hsuccess with ⟨width0, hwidth0, hsuccess⟩
          rw [bind_eq_ok_iff] at hsuccess
          rcases hsuccess with ⟨helper0Result, hcall0, hsuccess⟩
          rcases helper0Result with ⟨r2, level1, next1⟩
          cases r2 with
          | Err openingError =>
              simp [core.result.Result.map_err,
                private_openings.verify_v5_private_openings_from_proof.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyPrivateOpeningErrorV5PrivateOpeningError.call_once,
                core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                at hsuccess
          | Ok openingPair0 =>
              rcases openingPair0 with ⟨opening0, remainder0⟩
              simp [core.result.Result.map_err,
                private_openings.verify_v5_private_openings_from_proof.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyPrivateOpeningErrorV5PrivateOpeningError.call_once,
                core.result.Result.Insts.CoreOpsTry.branch] at hsuccess
              rw [bind_eq_ok_iff] at hsuccess
              rcases hsuccess with ⟨root1, hroot1, hsuccess⟩
              rw [bind_eq_ok_iff] at hsuccess
              rcases hsuccess with ⟨depth1, hdepth1, hsuccess⟩
              rw [bind_eq_ok_iff] at hsuccess
              rcases hsuccess with ⟨tag1, htag1, hsuccess⟩
              rw [bind_eq_ok_iff] at hsuccess
              rcases hsuccess with ⟨width1, hwidth1, hsuccess⟩
              rw [bind_eq_ok_iff] at hsuccess
              rcases hsuccess with ⟨helper1Result, hcall1, hsuccess⟩
              rcases helper1Result with ⟨r4, level2, next2⟩
              cases r4 with
              | Err openingError =>
                  simp [core.result.Result.map_err,
                    private_openings.verify_v5_private_openings_from_proof.closure_1.Insts.CoreOpsFunctionFnOnceTupleStateOnlyPrivateOpeningErrorV5PrivateOpeningError.call_once,
                    core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                    at hsuccess
              | Ok openingPair1 =>
                  rcases openingPair1 with ⟨opening1, remainder1⟩
                  simp [core.result.Result.map_err,
                    private_openings.verify_v5_private_openings_from_proof.closure_1.Insts.CoreOpsFunctionFnOnceTupleStateOnlyPrivateOpeningErrorV5PrivateOpeningError.call_once,
                    core.result.Result.Insts.CoreOpsTry.branch] at hsuccess
                  rw [bind_eq_ok_iff] at hsuccess
                  rcases hsuccess with ⟨root2, hroot2, hsuccess⟩
                  rw [bind_eq_ok_iff] at hsuccess
                  rcases hsuccess with ⟨depth2, hdepth2, hsuccess⟩
                  rw [bind_eq_ok_iff] at hsuccess
                  rcases hsuccess with ⟨tag2, htag2, hsuccess⟩
                  rw [bind_eq_ok_iff] at hsuccess
                  rcases hsuccess with ⟨width2, hwidth2, hsuccess⟩
                  rw [bind_eq_ok_iff] at hsuccess
                  rcases hsuccess with ⟨queryArray0, hqueryArray0, hsuccess⟩
                  rw [bind_eq_ok_iff] at hsuccess
                  rcases hsuccess with ⟨helper2Result, hcall2, hsuccess⟩
                  rcases helper2Result with ⟨r6, level3, next3⟩
                  cases r6 with
                  | Err openingError =>
                      simp [core.result.Result.map_err,
                        private_openings.verify_v5_private_openings_from_proof.closure_2.Insts.CoreOpsFunctionFnOnceTupleStateOnlyPrivateOpeningErrorV5PrivateOpeningError.call_once,
                        core.result.Result.Insts.CoreOpsTry.branch,
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                        at hsuccess
                  | Ok openingPair2 =>
                      rcases openingPair2 with ⟨opening2, remainder2⟩
                      simp [core.result.Result.map_err,
                        private_openings.verify_v5_private_openings_from_proof.closure_2.Insts.CoreOpsFunctionFnOnceTupleStateOnlyPrivateOpeningErrorV5PrivateOpeningError.call_once,
                        core.result.Result.Insts.CoreOpsTry.branch] at hsuccess
                      rw [bind_eq_ok_iff] at hsuccess
                      rcases hsuccess with ⟨root3, hroot3, hsuccess⟩
                      rw [bind_eq_ok_iff] at hsuccess
                      rcases hsuccess with ⟨depth3, hdepth3, hsuccess⟩
                      rw [bind_eq_ok_iff] at hsuccess
                      rcases hsuccess with ⟨tag3, htag3, hsuccess⟩
                      rw [bind_eq_ok_iff] at hsuccess
                      rcases hsuccess with ⟨width3, hwidth3, hsuccess⟩
                      rw [bind_eq_ok_iff] at hsuccess
                      rcases hsuccess with ⟨queryArray1, hqueryArray1, hsuccess⟩
                      rw [bind_eq_ok_iff] at hsuccess
                      rcases hsuccess with ⟨helper3Result, hcall3, hsuccess⟩
                      rcases helper3Result with ⟨r8, level4, next4⟩
                      cases r8 with
                      | Err openingError =>
                          simp [core.result.Result.map_err,
                            private_openings.verify_v5_private_openings_from_proof.closure_3.Insts.CoreOpsFunctionFnOnceTupleStateOnlyPrivateOpeningErrorV5PrivateOpeningError.call_once,
                            core.result.Result.Insts.CoreOpsTry.branch,
                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                            at hsuccess
                      | Ok openingPair3 =>
                          rcases openingPair3 with ⟨opening3, remainder3⟩
                          simp [core.result.Result.map_err,
                            private_openings.verify_v5_private_openings_from_proof.closure_3.Insts.CoreOpsFunctionFnOnceTupleStateOnlyPrivateOpeningErrorV5PrivateOpeningError.call_once,
                            core.result.Result.Insts.CoreOpsTry.branch] at hsuccess
                          rw [bind_eq_ok_iff] at hsuccess
                          rcases hsuccess with ⟨root4, hroot4, hsuccess⟩
                          rw [bind_eq_ok_iff] at hsuccess
                          rcases hsuccess with ⟨depth4, hdepth4, hsuccess⟩
                          rw [bind_eq_ok_iff] at hsuccess
                          rcases hsuccess with ⟨tag4, htag4, hsuccess⟩
                          rw [bind_eq_ok_iff] at hsuccess
                          rcases hsuccess with ⟨width4, hwidth4, hsuccess⟩
                          rw [bind_eq_ok_iff] at hsuccess
                          rcases hsuccess with ⟨queryArray2, hqueryArray2, hsuccess⟩
                          rw [bind_eq_ok_iff] at hsuccess
                          rcases hsuccess with ⟨helper4Result, hcall4, hsuccess⟩
                          rcases helper4Result with ⟨r10, level5, next5⟩
                          cases r10 with
                          | Err openingError =>
                              simp [core.result.Result.map_err,
                                private_openings.verify_v5_private_openings_from_proof.closure_4.Insts.CoreOpsFunctionFnOnceTupleStateOnlyPrivateOpeningErrorV5PrivateOpeningError.call_once,
                                core.result.Result.Insts.CoreOpsTry.branch,
                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                                at hsuccess
                          | Ok openingPair4 =>
                              rcases openingPair4 with ⟨opening4, remainder4⟩
                              simp [core.result.Result.map_err,
                                private_openings.verify_v5_private_openings_from_proof.closure_4.Insts.CoreOpsFunctionFnOnceTupleStateOnlyPrivateOpeningErrorV5PrivateOpeningError.call_once,
                                core.result.Result.Insts.CoreOpsTry.branch]
                                at hsuccess
                              simp [Aeneas.Std.lift] at hsuccess
                              rcases hsuccess with ⟨hverified, hremainder⟩
                              refine ⟨{
                                layer0Leaves := layer0Leaves
                                indices := indices
                                rootsArray := rootsArray
                                tags := tags
                                topology := topology
                                root0 := root0
                                root1 := root1
                                root2 := root2
                                root3 := root3
                                root4 := root4
                                depth0 := depth0
                                depth1 := depth1
                                depth2 := depth2
                                depth3 := depth3
                                depth4 := depth4
                                tag0 := tag0
                                tag1 := tag1
                                tag2 := tag2
                                tag3 := tag3
                                tag4 := tag4
                                width0 := width0
                                width1 := width1
                                width2 := width2
                                width3 := width3
                                width4 := width4
                                queryArray0 := queryArray0
                                queryArray1 := queryArray1
                                queryArray2 := queryArray2
                                opening0 := opening0
                                opening1 := opening1
                                opening2 := opening2
                                opening3 := opening3
                                opening4 := opening4
                                remainder0 := remainder0
                                remainder1 := remainder1
                                remainder2 := remainder2
                                remainder3 := remainder3
                                remainder4 := remainder4
                                level1 := level1
                                next1 := next1
                                level2 := level2
                                next2 := next2
                                level3 := level3
                                next3 := next3
                                level4 := level4
                                next4 := next4
                                level5 := level5
                                next5 := next5
                                bytesConsumed :=
                                  Std.Usize.wrapping_sub (Slice.len proofBytes)
                                    (Slice.len remainder4)
                                layer0Leaves_eq := hlayer0Leaves
                                indices_eq := hqueryResult
                                roots_eq := hroots
                                tags_eq := htags
                                root0_eq := hroot0
                                root1_eq := hroot1
                                root2_eq := hroot2
                                root3_eq := hroot3
                                root4_eq := hroot4
                                depth0_eq := hdepth0
                                depth1_eq := hdepth1
                                depth2_eq := hdepth2
                                depth3_eq := hdepth3
                                depth4_eq := hdepth4
                                tag0_eq := htag0
                                tag1_eq := htag1
                                tag2_eq := htag2
                                tag3_eq := htag3
                                tag4_eq := htag4
                                width0_eq := hwidth0
                                width1_eq := hwidth1
                                width2_eq := hwidth2
                                width3_eq := hwidth3
                                width4_eq := hwidth4
                                queryArray0_eq := hqueryArray0
                                queryArray1_eq := hqueryArray1
                                queryArray2_eq := hqueryArray2
                                topology_eq := htopologyOption
                                call0 := hcall0
                                call1 := hcall1
                                call2 := hcall2
                                call3 := hcall3
                                call4 := hcall4
                                bytesConsumed_eq := rfl
                                verified_eq := hverified.symm
                                remainder_eq := hremainder.symm
                              }⟩

theorem generated_verify_success_iff_from_proof_success_empty
    (roots : private_openings.V5PrivateOpeningRoots)
    (queries : Slice Std.U32) (proofBytes : Slice Std.U8)
    (verified : private_openings.VerifiedV5PrivateOpenings) :
    private_openings.verify_v5_private_openings roots queries proofBytes =
        .ok (.Ok verified) ↔
      ∃ remainder,
        private_openings.verify_v5_private_openings_from_proof
            roots queries proofBytes = .ok (.Ok (verified, remainder)) ∧
        remainder.val = [] := by
  unfold private_openings.verify_v5_private_openings
  generalize hresult :
      private_openings.verify_v5_private_openings_from_proof
        roots queries proofBytes = result
  cases result with
  | fail error => simp [hresult]
  | div => simp [hresult]
  | ok inner =>
      cases inner with
      | Err error =>
          simp [hresult,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
      | Ok pair =>
          rcases pair with ⟨value, remainder⟩
          by_cases hempty : remainder.val = []
          · simp [hresult, hempty, core.slice.Slice.is_empty,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
          · simp [hresult, hempty, core.slice.Slice.is_empty,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]

/-- A successful result from the generated public driver determines the exact
five-section trace and proves that the final proof remainder is empty. -/
theorem generated_verify_success_yields_five_section_trace
    (roots : private_openings.V5PrivateOpeningRoots)
    (queries : Slice Std.U32) (proofBytes : Slice Std.U8)
    (verified : private_openings.VerifiedV5PrivateOpenings)
    (hverify :
      private_openings.verify_v5_private_openings roots queries proofBytes =
        .ok (.Ok verified)) :
    ∃ remainder,
      remainder.val = [] ∧
      Nonempty
        (GeneratedFiveSectionTrace roots queries proofBytes verified remainder) := by
  rcases
      (generated_verify_success_iff_from_proof_success_empty
        roots queries proofBytes verified).mp hverify with
    ⟨remainder, hfromProof, hremainder⟩
  exact ⟨remainder, hremainder,
    generated_from_proof_success_yields_five_section_trace
      roots queries proofBytes remainder verified hfromProof⟩

end V5MerkleGeneratedDriverInversion
