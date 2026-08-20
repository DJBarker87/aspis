import V5MerkleUnchangedFull.Funs
import Aeneas.Tactic.Simp.SimpScalar

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V5MerkleUnchangedDriverProof

open V5MerkleUnchangedFull

abbrev Digest := Array Std.U8 32#usize
abbrev Opening :=
  aspis_core.state_only_private_openings.StateOnlyPrivateOpening
abbrev HashBuffer := alloc.vec.Vec Digest
abbrev Topology := aspis_core.merkle.Radix4BinaryCapTopology
abbrev QueryIndices :=
  aspis_core.circle_line_merkle.CircleLineQueryIndices

theorem bind_eq_ok_iff {A B : Type} (x : Result A) (f : A → Result B)
    (y : B) :
    Bind.bind x f = .ok y ↔ ∃ value, x = .ok value ∧ f value = .ok y := by
  cases x <;> simp [Bind.bind, Aeneas.Std.bind]

private theorem range_next_0 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 0#usize, «end» := 5#usize } =
      .ok (some 0#usize, { start := 1#usize, «end» := 5#usize }) := by
  have hmax : 0 < UScalar.max UScalarTy.Usize := by scalar_tac
  simp [core.iter.range.IteratorRange.next, core.iter.range.StepUsize,
    core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked,
    core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt, hmax]

private theorem range_next_1 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 1#usize, «end» := 5#usize } =
      .ok (some 1#usize, { start := 2#usize, «end» := 5#usize }) := by
  have hmax : 1 < UScalar.max UScalarTy.Usize := by scalar_tac
  simp [core.iter.range.IteratorRange.next, core.iter.range.StepUsize,
    core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked,
    core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt, hmax]

private theorem range_next_2 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 2#usize, «end» := 5#usize } =
      .ok (some 2#usize, { start := 3#usize, «end» := 5#usize }) := by
  have hmax : 2 < UScalar.max UScalarTy.Usize := by scalar_tac
  simp [core.iter.range.IteratorRange.next, core.iter.range.StepUsize,
    core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked,
    core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt, hmax]

private theorem range_next_3 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 3#usize, «end» := 5#usize } =
      .ok (some 3#usize, { start := 4#usize, «end» := 5#usize }) := by
  have hmax : 3 < UScalar.max UScalarTy.Usize := by scalar_tac
  simp [core.iter.range.IteratorRange.next, core.iter.range.StepUsize,
    core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked,
    core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt, hmax]

private theorem range_next_4 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 4#usize, «end» := 5#usize } =
      .ok (some 4#usize, { start := 5#usize, «end» := 5#usize }) := by
  have hmax : 4 < UScalar.max UScalarTy.Usize := by scalar_tac
  simp [core.iter.range.IteratorRange.next, core.iter.range.StepUsize,
    core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked,
    core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt, hmax]

private theorem range_next_5 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 5#usize, «end» := 5#usize } =
      .ok (none, { start := 5#usize, «end» := 5#usize }) := by
  simp [core.iter.range.IteratorRange.next, core.iter.range.StepUsize,
    core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked,
    core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt]

/-- One successful iteration of the unchanged production five-section loop.
Every argument and every threaded output is retained literally. -/
structure GeneratedSectionCall
    (hash : Slice (Slice Std.U8) → Digest)
    (selected : Slice Std.U32) (roots : Array Digest 5#usize)
    (topology : Topology) (sectionIndex radixLevel : Std.Usize)
    (level0 next0 level1 next1 : HashBuffer)
    (remainder0 remainder1 : Slice Std.U8)
    (parsed0 parsed1 : Array (Option Opening) 5#usize) where
  root : Digest
  depth : Std.U32
  tags : Array Std.U8 5#usize
  tag : Std.U8
  width : Std.Usize
  opening : Opening
  root_eq : Array.index_usize roots sectionIndex = .ok root
  depth_eq :
    Array.index_usize private_openings.V5_PRIVATE_DEPTHS sectionIndex = .ok depth
  tags_eq : private_openings.V5_PRIVATE_TREE_TAGS = .ok tags
  tag_eq : Array.index_usize tags sectionIndex = .ok tag
  width_eq :
    Array.index_usize private_openings.V5_PRIVATE_VALUE_WIDTHS sectionIndex =
      .ok width
  helper_call :
    aspis_core.state_only_private_openings.verify_state_only_private_opening_from_proof_with_topology
        hash root depth tag width selected remainder0 topology radixLevel level0 next0 =
      .ok (.Ok (opening, remainder1), level1, next1)
  parsed_update :
    Array.update parsed0 sectionIndex (some opening) = .ok parsed1

private theorem selected_0 (s0 s1 s2 s3 s4 : Slice Std.U32) :
    Array.index_usize (Array.make 5#usize [s0, s1, s2, s3, s4]) 0#usize =
      .ok s0 := by
  simp [Array.index_usize, Array.make]

private theorem selected_1 (s0 s1 s2 s3 s4 : Slice Std.U32) :
    Array.index_usize (Array.make 5#usize [s0, s1, s2, s3, s4]) 1#usize =
      .ok s1 := by
  simp [Array.index_usize, Array.make]

private theorem selected_2 (s0 s1 s2 s3 s4 : Slice Std.U32) :
    Array.index_usize (Array.make 5#usize [s0, s1, s2, s3, s4]) 2#usize =
      .ok s2 := by
  simp [Array.index_usize, Array.make]

private theorem selected_3 (s0 s1 s2 s3 s4 : Slice Std.U32) :
    Array.index_usize (Array.make 5#usize [s0, s1, s2, s3, s4]) 3#usize =
      .ok s3 := by
  simp [Array.index_usize, Array.make]

private theorem selected_4 (s0 s1 s2 s3 s4 : Slice Std.U32) :
    Array.index_usize (Array.make 5#usize [s0, s1, s2, s3, s4]) 4#usize =
      .ok s4 := by
  simp [Array.index_usize, Array.make]

private theorem radix_0 :
    (if 0#usize < 2#usize then ok 0#usize
      else ok (Std.Usize.wrapping_sub 0#usize 1#usize)) =
        (.ok 0#usize : Result Std.Usize) := by simp

private theorem radix_1 :
    (if 1#usize < 2#usize then ok 0#usize
      else ok (Std.Usize.wrapping_sub 1#usize 1#usize)) =
        (.ok 0#usize : Result Std.Usize) := by simp

private theorem radix_2 :
    (if 2#usize < 2#usize then ok 0#usize
      else ok (Std.Usize.wrapping_sub 2#usize 1#usize)) =
        (.ok 1#usize : Result Std.Usize) := by
  simp
  apply UScalar.eq_of_val_eq
  cases h : System.Platform.numBits_eq <;>
    simp_all [Usize.size, Usize.numBits, UScalarTy.numBits]

private theorem radix_3 :
    (if 3#usize < 2#usize then ok 0#usize
      else ok (Std.Usize.wrapping_sub 3#usize 1#usize)) =
        (.ok 2#usize : Result Std.Usize) := by
  simp
  apply UScalar.eq_of_val_eq
  cases h : System.Platform.numBits_eq <;>
    simp_all [Usize.size, Usize.numBits, UScalarTy.numBits]

private theorem radix_4 :
    (if 4#usize < 2#usize then ok 0#usize
      else ok (Std.Usize.wrapping_sub 4#usize 1#usize)) =
        (.ok 3#usize : Result Std.Usize) := by
  simp
  apply UScalar.eq_of_val_eq
  cases h : System.Platform.numBits_eq <;>
    simp_all [Usize.size, Usize.numBits, UScalarTy.numBits]

private theorem body_cont_yields_call
    (hash : Slice (Slice Std.U8) → Digest)
    (s0 s1 s2 s3 s4 selected : Slice Std.U32)
    (roots : Array Digest 5#usize) (topology : Topology)
    (sectionIndex nextSection radixLevel : Std.Usize)
    (iterOut : core.ops.range.Range Std.Usize)
    (level0 next0 level1 next1 : HashBuffer)
    (remainder0 remainder1 : Slice Std.U8)
    (parsed0 parsed1 : Array (Option Opening) 5#usize)
    (hnext :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize
          { start := sectionIndex, «end» := 5#usize } =
        .ok (some sectionIndex,
          { start := nextSection, «end» := 5#usize }))
    (hselected :
      Array.index_usize (Array.make 5#usize [s0, s1, s2, s3, s4]) sectionIndex =
        .ok selected)
    (hradix :
      (if sectionIndex < 2#usize
        then ok 0#usize
        else ok (Std.Usize.wrapping_sub sectionIndex 1#usize)) =
          (.ok radixLevel : Result Std.Usize))
    (hbody :
      private_openings.verify_v5_private_openings_from_proof_loop.body
          hash s0 s1 s2 s3 s4 roots topology
          { start := sectionIndex, «end» := 5#usize }
          level0 next0 remainder0 parsed0 =
        .ok (.cont
          (iterOut, level1, next1, remainder1, parsed1))) :
    iterOut = { start := nextSection, «end» := 5#usize } ∧
    Nonempty
      (GeneratedSectionCall hash selected roots topology sectionIndex radixLevel
        level0 next0 level1 next1 remainder0 remainder1 parsed0 parsed1) := by
  unfold private_openings.verify_v5_private_openings_from_proof_loop.body at hbody
  simp only [hnext, bind_tc_ok] at hbody
  rw [bind_eq_ok_iff] at hbody
  rcases hbody with ⟨root, hroot, hbody⟩
  rw [bind_eq_ok_iff] at hbody
  rcases hbody with ⟨depth, hdepth, hbody⟩
  rw [bind_eq_ok_iff] at hbody
  rcases hbody with ⟨tags, htags, hbody⟩
  rw [bind_eq_ok_iff] at hbody
  rcases hbody with ⟨tag, htag, hbody⟩
  rw [bind_eq_ok_iff] at hbody
  rcases hbody with ⟨width, hwidth, hbody⟩
  simp only [hselected, bind_tc_ok] at hbody
  by_cases hsmall : sectionIndex < 2#usize
  all_goals
    simp only [hsmall, ↓reduceIte] at hradix hbody
    injection hradix with hradixValue
    subst radixLevel
    rw [bind_eq_ok_iff] at hbody
    rcases hbody with ⟨helperResult, hcall, hbody⟩
    rcases helperResult with ⟨openingResult, outLevel, outNext⟩
    cases openingResult with
    | Err openingError =>
        unfold core.result.Result.map_err at hbody
        simp [
          private_openings.verify_v5_private_openings_from_proof.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyPrivateOpeningErrorV5PrivateOpeningError.call_once,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
          at hbody
        simp [lift] at hbody
    | Ok openingPair =>
        rcases openingPair with ⟨opening, nextRemainder⟩
        unfold core.result.Result.map_err at hbody
        simp [core.result.Result.Insts.CoreOpsTry.branch] at hbody
        rw [bind_eq_ok_iff] at hbody
        rcases hbody with ⟨updated, hupdate, hout⟩
        simp at hout
        rcases hout with ⟨hiter, rfl, rfl, rfl, rfl⟩
        exact ⟨hiter.symm, ⟨{
          root := root
          depth := depth
          tags := tags
          tag := tag
          width := width
          opening := opening
          root_eq := hroot
          depth_eq := hdepth
          tags_eq := htags
          tag_eq := htag
          width_eq := hwidth
          helper_call := hcall
          parsed_update := hupdate
        }⟩⟩

private theorem active_body_ne_done_none
    (hash : Slice (Slice Std.U8) → Digest)
    (s0 s1 s2 s3 s4 selected : Slice Std.U32)
    (roots : Array Digest 5#usize) (topology : Topology)
    (sectionIndex nextSection radixLevel : Std.Usize)
    (level0 next0 : HashBuffer) (remainder0 finalRemainder : Slice Std.U8)
    (parsed0 finalParsed : Array (Option Opening) 5#usize)
    (hnext :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize
          { start := sectionIndex, «end» := 5#usize } =
        .ok (some sectionIndex,
          { start := nextSection, «end» := 5#usize }))
    (hselected :
      Array.index_usize (Array.make 5#usize [s0, s1, s2, s3, s4]) sectionIndex =
        .ok selected)
    (hradix :
      (if sectionIndex < 2#usize
        then ok 0#usize
        else ok (Std.Usize.wrapping_sub sectionIndex 1#usize)) =
          (.ok radixLevel : Result Std.Usize)) :
    private_openings.verify_v5_private_openings_from_proof_loop.body
        hash s0 s1 s2 s3 s4 roots topology
        { start := sectionIndex, «end» := 5#usize }
        level0 next0 remainder0 parsed0 ≠
      .ok (.done (finalRemainder, finalParsed, none)) := by
  intro hbody
  unfold private_openings.verify_v5_private_openings_from_proof_loop.body at hbody
  simp only [hnext, bind_tc_ok] at hbody
  rw [bind_eq_ok_iff] at hbody
  rcases hbody with ⟨root, hroot, hbody⟩
  rw [bind_eq_ok_iff] at hbody
  rcases hbody with ⟨depth, hdepth, hbody⟩
  rw [bind_eq_ok_iff] at hbody
  rcases hbody with ⟨tags, htags, hbody⟩
  rw [bind_eq_ok_iff] at hbody
  rcases hbody with ⟨tag, htag, hbody⟩
  rw [bind_eq_ok_iff] at hbody
  rcases hbody with ⟨width, hwidth, hbody⟩
  simp only [hselected, bind_tc_ok] at hbody
  by_cases hsmall : sectionIndex < 2#usize
  all_goals
    simp only [hsmall, ↓reduceIte] at hradix hbody
    injection hradix with hradixValue
    subst radixLevel
    rw [bind_eq_ok_iff] at hbody
    rcases hbody with ⟨helperResult, hcall, hbody⟩
    rcases helperResult with ⟨openingResult, outLevel, outNext⟩
    cases openingResult with
    | Err openingError =>
        unfold core.result.Result.map_err at hbody
        simp [
          private_openings.verify_v5_private_openings_from_proof.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyPrivateOpeningErrorV5PrivateOpeningError.call_once,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
          at hbody
        simp [lift] at hbody
    | Ok openingPair =>
        rcases openingPair with ⟨opening, nextRemainder⟩
        unfold core.result.Result.map_err at hbody
        simp [core.result.Result.Insts.CoreOpsTry.branch] at hbody
        rw [bind_eq_ok_iff] at hbody
        rcases hbody with ⟨updated, hupdate, hout⟩
        simp at hout

private theorem active_body_ne_done_some_ok
    (hash : Slice (Slice Std.U8) → Digest)
    (s0 s1 s2 s3 s4 selected : Slice Std.U32)
    (roots : Array Digest 5#usize) (topology : Topology)
    (sectionIndex nextSection radixLevel : Std.Usize)
    (level0 next0 : HashBuffer) (remainder0 finalRemainder : Slice Std.U8)
    (parsed0 finalParsed : Array (Option Opening) 5#usize)
    (accepted : private_openings.VerifiedV5PrivateOpenings × Slice Std.U8)
    (hnext :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize
          { start := sectionIndex, «end» := 5#usize } =
        .ok (some sectionIndex,
          { start := nextSection, «end» := 5#usize }))
    (hselected :
      Array.index_usize (Array.make 5#usize [s0, s1, s2, s3, s4]) sectionIndex =
        .ok selected)
    (hradix :
      (if sectionIndex < 2#usize
        then ok 0#usize
        else ok (Std.Usize.wrapping_sub sectionIndex 1#usize)) =
          (.ok radixLevel : Result Std.Usize)) :
    private_openings.verify_v5_private_openings_from_proof_loop.body
        hash s0 s1 s2 s3 s4 roots topology
        { start := sectionIndex, «end» := 5#usize }
        level0 next0 remainder0 parsed0 ≠
      .ok (.done (finalRemainder, finalParsed, some (.Ok accepted))) := by
  intro hbody
  unfold private_openings.verify_v5_private_openings_from_proof_loop.body at hbody
  simp only [hnext, bind_tc_ok] at hbody
  rw [bind_eq_ok_iff] at hbody
  rcases hbody with ⟨root, hroot, hbody⟩
  rw [bind_eq_ok_iff] at hbody
  rcases hbody with ⟨depth, hdepth, hbody⟩
  rw [bind_eq_ok_iff] at hbody
  rcases hbody with ⟨tags, htags, hbody⟩
  rw [bind_eq_ok_iff] at hbody
  rcases hbody with ⟨tag, htag, hbody⟩
  rw [bind_eq_ok_iff] at hbody
  rcases hbody with ⟨width, hwidth, hbody⟩
  simp only [hselected, bind_tc_ok] at hbody
  by_cases hsmall : sectionIndex < 2#usize
  all_goals
    simp only [hsmall, ↓reduceIte] at hradix hbody
    injection hradix with hradixValue
    subst radixLevel
    rw [bind_eq_ok_iff] at hbody
    rcases hbody with ⟨helperResult, hcall, hbody⟩
    rcases helperResult with ⟨openingResult, outLevel, outNext⟩
    cases openingResult with
    | Err openingError =>
        unfold core.result.Result.map_err at hbody
        simp [
          private_openings.verify_v5_private_openings_from_proof.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyPrivateOpeningErrorV5PrivateOpeningError.call_once,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
          at hbody
        simp [lift] at hbody
    | Ok openingPair =>
        rcases openingPair with ⟨opening, nextRemainder⟩
        unfold core.result.Result.map_err at hbody
        simp [core.result.Result.Insts.CoreOpsTry.branch] at hbody
        rw [bind_eq_ok_iff] at hbody
        rcases hbody with ⟨updated, hupdate, hout⟩
        simp at hout

private theorem loop_active_step
    (hash : Slice (Slice Std.U8) → Digest)
    (s0 s1 s2 s3 s4 selected : Slice Std.U32)
    (roots : Array Digest 5#usize) (topology : Topology)
    (sectionIndex nextSection radixLevel : Std.Usize)
    (level0 next0 : HashBuffer) (remainder0 : Slice Std.U8)
    (parsed0 : Array (Option Opening) 5#usize)
    (finalRemainder : Slice Std.U8)
    (finalParsed : Array (Option Opening) 5#usize)
    (hnext :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize
          { start := sectionIndex, «end» := 5#usize } =
        .ok (some sectionIndex,
          { start := nextSection, «end» := 5#usize }))
    (hselected :
      Array.index_usize (Array.make 5#usize [s0, s1, s2, s3, s4]) sectionIndex =
        .ok selected)
    (hradix :
      (if sectionIndex < 2#usize
        then ok 0#usize
        else ok (Std.Usize.wrapping_sub sectionIndex 1#usize)) =
          (.ok radixLevel : Result Std.Usize))
    (hloop :
      private_openings.verify_v5_private_openings_from_proof_loop
          { start := sectionIndex, «end» := 5#usize }
          hash s0 s1 s2 s3 s4 roots topology level0 next0 remainder0 parsed0 =
        .ok (finalRemainder, finalParsed, none)) :
    ∃ level1 next1 remainder1 parsed1,
      Nonempty
        (GeneratedSectionCall hash selected roots topology sectionIndex radixLevel
          level0 next0 level1 next1 remainder0 remainder1 parsed0 parsed1) ∧
      private_openings.verify_v5_private_openings_from_proof_loop
          { start := nextSection, «end» := 5#usize }
          hash s0 s1 s2 s3 s4 roots topology level1 next1 remainder1 parsed1 =
        .ok (finalRemainder, finalParsed, none) := by
  unfold private_openings.verify_v5_private_openings_from_proof_loop at hloop
  rw [loop.eq_def] at hloop
  simp only at hloop
  generalize hbodyResult :
      private_openings.verify_v5_private_openings_from_proof_loop.body
          hash s0 s1 s2 s3 s4 roots topology
          { start := sectionIndex, «end» := 5#usize }
          level0 next0 remainder0 parsed0 = bodyResult at hloop
  cases bodyResult with
  | fail error =>
      simp only at hloop
      cases hloop
  | div =>
      simp only at hloop
      cases hloop
  | ok flow =>
      cases flow with
      | done early =>
          simp only at hloop
          injection hloop with hearly
          subst early
          exact False.elim
            ((active_body_ne_done_none hash s0 s1 s2 s3 s4 selected roots
              topology sectionIndex nextSection radixLevel level0 next0
              remainder0 finalRemainder parsed0 finalParsed hnext hselected hradix)
              hbodyResult)
      | cont state =>
          rcases state with ⟨iterOut, level1, next1, remainder1, parsed1⟩
          simp only at hloop
          obtain ⟨hiter, hcall⟩ :=
            body_cont_yields_call hash s0 s1 s2 s3 s4 selected roots topology
              sectionIndex nextSection radixLevel iterOut level0 next0 level1
              next1 remainder0 remainder1 parsed0 parsed1 hnext hselected hradix
              hbodyResult
          subst iterOut
          exact ⟨level1, next1, remainder1, parsed1, hcall,
            by simpa [private_openings.verify_v5_private_openings_from_proof_loop]
              using hloop⟩

private theorem loop_active_step_some_ok
    (hash : Slice (Slice Std.U8) → Digest)
    (s0 s1 s2 s3 s4 selected : Slice Std.U32)
    (roots : Array Digest 5#usize) (topology : Topology)
    (sectionIndex nextSection radixLevel : Std.Usize)
    (level0 next0 : HashBuffer) (remainder0 : Slice Std.U8)
    (parsed0 : Array (Option Opening) 5#usize)
    (finalRemainder : Slice Std.U8)
    (finalParsed : Array (Option Opening) 5#usize)
    (accepted : private_openings.VerifiedV5PrivateOpenings × Slice Std.U8)
    (hnext :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize
          { start := sectionIndex, «end» := 5#usize } =
        .ok (some sectionIndex,
          { start := nextSection, «end» := 5#usize }))
    (hselected :
      Array.index_usize (Array.make 5#usize [s0, s1, s2, s3, s4]) sectionIndex =
        .ok selected)
    (hradix :
      (if sectionIndex < 2#usize
        then ok 0#usize
        else ok (Std.Usize.wrapping_sub sectionIndex 1#usize)) =
          (.ok radixLevel : Result Std.Usize))
    (hloop :
      private_openings.verify_v5_private_openings_from_proof_loop
          { start := sectionIndex, «end» := 5#usize }
          hash s0 s1 s2 s3 s4 roots topology level0 next0 remainder0 parsed0 =
        .ok (finalRemainder, finalParsed, some (.Ok accepted))) :
    ∃ level1 next1 remainder1 parsed1,
      Nonempty
        (GeneratedSectionCall hash selected roots topology sectionIndex radixLevel
          level0 next0 level1 next1 remainder0 remainder1 parsed0 parsed1) ∧
      private_openings.verify_v5_private_openings_from_proof_loop
          { start := nextSection, «end» := 5#usize }
          hash s0 s1 s2 s3 s4 roots topology level1 next1 remainder1 parsed1 =
        .ok (finalRemainder, finalParsed, some (.Ok accepted)) := by
  unfold private_openings.verify_v5_private_openings_from_proof_loop at hloop
  rw [loop.eq_def] at hloop
  simp only at hloop
  generalize hbodyResult :
      private_openings.verify_v5_private_openings_from_proof_loop.body
          hash s0 s1 s2 s3 s4 roots topology
          { start := sectionIndex, «end» := 5#usize }
          level0 next0 remainder0 parsed0 = bodyResult at hloop
  cases bodyResult with
  | fail error =>
      simp only at hloop
      cases hloop
  | div =>
      simp only at hloop
      cases hloop
  | ok flow =>
      cases flow with
      | done early =>
          simp only at hloop
          injection hloop with hearly
          subst early
          exact False.elim
            ((active_body_ne_done_some_ok hash s0 s1 s2 s3 s4 selected roots
              topology sectionIndex nextSection radixLevel level0 next0
              remainder0 finalRemainder parsed0 finalParsed accepted hnext
              hselected hradix) hbodyResult)
      | cont state =>
          rcases state with ⟨iterOut, level1, next1, remainder1, parsed1⟩
          simp only at hloop
          obtain ⟨hiter, hcall⟩ :=
            body_cont_yields_call hash s0 s1 s2 s3 s4 selected roots topology
              sectionIndex nextSection radixLevel iterOut level0 next0 level1
              next1 remainder0 remainder1 parsed0 parsed1 hnext hselected hradix
              hbodyResult
          subst iterOut
          exact ⟨level1, next1, remainder1, parsed1, hcall,
            by simpa [private_openings.verify_v5_private_openings_from_proof_loop]
              using hloop⟩

private theorem body_at_5_done
    (hash : Slice (Slice Std.U8) → Digest)
    (s0 s1 s2 s3 s4 : Slice Std.U32)
    (roots : Array Digest 5#usize) (topology : Topology)
    (level next : HashBuffer) (remainder : Slice Std.U8)
    (parsed : Array (Option Opening) 5#usize) :
    private_openings.verify_v5_private_openings_from_proof_loop.body
        hash s0 s1 s2 s3 s4 roots topology
        { start := 5#usize, «end» := 5#usize }
        level next remainder parsed =
      .ok (.done (remainder, parsed, none)) := by
  unfold private_openings.verify_v5_private_openings_from_proof_loop.body
  simp only [range_next_5, bind_tc_ok]

private theorem loop_at_5_done
    (hash : Slice (Slice Std.U8) → Digest)
    (s0 s1 s2 s3 s4 : Slice Std.U32)
    (roots : Array Digest 5#usize) (topology : Topology)
    (level next : HashBuffer) (remainder : Slice Std.U8)
    (parsed : Array (Option Opening) 5#usize) :
    private_openings.verify_v5_private_openings_from_proof_loop
        { start := 5#usize, «end» := 5#usize }
        hash s0 s1 s2 s3 s4 roots topology level next remainder parsed =
      .ok (remainder, parsed, none) := by
  unfold private_openings.verify_v5_private_openings_from_proof_loop
  rw [loop.eq_def]
  simp only
  rw [body_at_5_done]

/-- The lowered early-return slot can only carry an error.  In particular,
the exact five-section loop cannot report an accepted value through that
slot. -/
theorem generated_loop_ne_some_ok
    (hash : Slice (Slice Std.U8) → Digest)
    (s0 s1 s2 s3 s4 : Slice Std.U32)
    (roots : Array Digest 5#usize) (topology : Topology)
    (level0 next0 : HashBuffer) (proofBytes finalRemainder : Slice Std.U8)
    (parsed0 finalParsed : Array (Option Opening) 5#usize)
    (accepted : private_openings.VerifiedV5PrivateOpenings × Slice Std.U8) :
    private_openings.verify_v5_private_openings_from_proof_loop
        { start := 0#usize, «end» := 5#usize }
        hash s0 s1 s2 s3 s4 roots topology level0 next0 proofBytes parsed0 ≠
      .ok (finalRemainder, finalParsed, some (.Ok accepted)) := by
  intro hloop
  obtain ⟨level1, next1, remainder1, parsed1, _call0, hloop1⟩ :=
    loop_active_step_some_ok hash s0 s1 s2 s3 s4 s0 roots topology
      0#usize 1#usize 0#usize level0 next0 proofBytes parsed0
      finalRemainder finalParsed accepted range_next_0
      (selected_0 s0 s1 s2 s3 s4) radix_0 hloop
  obtain ⟨level2, next2, remainder2, parsed2, _call1, hloop2⟩ :=
    loop_active_step_some_ok hash s0 s1 s2 s3 s4 s1 roots topology
      1#usize 2#usize 0#usize level1 next1 remainder1 parsed1
      finalRemainder finalParsed accepted range_next_1
      (selected_1 s0 s1 s2 s3 s4) radix_1 hloop1
  obtain ⟨level3, next3, remainder3, parsed3, _call2, hloop3⟩ :=
    loop_active_step_some_ok hash s0 s1 s2 s3 s4 s2 roots topology
      2#usize 3#usize 1#usize level2 next2 remainder2 parsed2
      finalRemainder finalParsed accepted range_next_2
      (selected_2 s0 s1 s2 s3 s4) radix_2 hloop2
  obtain ⟨level4, next4, remainder4, parsed4, _call3, hloop4⟩ :=
    loop_active_step_some_ok hash s0 s1 s2 s3 s4 s3 roots topology
      3#usize 4#usize 2#usize level3 next3 remainder3 parsed3
      finalRemainder finalParsed accepted range_next_3
      (selected_3 s0 s1 s2 s3 s4) radix_3 hloop3
  obtain ⟨level5, next5, remainder5, parsed5, _call4, hloop5⟩ :=
    loop_active_step_some_ok hash s0 s1 s2 s3 s4 s4 roots topology
      4#usize 5#usize 3#usize level4 next4 remainder4 parsed4
      finalRemainder finalParsed accepted range_next_4
      (selected_4 s0 s1 s2 s3 s4) radix_4 hloop4
  rw [loop_at_5_done] at hloop5
  simp at hloop5

/-- Exact call chain retained by a successful execution of the unchanged
`0..5` production loop. -/
structure GeneratedFiveCallTrace
    (hash : Slice (Slice Std.U8) → Digest)
    (s0 s1 s2 s3 s4 : Slice Std.U32)
    (roots : Array Digest 5#usize) (topology : Topology)
    (level0 next0 : HashBuffer) (proofBytes : Slice Std.U8)
    (parsed0 : Array (Option Opening) 5#usize)
    (finalRemainder : Slice Std.U8)
    (finalParsed : Array (Option Opening) 5#usize) where
  level1 : HashBuffer
  next1 : HashBuffer
  remainder1 : Slice Std.U8
  parsed1 : Array (Option Opening) 5#usize
  level2 : HashBuffer
  next2 : HashBuffer
  remainder2 : Slice Std.U8
  parsed2 : Array (Option Opening) 5#usize
  level3 : HashBuffer
  next3 : HashBuffer
  remainder3 : Slice Std.U8
  parsed3 : Array (Option Opening) 5#usize
  level4 : HashBuffer
  next4 : HashBuffer
  remainder4 : Slice Std.U8
  parsed4 : Array (Option Opening) 5#usize
  level5 : HashBuffer
  next5 : HashBuffer
  call0 : GeneratedSectionCall hash s0 roots topology 0#usize 0#usize
    level0 next0 level1 next1 proofBytes remainder1 parsed0 parsed1
  call1 : GeneratedSectionCall hash s1 roots topology 1#usize 0#usize
    level1 next1 level2 next2 remainder1 remainder2 parsed1 parsed2
  call2 : GeneratedSectionCall hash s2 roots topology 2#usize 1#usize
    level2 next2 level3 next3 remainder2 remainder3 parsed2 parsed3
  call3 : GeneratedSectionCall hash s3 roots topology 3#usize 2#usize
    level3 next3 level4 next4 remainder3 remainder4 parsed3 parsed4
  call4 : GeneratedSectionCall hash s4 roots topology 4#usize 3#usize
    level4 next4 level5 next5 remainder4 finalRemainder parsed4 finalParsed

/-- A successful result from the exact Aeneas translation of the unchanged
production `0..5` loop determines all five helper calls in source order. -/
theorem generated_loop_success_yields_five_call_trace
    (hash : Slice (Slice Std.U8) → Digest)
    (s0 s1 s2 s3 s4 : Slice Std.U32)
    (roots : Array Digest 5#usize) (topology : Topology)
    (level0 next0 : HashBuffer) (proofBytes : Slice Std.U8)
    (parsed0 : Array (Option Opening) 5#usize)
    (finalRemainder : Slice Std.U8)
    (finalParsed : Array (Option Opening) 5#usize)
    (hloop :
      private_openings.verify_v5_private_openings_from_proof_loop
          { start := 0#usize, «end» := 5#usize }
          hash s0 s1 s2 s3 s4 roots topology level0 next0 proofBytes parsed0 =
        .ok (finalRemainder, finalParsed, none)) :
    Nonempty
      (GeneratedFiveCallTrace hash s0 s1 s2 s3 s4 roots topology level0 next0
        proofBytes parsed0 finalRemainder finalParsed) := by
  obtain ⟨level1, next1, remainder1, parsed1, call0, hloop1⟩ :=
    loop_active_step hash s0 s1 s2 s3 s4 s0 roots topology
      0#usize 1#usize 0#usize level0 next0 proofBytes parsed0
      finalRemainder finalParsed range_next_0 (selected_0 s0 s1 s2 s3 s4)
      radix_0 hloop
  obtain ⟨level2, next2, remainder2, parsed2, call1, hloop2⟩ :=
    loop_active_step hash s0 s1 s2 s3 s4 s1 roots topology
      1#usize 2#usize 0#usize level1 next1 remainder1 parsed1
      finalRemainder finalParsed range_next_1 (selected_1 s0 s1 s2 s3 s4)
      radix_1 hloop1
  obtain ⟨level3, next3, remainder3, parsed3, call2, hloop3⟩ :=
    loop_active_step hash s0 s1 s2 s3 s4 s2 roots topology
      2#usize 3#usize 1#usize level2 next2 remainder2 parsed2
      finalRemainder finalParsed range_next_2 (selected_2 s0 s1 s2 s3 s4)
      radix_2 hloop2
  obtain ⟨level4, next4, remainder4, parsed4, call3, hloop4⟩ :=
    loop_active_step hash s0 s1 s2 s3 s4 s3 roots topology
      3#usize 4#usize 2#usize level3 next3 remainder3 parsed3
      finalRemainder finalParsed range_next_3 (selected_3 s0 s1 s2 s3 s4)
      radix_3 hloop3
  obtain ⟨level5, next5, remainder5, parsed5, call4, hloop5⟩ :=
    loop_active_step hash s0 s1 s2 s3 s4 s4 roots topology
      4#usize 5#usize 3#usize level4 next4 remainder4 parsed4
      finalRemainder finalParsed range_next_4 (selected_4 s0 s1 s2 s3 s4)
      radix_4 hloop4
  rw [loop_at_5_done] at hloop5
  simp at hloop5
  rcases hloop5 with ⟨hremainder, hparsed⟩
  subst finalRemainder
  subst finalParsed
  rcases call0 with ⟨call0⟩
  rcases call1 with ⟨call1⟩
  rcases call2 with ⟨call2⟩
  rcases call3 with ⟨call3⟩
  rcases call4 with ⟨call4⟩
  exact ⟨{
    level1 := level1
    next1 := next1
    remainder1 := remainder1
    parsed1 := parsed1
    level2 := level2
    next2 := next2
    remainder2 := remainder2
    parsed2 := parsed2
    level3 := level3
    next3 := next3
    remainder3 := remainder3
    parsed3 := parsed3
    level4 := level4
    next4 := next4
    remainder4 := remainder4
    parsed4 := parsed4
    level5 := level5
    next5 := next5
    call0 := call0
    call1 := call1
    call2 := call2
    call3 := call3
    call4 := call4
  }⟩

/-- The exact metadata and five-call loop selected by a successful generated
`verify_v5_private_openings_from_proof` execution. -/
structure GeneratedFromProofCallTrace
    (hash : Slice (Slice Std.U8) → Digest)
    (roots : private_openings.V5PrivateOpeningRoots)
    (queries : Slice Std.U32) (proofBytes : Slice Std.U8)
    (verified : private_openings.VerifiedV5PrivateOpenings)
    (remainder : Slice Std.U8) where
  layer0Leaves : Std.Usize
  indices : QueryIndices
  later0 : alloc.vec.Vec Std.U32
  later1 : alloc.vec.Vec Std.U32
  later2 : alloc.vec.Vec Std.U32
  rootsArray : Array Digest 5#usize
  depth0 : Std.U32
  topology : Topology
  finalRemainder : Slice Std.U8
  finalParsed : Array (Option Opening) 5#usize
  layer0Leaves_eq :
    private_openings.V5_PRIVATE_LAYER0_LEAVES = .ok layer0Leaves
  indices_eq :
    aspis_core.circle_line_merkle.derive_circle_line_query_indices_for_count
      queries layer0Leaves = .ok (.Ok indices)
  later0_eq : Array.index_usize indices.later 0#usize = .ok later0
  later1_eq : Array.index_usize indices.later 1#usize = .ok later1
  later2_eq : Array.index_usize indices.later 2#usize = .ok later2
  roots_eq : roots.as_array = .ok rootsArray
  depth0_eq :
    Array.index_usize private_openings.V5_PRIVATE_DEPTHS 0#usize = .ok depth0
  topology_eq :
    aspis_core.merkle.Radix4BinaryCapTopology.new depth0
      (alloc.vec.Vec.deref indices.layer0) = .ok (some topology)
  callTrace : Nonempty
    (GeneratedFiveCallTrace hash
      (alloc.vec.Vec.deref indices.layer0)
      (alloc.vec.Vec.deref indices.layer0)
      (alloc.vec.Vec.deref later0)
      (alloc.vec.Vec.deref later1)
      (alloc.vec.Vec.deref later2)
      rootsArray topology
      (alloc.vec.Vec.with_capacity Digest (alloc.vec.Vec.len indices.layer0))
      (alloc.vec.Vec.with_capacity Digest (alloc.vec.Vec.len indices.layer0))
      proofBytes (Array.repeat 5#usize none) finalRemainder finalParsed)
  returned_remainder_eq : finalRemainder = remainder

theorem generated_from_proof_success_yields_call_trace
    (hash : Slice (Slice Std.U8) → Digest)
    (roots : private_openings.V5PrivateOpeningRoots)
    (queries : Slice Std.U32) (proofBytes remainder : Slice Std.U8)
    (verified : private_openings.VerifiedV5PrivateOpenings)
    (hsuccess :
      private_openings.verify_v5_private_openings_from_proof
        hash roots queries proofBytes = .ok (.Ok (verified, remainder))) :
    Nonempty
      (GeneratedFromProofCallTrace hash roots queries proofBytes verified
        remainder) := by
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
      rcases hsuccess with ⟨later0, hlater0, hsuccess⟩
      rw [bind_eq_ok_iff] at hsuccess
      rcases hsuccess with ⟨later1, hlater1, hsuccess⟩
      rw [bind_eq_ok_iff] at hsuccess
      rcases hsuccess with ⟨later2, hlater2, hsuccess⟩
      rw [bind_eq_ok_iff] at hsuccess
      rcases hsuccess with ⟨rootsArray, hroots, hsuccess⟩
      rw [bind_eq_ok_iff] at hsuccess
      rcases hsuccess with ⟨depth0, hdepth0, hsuccess⟩
      rw [bind_eq_ok_iff] at hsuccess
      rcases hsuccess with ⟨topologyOption, htopologyOption, hsuccess⟩
      cases topologyOption with
      | none =>
          simp [core.option.Option.ok_or,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
            at hsuccess
      | some topology =>
          simp [core.option.Option.ok_or] at hsuccess
          rw [bind_eq_ok_iff] at hsuccess
          rcases hsuccess with ⟨loopResult, hloop, hsuccess⟩
          rcases loopResult with ⟨finalRemainder, finalParsed, pending⟩
          cases pending with
          | some pendingResult =>
              simp at hsuccess
              subst pendingResult
              exfalso
              apply generated_loop_ne_some_ok hash
                (alloc.vec.Vec.deref indices.layer0)
                (alloc.vec.Vec.deref indices.layer0)
                (alloc.vec.Vec.deref later0)
                (alloc.vec.Vec.deref later1)
                (alloc.vec.Vec.deref later2)
                rootsArray topology
                (alloc.vec.Vec.with_capacity Digest
                  (alloc.vec.Vec.len indices.layer0))
                (alloc.vec.Vec.with_capacity Digest
                  (alloc.vec.Vec.len indices.layer0))
                proofBytes finalRemainder (Array.repeat 5#usize none)
                finalParsed (verified, remainder)
              simpa [private_openings.V5_PRIVATE_SECTION_COUNT] using hloop
          | none =>
              simp only at hsuccess
              rw [bind_eq_ok_iff] at hsuccess
              rcases hsuccess with ⟨bytesConsumed, hbytesConsumed, hsuccess⟩
              rw [bind_eq_ok_iff] at hsuccess
              rcases hsuccess with ⟨option0, hoption0, hsuccess⟩
              rw [bind_eq_ok_iff] at hsuccess
              rcases hsuccess with ⟨opening0, hopening0, hsuccess⟩
              rw [bind_eq_ok_iff] at hsuccess
              rcases hsuccess with ⟨option1, hoption1, hsuccess⟩
              rw [bind_eq_ok_iff] at hsuccess
              rcases hsuccess with ⟨opening1, hopening1, hsuccess⟩
              rw [bind_eq_ok_iff] at hsuccess
              rcases hsuccess with ⟨option2, hoption2, hsuccess⟩
              rw [bind_eq_ok_iff] at hsuccess
              rcases hsuccess with ⟨opening2, hopening2, hsuccess⟩
              rw [bind_eq_ok_iff] at hsuccess
              rcases hsuccess with ⟨option3, hoption3, hsuccess⟩
              rw [bind_eq_ok_iff] at hsuccess
              rcases hsuccess with ⟨opening3, hopening3, hsuccess⟩
              rw [bind_eq_ok_iff] at hsuccess
              rcases hsuccess with ⟨option4, hoption4, hsuccess⟩
              rw [bind_eq_ok_iff] at hsuccess
              rcases hsuccess with ⟨opening4, hopening4, hsuccess⟩
              simp at hsuccess
              rcases hsuccess with ⟨_hverified, hremainder⟩
              have hloop' :
                  private_openings.verify_v5_private_openings_from_proof_loop
                      { start := 0#usize, «end» := 5#usize }
                      hash
                      (alloc.vec.Vec.deref indices.layer0)
                      (alloc.vec.Vec.deref indices.layer0)
                      (alloc.vec.Vec.deref later0)
                      (alloc.vec.Vec.deref later1)
                      (alloc.vec.Vec.deref later2)
                      rootsArray topology
                      (alloc.vec.Vec.with_capacity Digest
                        (alloc.vec.Vec.len indices.layer0))
                      (alloc.vec.Vec.with_capacity Digest
                        (alloc.vec.Vec.len indices.layer0))
                      proofBytes (Array.repeat 5#usize none) =
                    .ok (finalRemainder, finalParsed, none) := by
                simpa [private_openings.V5_PRIVATE_SECTION_COUNT] using hloop
              have callTrace :=
                generated_loop_success_yields_five_call_trace hash
                  (alloc.vec.Vec.deref indices.layer0)
                  (alloc.vec.Vec.deref indices.layer0)
                  (alloc.vec.Vec.deref later0)
                  (alloc.vec.Vec.deref later1)
                  (alloc.vec.Vec.deref later2)
                  rootsArray topology
                  (alloc.vec.Vec.with_capacity Digest
                    (alloc.vec.Vec.len indices.layer0))
                  (alloc.vec.Vec.with_capacity Digest
                    (alloc.vec.Vec.len indices.layer0))
                  proofBytes (Array.repeat 5#usize none)
                  finalRemainder finalParsed hloop'
              exact ⟨{
                layer0Leaves := layer0Leaves
                indices := indices
                later0 := later0
                later1 := later1
                later2 := later2
                rootsArray := rootsArray
                depth0 := depth0
                topology := topology
                finalRemainder := finalRemainder
                finalParsed := finalParsed
                layer0Leaves_eq := hlayer0Leaves
                indices_eq := hqueryResult
                later0_eq := hlater0
                later1_eq := hlater1
                later2_eq := hlater2
                roots_eq := hroots
                depth0_eq := hdepth0
                topology_eq := htopologyOption
                callTrace := callTrace
                returned_remainder_eq := hremainder
              }⟩

/-- The generated public wrapper succeeds exactly when the generated parser
succeeds and consumes every proof byte. -/
theorem generated_verify_success_iff_from_proof_success_empty
    (hash : Slice (Slice Std.U8) → Digest)
    (roots : private_openings.V5PrivateOpeningRoots)
    (queries : Slice Std.U32) (proofBytes : Slice Std.U8)
    (verified : private_openings.VerifiedV5PrivateOpenings) :
    private_openings.verify_v5_private_openings
        hash roots queries proofBytes = .ok (.Ok verified) ↔
      ∃ remainder,
        private_openings.verify_v5_private_openings_from_proof
            hash roots queries proofBytes = .ok (.Ok (verified, remainder)) ∧
        remainder.val = [] := by
  unfold private_openings.verify_v5_private_openings
  generalize hresult :
      private_openings.verify_v5_private_openings_from_proof
        hash roots queries proofBytes = result
  cases result with
  | fail error => simp
  | div => simp
  | ok inner =>
      cases inner with
      | Err error =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
      | Ok pair =>
          rcases pair with ⟨value, remainder⟩
          by_cases hempty : remainder.val = []
          · simp [hempty, core.slice.Slice.is_empty,
              core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
          · simp [hempty, core.slice.Slice.is_empty,
              core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]

/-- A successful result from the exact generated public verifier determines
the five helper calls and proves that the fifth call consumed the entire proof
slice. -/
theorem generated_verify_success_yields_call_trace
    (hash : Slice (Slice Std.U8) → Digest)
    (roots : private_openings.V5PrivateOpeningRoots)
    (queries : Slice Std.U32) (proofBytes : Slice Std.U8)
    (verified : private_openings.VerifiedV5PrivateOpenings)
    (hverify :
      private_openings.verify_v5_private_openings
        hash roots queries proofBytes = .ok (.Ok verified)) :
    ∃ remainder,
      remainder.val = [] ∧
      Nonempty
        (GeneratedFromProofCallTrace hash roots queries proofBytes verified
          remainder) := by
  rcases
      (generated_verify_success_iff_from_proof_success_empty
        hash roots queries proofBytes verified).mp hverify with
    ⟨remainder, hfromProof, hremainder⟩
  exact ⟨remainder, hremainder,
    generated_from_proof_success_yields_call_trace
      hash roots queries proofBytes remainder verified hfromProof⟩

#print axioms range_next_0
#print axioms range_next_5
#print axioms generated_loop_ne_some_ok
#print axioms generated_loop_success_yields_five_call_trace
#print axioms generated_from_proof_success_yields_call_trace
#print axioms generated_verify_success_iff_from_proof_success_empty
#print axioms generated_verify_success_yields_call_trace

end V5MerkleUnchangedDriverProof
