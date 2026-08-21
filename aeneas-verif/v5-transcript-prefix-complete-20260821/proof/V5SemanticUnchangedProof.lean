import Semantic.Funs
import Aeneas.Tactic.Simp.SimpScalar

open Aeneas Aeneas.Std Result ControlFlow Error
open V5SemanticUnchangedGenerated

set_option maxRecDepth 50000

namespace V5SemanticUnchangedProof

abbrev Transcript :=
  V5SemanticUnchangedGenerated.aspis_core.transcript.Transcript

def semanticRoundEvents (round : Std.U8) (encoded : List Std.U8) :
    List SemanticTranscriptEvent :=
  [.absorb 29#u8 (round :: encoded), .squeeze]

private def nextRound (round : Std.Usize) : Std.Usize :=
  ⟨round.bv + 1⟩

def semanticRoundSequence (round : Std.Usize) :
    List (Array Std.U8 448#usize) → List SemanticTranscriptEvent
  | [] => []
  | encoded :: tail =>
      semanticRoundEvents (UScalar.cast .U8 round) encoded.val ++
        semanticRoundSequence (nextRound round) tail

private theorem joinedRoundBytes_length
    (chunks : List (Array Std.U8 448#usize)) :
    (chunks.flatMap fun chunk => chunk.val).length = 448 * chunks.length := by
  induction chunks with
  | nil => simp
  | cons chunk tail ih =>
      simp [chunk.property, ih, Nat.mul_succ]
      omega

def joinedRoundSlice
    (chunks : List (Array Std.U8 448#usize)) (hcount : chunks.length = 10) :
    Slice Std.U8 :=
  ⟨chunks.flatMap (fun chunk => chunk.val), by
    rw [joinedRoundBytes_length, hcount]
    scalar_tac⟩

private theorem toChunksExact_append_exact
    {T : Type} (head tail : List T) (hhead : head.length = 448) :
    List.toChunksExact 448 (by decide) (head ++ tail) =
      let rest := List.toChunksExact 448 (by decide) tail
      (head :: rest.1, rest.2) := by
  conv_lhs => unfold List.toChunksExact
  simp [hhead]

private theorem toChunksExact_joined_rounds
    (chunks : List (Array Std.U8 448#usize)) :
    List.toChunksExact 448 (by decide)
        (chunks.flatMap fun chunk => chunk.val) =
      (chunks.map fun chunk => chunk.val, []) := by
  induction chunks with
  | nil => simp [List.toChunksExact]
  | cons chunk tail ih =>
      rw [List.flatMap_cons,
        toChunksExact_append_exact chunk.val
          (tail.flatMap fun item => item.val) chunk.property, ih]
      rfl

private def emptySlice : Slice Std.U8 :=
  ⟨[], by simp⟩

private theorem attached_values {T : Type} (source : List T) :
    source.attach.map (fun item => item.val) = source := by
  induction source with
  | nil => rfl
  | cons head tail ih =>
      rw [List.attach_cons]
      simp only [List.map_cons, List.map_map]
      apply congrArg (List.cons head)
      calc
        List.map
            ((fun item : { value // value ∈ head :: tail } => item.val) ∘
              (fun item : { value // value ∈ tail } =>
                (⟨item.val, by simp [item.property]⟩ :
                  { value // value ∈ head :: tail }))) tail.attach =
            tail.attach.map (fun item => item.val) := by
              apply List.map_congr_left
              intro item _
              rfl
        _ = tail := ih

private theorem slice_list_eq_of_values_eq
    {T : Type} (left right : List (Slice T))
    (hvalues : left.map (fun item => item.val) =
      right.map fun item => item.val) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp_all
  | cons head tail ih =>
      cases right with
      | nil => simp_all
      | cons other rest =>
          simp only [List.map_cons, List.cons.injEq] at hvalues
          rcases hvalues with ⟨hhead, htail⟩
          congr
          · exact Subtype.ext hhead
          · exact ih rest htail

private theorem attachedChunkSlices_eq
    {T : Type} (source : List (List T)) (target : List (Slice T))
    (hsource : source = target.map fun item => item.val)
    (makeProof : ∀ item : { chunk // chunk ∈ source },
      item.val.length ≤ Std.Usize.max) :
    source.attach.map
        (fun item => (⟨item.val, makeProof item⟩ : Slice T)) = target := by
  apply slice_list_eq_of_values_eq
  calc
    (source.attach.map
        (fun item => (⟨item.val, makeProof item⟩ : Slice T))).map
          (fun item => item.val) =
        source.attach.map (fun item => item.val) := by
          rw [List.map_map]
          apply List.map_congr_left
          intro item _
          rfl
    _ = source := attached_values source
    _ = target.map (fun item => item.val) := hsource

theorem generated_chunks_exact_joined_rounds
    (chunks : List (Array Std.U8 448#usize)) (hcount : chunks.length = 10) :
    core.slice.Slice.chunks_exact (joinedRoundSlice chunks hcount) 448#usize =
      .ok { chunks := chunks.map Array.to_slice, remainder := emptySlice } := by
  have hchunks :
      List.toChunksExact (448#usize).val (by decide)
          (joinedRoundSlice chunks hcount).val =
        (chunks.map fun chunk => chunk.val, []) := by
    simpa only [joinedRoundSlice, show (448#usize).val = 448 by decide] using
      toChunksExact_joined_rounds chunks
  simp [core.slice.Slice.chunks_exact, hchunks, Array.to_slice, emptySlice]
  constructor
  · apply attachedChunkSlices_eq
    calc
      (List.toChunksExact (448#usize).val (by decide)
          (joinedRoundSlice chunks hcount).val).1 =
          chunks.map (fun item => item.val) := congrArg Prod.fst hchunks
      _ = (chunks.map Array.to_slice).map (fun item => item.val) := by
        simp [List.map_map, Array.to_slice]
  · apply Subtype.ext
    exact congrArg Prod.snd hchunks

private theorem unitList_eq_of_length (left right : List Unit)
    (hlength : left.length = right.length) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp_all
  | cons _ tail ih =>
      cases right with
      | nil => simp_all
      | cons _ rest =>
          congr
          exact ih rest (by simpa using hlength)

private instance {n : Std.Usize} : Subsingleton (Array Unit n) where
  allEq left right := by
    apply Subtype.ext
    apply unitList_eq_of_length
    simpa [left.property, right.property]

private theorem usizeAddExact (x y z : Std.Usize)
    (hbound : x.val + y.val ≤ Std.Usize.max)
    (hval : z.val = x.val + y.val) :
    x + y = ok z := by
  have hspec := Std.Usize.add_spec (x := x) (y := y) hbound
  obtain ⟨value, valueEquation, valueVal⟩ := WP.spec_imp_exists hspec
  have valueIsZ : value = z := by
    apply UScalar.eq_of_val_eq
    omega
  rw [valueEquation, valueIsZ]

syntax "usize_add_fact " ident ", " term ", " term ", " term : command

macro_rules
  | `(usize_add_fact $name:ident, $x:term, $y:term, $z:term) =>
      `(@[local simp] private theorem $name :
          ($x + $y : Result Std.Usize) = .ok $z := by
        apply usizeAddExact <;> scalar_tac)

usize_add_fact add_0_1, 0#usize, 1#usize, 1#usize
usize_add_fact add_1_1, 1#usize, 1#usize, 2#usize
usize_add_fact add_2_1, 2#usize, 1#usize, 3#usize
usize_add_fact add_3_1, 3#usize, 1#usize, 4#usize
usize_add_fact add_4_1, 4#usize, 1#usize, 5#usize
usize_add_fact add_5_1, 5#usize, 1#usize, 6#usize
usize_add_fact add_6_1, 6#usize, 1#usize, 7#usize
usize_add_fact add_7_1, 7#usize, 1#usize, 8#usize
usize_add_fact add_8_1, 8#usize, 1#usize, 9#usize
usize_add_fact add_9_1, 9#usize, 1#usize, 10#usize

/-- The unchanged production framing helper prefixes the exact 448 proof
bytes with the round byte, absorbs those 449 bytes under label 29, and then
requests the challenge returned to its caller. -/
theorem generated_absorb_semantic_round_exact
    (round : Std.Usize) (encoded : Array Std.U8 448#usize)
    (transcript : Transcript) :
    aspis_core.state_only_sumcheck.absorb_state_only_sumcheck_round
        transcript round encoded =
      .ok (.Ok (), { events := transcript.events ++
        semanticRoundEvents (UScalar.cast .U8 round) encoded.val }) := by
  simp [aspis_core.state_only_sumcheck.absorb_state_only_sumcheck_round,
    aspis_core.transcript.label.M31_STATE_ONLY_ZEROCHECK_SUMCHECK,
    aspis_core.transcript.Transcript.absorb,
    aspis_core.transcript.Transcript.challenge_qm31,
    core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.SliceIndexRangeFromUsizeSlice,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut,
    core.slice.Slice.copy_from_slice, Array.repeat, Array.update,
    Array.to_slice, Array.from_slice, Slice.drop, Slice.setSlice!,
    List.setSlice!, Slice.len, semanticRoundEvents, lift, encoded.property,
    List.append_assoc]

/-- One successful iteration of the unchanged streaming verifier consumes the
next exact 448-byte chunk, frames it with its round byte under label 29, then
requests one field challenge. -/
theorem generated_semantic_round_body_exact
    (round next : Std.Usize)
    (hround : round.val < 10)
    (hnext : next.val = round.val + 1)
    (encoded : Array Std.U8 448#usize)
    (tail : List (Slice Std.U8)) (remainder : Slice Std.U8)
    (transcript : Transcript)
    (point : Array aspis_core.field.QM31 10#usize) :
    aspis_core.state_only_sumcheck.verify_state_only_sumcheck_streaming_loop.body
        { iter := { chunks := Array.to_slice encoded :: tail, remainder },
          count := round }
        transcript point () =
      .ok (.cont
        ({ iter := { chunks := tail, remainder }, count := next },
          { events := transcript.events ++
              semanticRoundEvents (UScalar.cast .U8 round) encoded.val },
          point, ())) := by
  have hadd : round + 1#usize = ok next := by
    apply usizeAddExact
    · scalar_tac
    · exact hnext
  have hpoint : Array.update point round () = ok point := by
    have hspec := Array.update_spec point round () (by simpa using hround)
    obtain ⟨updated, heq, _⟩ := WP.spec_imp_exists hspec
    have hsame : updated = point := Subsingleton.elim _ _
    simpa [hsame] using heq
  have hsliceLength : Slice.len (Array.to_slice encoded) = 448#usize := by
    apply UScalar.eq_of_val_eq
    simp [Slice.len, Array.to_slice, encoded.property]
  have htry :
      core.array.TryFromSharedArraySlice.try_from 448#usize
          (Array.to_slice encoded) = .ok (.Ok encoded) := by
    simp [core.array.TryFromSharedArraySlice.try_from, hsliceLength,
      Array.to_slice]
  simp [aspis_core.state_only_sumcheck.verify_state_only_sumcheck_streaming_loop.body,
      core.iter.adapters.enumerate.IteratorEnumerate.next,
      core.slice.iter.IteratorChunksExact.next,
      aspis_core.state_only_sumcheck.decode_state_only_polynomial,
      aspis_core.state_only_sumcheck.state_only_boundary_sum,
      aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq,
      core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
      core.result.Result.expect,
      core.result.Result.Insts.CoreOpsTry.branch,
      generated_absorb_semantic_round_exact,
      aspis_core.state_only_sumcheck.evaluate_state_only_polynomial,
      core.array.Array.index_mut, core.ops.index.IndexMutSlice,
      core.slice.index.SliceIndexRangeFromUsizeSlice,
      core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut,
      core.slice.Slice.copy_from_slice, Array.repeat,
      Array.from_slice, List.setSlice!, semanticRoundEvents,
      Slice.len, lift, hadd, hpoint, htry, List.append_assoc]

private theorem nextRound_val
    (round : Std.Usize) (hround : round.val < 10) :
    (nextRound round).val = round.val + 1 := by
  change (round.bv + 1).toNat = round.bv.toNat + 1
  cases System.Platform.numBits_eq <;>
    simp_all [BitVec.toNat_add] <;> omega

/-- The extracted loop consumes each exact 448-byte round in order.  For an
accepted ten-round input this records all ten framed absorbs and all ten
returned challenges, while forwarding the final point and claim. -/
theorem generated_semantic_loop_exact
    (round : Std.Usize) (chunks : List (Array Std.U8 448#usize))
    (remainder : Slice Std.U8) (transcript : Transcript)
    (point : Array aspis_core.field.QM31 10#usize)
    (runningClaim : aspis_core.field.QM31)
    (hbound : round.val + chunks.length ≤ 10) :
    aspis_core.state_only_sumcheck.verify_state_only_sumcheck_streaming_loop
        { iter := { chunks := chunks.map Array.to_slice, remainder },
          count := round }
        transcript point runningClaim =
      .ok (.Ok { point, terminal_claim := () },
        { events := transcript.events ++ semanticRoundSequence round chunks }) := by
  induction chunks generalizing round transcript point runningClaim with
  | nil =>
      unfold aspis_core.state_only_sumcheck.verify_state_only_sumcheck_streaming_loop
      rw [loop.eq_def]
      simp [aspis_core.state_only_sumcheck.verify_state_only_sumcheck_streaming_loop.body,
        core.iter.adapters.enumerate.IteratorEnumerate.next,
        core.slice.iter.IteratorChunksExact.next, semanticRoundSequence]
  | cons encoded tail ih =>
      cases runningClaim
      have hround : round.val < 10 := by
        simp at hbound
        omega
      let next := nextRound round
      have hnext : next.val = round.val + 1 := nextRound_val round hround
      have hnextBound : next.val + tail.length ≤ 10 := by
        simp [hnext] at hbound ⊢
        omega
      let nextTranscript : Transcript :=
        { events := transcript.events ++
            semanticRoundEvents (UScalar.cast .U8 round) encoded.val }
      have hstep := generated_semantic_round_body_exact round next hround hnext
        encoded (tail.map Array.to_slice) remainder transcript point
      have hrest := ih next nextTranscript point () hnextBound
      unfold aspis_core.state_only_sumcheck.verify_state_only_sumcheck_streaming_loop at hrest
      unfold aspis_core.state_only_sumcheck.verify_state_only_sumcheck_streaming_loop
      rw [loop.eq_def]
      simp only [List.map]
      rw [hstep]
      simp only [bind_tc_ok]
      simpa [semanticRoundSequence, next, nextTranscript,
        List.append_assoc] using hrest

private theorem joinedRoundSlice_len_exact
    (chunks : List (Array Std.U8 448#usize)) (hcount : chunks.length = 10) :
    Slice.len (joinedRoundSlice chunks hcount) = 4480#usize := by
  apply UScalar.eq_of_val_eq
  simp [Slice.len, joinedRoundSlice, joinedRoundBytes_length, hcount]

/-- The complete unchanged streaming helper accepts an exact ten-round wire,
partitions it into ten consecutive 448-byte arrays, and produces precisely
the ten round absorbs and ten returned challenges in order. -/
theorem extracted_semantic_sumcheck_success_exact
    (chunks : List (Array Std.U8 448#usize)) (hcount : chunks.length = 10)
    (transcript : Transcript)
    (initialClaim : aspis_core.field.QM31) :
    V5SemanticUnchangedGenerated.extract_verify_state_only_sumcheck_streaming
        transcript (joinedRoundSlice chunks hcount) initialClaim =
      .ok (.Ok
          { point := Array.repeat 10#usize (), terminal_claim := () },
        { events := transcript.events ++
            semanticRoundSequence 0#usize chunks }) := by
  rw [V5SemanticUnchangedGenerated.extract_verify_state_only_sumcheck_streaming]
  simp [aspis_core.state_only_sumcheck.verify_state_only_sumcheck_streaming,
    aspis_core.state_only_sumcheck.STATE_ONLY_SUMCHECK_BYTES,
    aspis_core.state_only_sumcheck.STATE_ONLY_SUMCHECK_ROUND_BYTES,
    joinedRoundSlice_len_exact,
    generated_chunks_exact_joined_rounds,
    aspis_core.field.QM31.ZERO,
    core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default,
    generated_semantic_loop_exact, hcount]

#print axioms generated_semantic_round_body_exact
#print axioms generated_semantic_loop_exact
#print axioms generated_chunks_exact_joined_rounds
#print axioms extracted_semantic_sumcheck_success_exact

end V5SemanticUnchangedProof
