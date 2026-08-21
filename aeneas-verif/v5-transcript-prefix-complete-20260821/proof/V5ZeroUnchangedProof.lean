import Zero.Funs
import Aeneas.Tactic.Simp.SimpScalar

open Aeneas Aeneas.Std Result ControlFlow Error
open V5ZeroUnchangedGenerated

set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

namespace V5ZeroUnchangedProof

abbrev QM31 := V5ZeroUnchangedGenerated.aspis_core.field.QM31
abbrev Transcript :=
  V5ZeroUnchangedGenerated.aspis_core.transcript.Transcript

def registryBytes : List Std.U8 :=
  [1#u8, 29#u8, 95#u8, 0#u8, 10#u8, 27#u8, 28#u8, 102#u8,
    0#u8, 17#u8, 48#u8, 33#u8, 175#u8, 20#u8, 236#u8, 180#u8,
    29#u8, 18#u8, 251#u8, 234#u8, 229#u8, 239#u8, 81#u8, 34#u8,
    103#u8, 18#u8, 0#u8, 0#u8]

def registryArray : Array Std.U8 28#usize :=
  ⟨registryBytes, by simp [registryBytes]⟩

def registryStage1Bytes : List Std.U8 :=
  [1#u8, 29#u8, 95#u8, 0#u8] ++ List.replicate 24 0#u8

def registryStage2Bytes : List Std.U8 :=
  [1#u8, 29#u8, 95#u8, 0#u8, 10#u8, 27#u8, 28#u8, 102#u8,
    0#u8] ++ List.replicate 19 0#u8

def registryStage3Bytes : List Std.U8 :=
  [1#u8, 29#u8, 95#u8, 0#u8, 10#u8, 27#u8, 28#u8, 102#u8,
    0#u8, 17#u8, 48#u8, 33#u8, 175#u8, 20#u8, 236#u8, 180#u8,
    29#u8, 18#u8] ++ List.replicate 10 0#u8

def registryStage1Array : Array Std.U8 28#usize :=
  ⟨registryStage1Bytes, by simp [registryStage1Bytes]⟩

def registryStage2Array : Array Std.U8 28#usize :=
  ⟨registryStage2Bytes, by simp [registryStage2Bytes]⟩

def registryStage3Array : Array Std.U8 28#usize :=
  ⟨registryStage3Bytes, by simp [registryStage3Bytes]⟩

private def semanticLaneBytes : Array Std.U8 2#usize :=
  ⟨[95#u8, 0#u8], by simp⟩

private def copyLinkBytes : Array Std.U8 2#usize :=
  ⟨[102#u8, 0#u8], by simp⟩

private def layoutFingerprintBytes : Array Std.U8 8#usize :=
  ⟨[48#u8, 33#u8, 175#u8, 20#u8, 236#u8, 180#u8, 29#u8,
      18#u8], by simp⟩

private def hidingFingerprintBytes : Array Std.U8 8#usize :=
  ⟨[251#u8, 234#u8, 229#u8, 239#u8, 81#u8, 34#u8, 103#u8,
      18#u8], by simp⟩

@[local simp] private theorem semantic_lane_bytes_exact :
    core.num.U16.to_le_bytes 95#u16 = semanticLaneBytes := by
  apply Subtype.ext
  simp [core.num.U16.to_le_bytes, semanticLaneBytes, BitVec.toLEBytes]
  repeat' apply And.intro
  all_goals apply UScalar.eq_of_val_eq <;> decide

@[local simp] private theorem copy_link_bytes_exact :
    core.num.U16.to_le_bytes 102#u16 = copyLinkBytes := by
  apply Subtype.ext
  simp [core.num.U16.to_le_bytes, copyLinkBytes, BitVec.toLEBytes]
  repeat' apply And.intro
  all_goals apply UScalar.eq_of_val_eq <;> decide

@[local simp] private theorem layout_fingerprint_bytes_exact :
    core.num.U64.to_le_bytes 1305398393059615024#u64 =
      layoutFingerprintBytes := by
  apply Subtype.ext
  simp [core.num.U64.to_le_bytes, layoutFingerprintBytes, BitVec.toLEBytes]
  repeat' apply And.intro
  all_goals apply UScalar.eq_of_val_eq <;> decide

@[local simp] private theorem hiding_fingerprint_bytes_exact :
    core.num.U64.to_le_bytes 1326066350596418299#u64 =
      hidingFingerprintBytes := by
  apply Subtype.ext
  simp [core.num.U64.to_le_bytes, hidingFingerprintBytes, BitVec.toLEBytes]
  repeat' apply And.intro
  all_goals apply UScalar.eq_of_val_eq <;> decide

@[local simp] private theorem cast_rounds_exact :
    UScalar.cast .U8 10#usize = 10#u8 := by
  apply UScalar.eq_of_val_eq
  simp [UScalar.cast_val_eq]

@[local simp] private theorem cast_degree_exact :
    UScalar.cast .U8 27#usize = 27#u8 := by
  apply UScalar.eq_of_val_eq
  simp [UScalar.cast_val_eq]

@[local simp] private theorem cast_coefficients_exact :
    UScalar.cast .U8 28#usize = 28#u8 := by
  apply UScalar.eq_of_val_eq
  simp [UScalar.cast_val_eq]

/-- First four bytes of the exact inline registry construction. -/
def generatedRegistryStage1 : Result (Array Std.U8 28#usize) := do
  let registry := Array.repeat 28#usize 0#u8
  let i ←
    aspis_core.state_only_sumcheck.STATE_ONLY_CONSTRAINT_REGISTRY_VERSION
  let registry1 ← Array.update registry 0#usize i
  let i1 ←
    aspis_core.state_only_sumcheck.STATE_ONLY_RANDOMIZED_CONSTRAINT_LANES
  let registry2 ← Array.update registry1 1#usize i1
  let (s, index_mut_back) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) registry2
      { start := 2#usize, «end» := 4#usize }
  let i2 ← aspis_core.state_only_sumcheck.STATE_ONLY_SEMANTIC_SOURCE_LANES
  let a ← lift (core.num.U16.to_le_bytes i2)
  let s1 ← lift (Array.to_slice a)
  let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
  ok (index_mut_back s2)

/-- Round, degree, coefficient count, and copy-link bytes. -/
def generatedRegistryStage2
    (registry3 : Array Std.U8 28#usize) :
    Result (Array Std.U8 28#usize) := do
  let i3 ← aspis_core.state_only_sumcheck.STATE_ONLY_SUMCHECK_ROUNDS
  let i4 ← lift (UScalar.cast .U8 i3)
  let registry4 ← Array.update registry3 4#usize i4
  let i5 ← aspis_core.state_only_sumcheck.STATE_ONLY_SUMCHECK_DEGREE
  let i6 ← lift (UScalar.cast .U8 i5)
  let registry5 ← Array.update registry4 5#usize i6
  let i7 ← aspis_core.state_only_sumcheck.STATE_ONLY_SUMCHECK_COEFFICIENTS
  let i8 ← lift (UScalar.cast .U8 i7)
  let registry6 ← Array.update registry5 6#usize i8
  let (s3, index_mut_back1) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) registry6
      { start := 7#usize, «end» := 9#usize }
  let i9 ← aspis_core.state_only_sumcheck.STATE_ONLY_COPY_LINKS
  let a1 ← lift (core.num.U16.to_le_bytes i9)
  let s4 ← lift (Array.to_slice a1)
  let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3 s4
  ok (index_mut_back1 s5)

/-- Tuple width and the layout fingerprint. -/
def generatedRegistryStage3
    (registry7 : Array Std.U8 28#usize) :
    Result (Array Std.U8 28#usize) := do
  let i10 ← aspis_core.state_only_sumcheck.STATE_ONLY_COPY_TUPLE_WIDTH
  let registry8 ← Array.update registry7 9#usize i10
  let (s6, index_mut_back2) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) registry8
      { start := 10#usize, «end» := 18#usize }
  let i11 ← aspis_core.state_only_sumcheck.STATE_ONLY_LAYOUT_FINGERPRINT
  let a2 ← lift (core.num.U64.to_le_bytes i11)
  let s7 ← lift (Array.to_slice a2)
  let s8 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s6 s7
  ok (index_mut_back2 s8)

/-- The hiding-factor fingerprint. -/
def generatedRegistryStage4
    (registry9 : Array Std.U8 28#usize) :
    Result (Array Std.U8 28#usize) := do
  let (s9, index_mut_back3) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) registry9
      { start := 18#usize, «end» := 26#usize }
  let i12 ←
    aspis_core.state_only_sumcheck.STATE_ONLY_HIDING_FACTOR_FINGERPRINT
  let a3 ← lift (core.num.U64.to_le_bytes i12)
  let s10 ← lift (Array.to_slice a3)
  let s11 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s9 s10
  ok (index_mut_back3 s11)

theorem generatedRegistryStage1_exact :
    generatedRegistryStage1 = .ok registryStage1Array := by
  simp [generatedRegistryStage1,
    aspis_core.state_only_sumcheck.STATE_ONLY_CONSTRAINT_REGISTRY_VERSION,
    aspis_core.state_only_sumcheck.STATE_ONLY_RANDOMIZED_CONSTRAINT_LANES,
    aspis_core.state_only_sumcheck.STATE_ONLY_SEMANTIC_SOURCE_LANES,
    core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
    core.slice.Slice.copy_from_slice, Array.repeat, Array.update,
    Array.to_slice, Array.from_slice, List.setSlice!, Slice.len,
    lift, semanticLaneBytes, registryStage1Array, registryStage1Bytes]

theorem generatedRegistryStage2_exact :
    generatedRegistryStage2 registryStage1Array =
      .ok registryStage2Array := by
  simp [generatedRegistryStage2,
    aspis_core.state_only_sumcheck.STATE_ONLY_SUMCHECK_ROUNDS,
    aspis_core.state_only_sumcheck.STATE_ONLY_SUMCHECK_DEGREE,
    aspis_core.state_only_sumcheck.STATE_ONLY_SUMCHECK_COEFFICIENTS,
    aspis_core.state_only_sumcheck.STATE_ONLY_COPY_LINKS,
    core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
    core.slice.Slice.copy_from_slice, Array.update, Array.to_slice,
    Array.from_slice, List.setSlice!, Slice.len, lift, copyLinkBytes,
    registryStage1Array, registryStage1Bytes, registryStage2Array,
    registryStage2Bytes]

theorem generatedRegistryStage3_exact :
    generatedRegistryStage3 registryStage2Array =
      .ok registryStage3Array := by
  simp [generatedRegistryStage3,
    aspis_core.state_only_sumcheck.STATE_ONLY_COPY_TUPLE_WIDTH,
    aspis_core.state_only_sumcheck.STATE_ONLY_LAYOUT_FINGERPRINT,
    core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
    core.slice.Slice.copy_from_slice, Array.update, Array.to_slice,
    Array.from_slice, List.setSlice!, Slice.len, lift, layoutFingerprintBytes,
    registryStage2Array, registryStage2Bytes, registryStage3Array,
    registryStage3Bytes]

theorem generatedRegistryStage4_exact :
    generatedRegistryStage4 registryStage3Array = .ok registryArray := by
  simp [generatedRegistryStage4,
    aspis_core.state_only_sumcheck.STATE_ONLY_HIDING_FACTOR_FINGERPRINT,
    core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
    core.slice.Slice.copy_from_slice, Array.to_slice, Array.from_slice,
    List.setSlice!, Slice.len, lift, hidingFingerprintBytes,
    registryStage3Array, registryStage3Bytes, registryArray, registryBytes]

/-- The exact straight-line registry construction occurring at the start of
the unchanged Rust helper. -/
def generatedRegistryBuild : Result (Array Std.U8 28#usize) := do
  let registry3 ← generatedRegistryStage1
  let registry7 ← generatedRegistryStage2 registry3
  let registry9 ← generatedRegistryStage3 registry7
  generatedRegistryStage4 registry9

theorem generatedRegistryBuild_exact :
    generatedRegistryBuild = .ok registryArray := by
  simp [generatedRegistryBuild, generatedRegistryStage1_exact,
    generatedRegistryStage2_exact, generatedRegistryStage3_exact,
    generatedRegistryStage4_exact]

def zerocheckEvents : List ZeroTranscriptEvent :=
  [.absorb 32#u8 registryBytes,
    .absorb 33#u8 (List.replicate 16 0#u8)] ++
    List.replicate 12 .squeeze

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

def expectedChallenges :
    aspis_core.statement_sumcheck.PaymentConstraintChallenges where
  theta := ()
  zerocheck_point := Array.repeat 10#usize ()
  mu := ()

private theorem generated_zero_loop_exact
    (remaining : Nat)
    (intoBack : core.slice.iter.IterMut QM31 → Array QM31 10#usize)
    (iter : core.slice.iter.IterMut QM31)
    (back : core.slice.iter.IterMut QM31 → core.slice.iter.IterMut QM31)
    (transcript : Transcript)
    (hposition : iter.i ≤ iter.slice.val.length)
    (hremaining : iter.slice.val.length - iter.i = remaining) :
    aspis_core.state_only_sumcheck.begin_state_only_zerocheck_loop
        intoBack iter back transcript () =
      .ok (.Ok expectedChallenges,
        { events := transcript.events ++ List.replicate (remaining + 1) .squeeze }) := by
  induction remaining generalizing iter back transcript with
  | zero =>
      have hdone : ¬ iter.i < iter.slice.val.length := by omega
      unfold aspis_core.state_only_sumcheck.begin_state_only_zerocheck_loop
      rw [loop.eq_def]
      simp [aspis_core.state_only_sumcheck.begin_state_only_zerocheck_loop.body,
        core.slice.iter.IteratorIterMut.next,
        aspis_core.transcript.Transcript.challenge_qm31,
        core.result.Result.Insts.CoreOpsTry.branch,
        hdone, expectedChallenges, List.append_assoc]
      apply Subsingleton.elim
  | succ count ih =>
      have hactive : iter.i < iter.slice.val.length := by omega
      let nextIter : core.slice.iter.IterMut QM31 :=
        { iter with i := iter.i + 1 }
      let nextBack : core.slice.iter.IterMut QM31 → Option QM31 →
          core.slice.iter.IterMut QM31 :=
        fun updated value =>
          match value with
          | none => updated
          | some value =>
              { updated with slice := updated.slice.setAtNat iter.i value }
      let continuedBack : core.slice.iter.IterMut QM31 →
          core.slice.iter.IterMut QM31 :=
        fun updated => back (nextBack updated (some ()))
      let nextTranscript : Transcript :=
        { events := transcript.events ++ [.squeeze] }
      have hnextPosition : nextIter.i ≤ nextIter.slice.val.length := by
        simp [nextIter]
        omega
      have hnextRemaining :
          nextIter.slice.val.length - nextIter.i = count := by
        simp [nextIter]
        omega
      have hstep :
          aspis_core.state_only_sumcheck.begin_state_only_zerocheck_loop.body
              intoBack () iter back transcript =
            .ok (.cont (nextIter, continuedBack, nextTranscript)) := by
        simp [aspis_core.state_only_sumcheck.begin_state_only_zerocheck_loop.body,
          core.slice.iter.IteratorIterMut.next,
          aspis_core.transcript.Transcript.challenge_qm31,
          core.result.Result.Insts.CoreOpsTry.branch,
          hactive, nextIter, nextBack, continuedBack, nextTranscript]
      have hrest := ih nextIter continuedBack nextTranscript
        hnextPosition hnextRemaining
      unfold aspis_core.state_only_sumcheck.begin_state_only_zerocheck_loop at hrest
      unfold aspis_core.state_only_sumcheck.begin_state_only_zerocheck_loop
      rw [loop.eq_def]
      simp only
      rw [hstep]
      simp only [bind_tc_ok]
      simpa [nextTranscript, List.replicate_succ, List.append_assoc] using hrest

private theorem generated_begin_reduces_to_loop
    (events : List ZeroTranscriptEvent) :
    let zeroPoint := Array.repeat 10#usize ()
    let iter : core.slice.iter.IterMut QM31 :=
      { slice := Array.to_slice zeroPoint }
    aspis_core.state_only_sumcheck.begin_state_only_zerocheck { events } =
      aspis_core.state_only_sumcheck.begin_state_only_zerocheck_loop
        (fun updated => Array.from_slice zeroPoint updated.slice)
        iter (fun updated => updated)
        { events := events ++
            [.absorb 32#u8 registryBytes,
              .absorb 33#u8 (List.replicate 16 0#u8), .squeeze] }
        () := by
  dsimp only
  simp (config := { maxSteps := 200000 })
    [aspis_core.state_only_sumcheck.begin_state_only_zerocheck,
    aspis_core.state_only_sumcheck.STATE_ONLY_CONSTRAINT_REGISTRY_VERSION,
    aspis_core.state_only_sumcheck.STATE_ONLY_RANDOMIZED_CONSTRAINT_LANES,
    aspis_core.state_only_sumcheck.STATE_ONLY_SEMANTIC_SOURCE_LANES,
    aspis_core.state_only_sumcheck.STATE_ONLY_SUMCHECK_ROUNDS,
    aspis_core.state_only_sumcheck.STATE_ONLY_SUMCHECK_DEGREE,
    aspis_core.state_only_sumcheck.STATE_ONLY_SUMCHECK_COEFFICIENTS,
    aspis_core.state_only_sumcheck.STATE_ONLY_COPY_LINKS,
    aspis_core.state_only_sumcheck.STATE_ONLY_COPY_TUPLE_WIDTH,
    aspis_core.state_only_sumcheck.STATE_ONLY_LAYOUT_FINGERPRINT,
    aspis_core.state_only_sumcheck.STATE_ONLY_HIDING_FACTOR_FINGERPRINT,
    registryArray,
    aspis_core.transcript.label.M31_STATE_ONLY_CONSTRAINT_REGISTRY,
    aspis_core.transcript.label.M31_STATE_ONLY_HELPER_SUM,
    aspis_core.transcript.Transcript.absorb,
    aspis_core.transcript.Transcript.challenge_qm31,
    core.result.Result.Insts.CoreOpsTry.branch,
    aspis_core.field.QM31.ZERO,
    MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter,
    core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
    core.slice.Slice.copy_from_slice, Array.repeat, Array.update,
    Array.to_slice, Array.from_slice, List.setSlice!, Slice.len,
    semanticLaneBytes, copyLinkBytes, layoutFingerprintBytes,
    hidingFingerprintBytes, registryBytes, lift,
    List.append_assoc]

/-- Exact successful event trace and challenge forwarding of the unchanged
production `begin_state_only_zerocheck` body generated by Charon/Aeneas. -/
theorem extracted_zerocheck_success_exact
    (events : List ZeroTranscriptEvent) :
    V5ZeroUnchangedGenerated.extract_begin_state_only_zerocheck
        { events } =
      .ok (.Ok
          { theta := (), zerocheck_point := Array.repeat 10#usize (), mu := () },
        { events := events ++ zerocheckEvents }) := by
  rw [V5ZeroUnchangedGenerated.extract_begin_state_only_zerocheck,
    generated_begin_reduces_to_loop]
  let zeroPoint := Array.repeat 10#usize ()
  let iter : core.slice.iter.IterMut QM31 :=
    { slice := Array.to_slice zeroPoint }
  have hloop := generated_zero_loop_exact 10
    (fun updated => Array.from_slice zeroPoint updated.slice)
    iter (fun updated => updated)
    { events := events ++
        [.absorb 32#u8 registryBytes,
          .absorb 33#u8 (List.replicate 16 0#u8), .squeeze] }
    (by simp [iter, zeroPoint, Array.to_slice, Array.repeat])
    (by simp [iter, zeroPoint, Array.to_slice, Array.repeat])
  simpa [zeroPoint, iter, expectedChallenges, zerocheckEvents,
    List.replicate_succ, List.append_assoc] using hloop

#print axioms extracted_zerocheck_success_exact

end V5ZeroUnchangedProof
