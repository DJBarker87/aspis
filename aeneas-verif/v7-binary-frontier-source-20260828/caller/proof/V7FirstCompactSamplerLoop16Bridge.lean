import V7FirstCompactSamplerInnerBridge

open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace V7FirstCompactSamplerLoop16Bridge

open AspisV5QuerySamplerControl
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73SamplerDecoder

def q16Count : Std.Usize := 16#usize
def q16MaxDraws : Std.Usize := 64#usize
def q16Mask : Std.U32 := 262143#u32

@[simp] theorem q16Count_val : q16Count.val = 16 := by rfl
@[simp] theorem q16MaxDraws_val : q16MaxDraws.val = 64 := by rfl

/-- The exact K1.3 byte view of one current translated 32-byte squeeze block. -/
def sourceDigest (block : Array Std.U8 32#usize) : Digest256 :=
  fun index => UInt8.ofNat
    (block.val[index.val]'(by
      have hindex := index.isLt
      simpa [block.property] using hindex)).val

@[simp] theorem sourceDigest_toNat
    (block : Array Std.U8 32#usize) (index : Fin 32) :
    (sourceDigest block index).toNat =
      (block.val[index.val]'(by
        have hindex := index.isLt
        simpa [block.property] using hindex)).val := by
  simp [sourceDigest]

/-- Aeneas' literal four-byte decoder equals K1.3's mathematical little-endian
word on the corresponding source block. -/
theorem generated_word_value_eq_k13
    (block : Array Std.U8 32#usize) (word : Fin 8) :
    (core.num.U32.from_le_bytes
      (V5QuerySamplerGeneratedSemantics.wordArray block word)).val =
      littleEndianWord (sourceDigest block) word := by
  rw [V5QuerySamplerGeneratedSemantics.generated_word_value_eq_u32LE]
  simp [AspisV5TranscriptConnection.u32LE,
    AspisV5TranscriptConnection.blockByte,
    V5TranscriptPrimitivesProof.arrayDigest,
    V5TranscriptPrimitivesProof.toByte,
    littleEndianWord, sourceDigest]

/-- The literal decoded-and-masked source word is exactly K1.3's q16
candidate for that block position. -/
theorem generated_candidate_eq_k13
    (block : Array Std.U8 32#usize) (word : Fin 8) :
    ((core.num.U32.from_le_bytes
      (V5QuerySamplerGeneratedSemantics.wordArray block word)) &&&
        q16Mask).val =
      q16Candidate (littleEndianWord (sourceDigest block) word) := by
  change ((core.num.U32.from_le_bytes
    (V5QuerySamplerGeneratedSemantics.wordArray block word)) &&&
      262143#u32).val = _
  rw [V7FirstCompactSamplerInnerBridge.current_q16_mask_is_exact]
  exact congrArg q16Candidate (generated_word_value_eq_k13 block word)

def candidateOfSlice (word : Slice Std.U8) : Nat :=
  if h : word.val.length = 4 then
    ((core.num.U32.from_le_bytes
        (⟨word.val, by simpa using h⟩ : Array Std.U8 4#usize)) &&&
      q16Mask).val
  else 0

def iteratorCandidates (iter : core.slice.iter.ChunksExact Std.U8) :
    List Nat := iter.chunks.map candidateOfSlice

theorem candidateOfSlice_wordSlice
    (block : Array Std.U8 32#usize) (word : Fin 8) :
    candidateOfSlice
        (V5QuerySamplerGeneratedSemantics.wordSlice block word) =
      q16Candidate (littleEndianWord (sourceDigest block) word) := by
  unfold candidateOfSlice
  simp only [V5QuerySamplerGeneratedSemantics.wordSlice, List.length_ofFn,
    ↓reduceDIte]
  rw [← generated_candidate_eq_k13 block word]
  rfl

/-- One literal `chunks_exact(4)` block yields exactly K1.3's eight q16
candidates in chronological order. -/
theorem iteratorCandidates_blockChunks
    (block : Array Std.U8 32#usize) :
    iteratorCandidates
        (V5QuerySamplerGeneratedSemantics.blockChunks block) =
      (blockWords (sourceDigest block)).map q16Candidate := by
  simp [iteratorCandidates, V5QuerySamplerGeneratedSemantics.blockChunks,
    blockWords, candidateOfSlice_wordSlice]

def vecNats (values : alloc.vec.Vec Std.U32) : List Nat :=
  values.val.map UScalar.val

@[simp] theorem vecNats_length (values : alloc.vec.Vec Std.U32) :
    (vecNats values).length = values.val.length := by
  simp [vecNats]

theorem contains_u32_is_membership
    (values : alloc.vec.Vec Std.U32) (candidate : Std.U32) :
    core.slice.Slice.contains core.cmp.PartialEqU32
        (alloc.vec.Vec.deref values) candidate =
      .ok (decide (candidate ∈ values.val)) := by
  rcases values with ⟨values, hvalues⟩
  induction values with
  | nil => rfl
  | cons head tail ih =>
      have htail : tail.length ≤ Std.Usize.max := by
        have : tail.length < Std.Usize.max := by simpa using hvalues
        exact Nat.le_of_lt this
      have ih' := ih htail
      by_cases heq : candidate = head
      · subst head
        simp [core.slice.Slice.contains, alloc.vec.Vec.deref,
          List.anyM, liftFun2, core.cmp.impls.PartialEqU32.eq]
        rfl
      · simp only [core.slice.Slice.contains, alloc.vec.Vec.deref] at ih'
        simp [core.slice.Slice.contains, alloc.vec.Vec.deref,
          List.anyM, liftFun2, core.cmp.impls.PartialEqU32.eq, heq, ih']

theorem u32_membership_iff_val_membership
    (values : alloc.vec.Vec Std.U32) (candidate : Std.U32) :
    candidate ∈ values.val ↔ candidate.val ∈ vecNats values := by
  constructor
  · intro hcandidate
    rw [vecNats, List.mem_map]
    exact ⟨candidate, hcandidate, rfl⟩
  · intro hcandidate
    rw [vecNats, List.mem_map] at hcandidate
    obtain ⟨value, hvalue, heq⟩ := hcandidate
    have : value = candidate := UScalar.eq_of_val_eq heq
    simpa [this] using hvalue

theorem vecNats_push
    (values pushed : alloc.vec.Vec Std.U32) (candidate : Std.U32)
    (hpush : alloc.vec.Vec.push values candidate = .ok pushed) :
    vecNats pushed = vecNats values ++ [candidate.val] := by
  unfold alloc.vec.Vec.push at hpush
  dsimp only at hpush
  split at hpush
  · simp only [Result.ok.injEq] at hpush
    rw [← hpush]
    simp [vecNats]
  · simp at hpush

def arrayOfWord (word : Slice Std.U8) (hlength : word.val.length = 4) :
    Array Std.U8 4#usize :=
  ⟨word.val, by simpa using hlength⟩

def maskedWordCandidate (word : Slice Std.U8)
    (hlength : word.val.length = 4) : Std.U32 :=
  (core.num.U32.from_le_bytes (arrayOfWord word hlength)) &&& q16Mask

theorem try_from_word_of_length
    (word : Slice Std.U8) (hlength : word.val.length = 4) :
    core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8 word =
      .ok (.Ok (arrayOfWord word hlength)) := by
  unfold core.array.TryFromArrayCopySlice.try_from
  simp [hlength, arrayOfWord]

theorem maskedWordCandidate_val
    (word : Slice Std.U8) (hlength : word.val.length = 4) :
    (maskedWordCandidate word hlength).val = candidateOfSlice word := by
  simp [maskedWordCandidate, candidateOfSlice, hlength, arrayOfWord]

def generatedBlockScanState (out : alloc.vec.Vec Std.U32)
    (draws : Std.Usize) (consumedBlocks : Nat) : BlockScanState where
  accepted := vecNats out
  draws := draws.val
  consumedBlocks := consumedBlocks

@[simp] theorem generatedBlockScanState_accepted
    (out : alloc.vec.Vec Std.U32) (draws : Std.Usize) (consumedBlocks : Nat) :
    (generatedBlockScanState out draws consumedBlocks).accepted = vecNats out :=
  rfl

@[simp] theorem generatedBlockScanState_draws
    (out : alloc.vec.Vec Std.U32) (draws : Std.Usize) (consumedBlocks : Nat) :
    (generatedBlockScanState out draws consumedBlocks).draws = draws.val := rfl

@[simp] theorem generatedBlockScanState_consumedBlocks
    (out : alloc.vec.Vec Std.U32) (draws : Std.Usize) (consumedBlocks : Nat) :
    (generatedBlockScanState out draws consumedBlocks).consumedBlocks =
      consumedBlocks := rfl

def ValidWordIterator (iter : core.slice.iter.ChunksExact Std.U8) : Prop :=
  ∀ word ∈ iter.chunks, word.val.length = 4

def wordScanMarker (scanned : WordScanResult) : Nat :=
  if scanned.stopOuter then 0 else 1

/-- Induction over the generated inner `chunks_exact(4)` loop.  The result is
the maintained eight-word scan, including the labelled break marker used by
the generated outer loop. -/
theorem generated_inner_loop_matches_scanWords
    (iter : core.slice.iter.ChunksExact Std.U8)
    (out : alloc.vec.Vec Std.U32) (draws : Std.Usize)
    (consumedBlocks : Nat)
    (hvalid : ValidWordIterator iter)
    (hout : out.val.length ≤ 16)
    (hdraws : draws.val ≤ 64) :
    V7FirstCompactSource.transcript.Transcript.challenge_queries_without_replacement_loop0_loop0
        iter q16Count q16MaxDraws q16Mask out draws
      ⦃ result =>
        let scanned := scanWords 16 64
          (generatedBlockScanState out draws consumedBlocks)
          (iteratorCandidates iter)
        generatedBlockScanState result.1 result.2.1 consumedBlocks =
            scanned.state ∧
          result.2.2.val = wordScanMarker scanned ⦄ := by
  let expected := scanWords 16 64
    (generatedBlockScanState out draws consumedBlocks)
    (iteratorCandidates iter)
  simp only [V7FirstCompactSource.transcript.Transcript.challenge_queries_without_replacement_loop0_loop0]
  apply loop.spec_decr_nat
    (fun state : core.slice.iter.ChunksExact Std.U8 ×
        alloc.vec.Vec Std.U32 × Std.Usize => state.1.chunks.length)
    (fun state =>
      ValidWordIterator state.1 ∧
        state.2.1.val.length ≤ 16 ∧
        state.2.2.val ≤ 64 ∧
        scanWords 16 64
          (generatedBlockScanState state.2.1 state.2.2 consumedBlocks)
          (iteratorCandidates state.1) = expected)
    (fun result : alloc.vec.Vec Std.U32 × Std.Usize × Std.U32 =>
      generatedBlockScanState result.1 result.2.1 consumedBlocks =
          expected.state ∧
        result.2.2.val = wordScanMarker expected)
  · rintro ⟨currentIter, currentOut, currentDraws⟩
      ⟨hcurrentValid, hcurrentOut, hcurrentDraws, hcurrentExpected⟩
    change ValidWordIterator currentIter at hcurrentValid
    change currentOut.val.length ≤ 16 at hcurrentOut
    change currentDraws.val ≤ 64 at hcurrentDraws
    change scanWords 16 64
      (generatedBlockScanState currentOut currentDraws consumedBlocks)
      (iteratorCandidates currentIter) = expected at hcurrentExpected
    cases hchunks : currentIter.chunks with
    | nil =>
        have hnext :
            core.slice.iter.IteratorChunksExact.next currentIter =
              .ok (none, currentIter) := by
          simp [core.slice.iter.IteratorChunksExact.next, hchunks]
        unfold V7FirstCompactSource.transcript.Transcript.challenge_queries_without_replacement_loop0_loop0.body
        rw [hnext]
        simp only [bind_tc_ok, Aeneas.Std.WP.spec_ok]
        have hscan : scanWords 16 64
            (generatedBlockScanState currentOut currentDraws consumedBlocks)
            (iteratorCandidates currentIter) =
          ⟨generatedBlockScanState currentOut currentDraws consumedBlocks,
            false⟩ := by
          simp [iteratorCandidates, hchunks, scanWords]
        rw [hscan] at hcurrentExpected
        rw [← hcurrentExpected]
        simp [wordScanMarker]
    | cons word remaining =>
        let nextIter : core.slice.iter.ChunksExact Std.U8 :=
          { chunks := remaining, remainder := currentIter.remainder }
        have hnext :
            core.slice.iter.IteratorChunksExact.next currentIter =
              .ok (some word, nextIter) := by
          simp [core.slice.iter.IteratorChunksExact.next, hchunks, nextIter]
        have hword : word.val.length = 4 :=
          hcurrentValid word (by simp [hchunks])
        have hremaining : ValidWordIterator nextIter := by
          intro tailWord htailWord
          exact hcurrentValid tailWord (by simp [hchunks, nextIter, htailWord])
        have hcandidates :
            iteratorCandidates currentIter =
              candidateOfSlice word :: iteratorCandidates nextIter := by
          simp [iteratorCandidates, hchunks, nextIter]
        unfold V7FirstCompactSource.transcript.Transcript.challenge_queries_without_replacement_loop0_loop0.body
        rw [hnext]
        simp only [bind_tc_ok]
        split <;> rename_i hcount
        · have hcomplete : currentOut.val.length = 16 := by
            have hvals := congrArg UScalar.val hcount
            simpa using hvals
          have hscan : scanWords 16 64
              (generatedBlockScanState currentOut currentDraws consumedBlocks)
              (iteratorCandidates currentIter) =
            ⟨generatedBlockScanState currentOut currentDraws consumedBlocks,
              true⟩ := by
            rw [hcandidates]
            simp [scanWords, hcomplete]
          rw [hscan] at hcurrentExpected
          rw [← hcurrentExpected]
          simp [wordScanMarker]
        · have hcomplete : currentOut.val.length ≠ 16 := by
            intro heq
            apply hcount
            apply UScalar.eq_of_val_eq
            simpa using heq
          split <;> rename_i hmax
          · have hlimit : currentDraws.val = 64 := by
              have hvals := congrArg UScalar.val hmax
              simpa using hvals
            have hscan : scanWords 16 64
                (generatedBlockScanState currentOut currentDraws consumedBlocks)
                (iteratorCandidates currentIter) =
              ⟨generatedBlockScanState currentOut currentDraws consumedBlocks,
                true⟩ := by
              rw [hcandidates]
              simp [scanWords, hcomplete, hlimit]
            rw [hscan] at hcurrentExpected
            rw [← hcurrentExpected]
            simp [wordScanMarker]
          · have hlimit : currentDraws.val ≠ 64 := by
              intro heq
              apply hmax
              apply UScalar.eq_of_val_eq
              simpa using heq
            have hdrawLt : currentDraws.val < 64 := by omega
            rw [V7FirstCompactSamplerInnerBridge.current_checked_draw_increment_matches_verified
              currentDraws hdrawLt]
            simp only [bind_tc_ok]
            let nextDraws : Std.Usize := Std.Usize.wrapping_add
              currentDraws 1#usize
            have hnextDraws : nextDraws.val = currentDraws.val + 1 := by
              simp [nextDraws, Std.Usize.wrapping_add_val_eq]
              apply Nat.mod_eq_of_lt
              have : currentDraws.val + 1 ≤ 64 := by omega
              scalar_tac
            have htry := try_from_word_of_length word hword
            rw [show Std.Usize.wrapping_add currentDraws 1#usize =
                nextDraws by rfl]
            change (do
              let r ← core.array.TryFromArrayCopySlice.try_from
                4#usize core.marker.CopyU8 word
              let a ← core.result.Result.unwrap
                core.fmt.DebugTryFromSliceError r
              let i1 ← lift (core.num.U32.from_le_bytes a)
              let candidate ← lift (i1 &&& q16Mask)
              let b ← core.slice.Slice.contains core.cmp.PartialEqU32
                (alloc.vec.Vec.deref currentOut) candidate
              if b then
                ok (cont (nextIter, currentOut, nextDraws))
              else
                let out1 ← alloc.vec.Vec.push currentOut candidate
                ok (cont (nextIter, out1, nextDraws))) ⦃ _ ⦄
            rw [htry]
            simp only [bind_tc_ok, core.result.Result.unwrap, lift]
            let candidate := maskedWordCandidate word hword
            rw [show (core.num.U32.from_le_bytes (arrayOfWord word hword) &&&
                q16Mask) = candidate by rfl]
            rw [contains_u32_is_membership currentOut candidate]
            simp only [bind_tc_ok]
            by_cases hmember : candidate ∈ currentOut.val
            · rw [if_pos (by simpa [hmember])]
              simp only [Aeneas.Std.WP.spec_ok]
              refine ⟨⟨hremaining, hcurrentOut, ?_, ?_⟩, ?_⟩
              · rw [hnextDraws]
                omega
              · rw [hcandidates, scanWords] at hcurrentExpected
                simp only [generatedBlockScanState_accepted, vecNats_length,
                  hcomplete, generatedBlockScanState_draws, hlimit,
                  false_or, ↓reduceIte] at hcurrentExpected
                have hmemberNat : candidate.val ∈ vecNats currentOut :=
                  (u32_membership_iff_val_membership currentOut candidate).1
                    hmember
                have hcandidate : candidate.val = candidateOfSlice word :=
                  maskedWordCandidate_val word hword
                simp [keepIfNew, hmemberNat, hcandidate.symm] at hcurrentExpected
                simpa [generatedBlockScanState, hnextDraws] using
                  hcurrentExpected
              · simp [nextIter]
            · rw [if_neg (by simpa [hmember])]
              have hpushBound : currentOut.val.length < Std.Usize.max := by
                exact lt_of_le_of_lt hcurrentOut (by scalar_tac)
              obtain ⟨pushed, hpush, hpushed⟩ :=
                Aeneas.Std.WP.spec_imp_exists
                  (alloc.vec.Vec.push_spec currentOut candidate hpushBound)
              rw [hpush]
              simp only [bind_tc_ok, Aeneas.Std.WP.spec_ok]
              refine ⟨⟨hremaining, ?_, ?_, ?_⟩, ?_⟩
              · rw [hpushed]
                simp
                omega
              · rw [hnextDraws]
                omega
              · rw [hcandidates, scanWords] at hcurrentExpected
                simp only [generatedBlockScanState_accepted, vecNats_length,
                  hcomplete, generatedBlockScanState_draws, hlimit,
                  false_or, ↓reduceIte] at hcurrentExpected
                have hnotMemberNat : candidate.val ∉ vecNats currentOut := by
                  simpa [u32_membership_iff_val_membership currentOut candidate]
                    using hmember
                have hpushedNats := vecNats_push currentOut pushed candidate hpush
                have hcandidate : candidate.val = candidateOfSlice word :=
                  maskedWordCandidate_val word hword
                simp [keepIfNew, hnotMemberNat, hcandidate.symm] at hcurrentExpected
                simpa [generatedBlockScanState, hnextDraws, hpushedNats] using
                  hcurrentExpected
              · simp [nextIter]
  · refine ⟨hvalid, hout, hdraws, ?_⟩
    change expected = expected
    rfl

#print axioms generated_inner_loop_matches_scanWords
#print axioms generated_word_value_eq_k13
#print axioms generated_candidate_eq_k13
#print axioms iteratorCandidates_blockChunks

end V7FirstCompactSamplerLoop16Bridge
