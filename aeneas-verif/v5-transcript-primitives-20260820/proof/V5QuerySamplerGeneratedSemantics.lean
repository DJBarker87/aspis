import V5TranscriptPrimitivesProof
import AspisFormal.V5QuerySamplerControl

/-! Semantic connection for the fixed production V5 query sampler. -/

open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace V5QuerySamplerGeneratedSemantics

open V5TranscriptPrimitivesGenerated
open V5TranscriptPrimitivesProof
open AspisV5TranscriptConnection
open AspisV5QuerySamplerControl

abbrev Byte := AspisFormal.V5ExactRuntimeWireRepair.Byte

def wordSlice (block : Array Std.U8 32#usize) (word : Fin 8) :
    Slice Std.U8 :=
  ⟨List.ofFn (fun byte : Fin 4 =>
      block.val[4 * word.val + byte.val]'(by
        have hword := word.isLt
        have hbyte := byte.isLt
        have hlength : block.val.length = 32 := by
          simpa using block.property
        omega)),
    by
      rw [List.length_ofFn]
      exact (by scalar_tac : 4 ≤ Std.Usize.max)⟩

def blockChunks (block : Array Std.U8 32#usize) :
    core.slice.iter.ChunksExact Std.U8 where
  chunks := List.ofFn (wordSlice block)
  remainder := ⟨[], by simp⟩

theorem chunksExact_ext {T : Type}
    (left right : core.slice.iter.ChunksExact T)
    (hchunks : left.chunks = right.chunks)
    (hremainder : left.remainder = right.remainder) :
    left = right := by
  cases left
  cases right
  simp_all

theorem chunks_exact_block_is_blockChunks
    (block : Array Std.U8 32#usize) :
    core.slice.Slice.chunks_exact (Array.to_slice block) 4#usize =
      .ok (blockChunks block) := by
  unfold core.slice.Slice.chunks_exact blockChunks wordSlice
  simp only [show (4#usize : Std.Usize).val > 0 by decide, ↓reduceDIte,
    Array.to_slice]
  simp only [Result.ok.injEq]
  apply chunksExact_ext
  · simp only
    apply List.ext_get
    · simp [List.toChunksExact, block.property]
    · intro i hleft hright
      simp [List.toChunksExact, block.property] at hleft hright
      interval_cases i <;> simp [List.toChunksExact, block.property] <;>
        apply Subtype.ext <;>
        apply List.ext_get
      all_goals try simp [block.property]
      all_goals
        intro n hn
        interval_cases n <;> simp
  · simp [List.toChunksExact, block.property]

def wordArray (block : Array Std.U8 32#usize) (word : Fin 8) :
    Array Std.U8 4#usize :=
  ⟨(wordSlice block word).val, by simp [wordSlice]⟩

theorem try_from_wordSlice_is_wordArray
    (block : Array Std.U8 32#usize) (word : Fin 8) :
    core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8
        (wordSlice block word) =
      .ok (.Ok (wordArray block word)) := by
  unfold core.array.TryFromArrayCopySlice.try_from
  simp [wordSlice, wordArray]

theorem fromLEBytes_four_toNat (b0 b1 b2 b3 : BitVec 8) :
    (BitVec.fromLEBytes [b0, b1, b2, b3]).toNat =
      b0.toNat + 256 * b1.toNat + 65536 * b2.toNat +
        16777216 * b3.toNat := by
  have hb0 : b0.toNat < 256 := by simpa using b0.isLt
  have hb1 : b1.toNat < 256 := by simpa using b1.isLt
  have hb2 : b2.toNat < 256 := by simpa using b2.isLt
  have hb3 : b3.toNat < 256 := by simpa using b3.isLt
  have hb3s : b3.toNat * 256 < 65536 := by omega
  have h23 : b2.toNat + 256 * b3.toNat < 65536 := by omega
  have h23s : (b2.toNat + 256 * b3.toNat) * 256 < 16777216 := by omega
  have h123 :
      b1.toNat + 256 * (b2.toNat + 256 * b3.toNat) < 16777216 := by
    omega
  have h123s :
      (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat)) * 256 <
        4294967296 := by
    omega
  simp only [BitVec.fromLEBytes, BitVec.toNat_or, BitVec.toNat_setWidth,
    BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, List.length_cons,
    List.length_nil, Nat.mul_zero, Nat.mul_one, Nat.reducePow,
    BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_mul, Nat.or_zero]
  norm_num at ⊢
  rw [Nat.mod_eq_of_lt (by omega : b0.toNat < 4294967296),
    Nat.mod_eq_of_lt (by omega : b1.toNat < 16777216),
    Nat.mod_eq_of_lt (by omega : b2.toNat < 65536), Nat.mod_eq_of_lt hb3]
  rw [Nat.mod_eq_of_lt hb3s]
  rw [show b2.toNat ||| b3.toNat * 256 =
      b2.toNat + 256 * b3.toNat by
    rw [Nat.or_comm, Nat.mul_comm]
    simpa [Nat.add_comm] using
      (Nat.two_pow_add_eq_or_of_lt (i := 8) hb2 b3.toNat).symm]
  rw [Nat.mod_eq_of_lt h23s]
  rw [show b1.toNat ||| (b2.toNat + 256 * b3.toNat) * 256 =
      b1.toNat + 256 * (b2.toNat + 256 * b3.toNat) by
    rw [Nat.or_comm, Nat.mul_comm]
    simpa [Nat.add_comm] using
      (Nat.two_pow_add_eq_or_of_lt (i := 8) hb1
        (b2.toNat + 256 * b3.toNat)).symm]
  rw [Nat.mod_eq_of_lt h123s]
  rw [show b0.toNat |||
        (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat)) * 256 =
      b0.toNat + 256 *
        (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat)) by
    rw [Nat.or_comm, Nat.mul_comm]
    simpa [Nat.add_comm] using
      (Nat.two_pow_add_eq_or_of_lt (i := 8) hb0
        (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat))).symm]
  omega

theorem generated_word_value_eq_u32LE
    (block : Array Std.U8 32#usize) (word : Fin 8) :
    (core.num.U32.from_le_bytes (wordArray block word)).val =
      u32LE (arrayDigest block) word := by
  unfold core.num.U32.from_le_bytes UScalar.val
  rw [BitVec.toNat_cast]
  have hbytes :
      List.map Std.U8.bv (wordArray block word).val =
        [(block.val[4 * word.val + 0]'(by
            have hw := word.isLt
            have hb : block.val.length = 32 := by simpa using block.property
            omega)).bv,
         (block.val[4 * word.val + 1]'(by
            have hw := word.isLt
            have hb : block.val.length = 32 := by simpa using block.property
            omega)).bv,
         (block.val[4 * word.val + 2]'(by
            have hw := word.isLt
            have hb : block.val.length = 32 := by simpa using block.property
            omega)).bv,
         (block.val[4 * word.val + 3]'(by
            have hw := word.isLt
            have hb : block.val.length = 32 := by simpa using block.property
            omega)).bv] := by
    simp [wordArray, wordSlice]
  rw [hbytes, fromLEBytes_four_toNat]
  simp [u32LE, blockByte, arrayDigest, toByte]

theorem generated_candidate_eq_queryCandidate
    (block : Array Std.U8 32#usize) (word : Fin 8) :
    ((core.num.U32.from_le_bytes (wordArray block word)) &&&
        131071#u32).val = queryCandidate (arrayDigest block) word := by
  rw [UScalar.val_and, generated_word_value_eq_u32LE]
  norm_num
  exact rust_query_mask_equals_queryCandidate (arrayDigest block) word

def candidateOfSlice (word : Slice Std.U8) : Nat :=
  if h : word.val.length = 4 then
    ((core.num.U32.from_le_bytes
        (⟨word.val, by simpa using h⟩ : Array Std.U8 4#usize)) &&&
      131071#u32).val
  else 0

def iteratorCandidates (iter : core.slice.iter.ChunksExact Std.U8) :
    List Nat :=
  iter.chunks.map candidateOfSlice

theorem candidateOfSlice_wordSlice
    (block : Array Std.U8 32#usize) (word : Fin 8) :
    candidateOfSlice (wordSlice block word) =
      queryCandidate (arrayDigest block) word := by
  unfold candidateOfSlice
  simp only [wordSlice, List.length_ofFn, ↓reduceDIte]
  rw [← generated_candidate_eq_queryCandidate block word]
  rfl

theorem blockChunks_candidates
    (block : Array Std.U8 32#usize) :
    iteratorCandidates (blockChunks block) =
      blockQueryCandidates (arrayDigest block) := by
  simp [iteratorCandidates, blockChunks, blockQueryCandidates,
    candidateOfSlice_wordSlice]

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
  (core.num.U32.from_le_bytes (arrayOfWord word hlength)) &&& 131071#u32

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
    (hout : out.val.length ≤ 18)
    (hdraws : draws.val ≤ 64) :
    V5TranscriptPrimitivesGenerated.aspis_core.transcript.Transcript.challenge_queries_without_replacement_loop0_loop0
        iter 18#usize 64#usize 131071#u32 out draws
      ⦃ result =>
        let scanned := scanWords 18 64
          (generatedBlockScanState out draws consumedBlocks)
          (iteratorCandidates iter)
        generatedBlockScanState result.1 result.2.1 consumedBlocks =
            scanned.state ∧
          result.2.2.val = wordScanMarker scanned ⦄ := by
  let expected := scanWords 18 64
    (generatedBlockScanState out draws consumedBlocks)
    (iteratorCandidates iter)
  simp only [V5TranscriptPrimitivesGenerated.aspis_core.transcript.Transcript.challenge_queries_without_replacement_loop0_loop0]
  apply loop.spec_decr_nat
    (fun state : core.slice.iter.ChunksExact Std.U8 ×
        alloc.vec.Vec Std.U32 × Std.Usize => state.1.chunks.length)
    (fun state =>
      ValidWordIterator state.1 ∧
        state.2.1.val.length ≤ 18 ∧
        state.2.2.val ≤ 64 ∧
        scanWords 18 64
          (generatedBlockScanState state.2.1 state.2.2 consumedBlocks)
          (iteratorCandidates state.1) = expected)
    (fun result : alloc.vec.Vec Std.U32 × Std.Usize × Std.U32 =>
      generatedBlockScanState result.1 result.2.1 consumedBlocks =
          expected.state ∧
        result.2.2.val = wordScanMarker expected)
  · rintro ⟨currentIter, currentOut, currentDraws⟩
      ⟨hcurrentValid, hcurrentOut, hcurrentDraws, hcurrentExpected⟩
    change ValidWordIterator currentIter at hcurrentValid
    change currentOut.val.length ≤ 18 at hcurrentOut
    change currentDraws.val ≤ 64 at hcurrentDraws
    change scanWords 18 64
      (generatedBlockScanState currentOut currentDraws consumedBlocks)
      (iteratorCandidates currentIter) = expected at hcurrentExpected
    cases hchunks : currentIter.chunks with
    | nil =>
        have hnext :
            core.slice.iter.IteratorChunksExact.next currentIter =
              .ok (none, currentIter) := by
          simp [core.slice.iter.IteratorChunksExact.next, hchunks]
        unfold V5TranscriptPrimitivesGenerated.aspis_core.transcript.Transcript.challenge_queries_without_replacement_loop0_loop0.body
        rw [hnext]
        simp only [bind_tc_ok, Aeneas.Std.WP.spec_ok]
        have hscan : scanWords 18 64
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
        unfold V5TranscriptPrimitivesGenerated.aspis_core.transcript.Transcript.challenge_queries_without_replacement_loop0_loop0.body
        rw [hnext]
        simp only [bind_tc_ok]
        by_cases hcomplete : currentOut.val.length = 18
        · have hcount : alloc.vec.Vec.len currentOut = 18#usize := by
            apply UScalar.eq_of_val_eq
            simpa using hcomplete
          rw [if_pos hcount]
          simp only [Aeneas.Std.WP.spec_ok]
          have hscan : scanWords 18 64
              (generatedBlockScanState currentOut currentDraws consumedBlocks)
              (iteratorCandidates currentIter) =
            ⟨generatedBlockScanState currentOut currentDraws consumedBlocks,
              true⟩ := by
            rw [hcandidates]
            simp [scanWords, hcomplete]
          rw [hscan] at hcurrentExpected
          rw [← hcurrentExpected]
          simp [wordScanMarker]
        · have hcount : alloc.vec.Vec.len currentOut ≠ 18#usize := by
            intro heq
            apply hcomplete
            have := congrArg UScalar.val heq
            simpa using this
          rw [if_neg hcount]
          by_cases hlimit : currentDraws.val = 64
          · have hmax : currentDraws = 64#usize :=
              UScalar.eq_of_val_eq (by simpa using hlimit)
            rw [if_pos hmax]
            simp only [Aeneas.Std.WP.spec_ok]
            have hscan : scanWords 18 64
                (generatedBlockScanState currentOut currentDraws consumedBlocks)
                (iteratorCandidates currentIter) =
              ⟨generatedBlockScanState currentOut currentDraws consumedBlocks,
                true⟩ := by
              rw [hcandidates]
              simp [scanWords, hcomplete, hlimit]
            rw [hscan] at hcurrentExpected
            rw [← hcurrentExpected]
            simp [wordScanMarker]
          · have hmax : currentDraws ≠ 64#usize := by
              intro heq
              apply hlimit
              have := congrArg UScalar.val heq
              simpa using this
            rw [if_neg hmax]
            have hdrawLt : currentDraws.val < 64 := by omega
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
            rw [htry]
            simp only [bind_tc_ok, core.result.Result.unwrap, lift]
            let candidate := maskedWordCandidate word hword
            rw [show (core.num.U32.from_le_bytes (arrayOfWord word hword) &&&
                131071#u32) = candidate by rfl]
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

theorem scanWords_draws_of_not_stopped
    (count maxDraws : Nat) (state : BlockScanState) (words : List Nat)
    (hnotStopped : (scanWords count maxDraws state words).stopOuter = false) :
    (scanWords count maxDraws state words).state.draws =
      state.draws + words.length := by
  induction words generalizing state with
  | nil => rfl
  | cons value remaining ih =>
      rw [scanWords] at hnotStopped ⊢
      by_cases hstop :
          (decide (state.accepted.length = count) ||
            decide (state.draws = maxDraws)) = true
      · rw [if_pos hstop] at hnotStopped
        contradiction
      ·
        rw [if_neg hstop] at hnotStopped ⊢
        have htail := ih
          { state with
              accepted := keepIfNew state.accepted value
              draws := state.draws + 1 }
          hnotStopped
        change (scanWords count maxDraws
          { state with
              accepted := keepIfNew state.accepted value
              draws := state.draws + 1 }
          remaining).state.draws =
            state.draws + 1 + remaining.length at htail
        simp only [List.length_cons]
        omega

inductive ExactSqueezeTrace :
    Transcript → List (Array Std.U8 32#usize) → Transcript → Prop
  | nil (self : Transcript) : ExactSqueezeTrace self [] self
  | cons (self next final : Transcript) (block : Array Std.U8 32#usize)
      (blocks : List (Array Std.U8 32#usize))
      (head :
        V5TranscriptPrimitivesGenerated.aspis_core.transcript.Transcript.squeeze_block
          self = .ok (block, next))
      (tail : ExactSqueezeTrace next blocks final) :
      ExactSqueezeTrace self (block :: blocks) final

abbrev QueryBlock := Array Std.U8 32#usize

def generatedCandidateBlocks
    (blocks : List (Array Std.U8 32#usize)) : List (List Nat) :=
  blocks.map (fun block => blockQueryCandidates (arrayDigest block))

@[simp] theorem generatedCandidateBlocks_nil :
    generatedCandidateBlocks [] = [] := rfl

@[simp] theorem generatedCandidateBlocks_cons
    (block : Array Std.U8 32#usize)
    (blocks : List (Array Std.U8 32#usize)) :
    generatedCandidateBlocks (block :: blocks) =
      blockQueryCandidates (arrayDigest block) ::
        generatedCandidateBlocks blocks := rfl

theorem exactSqueezeTrace_append_one
    {initial current next : Transcript}
    {blocks : List QueryBlock}
    {block : QueryBlock}
    (htrace : ExactSqueezeTrace initial blocks current)
    (hsqueeze :
      V5TranscriptPrimitivesGenerated.aspis_core.transcript.Transcript.squeeze_block
        current = .ok (block, next)) :
    ExactSqueezeTrace initial (blocks ++ [block]) next := by
  induction htrace generalizing next block with
  | nil traceSelf =>
      simpa using ExactSqueezeTrace.cons traceSelf next next block [] hsqueeze
        (ExactSqueezeTrace.nil next)
  | cons self middle final headBlock priorBlocks head tail ih =>
      rw [List.cons_append]
      exact ExactSqueezeTrace.cons self middle next headBlock
        (priorBlocks ++ [block]) head (ih hsqueeze)

@[simp] theorem generatedCandidateBlocks_append
    (left right : List QueryBlock) :
    generatedCandidateBlocks (left ++ right) =
      generatedCandidateBlocks left ++ generatedCandidateBlocks right := by
  induction left with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.cons_append, generatedCandidateBlocks_cons, ih,
        List.cons_append]

def OuterSamplerInvariant
    (initialSelf : Transcript) (initialOut : alloc.vec.Vec Std.U32)
    (initialDraws : Std.Usize) (initialConsumedBlocks : Nat)
    (current : Transcript × alloc.vec.Vec Std.U32 × Std.Usize) : Prop :=
  current.2.1.val.length ≤ 18 ∧ current.2.2.val ≤ 64 ∧
    ∃ blocks : List (Array Std.U8 32#usize),
      ExactSqueezeTrace initialSelf blocks current.1 ∧
      ∀ suffix : List (List Nat),
        scanBlocks 18 64
            (generatedBlockScanState initialOut initialDraws
              initialConsumedBlocks)
            (generatedCandidateBlocks blocks ++ suffix) =
          scanBlocks 18 64
            (generatedBlockScanState current.2.1 current.2.2
              (initialConsumedBlocks + blocks.length)) suffix

def OuterSamplerPost
    (initialSelf : Transcript) (initialOut : alloc.vec.Vec Std.U32)
    (initialDraws : Std.Usize) (initialConsumedBlocks : Nat)
    (result : Transcript × alloc.vec.Vec Std.U32) : Prop :=
  ∃ (blocks : List (Array Std.U8 32#usize)) (finalDraws : Std.Usize),
    ExactSqueezeTrace initialSelf blocks result.1 ∧
    finalDraws.val ≤ 64 ∧ result.2.val.length ≤ 18 ∧
    scanBlocks 18 64
        (generatedBlockScanState initialOut initialDraws initialConsumedBlocks)
        (generatedCandidateBlocks blocks) =
      generatedBlockScanState result.2 finalDraws
        (initialConsumedBlocks + blocks.length)

theorem validWordIterator_blockChunks
    (block : Array Std.U8 32#usize) :
    ValidWordIterator (blockChunks block) := by
  intro word hword
  simp only [blockChunks, List.mem_ofFn] at hword
  rcases hword with ⟨index, rfl⟩
  simp [wordSlice]

/-! The generated outer loop consumes exactly the blocks recorded by the
transcript trace and implements `scanBlocks`.  Its decreasing measure is the
remaining 64-word draw budget; every continuation consumes all eight words
of the block just squeezed. -/
theorem generated_outer_loop_matches_scanBlocks
    (self : Transcript) (out : alloc.vec.Vec Std.U32)
    (draws : Std.Usize) (consumedBlocks : Nat)
    (hout : out.val.length ≤ 18) (hdraws : draws.val ≤ 64) :
    V5TranscriptPrimitivesGenerated.aspis_core.transcript.Transcript.challenge_queries_without_replacement_loop0
        self 18#usize 64#usize 131071#u32 out draws
      ⦃ result => OuterSamplerPost self out draws consumedBlocks result ⦄ := by
  simp only [V5TranscriptPrimitivesGenerated.aspis_core.transcript.Transcript.challenge_queries_without_replacement_loop0]
  apply loop.spec_decr_nat
    (fun state : Transcript × alloc.vec.Vec Std.U32 × Std.Usize =>
      64 - state.2.2.val)
    (OuterSamplerInvariant self out draws consumedBlocks)
    (OuterSamplerPost self out draws consumedBlocks)
  · rintro ⟨currentSelf, currentOut, currentDraws⟩ hinvariant
    rcases hinvariant with
      ⟨hcurrentOut, hcurrentDraws, blocks, htrace, happend⟩
    dsimp only at hcurrentOut hcurrentDraws happend ⊢
    unfold V5TranscriptPrimitivesGenerated.aspis_core.transcript.Transcript.challenge_queries_without_replacement_loop0.body
    by_cases hactive : currentDraws.val < 64
    · have hactiveScalar : currentDraws < 64#usize := by
        scalar_tac
      rw [if_pos hactiveScalar]
      let block := currentSelf.hash (squeezeOutputInput currentSelf)
      let nextSelf : Transcript :=
        { currentSelf with
            state := currentSelf.hash (squeezeAdvanceInput currentSelf) }
      have hsqueeze :
          V5TranscriptPrimitivesGenerated.aspis_core.transcript.Transcript.squeeze_block
              currentSelf = .ok (block, nextSelf) := by
        simpa [block, nextSelf] using squeeze_block_run_is_exact currentSelf
      rw [hsqueeze]
      simp only [bind_tc_ok, lift]
      rw [chunks_exact_block_is_blockChunks block]
      simp only [bind_tc_ok]
      have hinner := generated_inner_loop_matches_scanWords
        (blockChunks block) currentOut currentDraws
        (consumedBlocks + blocks.length + 1)
        (validWordIterator_blockChunks block) hcurrentOut hcurrentDraws
      obtain ⟨innerResult, hinnerRun, hinnerPost⟩ :=
        Aeneas.Std.WP.spec_imp_exists hinner
      rcases innerResult with ⟨nextOut, nextDraws, marker⟩
      rw [hinnerRun]
      simp only [bind_tc_ok]
      let bumped : BlockScanState :=
        generatedBlockScanState currentOut currentDraws
          (consumedBlocks + blocks.length + 1)
      let scanned : WordScanResult :=
        scanWords 18 64 bumped (blockQueryCandidates (arrayDigest block))
      have hbumpedFromCurrent :
          { generatedBlockScanState currentOut currentDraws
              (consumedBlocks + blocks.length) with
            consumedBlocks :=
              (generatedBlockScanState currentOut currentDraws
                (consumedBlocks + blocks.length)).consumedBlocks + 1 } =
            bumped := by
        rfl
      have hinnerState :
          generatedBlockScanState nextOut nextDraws
              (consumedBlocks + blocks.length + 1) = scanned.state := by
        exact hinnerPost.1.trans (by
          simp only [scanned, bumped]
          rw [blockChunks_candidates])
      have hmarker : marker.val = wordScanMarker scanned := by
        simpa only [scanned, bumped, blockChunks_candidates] using hinnerPost.2
      have hnextOut : nextOut.val.length ≤ 18 := by
        have hmodel := scanWords_accepted_length_le 18 64 bumped
          (blockQueryCandidates (arrayDigest block)) (by
            simpa [bumped] using hcurrentOut)
        have haccepted := congrArg
          (fun state : BlockScanState => state.accepted.length) hinnerState
        simp only [generatedBlockScanState_accepted] at haccepted
        rw [← vecNats_length nextOut]
        rw [haccepted]
        exact hmodel
      have hnextDrawsLe : nextDraws.val ≤ 64 := by
        have hmodel := scanWords_draws_le 18 64 bumped
          (blockQueryCandidates (arrayDigest block)) (by
            simpa [bumped] using hcurrentDraws)
        have hdrawEq := congrArg BlockScanState.draws hinnerState
        simp only [generatedBlockScanState_draws] at hdrawEq
        rw [hdrawEq]
        exact hmodel
      by_cases hcontinue : marker = 1#u32
      · subst marker
        simp_scalar
        have hnotStopped : scanned.stopOuter = false := by
          cases hstop : scanned.stopOuter <;>
            simp [wordScanMarker, hstop] at hmarker ⊢
        have hnextDraws : nextDraws.val = currentDraws.val + 8 := by
          have hmodel := scanWords_draws_of_not_stopped 18 64 bumped
            (blockQueryCandidates (arrayDigest block)) hnotStopped
          calc
            nextDraws.val = scanned.state.draws := by
              simpa [generatedBlockScanState] using
                congrArg BlockScanState.draws hinnerState
            _ = bumped.draws +
                (blockQueryCandidates (arrayDigest block)).length := hmodel
            _ = currentDraws.val + 8 := by
              simp [bumped, blockQueryCandidates]
        let nextBlocks := blocks ++ [block]
        have hnextTrace :
            ExactSqueezeTrace self nextBlocks nextSelf := by
          exact exactSqueezeTrace_append_one htrace hsqueeze
        refine ⟨⟨hnextOut, hnextDrawsLe, nextBlocks, hnextTrace, ?_⟩, ?_⟩
        · intro suffix
          have hold := happend
            (blockQueryCandidates (arrayDigest block) :: suffix)
          simp only [nextBlocks, generatedCandidateBlocks_append,
            generatedCandidateBlocks_cons, generatedCandidateBlocks_nil,
            List.append_nil, List.append_assoc, List.singleton_append]
          rw [hold]
          rw [scanBlocks]
          simp only [generatedBlockScanState_draws, if_pos hactive]
          change (if scanned.stopOuter = true then scanned.state else
            scanBlocks 18 64 scanned.state suffix) = _
          simp only [hnotStopped, Bool.false_eq_true, ↓reduceIte]
          rw [← hinnerState]
          simpa [nextBlocks, generatedBlockScanState, Nat.add_assoc]
        · rw [hnextDraws]
          omega
      · have hstopped : scanned.stopOuter = true := by
          cases hstop : scanned.stopOuter
          · exfalso
            apply hcontinue
            apply UScalar.eq_of_val_eq
            simpa [wordScanMarker, hstop] using hmarker
          · rfl
        have hzero : marker = 0#u32 := by
          apply UScalar.eq_of_val_eq
          simpa [wordScanMarker, hstopped] using hmarker
        subst marker
        simp_scalar
        let finalBlocks := blocks ++ [block]
        refine ⟨finalBlocks, nextDraws,
          exactSqueezeTrace_append_one htrace hsqueeze,
          hnextDrawsLe, hnextOut, ?_⟩
        have hold := happend
          [blockQueryCandidates (arrayDigest block)]
        simp only [finalBlocks, generatedCandidateBlocks_append,
          generatedCandidateBlocks_cons, generatedCandidateBlocks_nil,
          List.append_nil, List.append_assoc, List.singleton_append]
        rw [hold]
        rw [scanBlocks]
        simp only [generatedBlockScanState_draws, if_pos hactive]
        change (if scanned.stopOuter = true then scanned.state else
          scanBlocks 18 64 scanned.state []) = _
        simp only [hstopped, ↓reduceIte]
        rw [← hinnerState]
        simpa [finalBlocks, generatedBlockScanState, Nat.add_assoc]
    · have hdrawsEq : currentDraws.val = 64 := by omega
      have hinactiveScalar : ¬ currentDraws < 64#usize := by
        scalar_tac
      rw [if_neg hinactiveScalar]
      simp only [Aeneas.Std.WP.spec_ok]
      refine ⟨blocks, currentDraws, htrace, hcurrentDraws,
        hcurrentOut, ?_⟩
      have hold := happend []
      simpa [scanBlocks] using hold
  · refine ⟨hout, hdraws, [], ExactSqueezeTrace.nil self, ?_⟩
    intro suffix
    rfl

#print axioms generated_inner_loop_matches_scanWords
#print axioms generated_outer_loop_matches_scanBlocks

end V5QuerySamplerGeneratedSemantics
