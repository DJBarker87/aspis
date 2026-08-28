import V7FirstCompactSamplerOuterBridge

open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false

namespace V7FirstCompactSamplerNativeBlockBridge

open V7FirstCompactSamplerLoop16Bridge
open V7FirstCompactSamplerOuterBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73SamplerDecoder

universe u v

abbrev FunctionCodomain {α : Sort u} {β : Sort v} (_ : α → β) : Sort v := β

/-- Exact block type from the translated Tag-73 transcript field; this avoids
re-elaborating Aeneas' proof-carrying `32#usize` literal. -/
abbrev NativeQueryBlock : Type :=
  FunctionCodomain V7FirstCompactSource.transcript.Transcript.state

def nativeWordSlice (block : NativeQueryBlock) (word : Fin 8) :
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

def nativeBlockChunks (block : NativeQueryBlock) :
    core.slice.iter.ChunksExact Std.U8 where
  chunks := List.ofFn (nativeWordSlice block)
  remainder := ⟨[], by simp⟩

@[irreducible] def nativeSourceDigest
    (block : NativeQueryBlock) : Digest256 :=
  fun (index : Fin 32) => UInt8.ofNat
    (block.val[index.val]'(by
      have hindex := index.isLt
      simpa [block.property] using hindex)).val

@[simp] theorem nativeSourceDigest_toNat
    (block : NativeQueryBlock) (index : Fin 32) :
    (nativeSourceDigest block index).toNat =
      (block.val[index.val]'(by
        have hindex := index.isLt
        simpa [block.property] using hindex)).val := by
  unfold nativeSourceDigest
  change (BitVec.ofNat 8
    (block.val[index.val]'(by
      have hindex := index.isLt
      simpa [block.property] using hindex)).val).toNat = _
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have hbyte := (block.val[index.val]'(by
    have hindex := index.isLt
    simpa [block.property] using hindex)).hBounds
  simpa [UScalarTy.numBits] using hbyte

def nativeWordArray (block : NativeQueryBlock) (word : Fin 8) :
    Array Std.U8 4#usize :=
  ⟨(nativeWordSlice block word).val, by simp [nativeWordSlice]⟩

theorem native_word_value_eq_k13
    (block : NativeQueryBlock) (word : Fin 8) :
    (core.num.U32.from_le_bytes (nativeWordArray block word)).val =
      littleEndianWord (nativeSourceDigest block) word := by
  unfold core.num.U32.from_le_bytes UScalar.val
  rw [BitVec.toNat_cast]
  have hbytes :
      List.map Std.U8.bv (nativeWordArray block word).val =
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
    simp [nativeWordArray, nativeWordSlice]
  rw [hbytes, V5QuerySamplerGeneratedSemantics.fromLEBytes_four_toNat]
  unfold littleEndianWord
  repeat rw [nativeSourceDigest_toNat]
  simp only [UScalar.val]
  simp only [Nat.add_zero]

theorem native_candidate_eq_k13
    (block : NativeQueryBlock) (word : Fin 8) :
    ((core.num.U32.from_le_bytes (nativeWordArray block word)) &&&
        q16Mask).val =
      q16Candidate (littleEndianWord (nativeSourceDigest block) word) := by
  change ((core.num.U32.from_le_bytes (nativeWordArray block word)) &&&
    262143#u32).val = _
  rw [V7FirstCompactSamplerInnerBridge.current_q16_mask_is_exact]
  exact congrArg q16Candidate (native_word_value_eq_k13 block word)

theorem native_candidateOfSlice_wordSlice
    (block : NativeQueryBlock) (word : Fin 8) :
    candidateOfSlice (nativeWordSlice block word) =
      q16Candidate (littleEndianWord (nativeSourceDigest block) word) := by
  unfold candidateOfSlice
  simp only [nativeWordSlice, List.length_ofFn, ↓reduceDIte]
  rw [← native_candidate_eq_k13 block word]
  rfl

theorem native_iteratorCandidates_blockChunks (block : NativeQueryBlock) :
    iteratorCandidates (nativeBlockChunks block) =
      (blockWords (nativeSourceDigest block)).map q16Candidate := by
  simp [iteratorCandidates, nativeBlockChunks, blockWords,
    native_candidateOfSlice_wordSlice]

theorem native_validWordIterator_blockChunks (block : NativeQueryBlock) :
    ValidWordIterator (nativeBlockChunks block) := by
  intro word hword
  simp only [nativeBlockChunks, List.mem_ofFn] at hword
  rcases hword with ⟨index, rfl⟩
  simp [nativeWordSlice]

#print axioms native_word_value_eq_k13
#print axioms native_candidate_eq_k13
#print axioms native_iteratorCandidates_blockChunks
#print axioms native_validWordIterator_blockChunks

end V7FirstCompactSamplerNativeBlockBridge
