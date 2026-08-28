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

/-- Stable byte view of a translated 32-byte squeeze block. The source array's
proof-carrying scalar length is deliberately erased after its byte length is
proved, so no re-elaborated scalar proof enters the semantic codec boundary. -/
def NativeQueryBlock : Type := { bytes : List Std.U8 // bytes.length = 32 }

abbrev SuccessfulFirstOfResultFunction
    {input first second : Type}
    (_ : input → Result (first × second)) : Type := first

/-- Literal array type returned by the translated production squeeze. -/
abbrev SourceSqueezeBlock : Type :=
  SuccessfulFirstOfResultFunction
    V7FirstCompactSource.transcript.Transcript.squeeze_block

def sourceSqueezeBytes (block : SourceSqueezeBlock) : NativeQueryBlock :=
  ⟨block.val, by simpa using block.property⟩

def nativeSourceSlice (block : NativeQueryBlock) : Slice Std.U8 :=
  ⟨block.val, by
    rw [block.property]
    scalar_tac⟩

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

/-- The literal current-source `Array.to_slice(...).chunks_exact(4)` call
returns the production-native iterator used by the codec theorems above. -/
theorem native_chunks_exact_block_is_nativeBlockChunks
    (block : NativeQueryBlock) :
    core.slice.Slice.chunks_exact (nativeSourceSlice block) 4#usize =
      .ok (nativeBlockChunks block) := by
  unfold core.slice.Slice.chunks_exact nativeSourceSlice nativeBlockChunks
    nativeWordSlice
  simp only [show (4#usize : Std.Usize).val > 0 by decide, ↓reduceDIte,
    block.property]
  simp only [Result.ok.injEq]
  apply V5QuerySamplerGeneratedSemantics.chunksExact_ext
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

@[simp] theorem sourceSqueezeBytes_value (block : SourceSqueezeBlock) :
    (sourceSqueezeBytes block).val = block.val := rfl

/-- The stable byte slice is byte-for-byte the literal translated source
array slice; only the proof-carrying scalar length witness is erased. -/
theorem sourceSqueezeSlice_eq_nativeSourceSlice
    (block : SourceSqueezeBlock) :
    Array.to_slice block = nativeSourceSlice (sourceSqueezeBytes block) := by
  apply Subtype.ext
  rfl

/-- Exact source-facing chunks endpoint, stated with the literal squeeze return
type rather than a separately elaborated `Array U8 32#usize`. -/
theorem sourceSqueeze_chunks_exact_is_nativeBlockChunks
    (block : SourceSqueezeBlock) :
    core.slice.Slice.chunks_exact (Array.to_slice block) 4#usize =
      .ok (nativeBlockChunks (sourceSqueezeBytes block)) := by
  rw [sourceSqueezeSlice_eq_nativeSourceSlice block]
  exact native_chunks_exact_block_is_nativeBlockChunks
    (sourceSqueezeBytes block)

#print axioms native_word_value_eq_k13
#print axioms native_candidate_eq_k13
#print axioms native_iteratorCandidates_blockChunks
#print axioms native_validWordIterator_blockChunks
#print axioms native_chunks_exact_block_is_nativeBlockChunks
#print axioms sourceSqueezeSlice_eq_nativeSourceSlice
#print axioms sourceSqueeze_chunks_exact_is_nativeBlockChunks

end V7FirstCompactSamplerNativeBlockBridge
