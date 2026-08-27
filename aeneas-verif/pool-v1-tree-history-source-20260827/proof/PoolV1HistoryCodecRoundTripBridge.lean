import PoolV1HistoryPersist.Funs
import PoolV1HistoryRead.Funs
import Aeneas.Tactic.Step.Step

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 10000

namespace PoolV1HistoryCodecRoundTripBridge

open Aeneas Aeneas.Std Result ControlFlow Error

namespace Persist

open PoolV1HistoryPersistGenerated

abbrev Digest := Array aspis_core.field.M31 8#usize
abbrev DigestIter := core.iter.adapters.enumerate.Enumerate
  (core.slice.iter.Iter aspis_core.field.M31)

def encodedPrefix (digest : Slice aspis_core.field.M31) : Nat → List Std.U8
  | 0 => List.replicate 32 0#u8
  | position + 1 =>
      if active : position < digest.val.length then
        (encodedPrefix digest position).setSlice! (position * 4)
          (core.num.U32.to_le_bytes digest[position]).val
      else encodedPrefix digest position

@[simp] theorem encodedPrefix_length
    (digest : Slice aspis_core.field.M31) (position : Nat) :
    (encodedPrefix digest position).length = 32 := by
  induction position with
  | zero => simp [encodedPrefix]
  | succ position ih =>
      by_cases active : position < digest.val.length
      · rw [encodedPrefix, dif_pos active, List.length_setSlice!, ih]
      · rw [encodedPrefix, dif_neg active, ih]

def digestLoopInvariant
    (digest : Slice aspis_core.field.M31)
    (state : DigestIter × Array Std.U8 32#usize) : Prop :=
  state.1.iter.slice = digest ∧
  state.1.iter.i ≤ digest.val.length ∧
  digest.val.length = 8 ∧
  state.1.count.val = state.1.iter.i ∧
  state.2.val = encodedPrefix digest state.1.iter.i

theorem encode_digest_canonical_loop_exact
    (digest : Slice aspis_core.field.M31)
    (iter : DigestIter) (bytes : Array Std.U8 32#usize)
    (hinvariant : digestLoopInvariant digest (iter, bytes)) :
    aspis_statement.atomic_statement.encode_digest_canonical_loop iter bytes
      ⦃ output => output.val = encodedPrefix digest digest.val.length ⦄ := by
  simp only [aspis_statement.atomic_statement.encode_digest_canonical_loop]
  apply Aeneas.Std.loop.spec_decr_nat
    (fun state : DigestIter × Array Std.U8 32#usize =>
      digest.val.length - state.1.iter.i)
    (digestLoopInvariant digest)
    (fun output : Array Std.U8 32#usize =>
      output.val = encodedPrefix digest digest.val.length)
  · rintro ⟨nextIter, nextBytes⟩ hnext
    unfold aspis_statement.atomic_statement.encode_digest_canonical_loop.body
    simp only [digestLoopInvariant, Prod.fst, Prod.snd] at hnext
    rcases hnext with ⟨hslice, hposition, hlength, hcount, hbytes⟩
    by_cases hactive : nextIter.iter.i < digest.val.length
    · have hactiveEight : nextIter.iter.i < 8 := by omega
      have hcountLt : nextIter.count.val < 8 := by omega
      have hbytesBound : nextIter.iter.i * 4 ≤ 28 := by omega
      have hsliceLength :
          (List.slice (nextIter.iter.i * 4)
            (nextIter.iter.i * 4 + 4) nextBytes.val).length = 4 := by
        simp only [List.slice_length, nextBytes.property]
        norm_num
        omega
      simp [core.iter.adapters.enumerate.IteratorEnumerate.next,
        core.slice.iter.IteratorSliceIter.next, hactive, hactiveEight,
        digestLoopInvariant, Std.lift, Array.to_slice,
        core.array.Array.index_mut, core.ops.index.IndexMutSlice,
        core.slice.index.Slice.index_mut,
        core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
        core.slice.Slice.copy_from_slice, Array.from_slice,
        Slice.len, Slice.length,
        aspis_core.field.M31.to_le_bytes, hlength, hcount, hcountLt,
        hbytesBound, hsliceLength, hslice]
      repeat' step
      all_goals simp_all [digestLoopInvariant, encodedPrefix,
        encodedPrefix_length,
        Std.lift, Array.to_slice, core.num.U32.to_le_bytes]
      all_goals try omega
    · have done : nextIter.iter.i = digest.val.length := by omega
      simp [core.iter.adapters.enumerate.IteratorEnumerate.next,
        core.slice.iter.IteratorSliceIter.next, hactive, done, hbytes, hslice]
  · exact hinvariant

theorem encode_digest_canonical_success_exact
    (digest : Digest) (output : Array Std.U8 32#usize)
    (run : aspis_statement.atomic_statement.encode_digest_canonical digest =
      .ok output) :
    output.val = encodedPrefix (Array.to_slice digest) digest.val.length := by
  have spec :
      aspis_statement.atomic_statement.encode_digest_canonical digest
        ⦃ result => result.val =
          encodedPrefix (Array.to_slice digest) digest.val.length ⦄ := by
    unfold aspis_statement.atomic_statement.encode_digest_canonical
    simp only [Std.lift, Array.to_slice, bind_tc_ok,
      core.slice.Slice.iter,
      core.iter.traits.iterator.Iterator.enumerate.trait_default,
      core.iter.traits.iterator.Iterator.enumerate.default, bind_tc_ok]
    apply encode_digest_canonical_loop_exact
    simp [digestLoopInvariant, encodedPrefix, digest.property]
  rw [run] at spec
  exact spec

end Persist

theorem word32_u32_to_le_bytes (value : Std.U32) :
    word32 (core.num.U32.to_le_bytes value).val = value := by
  apply UScalar.eq_of_val_eq
  have valueBound := value.lt_succ_max
  simp [word32, u32, core.num.U32.to_le_bytes, BitVec.toLEBytes]
  change
    (BitVec.setWidth 8 value.bv).toNat +
      256 * (BitVec.setWidth 8 (value.bv >>> 8)).toNat +
      65536 *
        (BitVec.setWidth 8
          (BitVec.setWidth 24 (value.bv >>> 8) >>> 8)).toNat +
      16777216 *
        (BitVec.setWidth 8
          (BitVec.setWidth 16
            (BitVec.setWidth 24 (value.bv >>> 8) >>> 8) >>> 8)).toNat =
      value.bv.toNat
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  norm_num only [Nat.reducePow]
  have q1Bound : value.bv.toNat / 256 < 16777216 := by
    have := valueBound
    omega
  have q2Bound : value.bv.toNat / 65536 < 65536 := by
    have := valueBound
    omega
  have q3Bound : value.bv.toNat / 16777216 < 256 := by
    have := valueBound
    omega
  simp only [Nat.mod_eq_of_lt q1Bound, Nat.mod_eq_of_lt q2Bound,
    Nat.mod_eq_of_lt q3Bound, Nat.div_div_eq_div_mul]
  norm_num only [Nat.reduceMul]
  change
    value.val % 256 +
      256 * ((value.val / 256) % 256) +
      65536 * ((value.val / 65536) % 256) +
      16777216 * (value.val / 16777216) =
      value.val
  have level0 := Nat.mod_add_div value.val 256
  have level1 := Nat.mod_add_div (value.val / 256) 256
  have level2 := Nat.mod_add_div (value.val / 65536) 256
  have div2 : value.val / 256 / 256 = value.val / 65536 := by
    simpa [Nat.div_div_eq_div_mul] using
      (Nat.div_div_eq_div_mul value.val 256 256)
  have div3 : value.val / 65536 / 256 = value.val / 16777216 := by
    simpa [Nat.div_div_eq_div_mul] using
      (Nat.div_div_eq_div_mul value.val 65536 256)
  rw [div3] at level2
  rw [div2] at level1
  have decomposition :
      value.val % 256 +
        256 * ((value.val / 256) % 256) +
        65536 * ((value.val / 65536) % 256) +
        16777216 * (value.val / 16777216) = value.val := by
    calc
      _ = value.val % 256 + 256 *
          ((value.val / 256) % 256 + 256 *
            ((value.val / 65536) % 256 + 256 *
              (value.val / 16777216))) := by ring
      _ = value.val % 256 + 256 *
          ((value.val / 256) % 256 + 256 *
            (value.val / 65536)) := by rw [level2]
      _ = value.val % 256 + 256 * (value.val / 256) := by rw [level1]
      _ = value.val := level0
  rw [decomposition]

theorem encodedPrefix_wordAt_exact
    (digest : Persist.Digest) (index : Fin 8) :
    wordAt (Persist.encodedPrefix (Array.to_slice digest) 8) index.val =
      digest[index.val] := by
  have written : ∀ (position slot byte : Nat),
      position ≤ 8 → slot < position → byte < 4 →
      (Persist.encodedPrefix (Array.to_slice digest) position)[4 * slot + byte]? =
        (core.num.U32.to_le_bytes digest.val[slot]!).val[byte]? := by
    intro position
    induction position with
    | zero => simp
    | succ position inductionHypothesis =>
        intro slot byte positionBound slotBound byteBound
        have active : position < digest.val.length := by
          have digestLength : digest.val.length = 8 := by
            simpa using digest.property
          omega
        have activeSlice :
            position < (Array.to_slice digest).val.length := by
          simpa [Array.to_slice] using active
        rw [Persist.encodedPrefix, dif_pos activeSlice]
        by_cases current : slot = position
        · subst slot
          rw [List.setSlice!_getElem?_middle]
          · rw [← List.Inhabited_getElem_eq_getElem! digest.val position active]
            congr 1
            omega
          · constructor
            · omega
            constructor
            · have currentBytesLength :
                  (core.num.U32.to_le_bytes
                    (Array.to_slice digest)[position]).val.length = 4 := by
                  simp [core.num.U32.to_le_bytes]
              rw [currentBytesLength]
              omega
            · rw [Persist.encodedPrefix_length]
              omega
        · have earlier : slot < position := by omega
          rw [List.setSlice!_getElem?_prefix]
          · exact inductionHypothesis slot byte (by omega) earlier byteBound
          · omega
  unfold wordAt
  have chunkExact :
      ((Persist.encodedPrefix (Array.to_slice digest) 8).drop
          (4 * index.val)).take 4 =
        (core.num.U32.to_le_bytes digest.val[index.val]!).val := by
    apply List.ext_getElem?
    intro byte
    by_cases byteBound : byte < 4
    · simp only [List.getElem?_take, byteBound, ↓reduceIte,
        List.getElem?_drop]
      exact written 8 index.val byte (by omega) index.isLt byteBound
    · have encodedLength :
          (core.num.U32.to_le_bytes digest.val[index.val]!).val.length = 4 := by
        simp [core.num.U32.to_le_bytes]
      simp [List.getElem?_take, byteBound, encodedLength]
  have word32Take (bytes : List Std.U8) :
      word32 bytes = word32 (bytes.take 4) := by
    simp [word32]
  rw [word32Take, chunkExact]
  rw [word32_u32_to_le_bytes]
  have digestIndexBound : index.val < digest.val.length := by
    have digestLength : digest.val.length = 8 := by simpa using digest.property
    omega
  exact (List.Inhabited_getElem_eq_getElem! digest.val index.val
    digestIndexBound).symm

theorem canonicalWord_encodedPrefix_exact
    (digest : Persist.Digest)
    (canonical : ∀ index : Fin 8, digest.val[index.val].val < m31Prime)
    (index : Fin 8) :
    canonicalWord (Persist.encodedPrefix (Array.to_slice digest) 8)
      index.val = some digest[index.val] := by
  unfold canonicalWord
  rw [encodedPrefix_wordAt_exact]
  simp [canonical index]

theorem decodeDigest_encodedPrefix_exact
    (digest : Persist.Digest)
    (canonical : ∀ index : Fin 8, digest.val[index.val].val < m31Prime) :
    decodeDigest (Persist.encodedPrefix (Array.to_slice digest) 8) =
      some digest := by
  unfold decodeDigest
  have present : ∀ index : Fin 8,
      (canonicalWord (Persist.encodedPrefix (Array.to_slice digest) 8)
        index.val).isSome := by
    intro index
    rw [canonicalWord_encodedPrefix_exact digest canonical index]
    rfl
  rw [dif_pos present]
  congr 1
  apply Subtype.ext
  apply List.ext_getElem
  · simpa using digest.property.symm
  · intro index leftBound rightBound
    have indexBound : index < 8 := by simpa using leftBound
    let finite : Fin 8 := ⟨index, indexBound⟩
    simp only [List.getElem_ofFn]
    have encoded := canonicalWord_encodedPrefix_exact digest canonical finite
    obtain ⟨someProof, getExact⟩ := Option.eq_some_iff_get_eq.mp encoded
    rw [← Array.getElem_Nat_eq digest index rightBound]
    exact getExact

theorem source_encoder_decoder_round_trip
    (digest : Persist.Digest) (output : Array Std.U8 32#usize)
    (canonical : ∀ index : Fin 8, digest.val[index.val].val < m31Prime)
    (run :
      PoolV1HistoryPersistGenerated.aspis_statement.atomic_statement.encode_digest_canonical
        digest = .ok output) :
    decodeDigest output.val = some digest := by
  rw [Persist.encode_digest_canonical_success_exact digest output run]
  simpa using decodeDigest_encodedPrefix_exact digest canonical

#print axioms Persist.encode_digest_canonical_loop_exact
#print axioms Persist.encode_digest_canonical_success_exact
#print axioms encodedPrefix_wordAt_exact
#print axioms decodeDigest_encodedPrefix_exact
#print axioms source_encoder_decoder_round_trip

end PoolV1HistoryCodecRoundTripBridge
