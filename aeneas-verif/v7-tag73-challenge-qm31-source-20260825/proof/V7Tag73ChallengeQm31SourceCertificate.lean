import V7Tag73ChallengeQm31.Funs
import AspisFormal.K1.V7Tag73SamplerDecoderExact

/-!
# Source certificate for the deployed Tag-73 `challenge_qm31`

This file reasons about the transparent Charon/Aeneas translation of the
deployed Rust method.  It does not assign a distribution to SHA-256 and does
not postulate sampler faithfulness.  The hash callback remains an arbitrary
total function supplied by the transcript value; every input to it is exposed
below.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
open V7Tag73ChallengeQm31Generated

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace V7Tag73ChallengeQm31SourceCertificate

abbrev Transcript :=
  V7Tag73ChallengeQm31Generated.aspis_core.transcript.Transcript

abbrev M31 := V7Tag73ChallengeQm31Generated.aspis_core.field.M31

abbrev QM31 := V7Tag73ChallengeQm31Generated.aspis_core.field.QM31

def taggedBytes (self : Transcript) (domain : Std.U8) :
    Array Std.U8 33#usize :=
  ⟨self.state.val ++ [domain], by simp [self.state.property]⟩

def taggedHashInput (self : Transcript) (domain : Std.U8) :
    Slice (Slice Std.U8) :=
  ⟨[⟨(taggedBytes self domain).val, by scalar_tac⟩], by scalar_tac⟩

@[simp] theorem taggedBytes_val (self : Transcript) (domain : Std.U8) :
    (taggedBytes self domain).val = self.state.val ++ [domain] := rfl

@[simp] theorem taggedHashInput_val (self : Transcript) (domain : Std.U8) :
    (taggedHashInput self domain).val =
      [⟨self.state.val ++ [domain], by scalar_tac⟩] := by
  rfl

def exactSqueezeRun (self : Transcript) :
    Result ((Array Std.U8 32#usize) × Transcript) := do
  let out ← self.hash (taggedHashInput self 1#u8)
  let nextState ← self.hash (taggedHashInput self 2#u8)
  let nextSelf : Transcript := { self with state := nextState }
  ok (out, nextSelf)

/-- `squeeze_block` hashes exactly `state || 1` for its output block and
`state || 2` for its successor state. -/
theorem squeeze_block_run_is_exact (self : Transcript) :
    V7Tag73ChallengeQm31Generated.aspis_core.transcript.Transcript.squeeze_block
        self = exactSqueezeRun self := by
  have stateLength : self.state.val.length = 32 := by
    simpa using self.state.property
  have takeState : List.take 32 self.state.val = self.state.val := by
    apply List.take_of_length_le
    omega
  simp [V7Tag73ChallengeQm31Generated.aspis_core.transcript.Transcript.squeeze_block,
    exactSqueezeRun, taggedHashInput, taggedBytes, lift,
    core.array.Array.index_mut,
    core.ops.index.IndexMutSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    core.slice.Slice.copy_from_slice, Array.repeat, Array.update,
    Array.to_slice, Array.make, List.setSlice!, Slice.len, stateLength,
    takeState,
    V7Tag73ChallengeQm31Generated.aspis_core.transcript.DOM_SQUEEZE,
    V7Tag73ChallengeQm31Generated.aspis_core.transcript.DOM_ADVANCE]

def wordSlice (block : Array Std.U8 32#usize) (word : Fin 8) : Slice Std.U8 :=
  ⟨List.ofFn (fun byte : Fin 4 =>
      block.val[4 * word.val + byte.val]'(by
        have hw := word.isLt
        have hb : block.val.length = 32 := by simpa using block.property
        omega)),
    by simp; scalar_tac⟩

def wordArray (block : Array Std.U8 32#usize) (word : Fin 8) :
    Array Std.U8 4#usize :=
  ⟨(wordSlice block word).val, by simp [wordSlice]⟩

def littleEndianWord (block : Array Std.U8 32#usize) (word : Fin 8) : Nat :=
  (block.val[4 * word.val + 0]'(by
      have hw := word.isLt
      have hb : block.val.length = 32 := by simpa using block.property
      omega)).val +
    256 * (block.val[4 * word.val + 1]'(by
      have hw := word.isLt
      have hb : block.val.length = 32 := by simpa using block.property
      omega)).val +
    65536 * (block.val[4 * word.val + 2]'(by
      have hw := word.isLt
      have hb : block.val.length = 32 := by simpa using block.property
      omega)).val +
    16777216 * (block.val[4 * word.val + 3]'(by
      have hw := word.isLt
      have hb : block.val.length = 32 := by simpa using block.property
      omega)).val

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

theorem generated_word_value_eq_littleEndianWord
    (block : Array Std.U8 32#usize) (word : Fin 8) :
    (core.num.U32.from_le_bytes (wordArray block word)).val =
      littleEndianWord block word := by
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
  simp [littleEndianWord]

theorem generated_mask_eq_decoder_mask
    (word : Std.U32) :
    (word &&& 2147483647#u32).val =
      AspisK1.V7Tag73SamplerDecoder.maskedM31 word.val := by
  rw [UScalar.val_and]
  change word.val &&& (2 ^ 31 - 1) =
    AspisK1.V7Tag73SamplerDecoder.maskedM31 word.val
  rw [Nat.and_two_pow_sub_one_eq_mod]
  rfl

theorem generated_candidate_eq_decoder_mask
    (block : Array Std.U8 32#usize) (word : Fin 8) :
    ((core.num.U32.from_le_bytes (wordArray block word)) &&&
        2147483647#u32).val =
      AspisK1.V7Tag73SamplerDecoder.maskedM31
        (littleEndianWord block word) := by
  rw [generated_mask_eq_decoder_mask,
    generated_word_value_eq_littleEndianWord]

theorem generated_rejects_exactly_noncanonical
    (word : Std.U32) :
    ((word &&& 2147483647#u32) = 2147483647#u32) ↔
      AspisK1.V7Tag73SamplerDecoder.maskedM31 word.val =
        AspisK1.V7Tag73SamplerDecoder.m31Prime := by
  constructor
  · intro equality
    have valueEquality := congrArg UScalar.val equality
    rw [generated_mask_eq_decoder_mask] at valueEquality
    norm_num [AspisK1.V7Tag73SamplerDecoder.m31Prime] at valueEquality ⊢
    exact valueEquality
  · intro equality
    apply UScalar.eq_of_val_eq
    rw [generated_mask_eq_decoder_mask]
    norm_num [AspisK1.V7Tag73SamplerDecoder.m31Prime] at equality ⊢
    exact equality

/-- The extracted wrapper is definitionally the extracted source method. -/
theorem wrapper_calls_source_method (self : Transcript) :
    V7Tag73ChallengeQm31Generated.extract_challenge_qm31 self =
      V7Tag73ChallengeQm31Generated.aspis_core.transcript.Transcript.challenge_qm31
        self := rfl

/-- The two source constants close to the exact deployed values. -/
theorem deployed_sampler_constants :
    V7Tag73ChallengeQm31Generated.aspis_core.transcript.CHALLENGE_RETRY_LIMIT =
        8#u32 ∧
      V7Tag73ChallengeQm31Generated.aspis_core.field.P =
        .ok 2147483647#u32 ∧
      V7Tag73ChallengeQm31Generated.aspis_core.field.M31.ZERO =
        .ok 0#u32 := by
  simp [V7Tag73ChallengeQm31Generated.aspis_core.transcript.CHALLENGE_RETRY_LIMIT,
    V7Tag73ChallengeQm31Generated.aspis_core.field.P,
    V7Tag73ChallengeQm31Generated.aspis_core.field.M31.ZERO]

/-- A source-shaped normal form for the complete method.  The only callback
left in this definition is the transcript's concrete hash function, invoked
through `exactSqueezeRun`; the retry loops themselves are transparent. -/
def sourceSamplerRun (self : Transcript) :
    Result ((core.result.Result QM31 Unit) × Transcript) := do
  let limbs := Array.repeat 4#usize (0#u32 : M31)
  let (block, self1) ← exactSqueezeRun self
  let (slice, toSliceMutBack) ← lift (Array.to_slice_mut limbs)
  let (iter, iterMutBack) ← core.slice.Slice.iter_mut slice
  let (self2, pendingReturn, back) ←
    V7Tag73ChallengeQm31Generated.aspis_core.transcript.Transcript.challenge_qm31_loop0
      iter (fun im => im) self1 block 0#usize
  match pendingReturn with
  | none =>
      let finalSlice := iterMutBack back
      let finalLimbs := toSliceMutBack finalSlice
      let m0 ← Array.index_usize finalLimbs 0#usize
      let m1 ← Array.index_usize finalLimbs 1#usize
      let m2 ← Array.index_usize finalLimbs 2#usize
      let m3 ← Array.index_usize finalLimbs 3#usize
      ok (.Ok { c0 := { a := m0, b := m1 },
                  c1 := { a := m2, b := m3 } }, self2)
  | some result => ok (result, self2)

theorem challenge_qm31_eq_sourceSamplerRun (self : Transcript) :
    V7Tag73ChallengeQm31Generated.aspis_core.transcript.Transcript.challenge_qm31
        self = sourceSamplerRun self := by
  unfold
    V7Tag73ChallengeQm31Generated.aspis_core.transcript.Transcript.challenge_qm31
    sourceSamplerRun
  simp only [V7Tag73ChallengeQm31Generated.aspis_core.field.M31.ZERO,
    bind_tc_ok]
  rw [squeeze_block_run_is_exact]
  rfl

@[simp] theorem initial_limb_buffer_is_four_zeros :
    (Array.repeat 4#usize (0#u32 : M31)).val =
      [0#u32, 0#u32, 0#u32, 0#u32] := by
  rfl

/-- The success constructor uses the deployed `(c0.a,c0.b,c1.a,c1.b)`
coordinate order, with no permutation or compression. -/
theorem four_limb_output_order (m0 m1 m2 m3 : M31) :
    (do
      let limbs : Array M31 4#usize := ⟨[m0, m1, m2, m3], by simp⟩
      let a ← Array.index_usize limbs 0#usize
      let b ← Array.index_usize limbs 1#usize
      let c ← Array.index_usize limbs 2#usize
      let d ← Array.index_usize limbs 3#usize
      ok ({ c0 := { a := a, b := b }, c1 := { a := c, b := d } } : QM31)) =
      .ok { c0 := { a := m0, b := m1 }, c1 := { a := m2, b := m3 } } := by
  simp [Array.index_usize]

/-- The source invokes exactly the range `0..8` for every limb selected by
the four-element mutable iterator. -/
theorem outer_body_uses_exact_eight_attempt_range
    (iter : core.slice.iter.IterMut M31)
    (back : core.slice.iter.IterMut M31 → core.slice.iter.IterMut M31)
    (self : Transcript) (block : Array Std.U8 32#usize)
    (wordIndex : Std.Usize) (limb : M31)
    (nextIter : core.slice.iter.IterMut M31)
    (nextBack : core.slice.iter.IterMut M31 → Option M31 →
      core.slice.iter.IterMut M31)
    (nextRun : core.slice.iter.IteratorIterMut.next iter =
      .ok (some limb, nextIter, nextBack)) :
    ∃ limbResult,
      V7Tag73ChallengeQm31Generated.aspis_core.transcript.Transcript.challenge_qm31_loop0_loop0
          { start := 0#u32, «end» := 8#u32 }
          self block wordIndex limb = limbResult ∧
      V7Tag73ChallengeQm31Generated.aspis_core.transcript.Transcript.challenge_qm31_loop0.body
          iter back self block wordIndex =
        (do
          let (nextSelf, nextBlock, nextIndex, nextLimb, accepted) ← limbResult
          if accepted then
            ok (.cont
              (nextIter,
               fun im => back (nextBack im (some nextLimb)),
               nextSelf, nextBlock, nextIndex))
          else
            ok (.done
              (nextSelf, some (.Err ()),
               back (nextBack nextIter (some nextLimb))))) := by
  refine ⟨V7Tag73ChallengeQm31Generated.aspis_core.transcript.Transcript.challenge_qm31_loop0_loop0
      { start := 0#u32, «end» := 8#u32 }
      self block wordIndex limb, rfl, ?_⟩
  simp [V7Tag73ChallengeQm31Generated.aspis_core.transcript.Transcript.challenge_qm31_loop0.body,
    nextRun,
    V7Tag73ChallengeQm31Generated.aspis_core.transcript.CHALLENGE_RETRY_LIMIT]

/-- One active retry which stays in the current 32-byte block, reduced only
by explicit arithmetic, slice, copy, and increment equations. -/
theorem inner_body_active_in_block_exact
    (limb : M31) (iter nextIter : core.ops.range.Range Std.U32)
    (self : Transcript) (block : Array Std.U8 32#usize)
    (wordIndex nextIndex start finish : Std.Usize)
    (drawn : Std.U32) (bytes : Slice Std.U8)
    (four : Array Std.U8 4#usize)
    (notBoundary : wordIndex ≠ 8#usize)
    (nextRun : core.iter.range.IteratorRange.next core.iter.range.StepU32 iter =
      .ok (some drawn, nextIter))
    (mulRun : wordIndex * 4#usize = Aeneas.Std.Result.ok start)
    (addRun : start + 4#usize = Aeneas.Std.Result.ok finish)
    (sliceRun :
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) block
        { start := start, «end» := finish } = .ok bytes)
    (copyRun :
      core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8
        bytes = .ok (.Ok four))
    (incrementRun : wordIndex + 1#usize = Aeneas.Std.Result.ok nextIndex) :
    let word := core.num.U32.from_le_bytes four
    let masked := word &&& 2147483647#u32
    V7Tag73ChallengeQm31Generated.aspis_core.transcript.Transcript.challenge_qm31_loop0_loop0.body
        limb iter self block wordIndex =
      if masked != 2147483647#u32 then
        .ok (.done (self, block, nextIndex, masked, true))
      else
        .ok (.cont (nextIter, self, block, nextIndex)) := by
  dsimp only
  unfold
    V7Tag73ChallengeQm31Generated.aspis_core.transcript.Transcript.challenge_qm31_loop0_loop0.body
  rw [nextRun]
  simp only [bind_tc_ok]
  rw [if_neg notBoundary, mulRun]
  simp only [bind_tc_ok]
  rw [addRun]
  simp only [bind_tc_ok]
  rw [sliceRun]
  simp only [bind_tc_ok]
  rw [copyRun]
  simp [core.result.Result.unwrap, lift,
    V7Tag73ChallengeQm31Generated.aspis_core.field.P, incrementRun]

/-- At the exact block boundary the body performs one source squeeze, resets
the coordinate to zero, and then applies the same explicit word equations. -/
theorem inner_body_active_at_resqueeze_exact
    (limb : M31) (iter nextIter : core.ops.range.Range Std.U32)
    (self nextSelf : Transcript)
    (block nextBlock : Array Std.U8 32#usize)
    (nextIndex start finish : Std.Usize)
    (drawn : Std.U32) (bytes : Slice Std.U8)
    (four : Array Std.U8 4#usize)
    (nextRun : core.iter.range.IteratorRange.next core.iter.range.StepU32 iter =
      .ok (some drawn, nextIter))
    (squeezeRun :
      V7Tag73ChallengeQm31Generated.aspis_core.transcript.Transcript.squeeze_block
          self = .ok (nextBlock, nextSelf))
    (mulRun : (0#usize : Std.Usize) * 4#usize =
      Aeneas.Std.Result.ok start)
    (addRun : start + 4#usize = Aeneas.Std.Result.ok finish)
    (sliceRun :
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) nextBlock
        { start := start, «end» := finish } = .ok bytes)
    (copyRun :
      core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8
        bytes = .ok (.Ok four))
    (incrementRun : (0#usize : Std.Usize) + 1#usize =
      Aeneas.Std.Result.ok nextIndex) :
    let word := core.num.U32.from_le_bytes four
    let masked := word &&& 2147483647#u32
    V7Tag73ChallengeQm31Generated.aspis_core.transcript.Transcript.challenge_qm31_loop0_loop0.body
        limb iter self block 8#usize =
      if masked != 2147483647#u32 then
        .ok (.done (nextSelf, nextBlock, nextIndex, masked, true))
      else
        .ok (.cont (nextIter, nextSelf, nextBlock, nextIndex)) := by
  dsimp only
  unfold
    V7Tag73ChallengeQm31Generated.aspis_core.transcript.Transcript.challenge_qm31_loop0_loop0.body
  rw [nextRun]
  simp only [bind_tc_ok]
  simp only [if_true]
  rw [squeezeRun]
  simp only [bind_tc_ok]
  rw [mulRun]
  simp only [bind_tc_ok]
  rw [addRun]
  simp only [bind_tc_ok]
  rw [sliceRun]
  simp only [bind_tc_ok]
  rw [copyRun]
  simp [core.result.Result.unwrap, lift,
    V7Tag73ChallengeQm31Generated.aspis_core.field.P, incrementRun]

/-! The remaining source-loop certificates are below.  They expose each
branch rather than replacing the loop with a conclusion-shaped premise. -/

universe u v

/-- A finite certificate made only from equations for the actual generated
loop body.  It is useful for replaying a concrete accepted or exhausted retry
path without postulating a property of the loop as a whole. -/
inductive ExactLoopTrace {State : Type u} {Output : Type v}
    (body : State → Result (ControlFlow State Output)) :
    State → Output → Type (max u v)
  | done {state output}
      (equation : body state = .ok (.done output)) :
      ExactLoopTrace body state output
  | cont {state next output}
      (equation : body state = .ok (.cont next))
      (tail : ExactLoopTrace body next output) :
      ExactLoopTrace body state output

/-- Number of literal generated `cont` edges before the terminating body
equation in an exact retry trace. -/
def ExactLoopTrace.contCount
    {State : Type u} {Output : Type v}
    {body : State → Result (ControlFlow State Output)}
    {state : State} {output : Output} :
    ExactLoopTrace body state output → Nat
  | .done _ => 0
  | .cont _ tail => tail.contCount + 1

/-- A finite chain of concrete body equations determines the result of the
Aeneas partial fixpoint.  No termination or faithfulness premise is used. -/
theorem exactLoopTrace_runs
    {State : Type u} {Output : Type v}
    {body : State → Result (ControlFlow State Output)}
    {state : State} {output : Output}
    (trace : ExactLoopTrace body state output) :
    loop body state = .ok output := by
  induction trace with
  | done equation =>
      rw [loop.eq_def, equation]
  | cont equation tail inductionHypothesis =>
      rw [loop.eq_def, equation]
      exact inductionHypothesis

/-- Specialization of `exactLoopTrace_runs` to the deployed one-limb retry
loop.  Every premise inside `trace` is an equation for the transparent
generated body at one exact range/block/word-index state. -/
theorem inner_loop_runs_from_exact_trace
    (limb : M31)
    (iter : core.ops.range.Range Std.U32)
    (self : Transcript) (block : Array Std.U8 32#usize)
    (wordIndex : Std.Usize)
    (nextSelf : Transcript) (nextBlock : Array Std.U8 32#usize)
    (nextIndex : Std.Usize) (nextLimb : M31) (accepted : Bool)
    (trace : ExactLoopTrace
      (fun state : core.ops.range.Range Std.U32 × Transcript ×
          Array Std.U8 32#usize × Std.Usize =>
        V7Tag73ChallengeQm31Generated.aspis_core.transcript.Transcript.challenge_qm31_loop0_loop0.body
          limb state.1 state.2.1 state.2.2.1 state.2.2.2)
      (iter, self, block, wordIndex)
      (nextSelf, nextBlock, nextIndex, nextLimb, accepted)) :
    V7Tag73ChallengeQm31Generated.aspis_core.transcript.Transcript.challenge_qm31_loop0_loop0
        iter self block wordIndex limb =
      .ok (nextSelf, nextBlock, nextIndex, nextLimb, accepted) := by
  unfold
    V7Tag73ChallengeQm31Generated.aspis_core.transcript.Transcript.challenge_qm31_loop0_loop0
  exact exactLoopTrace_runs trace

theorem inner_body_range_exhausted
    (limb : M31) (iter : core.ops.range.Range Std.U32)
    (self : Transcript) (block : Array Std.U8 32#usize)
    (wordIndex : Std.Usize)
    (nextIter : core.ops.range.Range Std.U32)
    (nextRun : core.iter.range.IteratorRange.next core.iter.range.StepU32 iter =
      .ok (none, nextIter)) :
    V7Tag73ChallengeQm31Generated.aspis_core.transcript.Transcript.challenge_qm31_loop0_loop0.body
        limb iter self block wordIndex =
      .ok (.done (self, block, wordIndex, limb, false)) := by
  simp [V7Tag73ChallengeQm31Generated.aspis_core.transcript.Transcript.challenge_qm31_loop0_loop0.body,
    nextRun]

theorem outer_body_iterator_exhausted
    (iter : core.slice.iter.IterMut M31)
    (back : core.slice.iter.IterMut M31 → core.slice.iter.IterMut M31)
    (self : Transcript) (block : Array Std.U8 32#usize)
    (wordIndex : Std.Usize)
    (nextIter : core.slice.iter.IterMut M31)
    (nextBack : core.slice.iter.IterMut M31 → Option M31 →
      core.slice.iter.IterMut M31)
    (nextRun : core.slice.iter.IteratorIterMut.next iter =
      .ok (none, nextIter, nextBack)) :
    V7Tag73ChallengeQm31Generated.aspis_core.transcript.Transcript.challenge_qm31_loop0.body
        iter back self block wordIndex =
      .ok (.done (self, none, back (nextBack nextIter none))) := by
  simp [V7Tag73ChallengeQm31Generated.aspis_core.transcript.Transcript.challenge_qm31_loop0.body,
    nextRun]

theorem outer_body_accepts_and_continues
    (iter : core.slice.iter.IterMut M31)
    (back : core.slice.iter.IterMut M31 → core.slice.iter.IterMut M31)
    (self nextSelf : Transcript)
    (block nextBlock : Array Std.U8 32#usize)
    (wordIndex nextWordIndex : Std.Usize)
    (limb nextLimb : M31)
    (nextIter : core.slice.iter.IterMut M31)
    (nextBack : core.slice.iter.IterMut M31 → Option M31 →
      core.slice.iter.IterMut M31)
    (nextRun : core.slice.iter.IteratorIterMut.next iter =
      .ok (some limb, nextIter, nextBack))
    (limbRun :
      V7Tag73ChallengeQm31Generated.aspis_core.transcript.Transcript.challenge_qm31_loop0_loop0
          { start := 0#u32,
            «end» := V7Tag73ChallengeQm31Generated.aspis_core.transcript.CHALLENGE_RETRY_LIMIT }
          self block wordIndex limb =
        .ok (nextSelf, nextBlock, nextWordIndex, nextLimb, true)) :
    V7Tag73ChallengeQm31Generated.aspis_core.transcript.Transcript.challenge_qm31_loop0.body
        iter back self block wordIndex =
      .ok (.cont
        (nextIter,
         fun im => back (nextBack im (some nextLimb)),
         nextSelf, nextBlock, nextWordIndex)) := by
  simp [V7Tag73ChallengeQm31Generated.aspis_core.transcript.Transcript.challenge_qm31_loop0.body,
    nextRun, limbRun]

theorem outer_body_exhaustion_returns_immediately
    (iter : core.slice.iter.IterMut M31)
    (back : core.slice.iter.IterMut M31 → core.slice.iter.IterMut M31)
    (self nextSelf : Transcript)
    (block nextBlock : Array Std.U8 32#usize)
    (wordIndex nextWordIndex : Std.Usize)
    (limb nextLimb : M31)
    (nextIter : core.slice.iter.IterMut M31)
    (nextBack : core.slice.iter.IterMut M31 → Option M31 →
      core.slice.iter.IterMut M31)
    (nextRun : core.slice.iter.IteratorIterMut.next iter =
      .ok (some limb, nextIter, nextBack))
    (limbRun :
      V7Tag73ChallengeQm31Generated.aspis_core.transcript.Transcript.challenge_qm31_loop0_loop0
          { start := 0#u32,
            «end» := V7Tag73ChallengeQm31Generated.aspis_core.transcript.CHALLENGE_RETRY_LIMIT }
          self block wordIndex limb =
        .ok (nextSelf, nextBlock, nextWordIndex, nextLimb, false)) :
    V7Tag73ChallengeQm31Generated.aspis_core.transcript.Transcript.challenge_qm31_loop0.body
        iter back self block wordIndex =
      .ok (.done
        (nextSelf, some (.Err ()),
         back (nextBack nextIter (some nextLimb)))) := by
  simp [V7Tag73ChallengeQm31Generated.aspis_core.transcript.Transcript.challenge_qm31_loop0.body,
    nextRun, limbRun]

/-- The pure four-limb decoder proves the fixed upper bound inherited by the
source loop: four independent eight-attempt limbs use at most 32 words, hence
at most four 32-byte blocks. -/
theorem exact_four_limb_word_and_block_cap
    (words : List Nat)
    (decoded : AspisK1.V7Tag73SamplerDecoder.FourLimbDecode)
    (run : AspisK1.V7Tag73SamplerDecoder.decodeLimbs 4 words = some decoded) :
    decoded.limbs.length = 4 ∧
      4 ≤ decoded.wordsUsed ∧
      decoded.wordsUsed ≤ 32 ∧
      AspisK1.V7Tag73SamplerDecoder.blocksNeededForWords decoded.wordsUsed ≤ 4 ∧
      ∀ limb ∈ decoded.limbs,
        limb < AspisK1.V7Tag73SamplerDecoder.m31Prime := by
  obtain ⟨length, lower, upper, canonical⟩ :=
    AspisK1.V7Tag73SamplerDecoderExact.decodeFourLimbs_word_cap
      words decoded run
  refine ⟨length, lower, upper, ?_, canonical⟩
  unfold AspisK1.V7Tag73SamplerDecoder.blocksNeededForWords
  omega

#print axioms squeeze_block_run_is_exact
#print axioms generated_candidate_eq_decoder_mask
#print axioms generated_rejects_exactly_noncanonical
#print axioms challenge_qm31_eq_sourceSamplerRun
#print axioms outer_body_uses_exact_eight_attempt_range
#print axioms inner_body_active_in_block_exact
#print axioms inner_body_active_at_resqueeze_exact
#print axioms exactLoopTrace_runs
#print axioms inner_loop_runs_from_exact_trace
#print axioms inner_body_range_exhausted
#print axioms outer_body_accepts_and_continues
#print axioms outer_body_exhaustion_returns_immediately
#print axioms exact_four_limb_word_and_block_cap

end V7Tag73ChallengeQm31SourceCertificate
