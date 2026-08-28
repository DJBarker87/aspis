import V7FirstCompactSamplerNativeBlockBridge

open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace V7FirstCompactSqueezeSourceBridge

open V7FirstCompactSource
open V7FirstCompactSamplerNativeBlockBridge
open AspisK1.V7Tag73TranscriptSchedule

abbrev Transcript := transcript.Transcript

def taggedBytes (self : Transcript) (domain : Std.U8) :
    Array Std.U8 33#usize :=
  ⟨self.state.val ++ [domain], by simp [self.state.property]⟩

def taggedHashInput (self : Transcript) (domain : Std.U8) :
    Slice (Slice Std.U8) :=
  ⟨[⟨(taggedBytes self domain).val, by scalar_tac⟩], by scalar_tac⟩

def exactSqueezeRun (self : Transcript) :
    Result (SourceSqueezeBlock × Transcript) := do
  let out ← self.hash (taggedHashInput self 1#u8)
  let nextState ← self.hash (taggedHashInput self 2#u8)
  ok (out, { self with state := nextState })

/-- The literal current-source squeeze hashes exactly `state || 1` for its
output and `state || 2` for its successor transcript. -/
theorem source_squeeze_block_run_is_exact (self : Transcript) :
    transcript.Transcript.squeeze_block self = exactSqueezeRun self := by
  have stateLength : self.state.val.length = 32 := by
    simpa using self.state.property
  have takeState : List.take 32 self.state.val = self.state.val := by
    apply List.take_of_length_le
    omega
  simp [transcript.Transcript.squeeze_block, exactSqueezeRun,
    taggedHashInput, taggedBytes, lift,
    core.array.Array.index_mut,
    core.ops.index.IndexMutSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    core.slice.Slice.copy_from_slice, Array.repeat, Array.update,
    Array.to_slice, Array.make, List.setSlice!, Slice.len, stateLength,
    takeState, transcript.DOM_SQUEEZE, transcript.DOM_ADVANCE]

def HashCallbackAlwaysSucceeds
    (hash : Slice (Slice Std.U8) → Result SourceSqueezeBlock) : Prop :=
  ∀ input, ∃ output, hash input = .ok output

/-- Exact mathematical bytes passed to the installed production hash
callback: concatenate the supplied slices in source order. -/
def nativeHashInputBytes (inputs : Slice (Slice Std.U8)) : ByteString :=
  (inputs.val.flatMap fun input => input.val).map
    (fun byte => UInt8.ofNat byte.val)

theorem bytes_native_source_digest (block : NativeQueryBlock) :
    bytes (nativeSourceDigest block) =
      block.val.map (fun byte => UInt8.ofNat byte.val) := by
  unfold bytes nativeSourceDigest
  simpa using List.ofFn_getElem_eq_map block.val
    (fun byte => UInt8.ofNat byte.val)

theorem native_hash_input_bytes_tagged
    (self : Transcript) (domain : Std.U8) :
    nativeHashInputBytes (taggedHashInput self domain) =
      bytes (nativeSourceDigest (sourceSqueezeBytes self.state)) ++
        [UInt8.ofNat domain.val] := by
  rw [bytes_native_source_digest]
  simp [nativeHashInputBytes, taggedHashInput, taggedBytes,
    sourceSqueezeBytes]

/-- The permitted SHA-256 source boundary.  It includes totality and states
that the successful callback output is SHA-256 of the exact concatenated
source slices; no generic fallibility premise survives above this interface. -/
def HashCallbackReturnsSha256
    (sha256 : ByteString → Digest256)
    (hash : Slice (Slice Std.U8) → Result SourceSqueezeBlock) : Prop :=
  ∀ input, ∃ output,
    hash input = .ok output ∧
    nativeSourceDigest (sourceSqueezeBytes output) =
      sha256 (nativeHashInputBytes input)

theorem hash_callback_sha256_implies_total
    (sha256 : ByteString → Digest256)
    (hash : Slice (Slice Std.U8) → Result SourceSqueezeBlock)
    (semantics : HashCallbackReturnsSha256 sha256 hash) :
    HashCallbackAlwaysSucceeds hash := by
  intro input
  obtain ⟨output, run, _⟩ := semantics input
  exact ⟨output, run⟩

/-- Totality of the one production hash callback is sufficient for every
squeeze reachable from a transcript carrying that callback. -/
theorem hash_callback_total_implies_squeeze_success
    (self : Transcript) (total : HashCallbackAlwaysSucceeds self.hash) :
    ∃ block next,
      transcript.Transcript.squeeze_block self = .ok (block, next) := by
  obtain ⟨out, outputRun⟩ := total (taggedHashInput self 1#u8)
  obtain ⟨nextState, advanceRun⟩ := total (taggedHashInput self 2#u8)
  refine ⟨out, { self with state := nextState }, ?_⟩
  rw [source_squeeze_block_run_is_exact]
  simp [exactSqueezeRun, outputRun, advanceRun]

/-- A successful translated squeeze exposes its two literal callback runs.
This is path-specific and introduces no callback totality assumption. -/
theorem successful_squeeze_exposes_hash_runs
    (self next : Transcript) (block : SourceSqueezeBlock)
    (run : transcript.Transcript.squeeze_block self = .ok (block, next)) :
    self.hash (taggedHashInput self 1#u8) = .ok block ∧
      self.hash (taggedHashInput self 2#u8) = .ok next.state := by
  rw [source_squeeze_block_run_is_exact] at run
  unfold exactSqueezeRun at run
  generalize outputRun : self.hash (taggedHashInput self 1#u8) = outputResult
    at run
  cases outputResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
  | div => simp [Bind.bind, Aeneas.Std.bind] at run
  | ok output =>
      simp only [bind_tc_ok] at run
      generalize advanceRun : self.hash (taggedHashInput self 2#u8) =
        advanceResult at run
      cases advanceResult with
      | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
      | div => simp [Bind.bind, Aeneas.Std.bind] at run
      | ok nextState =>
          simp only [bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at run
          rcases run with ⟨blockExact, nextExact⟩
          subst block
          subst next
          exact ⟨rfl, rfl⟩

/-- Successful source squeezing never changes the installed hash callback. -/
theorem successful_squeeze_preserves_hash
    (self next : Transcript) (block : SourceSqueezeBlock)
    (run : transcript.Transcript.squeeze_block self = .ok (block, next)) :
    next.hash = self.hash := by
  rw [source_squeeze_block_run_is_exact] at run
  unfold exactSqueezeRun at run
  generalize outputRun : self.hash (taggedHashInput self 1#u8) = outputResult
    at run
  cases outputResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
  | div => simp [Bind.bind, Aeneas.Std.bind] at run
  | ok out =>
      simp only [bind_tc_ok] at run
      generalize advanceRun : self.hash (taggedHashInput self 2#u8) =
        advanceResult at run
      cases advanceResult with
      | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
      | div => simp [Bind.bind, Aeneas.Std.bind] at run
      | ok nextState =>
          simp only [bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at run
          rcases run with ⟨_, nextExact⟩
          subst next
          rfl

#print axioms source_squeeze_block_run_is_exact
#print axioms native_hash_input_bytes_tagged
#print axioms hash_callback_sha256_implies_total
#print axioms hash_callback_total_implies_squeeze_success
#print axioms successful_squeeze_exposes_hash_runs
#print axioms successful_squeeze_preserves_hash

end V7FirstCompactSqueezeSourceBridge
