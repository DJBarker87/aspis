import V5TranscriptPrimitivesGenerated.Funs
import AspisFormal.V5TranscriptConnection

namespace V5TranscriptPrimitivesProof

open Aeneas Aeneas.Std Result
open AspisFormal.V5ExactRuntimeWireRepair
open AspisV5TranscriptConnection

open V5TranscriptPrimitivesGenerated

abbrev Transcript :=
  V5TranscriptPrimitivesGenerated.aspis_core.transcript.Transcript

def toByte (value : Std.U8) :
    AspisFormal.V5ExactRuntimeWireRepair.Byte :=
  ⟨value.val, Std.U8.lt_succ_max value⟩

def sliceBytes (value : Slice Std.U8) :
    List AspisFormal.V5ExactRuntimeWireRepair.Byte :=
  value.val.map toByte

def arrayBytes {n : Std.Usize} (value : Array Std.U8 n) :
    List AspisFormal.V5ExactRuntimeWireRepair.Byte :=
  value.val.map toByte

def arrayDigest (value : Array Std.U8 32#usize) : Digest32 :=
  fun index =>
    toByte (value.val[index.val]'(by
      have hindex := index.isLt
      simpa [value.property] using hindex))

theorem bytes_arrayDigest (value : Array Std.U8 32#usize) :
    bytes (arrayDigest value) = arrayBytes value := by
  simpa [bytes, arrayDigest, arrayBytes, value.property] using
    (List.ofFn_getElem_eq_map (l := value.val) toByte)

def hashVector (value : Slice (Slice Std.U8)) : HashVector :=
  value.val.map sliceBytes

def absorbInput (self : Transcript) (label : Std.U8)
    (data : Slice Std.U8) : Slice (Slice Std.U8) :=
  Array.to_slice
    (Array.make 3#usize
      [Array.to_slice self.state,
       Array.to_slice (Array.make 2#usize [0#u8, label]),
       data])

def squeezeOutputInput (self : Transcript) : Slice (Slice Std.U8) :=
  Array.to_slice
    (Array.make 2#usize
      [Array.to_slice self.state,
       Array.to_slice (Array.make 1#usize [1#u8])])

def squeezeAdvanceInput (self : Transcript) : Slice (Slice Std.U8) :=
  Array.to_slice
    (Array.make 2#usize
      [Array.to_slice self.state,
       Array.to_slice (Array.make 1#usize [2#u8])])

def grindingInput (self : Transcript) (nonce : Std.U64) :
    Result (Slice (Slice Std.U8)) := do
  let nonceBytes ← lift (core.num.U64.to_le_bytes nonce)
  ok <| Array.to_slice
    (Array.make 3#usize
      [Array.to_slice self.state,
       Array.to_slice (Array.make 1#usize [3#u8]),
       Array.to_slice nonceBytes])

theorem absorb_input_has_exact_slice_boundaries
    (self : Transcript) (label : Std.U8) (data : Slice Std.U8) :
    hashVector (absorbInput self label data) =
      [arrayBytes self.state, [0, toByte label], sliceBytes data] := by
  simp [hashVector, absorbInput, arrayBytes, sliceBytes, toByte,
    Array.to_slice, Array.make]

theorem squeeze_inputs_have_exact_slice_boundaries (self : Transcript) :
    hashVector (squeezeOutputInput self) = [arrayBytes self.state, [1]] ∧
    hashVector (squeezeAdvanceInput self) = [arrayBytes self.state, [2]] := by
  simp [hashVector, squeezeOutputInput, squeezeAdvanceInput, arrayBytes,
    sliceBytes, toByte, Array.to_slice, Array.make]

theorem absorb_input_is_maintained_hash_vector
    (self : Transcript) (label : Std.U8) (data : Slice Std.U8) :
    hashVector (absorbInput self label data) =
      absorbHashVector (arrayDigest self.state) (toByte label)
        (sliceBytes data) := by
  rw [absorb_input_has_exact_slice_boundaries, absorbHashVector,
    bytes_arrayDigest]

theorem squeeze_inputs_are_maintained_hash_vectors (self : Transcript) :
    hashVector (squeezeOutputInput self) =
        squeezeOutputHashVector (arrayDigest self.state) ∧
    hashVector (squeezeAdvanceInput self) =
        squeezeAdvanceHashVector (arrayDigest self.state) := by
  rw [(squeeze_inputs_have_exact_slice_boundaries self).1,
    (squeeze_inputs_have_exact_slice_boundaries self).2,
    squeezeOutputHashVector, squeezeAdvanceHashVector,
    bytes_arrayDigest]
  constructor <;> rfl

theorem absorb_run_is_exact
    (self : Transcript) (label : Std.U8) (data : Slice Std.U8) :
    V5TranscriptPrimitivesGenerated.aspis_core.transcript.Transcript.absorb
        self label data =
      .ok { self with state := self.hash (absorbInput self label data) } := by
  simp [V5TranscriptPrimitivesGenerated.aspis_core.transcript.Transcript.absorb,
    absorbInput, lift,
    Array.to_slice, Array.make,
    V5TranscriptPrimitivesGenerated.aspis_core.transcript.DOM_ABSORB]

theorem squeeze_block_run_is_exact (self : Transcript) :
    V5TranscriptPrimitivesGenerated.aspis_core.transcript.Transcript.squeeze_block
        self =
      .ok
        (self.hash (squeezeOutputInput self),
         { self with state := self.hash (squeezeAdvanceInput self) }) := by
  simp [V5TranscriptPrimitivesGenerated.aspis_core.transcript.Transcript.squeeze_block,
    squeezeOutputInput, squeezeAdvanceInput, lift, Array.to_slice, Array.make,
    V5TranscriptPrimitivesGenerated.aspis_core.transcript.DOM_SQUEEZE,
    V5TranscriptPrimitivesGenerated.aspis_core.transcript.DOM_ADVANCE]

theorem grinding_run_uses_exact_hash_input
    (self : Transcript) (nonce : Std.U64) (bits : Std.U8)
    (input : Slice (Slice Std.U8))
    (hinput : grindingInput self nonce = .ok input) :
    V5TranscriptPrimitivesGenerated.aspis_core.transcript.Transcript.grinding_ok
        self nonce bits =
      V5TranscriptPrimitivesGenerated.aspis_core.transcript.digest_has_leading_zero_bits
        (self.hash input) bits := by
  simp [grindingInput,
    V5TranscriptPrimitivesGenerated.aspis_core.transcript.Transcript.grinding_ok,
    lift, Array.to_slice, Array.make,
    V5TranscriptPrimitivesGenerated.aspis_core.transcript.DOM_GRIND] at hinput ⊢
  cases hinput
  rfl

theorem generated_wrapper_calls_are_exact
    (self : Transcript) (label : Std.U8) (data : Slice Std.U8)
    (count : Std.Usize) (bound : Std.U32) (maxDraws : Std.Usize)
    (nonce : Std.U64) (bits : Std.U8) :
    V5TranscriptPrimitivesGenerated.extract_absorb self label data =
        V5TranscriptPrimitivesGenerated.aspis_core.transcript.Transcript.absorb
          self label data ∧
    V5TranscriptPrimitivesGenerated.extract_squeeze_block self =
        V5TranscriptPrimitivesGenerated.aspis_core.transcript.Transcript.squeeze_block
          self ∧
    V5TranscriptPrimitivesGenerated.extract_queries_without_replacement
        self count bound maxDraws =
      V5TranscriptPrimitivesGenerated.aspis_core.transcript.Transcript.challenge_queries_without_replacement
        self count bound maxDraws ∧
    V5TranscriptPrimitivesGenerated.extract_grinding_ok self nonce bits =
        V5TranscriptPrimitivesGenerated.aspis_core.transcript.Transcript.grinding_ok
          self nonce bits := by
  exact ⟨rfl, rfl, rfl, rfl⟩

#print axioms absorb_input_is_maintained_hash_vector
#print axioms squeeze_inputs_are_maintained_hash_vectors
#print axioms absorb_run_is_exact
#print axioms squeeze_block_run_is_exact
#print axioms grinding_run_uses_exact_hash_input
#print axioms generated_wrapper_calls_are_exact

end V5TranscriptPrimitivesProof
