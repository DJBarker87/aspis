import AuthorizationReceiptRequestDigestDispatchBase

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisPool.AuthorizationReceiptRequestDigestSourceBridge

open AspisPool.AuthorizationReceiptAccountWireV1
open AuthorizationReceiptRequestDigestGenerated

abbrev GeneratedRequest :=
  pool_v1.verifier_dispatch.VerifierDispatchRequestV1

def requestOfGenerated (request : GeneratedRequest) : WireRequest where
  binding := bindingOfGenerated request.binding
  statementPayload := bytesOfGeneratedSlice request.statement_payload

def statementPayloadDigestDomain : ByteString :=
  [97, 115, 112, 105, 115, 47, 112, 111, 111, 108, 45, 118, 49, 47,
    112, 114, 111, 102, 105, 108, 101, 45, 115, 116, 97, 116, 101, 109,
    101, 110, 116, 45, 112, 97, 121, 108, 111, 97, 100, 45, 100, 105,
    103, 101, 115, 116, 47, 118, 49]

def wireStatementPayloadDigestPreimage (request : WireRequest) : ByteString :=
  statementPayloadDigestDomain ++
    [statementDigestVersion, statementVersion] ++
    bytes32List request.binding.profileBinding ++
    bytes32List request.binding.releaseBinding ++
    u32LE request.statementPayload.length ++ request.statementPayload

def statementPayloadDigestGeneratedInputs
    (statementVersionValue : Std.U8)
    (profileBinding releaseBinding : Array Std.U8 32#usize)
    (statementPayload : Slice Std.U8) : Slice (Slice Std.U8) :=
  Array.to_slice (Array.make 7#usize [
    pool_v1.verifier_dispatch.POOL_V1_VERIFIER_STATEMENT_PAYLOAD_DIGEST_DOMAIN,
    Array.to_slice (Array.make 1#usize [
      pool_v1.verifier_dispatch.POOL_V1_VERIFIER_STATEMENT_DIGEST_VERSION
    ] (by simp)),
    Array.to_slice (Array.make 1#usize [statementVersionValue] (by simp)),
    Array.to_slice profileBinding,
    Array.to_slice releaseBinding,
    Array.to_slice (core.num.U32.to_le_bytes
      (UScalar.cast .U32 (Slice.len statementPayload))),
    statementPayload
  ] (by simp))

theorem statement_payload_digest_domain_generated_exact :
    bytesOfGeneratedSlice
        pool_v1.verifier_dispatch.POOL_V1_VERIFIER_STATEMENT_PAYLOAD_DIGEST_DOMAIN =
      statementPayloadDigestDomain := by
  simp [bytesOfGeneratedSlice,
    pool_v1.verifier_dispatch.POOL_V1_VERIFIER_STATEMENT_PAYLOAD_DIGEST_DOMAIN,
    statementPayloadDigestDomain, byteOfGenerated, Array.to_slice, Array.make]

theorem statement_payload_digest_preimage_source_exact
    (request : GeneratedRequest)
    (hstatement : request.binding.statement_version = 1#u8)
    (hlength : request.statement_payload.val.length ≤ 640) :
    generatedShaPreimage
        (statementPayloadDigestGeneratedInputs
          request.binding.statement_version request.binding.profile_binding
          request.binding.release_binding request.statement_payload) =
      wireStatementPayloadDigestPreimage (requestOfGenerated request) := by
  have hcastBound :
      (Slice.len request.statement_payload).val <
        2 ^ UScalarTy.U32.numBits := by
    simp [Slice.len, Slice.length]
    omega
  have hcast :
      (UScalar.cast .U32 (Slice.len request.statement_payload)).val =
        request.statement_payload.val.length := by
    simpa [Slice.len, Slice.length] using
      (UScalar.cast_val_mod_pow_of_inBounds_eq .U32
        (Slice.len request.statement_payload) hcastBound)
  have hlengthBytes :
      bytesOfGenerated (core.num.U32.to_le_bytes
        (UScalar.cast .U32 (Slice.len request.statement_payload))) =
        u32LE request.statement_payload.val.length := by
    rw [← u32LE_generated, hcast]
  calc
    generatedShaPreimage
        (statementPayloadDigestGeneratedInputs
          request.binding.statement_version request.binding.profile_binding
          request.binding.release_binding request.statement_payload) =
      bytesOfGeneratedSlice
          pool_v1.verifier_dispatch.POOL_V1_VERIFIER_STATEMENT_PAYLOAD_DIGEST_DOMAIN ++
        [byteOfGenerated
          pool_v1.verifier_dispatch.POOL_V1_VERIFIER_STATEMENT_DIGEST_VERSION] ++
        [byteOfGenerated request.binding.statement_version] ++
        bytesOfGenerated request.binding.profile_binding ++
        bytesOfGenerated request.binding.release_binding ++
        bytesOfGenerated (core.num.U32.to_le_bytes
          (UScalar.cast .U32 (Slice.len request.statement_payload))) ++
        bytesOfGeneratedSlice request.statement_payload := by
      simp [generatedShaPreimage, statementPayloadDigestGeneratedInputs,
        bytesOfGeneratedSlice, bytesOfGenerated, Array.to_slice, Array.make,
        List.append_assoc]
    _ = wireStatementPayloadDigestPreimage (requestOfGenerated request) := by
      rw [statement_payload_digest_domain_generated_exact, hlengthBytes]
      simp [wireStatementPayloadDigestPreimage, requestOfGenerated,
        bindingOfGenerated, bytesOfGeneratedSlice,
        bytes32List_bytes32OfGenerated,
        pool_v1.verifier_dispatch.POOL_V1_VERIFIER_STATEMENT_DIGEST_VERSION,
        statementDigestVersion, statementVersion, hstatement,
        byteOfGenerated, List.append_assoc]

def requestHeaderArray : Array Std.U8 384#usize :=
  Array.make 384#usize
    ([65#u8, 83#u8, 86#u8, 81#u8] ++ List.replicate 4 0#u8 ++
      (core.num.U32.to_le_bytes 1#u32).val ++ List.replicate 372 0#u8)
    (by simp [core.num.U32.to_le_bytes])

def requestScalarPrefix (binding : GeneratedBinding) : List Std.U8 :=
  [65#u8, 83#u8, 86#u8, 81#u8, 1#u8, binding.statement_version,
    generatedTransitionByte binding.transition_kind, 1#u8] ++
  (core.num.U32.to_le_bytes 1#u32).val ++
  [1#u8, 0#u8, 0#u8, 0#u8]

def requestGeneratedBytes (binding : GeneratedBinding) : List Std.U8 :=
  [65#u8, 83#u8, 86#u8, 81#u8,
    1#u8, binding.statement_version,
    generatedTransitionByte binding.transition_kind, 1#u8] ++
  (core.num.U32.to_le_bytes 1#u32).val ++
  [1#u8, 0#u8, 0#u8, 0#u8] ++
  binding.verifier_program.val ++ binding.profile_binding.val ++
  binding.release_binding.val ++ binding.pool.val ++
  binding.deployment_domain.val ++
  (core.num.U64.to_le_bytes binding.anchor_sequence).val ++
  (encodedDigestArray binding.anchor_root).val ++
  (encodedDigestArray binding.nullifier).val ++
  binding.statement_digest.val ++ binding.envelope_digest.val ++
  binding.proof_account.val ++ binding.proof_body_digest.val ++
  (core.num.U32.to_le_bytes binding.proof_body_length).val ++
  (core.num.U32.to_le_bytes binding.statement_payload_length).val

def requestGeneratedArray (binding : GeneratedBinding) :
    Array Std.U8 384#usize :=
  ⟨requestGeneratedBytes binding, by
    simp [requestGeneratedBytes, binding.verifier_program.property,
      binding.profile_binding.property, binding.release_binding.property,
      binding.pool.property, binding.deployment_domain.property,
      binding.statement_digest.property, binding.envelope_digest.property,
      binding.proof_account.property, binding.proof_body_digest.property,
      (encodedDigestArray binding.anchor_root).property,
      (encodedDigestArray binding.nullifier).property,
      core.num.U32.to_le_bytes, core.num.U64.to_le_bytes]⟩

theorem request_header_scalar_prefix (binding : GeneratedBinding) :
    (((((requestHeaderArray.val.set 4 1#u8).set 5 binding.statement_version).set 6
      (generatedTransitionByte binding.transition_kind)).set 7 1#u8).set 12 1#u8) =
      requestScalarPrefix binding ++ List.replicate 368 0#u8 := by
  simp [requestHeaderArray, requestScalarPrefix, Array.make,
    core.num.U32.to_le_bytes]

theorem request_binding_result_bytes_as_writeSlices
    (binding : GeneratedBinding)
    (anchorBytes nullifierBytes : Array Std.U8 32#usize) :
    bindingResultBytes requestHeaderArray binding anchorBytes nullifierBytes =
      writeSlices
        (requestScalarPrefix binding ++ List.replicate 368 0#u8)
        (requestScalarPrefix binding).length
        (dispatchChunks binding anchorBytes nullifierBytes) := by
  simp only [bindingResultBytes]
  rw [request_header_scalar_prefix]
  simp [writeSlices, dispatchChunks, requestScalarPrefix,
    binding.verifier_program.property, binding.profile_binding.property,
    binding.release_binding.property, binding.pool.property,
    binding.deployment_domain.property, binding.statement_digest.property,
    binding.envelope_digest.property, binding.proof_account.property,
    binding.proof_body_digest.property, anchorBytes.property,
    nullifierBytes.property, core.num.U32.to_le_bytes,
    core.num.U64.to_le_bytes]

theorem bindingResultArray_request_header_exact
    (binding : GeneratedBinding)
    (anchorBytes nullifierBytes : Array Std.U8 32#usize)
    (hanchor : atomic_statement.encode_digest_canonical binding.anchor_root =
      .ok anchorBytes)
    (hnullifier : atomic_statement.encode_digest_canonical binding.nullifier =
      .ok nullifierBytes) :
    bindingResultArray requestHeaderArray binding anchorBytes nullifierBytes =
      requestGeneratedArray binding := by
  apply Subtype.ext
  simp only [bindingResultArray]
  rw [request_binding_result_bytes_as_writeSlices]
  rw [writeSlices_append_replicate]
  · rw [dispatchChunks_length]
    simp [requestGeneratedArray, requestGeneratedBytes, requestScalarPrefix,
      dispatchChunks, encodedDigestArray, hanchor, hnullifier,
      List.flatten, List.append_assoc]
  · simp

theorem encode_binding_fields_request_success_exact
    (binding : GeneratedBinding) (output : Array Std.U8 384#usize)
    (hrun :
      pool_v1.verifier_dispatch.encode_binding_fields requestHeaderArray binding =
        .ok output) :
    output = requestGeneratedArray binding := by
  obtain ⟨anchorBytes, hanchor⟩ :=
    encode_digest_canonical_total binding.anchor_root
  obtain ⟨nullifierBytes, hnullifier⟩ :=
    encode_digest_canonical_total binding.nullifier
  have hrunGeneric := encode_binding_fields_run_generic
    requestHeaderArray binding anchorBytes nullifierBytes hanchor hnullifier
  have harrayExact := bindingResultArray_request_header_exact binding anchorBytes
    nullifierBytes hanchor hnullifier
  exact Result.ok.inj (hrun.symm.trans (hrunGeneric.trans
    (congrArg Result.ok harrayExact)))

theorem request_header_generated_bind {T : Type}
    (next : Array Std.U8 384#usize → Result T) :
    (do
      let x ←
        core.array.Array.index_mut (core.ops.index.IndexMutSlice
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8))
          (Array.repeat 384#usize 0#u8) { «end» := 4#usize }
      let magic ← lift (Array.to_slice
        pool_v1.verifier_dispatch.POOL_V1_VERIFIER_DISPATCH_REQUEST_MAGIC)
      let slice ← core.slice.Slice.copy_from_slice core.marker.CopyU8 x.1 magic
      let x1 ←
        core.array.Array.index_mut (core.ops.index.IndexMutSlice
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) (x.2 slice)
          { start := 8#usize, «end» := 12#usize }
      let code ← lift (core.num.U32.to_le_bytes
        pool_v1.verifier_dispatch.POOL_V1_VERIFIER_DISPATCH_VERIFY_CODE)
      let code ← lift (Array.to_slice code)
      let slice ← core.slice.Slice.copy_from_slice core.marker.CopyU8 x1.1 code
      next (x1.2 slice)) = next requestHeaderArray := by
  simp [pool_v1.verifier_dispatch.POOL_V1_VERIFIER_DISPATCH_REQUEST_MAGIC,
    pool_v1.verifier_dispatch.POOL_V1_VERIFIER_DISPATCH_VERIFY_CODE,
    Std.lift, core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
    core.slice.Slice.copy_from_slice, Array.to_slice, Array.from_slice,
    Array.repeat, Array.make, List.setSlice!, Slice.len,
    requestHeaderArray, core.num.U32.to_le_bytes]
  simp_lists

theorem request_header_fields_bind (binding : GeneratedBinding) :
    (do
      let x ←
        core.array.Array.index_mut (core.ops.index.IndexMutSlice
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8))
          (Array.repeat 384#usize 0#u8) { «end» := 4#usize }
      let magic ← lift (Array.to_slice
        pool_v1.verifier_dispatch.POOL_V1_VERIFIER_DISPATCH_REQUEST_MAGIC)
      let slice ← core.slice.Slice.copy_from_slice core.marker.CopyU8 x.1 magic
      let x1 ←
        core.array.Array.index_mut (core.ops.index.IndexMutSlice
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) (x.2 slice)
          { start := 8#usize, «end» := 12#usize }
      let code ← lift (core.num.U32.to_le_bytes
        pool_v1.verifier_dispatch.POOL_V1_VERIFIER_DISPATCH_VERIFY_CODE)
      let code ← lift (Array.to_slice code)
      let slice ← core.slice.Slice.copy_from_slice core.marker.CopyU8 x1.1 code
      let fields ←
        pool_v1.verifier_dispatch.encode_binding_fields (x1.2 slice) binding
      ok fields) =
    (do
      let fields ← pool_v1.verifier_dispatch.encode_binding_fields
        requestHeaderArray binding
      ok fields : Result (Array Std.U8 384#usize)) := by
  exact request_header_generated_bind
    (next := fun header => do
      let fields ← pool_v1.verifier_dispatch.encode_binding_fields header binding
      ok fields)

end AspisPool.AuthorizationReceiptRequestDigestSourceBridge
