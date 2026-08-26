import AuthorizationReceiptRequestDigestRequestPrefix

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisPool.AuthorizationReceiptRequestDigestSourceBridge

open AspisPool.AuthorizationReceiptAccountWireV1
open AuthorizationReceiptRequestDigestGenerated

theorem statement_payload_digest_success_exact
    (request : GeneratedRequest)
    (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
    (digest : Array Std.U8 32#usize)
    (hstatement : request.binding.statement_version = 1#u8)
    (hnonempty : request.statement_payload.val ≠ [])
    (hlength : request.statement_payload.val.length ≤ 640)
    (hprofile :
      core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
        request.binding.profile_binding (Array.repeat 32#usize 0#u8) =
          .ok false)
    (hrelease :
      core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
        request.binding.release_binding (Array.repeat 32#usize 0#u8) =
          .ok false)
    (hhash : hash (statementPayloadDigestGeneratedInputs
      request.binding.statement_version request.binding.profile_binding
      request.binding.release_binding request.statement_payload) = .ok digest) :
    pool_v1.verifier_dispatch.verifier_statement_payload_digest_v1
        request.binding.statement_version request.binding.profile_binding
        request.binding.release_binding request.statement_payload hash =
      .ok (.Ok digest) := by
  have hpayloadBound : ¬ 640 < request.statement_payload.val.length := by
    omega
  simp only [statementPayloadDigestGeneratedInputs, hstatement,
    Slice.len, Slice.length, Array.to_slice, Array.make] at hhash
  simp [pool_v1.verifier_dispatch.verifier_statement_payload_digest_v1,
    pool_v1.historical_anchor.POOL_V1_HISTORICAL_ANCHOR_VERSION,
    pool_v1.verifier_dispatch.POOL_V1_VERIFIER_STATEMENT_PAYLOAD_MAX_BYTES,
    hstatement, hnonempty, hpayloadBound, hprofile, hrelease, hhash,
    core.slice.Slice.is_empty, Slice.len, Slice.length, Std.lift,
    Array.to_slice, Array.make]

def bytesOfGeneratedVec (values : alloc.vec.Vec Std.U8) : ByteString :=
  values.val.map byteOfGenerated

theorem request_generated_array_source_exact
    (binding : GeneratedBinding)
    (hstatement : binding.statement_version = 1#u8) :
    bytesOfGenerated (requestGeneratedArray binding) =
      encodeWireDispatchImage asvqMagic verifyCode (bindingOfGenerated binding) := by
  cases htransition : binding.transition_kind <;>
    simp [bytesOfGenerated, byteOfGenerated,
      encodeWireDispatchImage, bindingOfGenerated,
      transitionOfGenerated, bytes32List_bytes32OfGenerated,
      encodedDigestArray, u32LE_generated, u64LE_generated,
      asvqMagic, verifyCode, dispatchVersion, statementVersion,
      sha256Identifier, statementDigestVersion, transitionKindByte,
      requestGeneratedArray, requestGeneratedBytes,
      generatedTransitionByte, hstatement, htransition]
  all_goals
    simpa [bytesOfGenerated] using (u32LE_generated 1#u32).symm

theorem vec_extend_from_slice_success_exact
    (initial output : alloc.vec.Vec Std.U8) (source : Slice Std.U8)
    (hrun : alloc.vec.Vec.extend_from_slice core.clone.CloneU8 initial source =
      .ok output) :
    output.val = initial.val ++ source.val := by
  unfold alloc.vec.Vec.extend_from_slice at hrun
  split at hrun
  · split at hrun
    · rename_i cloned hclone
      have hsame : cloned = source := by
        obtain ⟨witness, hwitness, heq⟩ :=
          Aeneas.Std.WP.spec_imp_exists
            (Slice.clone_spec (clone := core.clone.CloneU8.clone)
              (s := source) (by simp))
        have : witness = cloned := Result.ok.inj (hwitness.symm.trans hclone)
        exact this ▸ heq.symm
      subst cloned
      exact congrArg (fun value : alloc.vec.Vec Std.U8 => value.val)
        (Result.ok.inj hrun).symm
    · simp at hrun
    · simp at hrun
  · simp at hrun

theorem request_header_generated_bind_after_lift {T : Type}
    (next : Array Std.U8 384#usize → Result T) :
    (do
      let x ←
        core.array.Array.index_mut (core.ops.index.IndexMutSlice
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8))
          (Array.repeat 384#usize 0#u8) { «end» := 4#usize }
      let slice ← core.slice.Slice.copy_from_slice core.marker.CopyU8 x.1
        pool_v1.verifier_dispatch.POOL_V1_VERIFIER_DISPATCH_REQUEST_MAGIC.to_slice
      let x1 ←
        core.array.Array.index_mut (core.ops.index.IndexMutSlice
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) (x.2 slice)
          { start := 8#usize, «end» := 12#usize }
      let slice ← core.slice.Slice.copy_from_slice core.marker.CopyU8 x1.1
        (core.num.U32.to_le_bytes
          pool_v1.verifier_dispatch.POOL_V1_VERIFIER_DISPATCH_VERIFY_CODE).to_slice
      next (x1.2 slice)) = next requestHeaderArray := by
  simpa only [Std.lift, bind_tc_ok] using
    (request_header_generated_bind next)

def requestHeaderGeneratedComputation : Result (Array Std.U8 384#usize) := do
  let x ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8))
      (Array.repeat 384#usize 0#u8) { «end» := 4#usize }
  let slice ← core.slice.Slice.copy_from_slice core.marker.CopyU8 x.1
    pool_v1.verifier_dispatch.POOL_V1_VERIFIER_DISPATCH_REQUEST_MAGIC.to_slice
  let x1 ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) (x.2 slice)
      { start := 8#usize, «end» := 12#usize }
  let slice ← core.slice.Slice.copy_from_slice core.marker.CopyU8 x1.1
    (core.num.U32.to_le_bytes
      pool_v1.verifier_dispatch.POOL_V1_VERIFIER_DISPATCH_VERIFY_CODE).to_slice
  ok (x1.2 slice)

theorem request_header_generated_computation_exact :
    requestHeaderGeneratedComputation = .ok requestHeaderArray := by
  simpa [requestHeaderGeneratedComputation] using
    (request_header_generated_bind_after_lift
      (fun header : Array Std.U8 384#usize => ok header))

theorem encode_dispatch_request_source_exact
    (request : GeneratedRequest)
    (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
    (output : alloc.vec.Vec Std.U8)
    (hrun :
      pool_v1.verifier_dispatch.encode_verifier_dispatch_request_v1 request hash =
        .ok (.Ok output)) :
    bytesOfGeneratedVec output =
      encodeWireDispatchRequest (requestOfGenerated request) := by
  unfold pool_v1.verifier_dispatch.encode_verifier_dispatch_request_v1 at hrun
  generalize hvalidate :
      pool_v1.verifier_dispatch.validate_verifier_dispatch_binding_v1
        request.binding = validation at hrun
  cases validation with
  | fail error => simp [hvalidate, Bind.bind, Aeneas.Std.bind] at hrun
  | div => simp [hvalidate, Bind.bind, Aeneas.Std.bind] at hrun
  | ok validation =>
      cases validation with
      | Err error =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame, core.convert.FromSame.from,
            Bind.bind, Aeneas.Std.bind] at hrun
      | Ok unit =>
          have hvalidation :
              pool_v1.verifier_dispatch.validate_verifier_dispatch_binding_v1
                  request.binding = .ok (.Ok ()) := by
            simpa using hvalidate
          have hstatement :=
            validation_success_statement_version request.binding hvalidation
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
            Std.lift] at hrun
          by_cases hpayloadLength :
              Slice.len request.statement_payload =
                UScalar.cast .Usize request.binding.statement_payload_length
          · simp only [hpayloadLength, ne_eq, not_true_eq_false,
              Bool.false_eq_true, if_false] at hrun
            generalize hdigest :
                pool_v1.verifier_dispatch.verifier_statement_payload_digest_v1
                  request.binding.statement_version request.binding.profile_binding
                  request.binding.release_binding request.statement_payload hash =
                    digestResult at hrun
            cases digestResult with
            | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
            | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
            | ok digestResult =>
                cases digestResult with
                | Err error =>
                    simp [core.result.Result.Insts.CoreOpsTry.branch,
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                      core.convert.FromSame, core.convert.FromSame.from,
                      Bind.bind, Aeneas.Std.bind] at hrun
                | Ok digest =>
                    simp only [core.result.Result.Insts.CoreOpsTry.branch,
                      bind_tc_ok] at hrun
                    generalize hdigestNe :
                        core.array.equality.PartialEqArray.ne
                          core.cmp.PartialEqU8 digest
                          request.binding.statement_digest = digestNeResult at hrun
                    cases digestNeResult with
                    | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
                    | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
                    | ok digestNe =>
                        cases digestNe with
                        | true => simp at hrun
                        | false =>
                          simp only [Std.lift, bind_tc_ok] at hrun
                          simp only [Bool.false_eq_true, if_false] at hrun
                          generalize hokOr :
                              core.option.Option.ok_or
                                (Usize.checked_add
                                  pool_v1.verifier_dispatch.POOL_V1_VERIFIER_DISPATCH_BINDING_PREFIX_BYTES
                                  (UScalar.cast .Usize
                                    request.binding.statement_payload_length))
                                pool_v1.verifier_dispatch.PoolV1VerifierDispatchFormatError.WrongLength =
                                  totalResult at hrun
                          cases totalResult with
                          | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
                          | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
                          | ok totalResult =>
                              cases totalResult with
                              | Err error =>
                                  simp [core.result.Result.Insts.CoreOpsTry.branch,
                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                    core.convert.FromSame, core.convert.FromSame.from,
                                    Bind.bind, Aeneas.Std.bind] at hrun
                              | Ok total =>
                                  simp only [core.result.Result.Insts.CoreOpsTry.branch,
                                    bind_tc_ok,
                                    pool_v1.verifier_dispatch.POOL_V1_VERIFIER_DISPATCH_REQUEST_MAX_BYTES,
                                    pool_v1.verifier_dispatch.POOL_V1_VERIFIER_DISPATCH_BINDING_PREFIX_BYTES,
                                    pool_v1.verifier_dispatch.POOL_V1_VERIFIER_STATEMENT_PAYLOAD_MAX_BYTES]
                                    at hrun
                                  obtain ⟨requestMax, hrequestMax,
                                      hrequestMaxVal⟩ :=
                                    Aeneas.Std.WP.spec_imp_exists
                                      (Usize.add_spec
                                        (x := 384#usize) (y := 640#usize)
                                        (by scalar_tac))
                                  have hrequestMaxEq :
                                      requestMax = 1024#usize := by
                                    apply UScalar.eq_of_val_eq
                                    simpa using hrequestMaxVal
                                  subst requestMax
                                  rw [hrequestMax] at hrun
                                  simp only [hpayloadLength, ne_eq,
                                    not_true_eq_false, Bool.false_eq_true,
                                    if_false, bind_tc_ok] at hrun
                                  split at hrun <;> try simp at hrun
                                  split at hrun <;> try simp at hrun
                                  focus
                                    let next : Array Std.U8 384#usize →
                                        Result (core.result.Result
                                          (alloc.vec.Vec Std.U8)
                                          pool_v1.verifier_dispatch.PoolV1VerifierDispatchFormatError) :=
                                      fun header => do
                                        let fields ←
                                          pool_v1.verifier_dispatch.encode_binding_fields
                                            header request.binding
                                        let first ← alloc.vec.Vec.extend_from_slice
                                          core.clone.CloneU8
                                          (alloc.vec.Vec.with_capacity Std.U8 total)
                                          (Array.to_slice fields)
                                        let second ← alloc.vec.Vec.extend_from_slice
                                          core.clone.CloneU8 first request.statement_payload
                                        ok (core.result.Result.Ok second)
                                    change
                                      (do
                                        let x ← core.array.Array.index_mut
                                          (core.ops.index.IndexMutSlice
                                            (core.slice.index.SliceIndexRangeToUsizeSlice
                                              Std.U8))
                                          (Array.repeat 384#usize 0#u8)
                                          { «end» := 4#usize }
                                        let slice ←
                                          core.slice.Slice.copy_from_slice
                                            core.marker.CopyU8 x.1
                                            pool_v1.verifier_dispatch.POOL_V1_VERIFIER_DISPATCH_REQUEST_MAGIC.to_slice
                                        let x1 ← core.array.Array.index_mut
                                          (core.ops.index.IndexMutSlice
                                            (core.slice.index.SliceIndexRangeUsizeSlice
                                              Std.U8))
                                          (x.2 slice)
                                          { start := 8#usize, «end» := 12#usize }
                                        let slice ←
                                          core.slice.Slice.copy_from_slice
                                            core.marker.CopyU8 x1.1
                                            (core.num.U32.to_le_bytes
                                              pool_v1.verifier_dispatch.POOL_V1_VERIFIER_DISPATCH_VERIFY_CODE).to_slice
                                        next (x1.2 slice)) =
                                          .ok (core.result.Result.Ok output) at hrun
                                    rw [request_header_generated_bind_after_lift next] at hrun
                                    simp only [next] at hrun
                                    generalize hfields :
                                        pool_v1.verifier_dispatch.encode_binding_fields
                                          requestHeaderArray request.binding = fieldsResult
                                          at hrun
                                    cases fieldsResult with
                                    | fail error =>
                                        simp [Bind.bind, Aeneas.Std.bind] at hrun
                                    | div =>
                                        simp [Bind.bind, Aeneas.Std.bind] at hrun
                                    | ok fields =>
                                        generalize hfirst :
                                            alloc.vec.Vec.extend_from_slice
                                              core.clone.CloneU8
                                              (alloc.vec.Vec.with_capacity Std.U8 total)
                                              (Array.to_slice fields) = firstResult at hrun
                                        cases firstResult with
                                        | fail error =>
                                            simp [hfirst, Bind.bind, Aeneas.Std.bind]
                                              at hrun
                                        | div =>
                                            simp [hfirst, Bind.bind, Aeneas.Std.bind]
                                              at hrun
                                        | ok first =>
                                            generalize hsecond :
                                                alloc.vec.Vec.extend_from_slice
                                                  core.clone.CloneU8 first
                                                  request.statement_payload = secondResult
                                                  at hrun
                                            cases secondResult with
                                            | fail error =>
                                                simp [hfirst, hsecond, Bind.bind,
                                                  Aeneas.Std.bind] at hrun
                                            | div =>
                                                simp [hfirst, hsecond, Bind.bind,
                                                  Aeneas.Std.bind] at hrun
                                            | ok second =>
                                                have houtput : output = second := by
                                                  simpa [hfirst, hsecond, Bind.bind,
                                                    Aeneas.Std.bind] using hrun.symm
                                                have hfieldsExact :=
                                                  encode_binding_fields_request_success_exact
                                                    request.binding fields hfields
                                                have hfirstExact :=
                                                  vec_extend_from_slice_success_exact
                                                    (alloc.vec.Vec.with_capacity Std.U8 total)
                                                    first (Array.to_slice fields) hfirst
                                                have hsecondExact :=
                                                  vec_extend_from_slice_success_exact
                                                    first second request.statement_payload hsecond
                                                subst output
                                                simp only [bytesOfGeneratedVec]
                                                rw [hsecondExact, hfirstExact, hfieldsExact]
                                                simp [bytesOfGeneratedVec,
                                                  alloc.vec.Vec.with_capacity,
                                                  alloc.vec.Vec.new, Array.to_slice,
                                                  requestOfGenerated,
                                                  encodeWireDispatchRequest,
                                                  List.map_append,
                                                  request_generated_array_source_exact
                                                    request.binding hstatement,
                                                  bytesOfGenerated,
                                                  bytesOfGeneratedSlice]
                                                simpa [bytesOfGenerated] using
                                                  request_generated_array_source_exact
                                                    request.binding hstatement
          · have hpayloadNe :
                (Slice.len request.statement_payload !=
                    UScalar.cast .Usize
                      request.binding.statement_payload_length) = true := by
              simpa only [bne_iff_ne] using hpayloadLength
            simp only [hpayloadNe, if_true] at hrun
            simp at hrun

def requestDigestGeneratedInputs
    (encodedRequest : alloc.vec.Vec Std.U8) : Slice (Slice Std.U8) :=
  Array.to_slice (Array.make 2#usize [
    pool_v1.authorization_receipt_account.POOL_V1_AUTHORIZATION_RECEIPT_REQUEST_DIGEST_DOMAIN,
    alloc.vec.Vec.deref encodedRequest
  ] (by simp))

theorem request_digest_domain_generated_exact :
    bytesOfGeneratedSlice
        pool_v1.authorization_receipt_account.POOL_V1_AUTHORIZATION_RECEIPT_REQUEST_DIGEST_DOMAIN =
      requestDigestDomain := by
  simp [bytesOfGeneratedSlice,
    pool_v1.authorization_receipt_account.POOL_V1_AUTHORIZATION_RECEIPT_REQUEST_DIGEST_DOMAIN,
    requestDigestDomain, byteOfGenerated, Array.to_slice, Array.make]

theorem request_digest_preimage_source_exact
    (request : GeneratedRequest) (encodedRequest : alloc.vec.Vec Std.U8)
    (hencode : bytesOfGeneratedVec encodedRequest =
      encodeWireDispatchRequest (requestOfGenerated request)) :
    generatedShaPreimage (requestDigestGeneratedInputs encodedRequest) =
      wireRequestDigestPreimage (requestOfGenerated request) := by
  calc
    generatedShaPreimage (requestDigestGeneratedInputs encodedRequest) =
      bytesOfGeneratedSlice
          pool_v1.authorization_receipt_account.POOL_V1_AUTHORIZATION_RECEIPT_REQUEST_DIGEST_DOMAIN ++
        bytesOfGeneratedVec encodedRequest := by
      simp [generatedShaPreimage, requestDigestGeneratedInputs,
        alloc.vec.Vec.deref, bytesOfGeneratedSlice, bytesOfGeneratedVec,
        Array.to_slice, Array.make]
    _ = requestDigestDomain ++
        encodeWireDispatchRequest (requestOfGenerated request) := by
      rw [request_digest_domain_generated_exact, hencode]
    _ = wireRequestDigestPreimage (requestOfGenerated request) := by
      rfl

theorem request_digest_source_exact
    (sha256 : Sha256)
    (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
    (hhash : GeneratedSha256Matches sha256 hash)
    (request : GeneratedRequest) (digest : Array Std.U8 32#usize)
    (hrun :
      pool_v1.authorization_receipt_account.pool_v1_authorization_receipt_request_digest_v1
        request hash = .ok (.Ok digest)) :
    bytesOfGenerated digest = bytes32List
      (sha256 (wireRequestDigestPreimage (requestOfGenerated request))) := by
  unfold
    pool_v1.authorization_receipt_account.pool_v1_authorization_receipt_request_digest_v1
    at hrun
  generalize hencode :
      pool_v1.verifier_dispatch.encode_verifier_dispatch_request_v1 request hash =
        encodeResult at hrun
  cases encodeResult with
  | fail error => simp [hencode, Bind.bind, Aeneas.Std.bind] at hrun
  | div => simp [hencode, Bind.bind, Aeneas.Std.bind] at hrun
  | ok encodeResult =>
      cases encodeResult with
      | Err error =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            pool_v1.authorization_receipt_account.PoolV1AuthorizationReceiptAccountErrorV1.Insts.CoreConvertFromPoolV1VerifierDispatchFormatError.from,
            Bind.bind, Aeneas.Std.bind] at hrun
      | Ok encodedRequest =>
          have hencodeExact :=
            encode_dispatch_request_source_exact request hash encodedRequest hencode
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
            Std.lift, Array.to_slice, bind_tc_ok] at hrun
          change
            (do
              let digest ← hash (requestDigestGeneratedInputs encodedRequest)
              ok (core.result.Result.Ok digest)) = .ok (.Ok digest) at hrun
          generalize hdigest :
              hash (requestDigestGeneratedInputs encodedRequest) = digestResult
              at hrun
          cases digestResult with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
          | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
          | ok generatedDigest =>
              have hdigestEq : digest = generatedDigest := by
                simpa using hrun.symm
              have hhashExact := hhash
                (requestDigestGeneratedInputs encodedRequest)
                generatedDigest hdigest
              subst digest
              rw [hhashExact,
                request_digest_preimage_source_exact request encodedRequest
                  hencodeExact]

#print axioms statement_payload_digest_preimage_source_exact
#print axioms statement_payload_digest_success_exact
#print axioms encode_dispatch_request_source_exact
#print axioms request_digest_preimage_source_exact
#print axioms request_digest_source_exact

end AspisPool.AuthorizationReceiptRequestDigestSourceBridge
