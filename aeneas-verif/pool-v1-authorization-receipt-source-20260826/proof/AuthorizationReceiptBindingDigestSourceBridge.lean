import AuthorizationReceiptBindingDigest.Funs
import AspisFormal.Pool.AuthorizationReceiptAccountWireV1
import Aeneas.Tactic.Step.Step

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisPool.AuthorizationReceiptBindingDigestSourceBridge

open AspisPool.AuthorizationReceiptAccountWireV1
open AuthorizationReceiptBindingDigestGenerated

abbrev GeneratedBinding :=
  pool_v1.verifier_dispatch.VerifierDispatchBindingV1

def byteOfGenerated (value : Std.U8) : UInt8 :=
  UInt8.ofNat value.val

@[simp] theorem byteOfGenerated_toNat (value : Std.U8) :
    (byteOfGenerated value).toNat = value.val := by
  simp [byteOfGenerated]

def bytesOfGenerated {N : Std.Usize} (values : Array Std.U8 N) : ByteString :=
  values.val.map byteOfGenerated

def bytes32OfGenerated (values : Array Std.U8 32#usize) : Bytes32 :=
  fun index => byteOfGenerated (values.val[index.val]'(by
    have hindex := index.isLt
    simpa [values.property] using hindex))

theorem bytes32List_bytes32OfGenerated
    (values : Array Std.U8 32#usize) :
    bytes32List (bytes32OfGenerated values) = bytesOfGenerated values := by
  simpa [bytes32List, bytes32OfGenerated, bytesOfGenerated, values.property]
    using (List.ofFn_getElem_eq_map (l := values.val) byteOfGenerated)

def encodedDigestArray
    (digest : Array aspis_core.field.M31 8#usize) : Array Std.U8 32#usize :=
  match atomic_statement.encode_digest_canonical digest with
  | .ok output => output
  | _ => Array.repeat 32#usize 0#u8

def transitionOfGenerated :
    pool_v1.historical_anchor.PoolV1TransitionKind →
      AspisPool.AuthorizationReceiptV1.TransitionKind
  | .PrivateTransfer => .privateTransfer
  | .Withdrawal => .withdrawal

def bindingOfGenerated (binding : GeneratedBinding) : WireBinding where
  transitionKind := transitionOfGenerated binding.transition_kind
  verifierProgram := bytes32OfGenerated binding.verifier_program
  profileBinding := bytes32OfGenerated binding.profile_binding
  releaseBinding := bytes32OfGenerated binding.release_binding
  pool := bytes32OfGenerated binding.pool
  deploymentDomain := bytes32OfGenerated binding.deployment_domain
  anchorSequence := binding.anchor_sequence.val
  anchorRootCanonical := bytes32OfGenerated (encodedDigestArray binding.anchor_root)
  nullifierCanonical := bytes32OfGenerated (encodedDigestArray binding.nullifier)
  statementDigest := bytes32OfGenerated binding.statement_digest
  envelopeDigest := bytes32OfGenerated binding.envelope_digest
  proofAccount := bytes32OfGenerated binding.proof_account
  proofBodyDigest := bytes32OfGenerated binding.proof_body_digest
  proofBodyLength := binding.proof_body_length.val
  statementPayloadLength := binding.statement_payload_length.val

theorem u32LE_generated (value : Std.U32) :
    u32LE value.val = bytesOfGenerated (core.num.U32.to_le_bytes value) := by
  have hvalue := value.lt_succ_max
  apply List.ext_getElem
  · simp [u32LE, bytesOfGenerated]
  · intro index hleft hright
    have hindex : index < 4 := by simpa [u32LE] using hleft
    interval_cases index <;>
      apply UInt8.toNat_inj.mp <;>
      simp [u32LE, littleEndianByte, bytesOfGenerated,
        core.num.U32.to_le_bytes, byteOfGenerated, BitVec.toLEBytes] <;>
      change _ = (BitVec.setWidth 8 _).toNat <;>
      simp [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
        Nat.shiftRight_eq_div_pow] <;> omega

theorem u64LE_generated (value : Std.U64) :
    u64LE value.val = bytesOfGenerated (core.num.U64.to_le_bytes value) := by
  have hvalue := value.lt_succ_max
  apply List.ext_getElem
  · simp [u64LE, bytesOfGenerated]
  · intro index hleft hright
    have hindex : index < 8 := by simpa [u64LE] using hleft
    interval_cases index <;>
      apply UInt8.toNat_inj.mp <;>
      simp [u64LE, littleEndianByte, bytesOfGenerated,
        core.num.U64.to_le_bytes, byteOfGenerated, BitVec.toLEBytes] <;>
      change _ = (BitVec.setWidth 8 _).toNat <;>
      simp [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
        Nat.shiftRight_eq_div_pow] <;> omega

def generatedTransitionByte :
    pool_v1.historical_anchor.PoolV1TransitionKind → Std.U8
  | .PrivateTransfer => 1#u8
  | .Withdrawal => 2#u8

@[simp] theorem transition_discriminant_cast
    (kind : pool_v1.historical_anchor.PoolV1TransitionKind) :
    lift (UScalar.cast .U8 (read_discriminant kind)) =
      .ok (generatedTransitionByte kind) := by
  cases kind <;> rfl

def dispatchGeneratedBytes (binding : GeneratedBinding) : List Std.U8 :=
  [65#u8, 83#u8, 86#u8, 83#u8,
    1#u8, binding.statement_version,
    generatedTransitionByte binding.transition_kind, 1#u8] ++
  (core.num.U32.to_le_bytes 1095958529#u32).val ++
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

def dispatchGeneratedArray (binding : GeneratedBinding) :
    Array Std.U8 384#usize :=
  ⟨dispatchGeneratedBytes binding, by
    simp [dispatchGeneratedBytes, binding.verifier_program.property,
      binding.profile_binding.property, binding.release_binding.property,
      binding.pool.property, binding.deployment_domain.property,
      binding.statement_digest.property, binding.envelope_digest.property,
      binding.proof_account.property, binding.proof_body_digest.property,
      (encodedDigestArray binding.anchor_root).property,
      (encodedDigestArray binding.nullifier).property,
      core.num.U32.to_le_bytes, core.num.U64.to_le_bytes]⟩

def dispatchHeaderArray : Array Std.U8 384#usize :=
  Array.make 384#usize
    ([65#u8, 83#u8, 86#u8, 83#u8] ++ List.replicate 4 0#u8 ++
      (core.num.U32.to_le_bytes 1095958529#u32).val ++ List.replicate 372 0#u8)
    (by simp [core.num.U32.to_le_bytes])

def dispatchScalarPrefix (binding : GeneratedBinding) : List Std.U8 :=
  [65#u8, 83#u8, 86#u8, 83#u8, 1#u8, binding.statement_version,
    generatedTransitionByte binding.transition_kind, 1#u8] ++
  (core.num.U32.to_le_bytes 1095958529#u32).val ++
  [1#u8, 0#u8, 0#u8, 0#u8]

theorem dispatch_header_scalar_prefix (binding : GeneratedBinding) :
    (((((dispatchHeaderArray.val.set 4 1#u8).set 5 binding.statement_version).set 6
      (generatedTransitionByte binding.transition_kind)).set 7 1#u8).set 12 1#u8) =
      dispatchScalarPrefix binding ++ List.replicate 368 0#u8 := by
  simp [dispatchHeaderArray, dispatchScalarPrefix, Array.make,
    core.num.U32.to_le_bytes]

theorem dispatch_header_run :
    (do
      let output := Array.repeat 384#usize 0#u8
      let (slice, back) ←
        core.array.Array.index_mut (core.ops.index.IndexMutSlice
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)) output
          { «end» := 4#usize }
      let magic ← lift (Array.to_slice
        pool_v1.verifier_dispatch.POOL_V1_VERIFIER_DISPATCH_RESULT_MAGIC)
      let slice ← core.slice.Slice.copy_from_slice core.marker.CopyU8 slice magic
      let output := back slice
      let (slice, back) ←
        core.array.Array.index_mut (core.ops.index.IndexMutSlice
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output
          { start := 8#usize, «end» := 12#usize }
      let code ← lift (core.num.U32.to_le_bytes 1095958529#u32)
      let code ← lift (Array.to_slice code)
      let slice ← core.slice.Slice.copy_from_slice core.marker.CopyU8 slice code
      ok (back slice)) = .ok dispatchHeaderArray := by
  simp [pool_v1.verifier_dispatch.POOL_V1_VERIFIER_DISPATCH_RESULT_MAGIC,
    Std.lift, Array.update, core.array.Array.index_mut,
    core.ops.index.IndexMutSlice, core.slice.index.Slice.index_mut,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
    core.slice.Slice.copy_from_slice, Array.to_slice, Array.from_slice,
    Array.repeat, Array.make, List.setSlice!, Slice.len, Slice.length,
    dispatchHeaderArray, core.num.U32.to_le_bytes]
  simp_lists

theorem dispatch_header_bind {T : Type}
    (next : Array Std.U8 384#usize → Result T) :
    (do
      let output := Array.repeat 384#usize 0#u8
      let (slice, back) ←
        core.array.Array.index_mut (core.ops.index.IndexMutSlice
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)) output
          { «end» := 4#usize }
      let magic ← lift (Array.to_slice
        pool_v1.verifier_dispatch.POOL_V1_VERIFIER_DISPATCH_RESULT_MAGIC)
      let slice ← core.slice.Slice.copy_from_slice core.marker.CopyU8 slice magic
      let output := back slice
      let (slice, back) ←
        core.array.Array.index_mut (core.ops.index.IndexMutSlice
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output
          { start := 8#usize, «end» := 12#usize }
      let code ← lift (core.num.U32.to_le_bytes 1095958529#u32)
      let code ← lift (Array.to_slice code)
      let slice ← core.slice.Slice.copy_from_slice core.marker.CopyU8 slice code
      next (back slice)) = next dispatchHeaderArray := by
  simp [pool_v1.verifier_dispatch.POOL_V1_VERIFIER_DISPATCH_RESULT_MAGIC,
    Std.lift, core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
    core.slice.Slice.copy_from_slice, Array.to_slice, Array.from_slice,
    Array.repeat, Array.make, List.setSlice!, Slice.len,
    dispatchHeaderArray, core.num.U32.to_le_bytes]
  simp_lists

def bindingResultBytes (initial : Array Std.U8 384#usize)
    (binding : GeneratedBinding)
    (anchorBytes nullifierBytes : Array Std.U8 32#usize) : List Std.U8 :=
  let output := initial.val.set 4 1#u8
  let output := output.set 5 binding.statement_version
  let output := output.set 6 (generatedTransitionByte binding.transition_kind)
  let output := output.set 7 1#u8
  let output := output.set 12 1#u8
  let output := output.setSlice! 16 binding.verifier_program.val
  let output := output.setSlice! 48 binding.profile_binding.val
  let output := output.setSlice! 80 binding.release_binding.val
  let output := output.setSlice! 112 binding.pool.val
  let output := output.setSlice! 144 binding.deployment_domain.val
  let output := output.setSlice! 176
    (core.num.U64.to_le_bytes binding.anchor_sequence).val
  let output := output.setSlice! 184 anchorBytes.val
  let output := output.setSlice! 216 nullifierBytes.val
  let output := output.setSlice! 248 binding.statement_digest.val
  let output := output.setSlice! 280 binding.envelope_digest.val
  let output := output.setSlice! 312 binding.proof_account.val
  let output := output.setSlice! 344 binding.proof_body_digest.val
  let output := output.setSlice! 376
    (core.num.U32.to_le_bytes binding.proof_body_length).val
  output.setSlice! 380
    (core.num.U32.to_le_bytes binding.statement_payload_length).val

def bindingResultArray (initial : Array Std.U8 384#usize)
    (binding : GeneratedBinding)
    (anchorBytes nullifierBytes : Array Std.U8 32#usize) :
    Array Std.U8 384#usize :=
  ⟨bindingResultBytes initial binding anchorBytes nullifierBytes, by
    simp [bindingResultBytes, initial.property,
      binding.verifier_program.property, binding.profile_binding.property,
      binding.release_binding.property, binding.pool.property,
      binding.deployment_domain.property, binding.statement_digest.property,
      binding.envelope_digest.property, binding.proof_account.property,
      binding.proof_body_digest.property, anchorBytes.property,
      nullifierBytes.property, core.num.U32.to_le_bytes,
      core.num.U64.to_le_bytes, List.setSlice!]⟩

theorem setSlice_append_replicate {alpha : Type}
    (front source : List alpha) (fill : alpha) (remaining : Nat)
    (hsource : source.length ≤ remaining) :
    (front ++ List.replicate remaining fill).setSlice! front.length source =
      (front ++ source) ++ List.replicate (remaining - source.length) fill := by
  simp [List.setSlice!, hsource]

theorem setSlice_append_replicate_at {alpha : Type}
    (front source : List alpha) (fill : alpha) (remaining index : Nat)
    (hindex : index = front.length) (hsource : source.length ≤ remaining) :
    (front ++ List.replicate remaining fill).setSlice! index source =
      (front ++ source) ++ List.replicate (remaining - source.length) fill := by
  subst index
  exact setSlice_append_replicate front source fill remaining hsource

def chunksLength {alpha : Type} : List (List alpha) → Nat
  | [] => 0
  | chunk :: chunks => chunk.length + chunksLength chunks

def writeSlices {alpha : Type} (output : List alpha) (offset : Nat) :
    List (List alpha) → List alpha
  | [] => output
  | chunk :: chunks =>
      writeSlices (output.setSlice! offset chunk) (offset + chunk.length) chunks

theorem writeSlices_append_replicate {alpha : Type}
    (front : List alpha) (chunks : List (List alpha)) (fill : alpha)
    (remaining : Nat) (hchunks : chunksLength chunks ≤ remaining) :
    writeSlices (front ++ List.replicate remaining fill) front.length chunks =
      (front ++ chunks.flatten) ++
        List.replicate (remaining - chunksLength chunks) fill := by
  induction chunks generalizing front remaining with
  | nil => simp [writeSlices, chunksLength]
  | cons chunk chunks inductionHypothesis =>
      simp only [writeSlices, chunksLength]
      simp only [chunksLength] at hchunks
      have hchunk : chunk.length ≤ remaining := by omega
      rw [setSlice_append_replicate front chunk fill remaining hchunk]
      rw [show front.length + chunk.length = (front ++ chunk).length by simp]
      have hrest : chunksLength chunks ≤ remaining - chunk.length := by omega
      rw [inductionHypothesis (front := front ++ chunk)
        (remaining := remaining - chunk.length) hrest]
      simp only [List.flatten_cons, List.append_assoc]
      congr 2
      rw [Nat.sub_sub]

def dispatchChunks (binding : GeneratedBinding)
    (anchorBytes nullifierBytes : Array Std.U8 32#usize) :
    List (List Std.U8) :=
  [binding.verifier_program.val,
    binding.profile_binding.val,
    binding.release_binding.val,
    binding.pool.val,
    binding.deployment_domain.val,
    (core.num.U64.to_le_bytes binding.anchor_sequence).val,
    anchorBytes.val,
    nullifierBytes.val,
    binding.statement_digest.val,
    binding.envelope_digest.val,
    binding.proof_account.val,
    binding.proof_body_digest.val,
    (core.num.U32.to_le_bytes binding.proof_body_length).val,
    (core.num.U32.to_le_bytes binding.statement_payload_length).val]

@[simp] theorem dispatchScalarPrefix_length (binding : GeneratedBinding) :
    (dispatchScalarPrefix binding).length = 16 := by
  simp [dispatchScalarPrefix, core.num.U32.to_le_bytes]

@[simp] theorem dispatchChunks_length (binding : GeneratedBinding)
    (anchorBytes nullifierBytes : Array Std.U8 32#usize) :
    chunksLength (dispatchChunks binding anchorBytes nullifierBytes) = 368 := by
  simp [chunksLength, dispatchChunks, binding.verifier_program.property,
    binding.profile_binding.property, binding.release_binding.property,
    binding.pool.property, binding.deployment_domain.property,
    binding.statement_digest.property, binding.envelope_digest.property,
    binding.proof_account.property, binding.proof_body_digest.property,
    anchorBytes.property, nullifierBytes.property,
    core.num.U32.to_le_bytes, core.num.U64.to_le_bytes]

theorem bindingResultBytes_as_writeSlices
    (binding : GeneratedBinding)
    (anchorBytes nullifierBytes : Array Std.U8 32#usize) :
    bindingResultBytes dispatchHeaderArray binding anchorBytes nullifierBytes =
      writeSlices
        (dispatchScalarPrefix binding ++ List.replicate 368 0#u8)
        (dispatchScalarPrefix binding).length
        (dispatchChunks binding anchorBytes nullifierBytes) := by
  simp only [bindingResultBytes]
  rw [dispatch_header_scalar_prefix]
  simp [writeSlices, dispatchChunks, binding.verifier_program.property,
    binding.profile_binding.property, binding.release_binding.property,
    binding.pool.property, binding.deployment_domain.property,
    binding.statement_digest.property, binding.envelope_digest.property,
    binding.proof_account.property, binding.proof_body_digest.property,
    anchorBytes.property, nullifierBytes.property,
    core.num.U32.to_le_bytes, core.num.U64.to_le_bytes]

theorem encode_binding_fields_run_generic
    (initial : Array Std.U8 384#usize)
    (binding : GeneratedBinding)
    (anchorBytes nullifierBytes : Array Std.U8 32#usize)
    (hanchor : atomic_statement.encode_digest_canonical binding.anchor_root =
      .ok anchorBytes)
    (hnullifier : atomic_statement.encode_digest_canonical binding.nullifier =
      .ok nullifierBytes) :
    pool_v1.verifier_dispatch.encode_binding_fields initial binding =
      .ok (bindingResultArray initial binding anchorBytes nullifierBytes) := by
  have hspec :
      pool_v1.verifier_dispatch.encode_binding_fields initial binding
        ⦃ output =>
          output = bindingResultArray initial binding anchorBytes nullifierBytes ⦄ := by
    unfold pool_v1.verifier_dispatch.encode_binding_fields
    simp only [transition_discriminant_cast, bind_tc_ok]
    repeat' step
    all_goals simp_all [
      pool_v1.verifier_dispatch.POOL_V1_VERIFIER_DISPATCH_VERSION,
      pool_v1.verifier_dispatch.POOL_V1_VERIFIER_DISPATCH_HASH_SHA256,
      pool_v1.verifier_dispatch.POOL_V1_VERIFIER_STATEMENT_DIGEST_VERSION,
      pool_v1.verifier_dispatch.VERIFIER_PROGRAM_OFFSET,
      pool_v1.verifier_dispatch.PROFILE_OFFSET,
      pool_v1.verifier_dispatch.RELEASE_OFFSET,
      pool_v1.verifier_dispatch.POOL_OFFSET,
      pool_v1.verifier_dispatch.DEPLOYMENT_DOMAIN_OFFSET,
      pool_v1.verifier_dispatch.ANCHOR_SEQUENCE_OFFSET,
      pool_v1.verifier_dispatch.ANCHOR_ROOT_OFFSET,
      pool_v1.verifier_dispatch.NULLIFIER_OFFSET,
      pool_v1.verifier_dispatch.STATEMENT_DIGEST_OFFSET,
      pool_v1.verifier_dispatch.ENVELOPE_DIGEST_OFFSET,
      pool_v1.verifier_dispatch.PROOF_ACCOUNT_OFFSET,
      pool_v1.verifier_dispatch.PROOF_BODY_DIGEST_OFFSET,
      pool_v1.verifier_dispatch.PROOF_BODY_LENGTH_OFFSET,
      pool_v1.verifier_dispatch.STATEMENT_PAYLOAD_LENGTH_OFFSET,
      Std.lift, Array.to_slice, Slice.length]
    repeat' step
    all_goals simp_all [
      pool_v1.verifier_dispatch.POOL_V1_VERIFIER_DISPATCH_VERSION,
      pool_v1.verifier_dispatch.POOL_V1_VERIFIER_DISPATCH_HASH_SHA256,
      pool_v1.verifier_dispatch.POOL_V1_VERIFIER_STATEMENT_DIGEST_VERSION,
      pool_v1.verifier_dispatch.VERIFIER_PROGRAM_OFFSET,
      pool_v1.verifier_dispatch.PROFILE_OFFSET,
      pool_v1.verifier_dispatch.RELEASE_OFFSET,
      pool_v1.verifier_dispatch.POOL_OFFSET,
      pool_v1.verifier_dispatch.DEPLOYMENT_DOMAIN_OFFSET,
      pool_v1.verifier_dispatch.ANCHOR_SEQUENCE_OFFSET,
      pool_v1.verifier_dispatch.ANCHOR_ROOT_OFFSET,
      pool_v1.verifier_dispatch.NULLIFIER_OFFSET,
      pool_v1.verifier_dispatch.STATEMENT_DIGEST_OFFSET,
      pool_v1.verifier_dispatch.ENVELOPE_DIGEST_OFFSET,
      pool_v1.verifier_dispatch.PROOF_ACCOUNT_OFFSET,
      pool_v1.verifier_dispatch.PROOF_BODY_DIGEST_OFFSET,
      pool_v1.verifier_dispatch.PROOF_BODY_LENGTH_OFFSET,
      pool_v1.verifier_dispatch.STATEMENT_PAYLOAD_LENGTH_OFFSET,
      Std.lift, Array.to_slice, Slice.length]
    repeat' step
    all_goals simp_all [
      pool_v1.verifier_dispatch.POOL_V1_VERIFIER_DISPATCH_VERSION,
      pool_v1.verifier_dispatch.POOL_V1_VERIFIER_DISPATCH_HASH_SHA256,
      pool_v1.verifier_dispatch.POOL_V1_VERIFIER_STATEMENT_DIGEST_VERSION,
      pool_v1.verifier_dispatch.VERIFIER_PROGRAM_OFFSET,
      pool_v1.verifier_dispatch.PROFILE_OFFSET,
      pool_v1.verifier_dispatch.RELEASE_OFFSET,
      pool_v1.verifier_dispatch.POOL_OFFSET,
      pool_v1.verifier_dispatch.DEPLOYMENT_DOMAIN_OFFSET,
      pool_v1.verifier_dispatch.ANCHOR_SEQUENCE_OFFSET,
      pool_v1.verifier_dispatch.ANCHOR_ROOT_OFFSET,
      pool_v1.verifier_dispatch.NULLIFIER_OFFSET,
      pool_v1.verifier_dispatch.STATEMENT_DIGEST_OFFSET,
      pool_v1.verifier_dispatch.ENVELOPE_DIGEST_OFFSET,
      pool_v1.verifier_dispatch.PROOF_ACCOUNT_OFFSET,
      pool_v1.verifier_dispatch.PROOF_BODY_DIGEST_OFFSET,
      pool_v1.verifier_dispatch.PROOF_BODY_LENGTH_OFFSET,
      pool_v1.verifier_dispatch.STATEMENT_PAYLOAD_LENGTH_OFFSET,
      Std.lift, Array.to_slice, Slice.length, bindingResultArray, bindingResultBytes,
      Array.set]
    apply Subtype.ext
    simpa [Array.to_slice, core.num.U64.to_le_bytes] using
      output_post3
        (Array.to_slice
          (core.num.U32.to_le_bytes binding.statement_payload_length))
  obtain ⟨output, hrun, hout⟩ := Aeneas.Std.WP.spec_imp_exists hspec
  simpa [hout] using hrun

/- Historical direct fourteen-write normalization, retained as excluded
documentation.  The checked declaration below uses the recursive chunk proof. -/
/-
theorem bindingResultArray_header_exact
    (binding : GeneratedBinding)
    (anchorBytes nullifierBytes : Array Std.U8 32#usize)
    (hanchor : atomic_statement.encode_digest_canonical binding.anchor_root =
      .ok anchorBytes)
    (hnullifier : atomic_statement.encode_digest_canonical binding.nullifier =
      .ok nullifierBytes) :
    bindingResultArray dispatchHeaderArray binding anchorBytes nullifierBytes =
      dispatchGeneratedArray binding := by
  have hverifierLength : binding.verifier_program.val.length = 32 := by
    simpa using binding.verifier_program.property
  have hprofileLength : binding.profile_binding.val.length = 32 := by
    simpa using binding.profile_binding.property
  have hreleaseLength : binding.release_binding.val.length = 32 := by
    simpa using binding.release_binding.property
  have hpoolLength : binding.pool.val.length = 32 := by
    simpa using binding.pool.property
  have hdomainLength : binding.deployment_domain.val.length = 32 := by
    simpa using binding.deployment_domain.property
  have hanchorLength : anchorBytes.val.length = 32 := by
    simpa using anchorBytes.property
  have hnullifierLength : nullifierBytes.val.length = 32 := by
    simpa using nullifierBytes.property
  have hstatementLength : binding.statement_digest.val.length = 32 := by
    simpa using binding.statement_digest.property
  have henvelopeLength : binding.envelope_digest.val.length = 32 := by
    simpa using binding.envelope_digest.property
  have hproofAccountLength : binding.proof_account.val.length = 32 := by
    simpa using binding.proof_account.property
  have hproofBodyDigestLength : binding.proof_body_digest.val.length = 32 := by
    simpa using binding.proof_body_digest.property
  have hanchorSequenceLength :
      (core.num.U64.to_le_bytes binding.anchor_sequence).val.length = 8 := by
    simp [core.num.U64.to_le_bytes]
  have hproofBodyLengthLength :
      (core.num.U32.to_le_bytes binding.proof_body_length).val.length = 4 := by
    simp [core.num.U32.to_le_bytes]
  have hpayloadLengthLength :
      (core.num.U32.to_le_bytes binding.statement_payload_length).val.length = 4 := by
    simp [core.num.U32.to_le_bytes]
  apply Subtype.ext
  simp only [bindingResultArray, bindingResultBytes]
  rw [dispatch_header_scalar_prefix]
  rw [setSlice_append_replicate_at _ binding.verifier_program.val 0#u8 368 16
    (by simp [dispatchScalarPrefix, core.num.U32.to_le_bytes])
    (by simp [binding.verifier_program.property])]
  simp only [hverifierLength, Nat.reduceSubDiff]
  rw [setSlice_append_replicate_at _ binding.profile_binding.val 0#u8 336 48
    (by simp [dispatchScalarPrefix, binding.verifier_program.property,
      core.num.U32.to_le_bytes])
    (by simp [binding.profile_binding.property])]
  simp only [hprofileLength, Nat.reduceSubDiff]
  rw [setSlice_append_replicate_at _ binding.release_binding.val 0#u8 304 80
    (by simp [dispatchScalarPrefix, binding.verifier_program.property,
      binding.profile_binding.property, core.num.U32.to_le_bytes])
    (by simp [binding.release_binding.property])]
  simp only [hreleaseLength, Nat.reduceSubDiff]
  rw [setSlice_append_replicate_at _ binding.pool.val 0#u8 272 112
    (by simp [dispatchScalarPrefix, binding.verifier_program.property,
      binding.profile_binding.property, binding.release_binding.property,
      core.num.U32.to_le_bytes])
    (by simp [binding.pool.property])]
  simp only [hpoolLength, Nat.reduceSubDiff]
  rw [setSlice_append_replicate_at _ binding.deployment_domain.val 0#u8 240 144
    (by simp [dispatchScalarPrefix, binding.verifier_program.property,
      binding.profile_binding.property, binding.release_binding.property,
      binding.pool.property, core.num.U32.to_le_bytes])
    (by simp [binding.deployment_domain.property])]
  simp only [hdomainLength, Nat.reduceSubDiff]
  rw [setSlice_append_replicate_at _
    (core.num.U64.to_le_bytes binding.anchor_sequence).val 0#u8 208 176
    (by simp [dispatchScalarPrefix, binding.verifier_program.property,
      binding.profile_binding.property, binding.release_binding.property,
      binding.pool.property, binding.deployment_domain.property,
      core.num.U32.to_le_bytes])
    (by simp [core.num.U64.to_le_bytes])]
  simp only [hanchorSequenceLength, Nat.reduceSubDiff]
  rw [setSlice_append_replicate_at _ anchorBytes.val 0#u8 200 184
    (by simp [dispatchScalarPrefix, binding.verifier_program.property,
      binding.profile_binding.property, binding.release_binding.property,
      binding.pool.property, binding.deployment_domain.property,
      core.num.U32.to_le_bytes])
    (by simp [anchorBytes.property])]
  simp only [hanchorLength, Nat.reduceSubDiff]
  rw [setSlice_append_replicate_at _ nullifierBytes.val 0#u8 168 216
    (by simp [dispatchScalarPrefix, binding.verifier_program.property,
      binding.profile_binding.property, binding.release_binding.property,
      binding.pool.property, binding.deployment_domain.property,
      anchorBytes.property, core.num.U32.to_le_bytes,
      core.num.U64.to_le_bytes])
    (by simp [nullifierBytes.property])]
  simp only [hnullifierLength, Nat.reduceSubDiff]
  rw [setSlice_append_replicate_at _ binding.statement_digest.val 0#u8 136 248
    (by simp [dispatchScalarPrefix, binding.verifier_program.property,
      binding.profile_binding.property, binding.release_binding.property,
      binding.pool.property, binding.deployment_domain.property,
      anchorBytes.property, nullifierBytes.property,
      core.num.U32.to_le_bytes, core.num.U64.to_le_bytes])
    (by simp [binding.statement_digest.property])]
  simp only [hstatementLength, Nat.reduceSubDiff]
  rw [setSlice_append_replicate_at _ binding.envelope_digest.val 0#u8 104 280
    (by simp [dispatchScalarPrefix, binding.verifier_program.property,
      binding.profile_binding.property, binding.release_binding.property,
      binding.pool.property, binding.deployment_domain.property,
      anchorBytes.property, nullifierBytes.property,
      binding.statement_digest.property, core.num.U32.to_le_bytes,
      core.num.U64.to_le_bytes])
    (by simp [binding.envelope_digest.property])]
  simp only [henvelopeLength, Nat.reduceSubDiff]
  rw [setSlice_append_replicate_at _ binding.proof_account.val 0#u8 72 312
    (by simp [dispatchScalarPrefix, binding.verifier_program.property,
      binding.profile_binding.property, binding.release_binding.property,
      binding.pool.property, binding.deployment_domain.property,
      anchorBytes.property, nullifierBytes.property,
      binding.statement_digest.property, binding.envelope_digest.property,
      core.num.U32.to_le_bytes, core.num.U64.to_le_bytes])
    (by simp [binding.proof_account.property])]
  simp only [hproofAccountLength, Nat.reduceSubDiff]
  rw [setSlice_append_replicate_at _ binding.proof_body_digest.val 0#u8 40 344
    (by simp [dispatchScalarPrefix, binding.verifier_program.property,
      binding.profile_binding.property, binding.release_binding.property,
      binding.pool.property, binding.deployment_domain.property,
      anchorBytes.property, nullifierBytes.property,
      binding.statement_digest.property, binding.envelope_digest.property,
      binding.proof_account.property, core.num.U32.to_le_bytes,
      core.num.U64.to_le_bytes])
    (by simp [binding.proof_body_digest.property])]
  simp only [hproofBodyDigestLength, Nat.reduceSubDiff]
  rw [setSlice_append_replicate_at _
    (core.num.U32.to_le_bytes binding.proof_body_length).val 0#u8 8 376
    (by simp [dispatchScalarPrefix, binding.verifier_program.property,
      binding.profile_binding.property, binding.release_binding.property,
      binding.pool.property, binding.deployment_domain.property,
      anchorBytes.property, nullifierBytes.property,
      binding.statement_digest.property, binding.envelope_digest.property,
      binding.proof_account.property, binding.proof_body_digest.property,
      core.num.U32.to_le_bytes, core.num.U64.to_le_bytes])
    (by simp [core.num.U32.to_le_bytes])]
  simp only [hproofBodyLengthLength, Nat.reduceSubDiff]
  rw [setSlice_append_replicate_at _
    (core.num.U32.to_le_bytes binding.statement_payload_length).val 0#u8 4 380
    (by simp [dispatchScalarPrefix, binding.verifier_program.property,
      binding.profile_binding.property, binding.release_binding.property,
      binding.pool.property, binding.deployment_domain.property,
      anchorBytes.property, nullifierBytes.property,
      binding.statement_digest.property, binding.envelope_digest.property,
      binding.proof_account.property, binding.proof_body_digest.property,
      core.num.U32.to_le_bytes, core.num.U64.to_le_bytes])
    (by simp [core.num.U32.to_le_bytes])]
  simp [dispatchGeneratedArray, dispatchGeneratedBytes, dispatchScalarPrefix,
    encodedDigestArray, hanchor, hnullifier, List.append_assoc]
-/

theorem bindingResultArray_header_exact
    (binding : GeneratedBinding)
    (anchorBytes nullifierBytes : Array Std.U8 32#usize)
    (hanchor : atomic_statement.encode_digest_canonical binding.anchor_root =
      .ok anchorBytes)
    (hnullifier : atomic_statement.encode_digest_canonical binding.nullifier =
      .ok nullifierBytes) :
    bindingResultArray dispatchHeaderArray binding anchorBytes nullifierBytes =
      dispatchGeneratedArray binding := by
  apply Subtype.ext
  simp only [bindingResultArray]
  rw [bindingResultBytes_as_writeSlices]
  rw [writeSlices_append_replicate]
  · rw [dispatchChunks_length]
    simp [dispatchGeneratedArray, dispatchGeneratedBytes, dispatchScalarPrefix,
      dispatchChunks, encodedDigestArray, hanchor, hnullifier,
      List.flatten, List.append_assoc]
  · simp

abbrev GeneratedDigestIter :=
  core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.Iter aspis_core.field.M31)

def digestLoopInvariant
    (state : GeneratedDigestIter × Array Std.U8 32#usize) : Prop :=
  state.1.iter.i ≤ state.1.iter.slice.length ∧
    state.1.iter.slice.length = 8 ∧
    state.1.count.val = state.1.iter.i

theorem encode_digest_canonical_loop_total
    (iter : GeneratedDigestIter) (bytes : Array Std.U8 32#usize)
    (hinvariant : digestLoopInvariant (iter, bytes)) :
    atomic_statement.encode_digest_canonical_loop iter bytes
      ⦃ _ => True ⦄ := by
  simp only [atomic_statement.encode_digest_canonical_loop]
  apply Aeneas.Std.loop.spec_decr_nat
    (fun state : GeneratedDigestIter × Array Std.U8 32#usize =>
      state.1.iter.slice.length - state.1.iter.i)
    digestLoopInvariant
    (fun _ => True)
  · rintro ⟨nextIter, nextBytes⟩ hnext
    unfold atomic_statement.encode_digest_canonical_loop.body
    simp only [digestLoopInvariant, Prod.fst, Prod.snd] at hnext
    rcases hnext with ⟨hposition, hlength, hcount⟩
    by_cases hactive : nextIter.iter.i < nextIter.iter.slice.length
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
        hbytesBound, hsliceLength]
      repeat' step
      all_goals simp_all [digestLoopInvariant, Std.lift, Array.to_slice,
        core.num.U32.to_le_bytes]
      all_goals omega
    · simp [core.iter.adapters.enumerate.IteratorEnumerate.next,
        core.slice.iter.IteratorSliceIter.next, hactive]
  · exact hinvariant

theorem encode_digest_canonical_total
    (digest : Array aspis_core.field.M31 8#usize) :
    ∃ output, atomic_statement.encode_digest_canonical digest = .ok output := by
  have hspec : atomic_statement.encode_digest_canonical digest
      ⦃ _ => True ⦄ := by
    unfold atomic_statement.encode_digest_canonical
    simp only [Std.lift, Array.to_slice, bind_tc_ok,
      core.slice.Slice.iter,
      core.iter.traits.iterator.Iterator.enumerate.trait_default,
      core.iter.traits.iterator.Iterator.enumerate.default, bind_tc_ok]
    apply encode_digest_canonical_loop_total
    simp [digestLoopInvariant, digest.property]
  obtain ⟨output, hrun, _⟩ := Aeneas.Std.WP.spec_imp_exists hspec
  exact ⟨output, hrun⟩

/- Replaced by the total-digest proof below. -/
/-
theorem encode_binding_fields_success_exact
    (binding : GeneratedBinding) (output : Array Std.U8 384#usize)
    (hrun :
      pool_v1.verifier_dispatch.encode_binding_fields dispatchHeaderArray binding =
        .ok output) :
    output = dispatchGeneratedArray binding := by
  generalize hanchor :
      atomic_statement.encode_digest_canonical binding.anchor_root =
        anchorResult
  cases anchorResult with
  | fail error =>
      unfold pool_v1.verifier_dispatch.encode_binding_fields at hrun
      simp [hanchor, Std.lift, Array.update, core.array.Array.index_mut,
        core.ops.index.IndexMutSlice, core.slice.index.Slice.index_mut,
        core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
        core.slice.Slice.copy_from_slice, Array.to_slice, Array.from_slice,
        List.setSlice!, Slice.len, Slice.length] at hrun
      simp_lists at hrun
  | div =>
      unfold pool_v1.verifier_dispatch.encode_binding_fields at hrun
      simp [hanchor, Std.lift, Array.update, core.array.Array.index_mut,
        core.ops.index.IndexMutSlice, core.slice.index.Slice.index_mut,
        core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
        core.slice.Slice.copy_from_slice, Array.to_slice, Array.from_slice,
        List.setSlice!, Slice.len, Slice.length] at hrun
      simp_lists at hrun
  | ok anchorBytes =>
      generalize hnullifier :
          atomic_statement.encode_digest_canonical binding.nullifier =
            nullifierResult
      cases nullifierResult with
      | fail error =>
          unfold pool_v1.verifier_dispatch.encode_binding_fields at hrun
          simp [hanchor, hnullifier, Std.lift, Array.update,
            core.array.Array.index_mut, core.ops.index.IndexMutSlice,
            core.slice.index.Slice.index_mut,
            core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
            core.slice.Slice.copy_from_slice, Array.to_slice, Array.from_slice,
            List.setSlice!, Slice.len, Slice.length] at hrun
          simp_lists at hrun
      | div =>
          unfold pool_v1.verifier_dispatch.encode_binding_fields at hrun
          simp [hanchor, hnullifier, Std.lift, Array.update,
            core.array.Array.index_mut, core.ops.index.IndexMutSlice,
            core.slice.index.Slice.index_mut,
            core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
            core.slice.Slice.copy_from_slice, Array.to_slice, Array.from_slice,
            List.setSlice!, Slice.len, Slice.length] at hrun
          simp_lists at hrun
      | ok nullifierBytes =>
          have hrunGeneric := encode_binding_fields_run_generic
            dispatchHeaderArray binding anchorBytes nullifierBytes hanchor hnullifier
          have harrayExact := bindingResultArray_header_exact binding anchorBytes
            nullifierBytes hanchor hnullifier
          exact Result.ok.inj (hrun.symm.trans (hrunGeneric.trans
            (congrArg Result.ok harrayExact)))
-/

theorem encode_binding_fields_success_exact
    (binding : GeneratedBinding) (output : Array Std.U8 384#usize)
    (hrun :
      pool_v1.verifier_dispatch.encode_binding_fields dispatchHeaderArray binding =
        .ok output) :
    output = dispatchGeneratedArray binding := by
  obtain ⟨anchorBytes, hanchor⟩ :=
    encode_digest_canonical_total binding.anchor_root
  obtain ⟨nullifierBytes, hnullifier⟩ :=
    encode_digest_canonical_total binding.nullifier
  have hrunGeneric := encode_binding_fields_run_generic
    dispatchHeaderArray binding anchorBytes nullifierBytes hanchor hnullifier
  have harrayExact := bindingResultArray_header_exact binding anchorBytes
    nullifierBytes hanchor hnullifier
  exact Result.ok.inj (hrun.symm.trans (hrunGeneric.trans
    (congrArg Result.ok harrayExact)))

theorem validation_success_statement_version
    (binding : GeneratedBinding)
    (hrun : pool_v1.verifier_dispatch.validate_verifier_dispatch_binding_v1 binding =
      .ok (.Ok ())) :
    binding.statement_version = 1#u8 := by
  unfold pool_v1.verifier_dispatch.validate_verifier_dispatch_binding_v1 at hrun
  by_cases hversion : binding.statement_version =
      pool_v1.historical_anchor.POOL_V1_HISTORICAL_ANCHOR_VERSION
  · simpa [pool_v1.historical_anchor.POOL_V1_HISTORICAL_ANCHOR_VERSION]
      using hversion
  · have hbne :
        (binding.statement_version !=
          pool_v1.historical_anchor.POOL_V1_HISTORICAL_ANCHOR_VERSION) = true := by
      simp [hversion]
    rw [if_pos hbne] at hrun
    simp at hrun

theorem dispatch_header_generated_bind {T : Type}
    (next : Array Std.U8 384#usize → Result T) :
    (do
      let x ←
        core.array.Array.index_mut (core.ops.index.IndexMutSlice
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8))
          (Array.repeat 384#usize 0#u8)
          { «end» := 4#usize }
      let magic ← lift (Array.to_slice
        pool_v1.verifier_dispatch.POOL_V1_VERIFIER_DISPATCH_RESULT_MAGIC)
      let slice ← core.slice.Slice.copy_from_slice core.marker.CopyU8 x.1 magic
      let x1 ←
        core.array.Array.index_mut (core.ops.index.IndexMutSlice
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) (x.2 slice)
          { start := 8#usize, «end» := 12#usize }
      let code ← lift (core.num.U32.to_le_bytes 1095958529#u32)
      let code ← lift (Array.to_slice code)
      let slice ← core.slice.Slice.copy_from_slice core.marker.CopyU8 x1.1 code
      next (x1.2 slice)) = next dispatchHeaderArray := by
  simp [pool_v1.verifier_dispatch.POOL_V1_VERIFIER_DISPATCH_RESULT_MAGIC,
    Std.lift, core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
    core.slice.Slice.copy_from_slice, Array.to_slice, Array.from_slice,
    Array.repeat, Array.make, List.setSlice!, Slice.len,
    dispatchHeaderArray, core.num.U32.to_le_bytes]
  simp_lists

theorem dispatch_header_fields_bind (binding : GeneratedBinding) :
    (do
      let x ←
        core.array.Array.index_mut (core.ops.index.IndexMutSlice
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8))
          (Array.repeat 384#usize 0#u8) { «end» := 4#usize }
      let magic ← lift (Array.to_slice
        pool_v1.verifier_dispatch.POOL_V1_VERIFIER_DISPATCH_RESULT_MAGIC)
      let slice ← core.slice.Slice.copy_from_slice core.marker.CopyU8 x.1 magic
      let x1 ←
        core.array.Array.index_mut (core.ops.index.IndexMutSlice
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) (x.2 slice)
          { start := 8#usize, «end» := 12#usize }
      let code ← lift (core.num.U32.to_le_bytes 1095958529#u32)
      let code ← lift (Array.to_slice code)
      let slice ← core.slice.Slice.copy_from_slice core.marker.CopyU8 x1.1 code
      let fields ←
        pool_v1.verifier_dispatch.encode_binding_fields (x1.2 slice) binding
      ok (core.result.Result.Ok fields)) =
    (do
      let fields ← pool_v1.verifier_dispatch.encode_binding_fields
        dispatchHeaderArray binding
      ok (core.result.Result.Ok fields) :
        Result (core.result.Result (Array Std.U8 384#usize)
          pool_v1.verifier_dispatch.PoolV1VerifierDispatchFormatError)) := by
  exact dispatch_header_generated_bind
    (next := fun header => do
      let fields ← pool_v1.verifier_dispatch.encode_binding_fields header binding
      ok (core.result.Result.Ok fields))

theorem encode_dispatch_result_source_exact
    (binding : GeneratedBinding) (output : Array Std.U8 384#usize)
    (hrun :
      pool_v1.verifier_dispatch.encode_verifier_dispatch_result_v1
        {
          success_code :=
            pool_v1.verifier_dispatch.POOL_V1_VERIFIER_DISPATCH_SUCCESS_CODE,
          binding
        } = .ok (.Ok output)) :
    bytesOfGenerated output = encodeWireDispatchResult (bindingOfGenerated binding) := by
  unfold pool_v1.verifier_dispatch.encode_verifier_dispatch_result_v1 at hrun
  simp only [pool_v1.verifier_dispatch.POOL_V1_VERIFIER_DISPATCH_SUCCESS_CODE]
    at hrun
  generalize hvalidate :
      pool_v1.verifier_dispatch.validate_verifier_dispatch_binding_v1 binding =
        validation at hrun
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
              pool_v1.verifier_dispatch.validate_verifier_dispatch_binding_v1 binding =
                .ok (.Ok ()) := by simpa using hvalidate
          have hstatement := validation_success_statement_version binding hvalidation
          have hcode :
              (1095958529#u32 != 1095958529#u32) = false := by decide
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
            hcode, Bool.false_eq_true, if_false] at hrun
          rw [dispatch_header_fields_bind] at hrun
          generalize hfields :
              pool_v1.verifier_dispatch.encode_binding_fields dispatchHeaderArray binding =
                fieldsResult at hrun
          cases fieldsResult with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
          | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
          | ok fieldsOutput =>
              have houtput : output = fieldsOutput := by simpa using hrun.symm
              have hfieldsExact :=
                encode_binding_fields_success_exact binding fieldsOutput hfields
              subst output
              rw [hfieldsExact]
              cases htransition : binding.transition_kind <;>
                simp [bytesOfGenerated, byteOfGenerated,
                encodeWireDispatchResult,
                encodeWireDispatchImage, bindingOfGenerated,
                transitionOfGenerated, bytes32List_bytes32OfGenerated,
                encodedDigestArray, u32LE_generated, u64LE_generated,
                asvsMagic, successCode, dispatchVersion, statementVersion,
                sha256Identifier, statementDigestVersion, transitionKindByte,
                dispatchGeneratedArray, dispatchGeneratedBytes,
                generatedTransitionByte, hstatement, htransition]
              all_goals
                simpa [bytesOfGenerated] using
                  (u32LE_generated 1095958529#u32).symm

def bytesOfGeneratedSlice (values : Slice Std.U8) : ByteString :=
  values.val.map byteOfGenerated

def generatedShaPreimage (inputs : Slice (Slice Std.U8)) : ByteString :=
  inputs.val.flatMap bytesOfGeneratedSlice

def GeneratedSha256Matches (sha256 : Sha256)
    (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) : Prop :=
  ∀ inputs digest, hash inputs = .ok digest →
    bytesOfGenerated digest = bytes32List (sha256 (generatedShaPreimage inputs))

def bindingDigestGeneratedInputs
    (dispatchOutput : Array Std.U8 384#usize) : Slice (Slice Std.U8) :=
  Array.to_slice (Array.make 2#usize [
    pool_v1.authorization_receipt_account.POOL_V1_AUTHORIZATION_RECEIPT_BINDING_DIGEST_DOMAIN,
    Array.to_slice dispatchOutput
  ] (by simp))

theorem binding_digest_domain_generated_exact :
    bytesOfGeneratedSlice
        pool_v1.authorization_receipt_account.POOL_V1_AUTHORIZATION_RECEIPT_BINDING_DIGEST_DOMAIN =
      bindingDigestDomain := by
  simp [bytesOfGeneratedSlice,
    pool_v1.authorization_receipt_account.POOL_V1_AUTHORIZATION_RECEIPT_BINDING_DIGEST_DOMAIN,
    bindingDigestDomain, byteOfGenerated, Array.to_slice, Array.make]

theorem binding_digest_preimage_source_exact
    (binding : GeneratedBinding) (dispatchOutput : Array Std.U8 384#usize)
    (hdispatch : bytesOfGenerated dispatchOutput =
      encodeWireDispatchResult (bindingOfGenerated binding)) :
    generatedShaPreimage (bindingDigestGeneratedInputs dispatchOutput) =
      wireBindingDigestPreimage (bindingOfGenerated binding) := by
  have hdispatchList :
      dispatchOutput.val.map byteOfGenerated =
        encodeWireDispatchResult (bindingOfGenerated binding) := by
    exact hdispatch
  simp [generatedShaPreimage, bindingDigestGeneratedInputs,
    bytesOfGeneratedSlice, Array.to_slice, Array.make,
    wireBindingDigestPreimage, hdispatchList]
  simpa [bytesOfGeneratedSlice] using binding_digest_domain_generated_exact

theorem binding_digest_source_exact
    (sha256 : Sha256)
    (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
    (hhash : GeneratedSha256Matches sha256 hash)
    (binding : GeneratedBinding) (output : Array Std.U8 32#usize)
    (hrun :
      pool_v1.authorization_receipt_account.pool_v1_authorization_receipt_binding_digest_v1
        binding hash = .ok (.Ok output)) :
    bytesOfGenerated output = bytes32List
      (sha256 (wireBindingDigestPreimage (bindingOfGenerated binding))) := by
  unfold
    pool_v1.authorization_receipt_account.pool_v1_authorization_receipt_binding_digest_v1
    at hrun
  generalize hdispatch :
      pool_v1.verifier_dispatch.encode_verifier_dispatch_result_v1
        {
          success_code :=
            pool_v1.verifier_dispatch.POOL_V1_VERIFIER_DISPATCH_SUCCESS_CODE,
          binding
        } = dispatchResult at hrun
  cases dispatchResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
  | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
  | ok dispatchResult =>
      cases dispatchResult with
      | Err error =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            pool_v1.authorization_receipt_account.PoolV1AuthorizationReceiptAccountErrorV1.Insts.CoreConvertFromPoolV1VerifierDispatchFormatError.from,
            Bind.bind, Aeneas.Std.bind] at hrun
      | Ok dispatchOutput =>
          have hdispatchExact :=
            encode_dispatch_result_source_exact binding dispatchOutput hdispatch
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at hrun
          simp [Std.lift, Array.to_slice, Array.make,
            Bind.bind, Aeneas.Std.bind] at hrun
          split at hrun
          case h_2 => simp at hrun
          case h_3 => simp at hrun
          case h_1 result digest digestRun =>
            have hdigestRaw := hhash _ digest digestRun
            have hdigestExact :
                bytesOfGenerated digest = bytes32List (sha256
                  (generatedShaPreimage
                    (bindingDigestGeneratedInputs dispatchOutput))) := by
              simpa [bindingDigestGeneratedInputs, Array.to_slice, Array.make]
                using hdigestRaw
            injection hrun with hgeneratedOutput
            injection hgeneratedOutput with hgeneratedArray
            subst output
            rw [hdigestExact,
              binding_digest_preimage_source_exact binding dispatchOutput
                hdispatchExact]

#print axioms byteOfGenerated_toNat
#print axioms bytes32List_bytes32OfGenerated
#print axioms u32LE_generated
#print axioms u64LE_generated
#print axioms transition_discriminant_cast
#print axioms dispatch_header_fields_bind
#print axioms encode_binding_fields_run_generic
#print axioms bindingResultArray_header_exact
#print axioms encode_digest_canonical_loop_total
#print axioms encode_digest_canonical_total
#print axioms encode_binding_fields_success_exact
#print axioms validation_success_statement_version
#print axioms encode_dispatch_result_source_exact
#print axioms binding_digest_domain_generated_exact
#print axioms binding_digest_preimage_source_exact
#print axioms binding_digest_source_exact

end AspisPool.AuthorizationReceiptBindingDigestSourceBridge
