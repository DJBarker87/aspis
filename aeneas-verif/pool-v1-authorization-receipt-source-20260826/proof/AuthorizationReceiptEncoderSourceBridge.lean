import AuthorizationReceiptEncoder.Funs
import AspisFormal.Pool.AuthorizationReceiptAccountWireV1
import Aeneas.Tactic.Step.Step

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisPool.AuthorizationReceiptEncoderSourceBridge

open AspisPool.AuthorizationReceiptAccountWireV1
open AuthorizationReceiptEncoderGenerated

abbrev GeneratedBinding :=
  pool_v1.verifier_dispatch.VerifierDispatchBindingV1

abbrev GeneratedReceipt :=
  pool_v1.authorization_receipt.PoolV1AuthorizationReceiptV1

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

def receiptOfGenerated (receipt : GeneratedReceipt) : WireReceipt where
  pdaBump := receipt.pda_bump.val
  verifiedSlot := receipt.verified_slot.val
  binding := bindingOfGenerated receipt.binding

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

@[simp] theorem resultOffset_exact :
    pool_v1.authorization_receipt.RESULT_OFFSET = 16#usize := by
  simp [pool_v1.authorization_receipt.RESULT_OFFSET,
    pool_v1.authorization_receipt.POOL_V1_AUTHORIZATION_RECEIPT_PREFIX_BYTES]

@[simp] theorem digestOffset_exact :
    pool_v1.authorization_receipt.DIGEST_OFFSET = .ok 400#usize := by
  have hspec := Std.Usize.add_spec (x := 16#usize) (y := 384#usize) (by
    scalar_tac)
  obtain ⟨value, valueEquation, valueVal⟩ :=
    Aeneas.Std.WP.spec_imp_exists hspec
  have valueIs400 : value = 400#usize := by
    apply UScalar.eq_of_val_eq
    simpa using valueVal
  unfold pool_v1.authorization_receipt.DIGEST_OFFSET
  rw [resultOffset_exact]
  simp only [pool_v1.verifier_dispatch.POOL_V1_VERIFIER_DISPATCH_RESULT_BYTES]
  rw [valueEquation, valueIs400]

def receiptFixedGeneratedBytes (receipt : GeneratedReceipt) : List Std.U8 :=
  [65#u8, 83#u8, 86#u8, 65#u8, 1#u8, 1#u8, 1#u8, receipt.pda_bump] ++
    (core.num.U64.to_le_bytes receipt.verified_slot).val

def receiptHeaderBytes (receipt : GeneratedReceipt) : List Std.U8 :=
  receiptFixedGeneratedBytes receipt ++ List.replicate 416 0#u8

def receiptHeaderArray (receipt : GeneratedReceipt) : Array Std.U8 432#usize :=
  ⟨receiptHeaderBytes receipt, by
    simp [receiptHeaderBytes, receiptFixedGeneratedBytes,
      core.num.U64.to_le_bytes]⟩

theorem receipt_header_generated_bind {T : Type}
    (receipt : GeneratedReceipt) (next : Array Std.U8 432#usize → Result T) :
    (do
      let output := Array.repeat 432#usize 0#u8
      let (s, index_mut_back) ←
        core.array.Array.index_mut (core.ops.index.IndexMutSlice
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)) output
          { «end» := 4#usize }
      let s1 ← lift (Array.to_slice
        pool_v1.authorization_receipt.POOL_V1_AUTHORIZATION_RECEIPT_MAGIC)
      let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
      let output1 := index_mut_back s2
      let output2 ← Array.update output1 4#usize
        pool_v1.authorization_receipt.POOL_V1_AUTHORIZATION_RECEIPT_VERSION
      let output3 ← Array.update output2 5#usize
        pool_v1.authorization_receipt.POOL_V1_AUTHORIZATION_RECEIPT_HASH_SHA256
      let output4 ← Array.update output3 6#usize
        pool_v1.authorization_receipt.POOL_V1_AUTHORIZATION_RECEIPT_STATUS_VERIFIED
      let output5 ← Array.update output4 7#usize receipt.pda_bump
      let (s3, index_mut_back1) ←
        core.array.Array.index_mut (core.ops.index.IndexMutSlice
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output5
          { start := 8#usize, «end» := 16#usize }
      let a ← lift (core.num.U64.to_le_bytes receipt.verified_slot)
      let s4 ← lift (Array.to_slice a)
      let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3 s4
      next (index_mut_back1 s5)) = next (receiptHeaderArray receipt) := by
  simp [pool_v1.authorization_receipt.POOL_V1_AUTHORIZATION_RECEIPT_MAGIC,
    pool_v1.authorization_receipt.POOL_V1_AUTHORIZATION_RECEIPT_VERSION,
    pool_v1.authorization_receipt.POOL_V1_AUTHORIZATION_RECEIPT_HASH_SHA256,
    pool_v1.authorization_receipt.POOL_V1_AUTHORIZATION_RECEIPT_STATUS_VERIFIED,
    Std.lift, core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
    core.slice.Slice.copy_from_slice, Array.to_slice, Array.from_slice,
    Array.update, Array.repeat, Array.make, List.setSlice!, Slice.len,
    receiptHeaderArray, receiptHeaderBytes, receiptFixedGeneratedBytes,
    core.num.U64.to_le_bytes]
  simp_lists

theorem receipt_header_extracted_bind {T : Type}
    (receipt : GeneratedReceipt) (next : Array Std.U8 432#usize → Result T) :
    (do
      let x ←
        core.array.Array.index_mut (core.ops.index.IndexMutSlice
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8))
          (Array.repeat 432#usize 0#u8) { «end» := 4#usize }
      let s1 ← lift (Array.to_slice
        pool_v1.authorization_receipt.POOL_V1_AUTHORIZATION_RECEIPT_MAGIC)
      let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 x.1 s1
      let output2 ← Array.update (x.2 s2) 4#usize
        pool_v1.authorization_receipt.POOL_V1_AUTHORIZATION_RECEIPT_VERSION
      let output3 ← Array.update output2 5#usize
        pool_v1.authorization_receipt.POOL_V1_AUTHORIZATION_RECEIPT_HASH_SHA256
      let output4 ← Array.update output3 6#usize
        pool_v1.authorization_receipt.POOL_V1_AUTHORIZATION_RECEIPT_STATUS_VERIFIED
      let output5 ← Array.update output4 7#usize receipt.pda_bump
      let x1 ←
        core.array.Array.index_mut (core.ops.index.IndexMutSlice
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output5
          { start := 8#usize, «end» := 16#usize }
      let a ← lift (core.num.U64.to_le_bytes receipt.verified_slot)
      let s4 ← lift (Array.to_slice a)
      let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 x1.1 s4
      next (x1.2 s5)) = next (receiptHeaderArray receipt) := by
  simp [pool_v1.authorization_receipt.POOL_V1_AUTHORIZATION_RECEIPT_MAGIC,
    pool_v1.authorization_receipt.POOL_V1_AUTHORIZATION_RECEIPT_VERSION,
    pool_v1.authorization_receipt.POOL_V1_AUTHORIZATION_RECEIPT_HASH_SHA256,
    pool_v1.authorization_receipt.POOL_V1_AUTHORIZATION_RECEIPT_STATUS_VERIFIED,
    Std.lift, core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
    core.slice.Slice.copy_from_slice, Array.to_slice, Array.from_slice,
    Array.update, Array.repeat, Array.make, List.setSlice!, Slice.len,
    receiptHeaderArray, receiptHeaderBytes, receiptFixedGeneratedBytes,
    core.num.U64.to_le_bytes]
  simp_lists

theorem receipt_header_initial_bind {T : Type}
    (receipt : GeneratedReceipt) (initial : Array Std.U8 432#usize)
    (hzero : initial.val = List.replicate 432 0#u8)
    (next : Array Std.U8 432#usize → Result T) :
    (do
      let x ←
        core.array.Array.index_mut (core.ops.index.IndexMutSlice
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)) initial
          { «end» := 4#usize }
      let s1 ← lift (Array.to_slice
        pool_v1.authorization_receipt.POOL_V1_AUTHORIZATION_RECEIPT_MAGIC)
      let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 x.1 s1
      let output2 ← Array.update (x.2 s2) 4#usize
        pool_v1.authorization_receipt.POOL_V1_AUTHORIZATION_RECEIPT_VERSION
      let output3 ← Array.update output2 5#usize
        pool_v1.authorization_receipt.POOL_V1_AUTHORIZATION_RECEIPT_HASH_SHA256
      let output4 ← Array.update output3 6#usize
        pool_v1.authorization_receipt.POOL_V1_AUTHORIZATION_RECEIPT_STATUS_VERIFIED
      let output5 ← Array.update output4 7#usize receipt.pda_bump
      let x1 ←
        core.array.Array.index_mut (core.ops.index.IndexMutSlice
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output5
          { start := 8#usize, «end» := 16#usize }
      let a ← lift (core.num.U64.to_le_bytes receipt.verified_slot)
      let s4 ← lift (Array.to_slice a)
      let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 x1.1 s4
      next (x1.2 s5)) = next (receiptHeaderArray receipt) := by
  have hinitial : initial = Array.repeat 432#usize 0#u8 := by
    apply Subtype.ext
    simpa [Array.repeat, Array.make] using hzero
  subst initial
  exact receipt_header_extracted_bind receipt next

def receiptPrefixGeneratedBytes (receipt : GeneratedReceipt)
    (dispatchOutput : Array Std.U8 384#usize) : List Std.U8 :=
  receiptFixedGeneratedBytes receipt ++ dispatchOutput.val

def receiptPrefixGeneratedArray (receipt : GeneratedReceipt)
    (dispatchOutput : Array Std.U8 384#usize) : Array Std.U8 400#usize :=
  ⟨receiptPrefixGeneratedBytes receipt dispatchOutput, by
    simp [receiptPrefixGeneratedBytes, receiptFixedGeneratedBytes,
      core.num.U64.to_le_bytes,
      dispatchOutput.property]⟩

def receiptPrefixPaddedArray (receipt : GeneratedReceipt)
    (dispatchOutput : Array Std.U8 384#usize) : Array Std.U8 432#usize :=
  ⟨receiptPrefixGeneratedBytes receipt dispatchOutput ++ List.replicate 32 0#u8,
    by simp [receiptPrefixGeneratedBytes, receiptFixedGeneratedBytes,
      core.num.U64.to_le_bytes,
      dispatchOutput.property]⟩

theorem receipt_header_setSlice_dispatch
    (receipt : GeneratedReceipt) (dispatchOutput : Array Std.U8 384#usize) :
    (receiptHeaderArray receipt).val.setSlice! 16 dispatchOutput.val =
      (receiptPrefixPaddedArray receipt dispatchOutput).val := by
  change
    (receiptFixedGeneratedBytes receipt ++ List.replicate 416 0#u8).setSlice!
        16 dispatchOutput.val =
      (receiptFixedGeneratedBytes receipt ++ dispatchOutput.val) ++
        List.replicate 32 0#u8
  rw [setSlice_append_replicate_at
    (receiptFixedGeneratedBytes receipt) dispatchOutput.val 0#u8 416 16
    (by simp [receiptFixedGeneratedBytes, core.num.U64.to_le_bytes])
    (by simp [dispatchOutput.property])]
  simp [dispatchOutput.property]

theorem receipt_prefix_padded_take
    (receipt : GeneratedReceipt) (dispatchOutput : Array Std.U8 384#usize) :
    List.take 400 (receiptPrefixPaddedArray receipt dispatchOutput).val =
      (receiptPrefixGeneratedArray receipt dispatchOutput).val := by
  have hprefixLength :
      (receiptPrefixGeneratedBytes receipt dispatchOutput).length = 400 := by
    simp [receiptPrefixGeneratedBytes, receiptFixedGeneratedBytes,
      dispatchOutput.property, core.num.U64.to_le_bytes]
  change
    List.take 400
        (receiptPrefixGeneratedBytes receipt dispatchOutput ++
          List.replicate 32 0#u8) =
      receiptPrefixGeneratedBytes receipt dispatchOutput
  rw [← hprefixLength]
  exact List.take_append_length

theorem take392_append_exact
    (left middle suffix : List Std.U8)
    (hleft : left.length = 8) (hmiddle : middle.length = 384) :
    List.take 392 (left ++ (middle ++ suffix)) = left ++ middle := by
  have hprefix : (left ++ middle).length = 392 := by
    simp [hleft, hmiddle]
  rw [← List.append_assoc, ← hprefix]
  exact List.take_append_length

theorem receipt_raw_tail_exact
    (receipt : GeneratedReceipt) (dispatchOutput : Array Std.U8 384#usize)
    (suffix : List Std.U8) :
    List.take 392
        (List.map (fun byte => (⟨byte⟩ : Std.U8))
            receipt.verified_slot.bv.toLEBytes ++
          (dispatchOutput.val ++ suffix)) =
      List.map (fun byte => (⟨byte⟩ : Std.U8))
          receipt.verified_slot.bv.toLEBytes ++ dispatchOutput.val := by
  let slotBytes : List Std.U8 :=
    List.map (fun byte => (⟨byte⟩ : Std.U8))
      receipt.verified_slot.bv.toLEBytes
  have hslot :
      slotBytes.length = 8 := by
    simp [slotBytes, BitVec.toLEBytes]
  have hdispatch : dispatchOutput.val.length = 384 := by
    simpa using dispatchOutput.property
  change
    List.take 392
        (slotBytes ++ (dispatchOutput.val ++ suffix)) =
      slotBytes ++ dispatchOutput.val
  exact take392_append_exact slotBytes dispatchOutput.val suffix hslot hdispatch

theorem receipt_dispatch_generated_bind {T : Type}
    (receipt : GeneratedReceipt) (dispatchOutput : Array Std.U8 384#usize)
    (next : Array Std.U8 432#usize → Slice Std.U8 → Result T) :
    (do
      let i ← pool_v1.authorization_receipt.DIGEST_OFFSET
      let (s6, index_mut_back2) ←
        core.array.Array.index_mut (core.ops.index.IndexMutSlice
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8))
          (receiptHeaderArray receipt)
          { start := pool_v1.authorization_receipt.RESULT_OFFSET, «end» := i }
      let s7 ← lift (Array.to_slice dispatchOutput)
      let s8 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s6 s7
      let output7 := index_mut_back2 s8
      let s9 ←
        core.array.Array.index (core.ops.index.IndexSlice
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)) output7
          { «end» := i }
      next output7 s9) =
      next (receiptPrefixPaddedArray receipt dispatchOutput)
        (Array.to_slice (receiptPrefixGeneratedArray receipt dispatchOutput)) := by
  rw [digestOffset_exact]
  simp [resultOffset_exact, Std.lift, core.array.Array.index_mut,
    core.ops.index.IndexMutSlice, core.slice.index.Slice.index_mut,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
    core.slice.index.SliceIndexRangeToUsizeSlice.index,
    core.slice.Slice.copy_from_slice, Array.to_slice, Array.from_slice,
    receipt_header_setSlice_dispatch, receipt_prefix_padded_take,
    Slice.len, dispatchOutput.property]
  split <;> simp_all [receipt_header_setSlice_dispatch,
    receipt_prefix_padded_take]
  all_goals try scalar_tac

def receiptDigestGeneratedInputs (receipt : GeneratedReceipt)
    (dispatchOutput : Array Std.U8 384#usize) : Slice (Slice Std.U8) :=
  Array.to_slice (Array.make 2#usize [
    pool_v1.authorization_receipt.POOL_V1_AUTHORIZATION_RECEIPT_DIGEST_DOMAIN,
    Array.to_slice (receiptPrefixGeneratedArray receipt dispatchOutput)
  ] (by simp))

theorem receipt_digest_generated_inputs
    (receipt : GeneratedReceipt) (dispatchOutput : Array Std.U8 384#usize)
    (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) :
    pool_v1.authorization_receipt.receipt_digest_v1
        (Array.to_slice (receiptPrefixGeneratedArray receipt dispatchOutput)) hash =
      hash (receiptDigestGeneratedInputs receipt dispatchOutput) := by
  simp [pool_v1.authorization_receipt.receipt_digest_v1,
    receiptDigestGeneratedInputs, Std.lift]

theorem receipt_digest_domain_generated_exact :
    bytesOfGeneratedSlice
        pool_v1.authorization_receipt.POOL_V1_AUTHORIZATION_RECEIPT_DIGEST_DOMAIN =
      receiptDigestDomain := by
  simp [bytesOfGeneratedSlice,
    pool_v1.authorization_receipt.POOL_V1_AUTHORIZATION_RECEIPT_DIGEST_DOMAIN,
    receiptDigestDomain, byteOfGenerated, Array.to_slice, Array.make]

theorem receipt_prefix_source_exact
    (receipt : GeneratedReceipt) (dispatchOutput : Array Std.U8 384#usize)
    (hdispatch : bytesOfGenerated dispatchOutput =
      encodeWireDispatchResult (bindingOfGenerated receipt.binding)) :
    bytesOfGenerated (receiptPrefixGeneratedArray receipt dispatchOutput) =
      wireReceiptPrefixResult (receiptOfGenerated receipt) := by
  have hslot := (u64LE_generated receipt.verified_slot).symm
  unfold bytesOfGenerated at hslot hdispatch
  simp [bytesOfGenerated, receiptPrefixGeneratedArray,
    receiptPrefixGeneratedBytes, receiptFixedGeneratedBytes,
    wireReceiptPrefixResult, receiptOfGenerated, asvaMagic,
    byteOfGenerated, List.map_append]
  rw [hslot, hdispatch]

theorem receipt_digest_preimage_source_exact
    (receipt : GeneratedReceipt) (dispatchOutput : Array Std.U8 384#usize)
    (hdispatch : bytesOfGenerated dispatchOutput =
      encodeWireDispatchResult (bindingOfGenerated receipt.binding)) :
    generatedShaPreimage (receiptDigestGeneratedInputs receipt dispatchOutput) =
      receiptDigestDomain ++
        wireReceiptPrefixResult (receiptOfGenerated receipt) := by
  simp [generatedShaPreimage, receiptDigestGeneratedInputs,
    bytesOfGeneratedSlice, Array.to_slice, Array.make,
    ← receipt_prefix_source_exact receipt dispatchOutput hdispatch,
    bytesOfGenerated]
  simpa [bytesOfGeneratedSlice] using receipt_digest_domain_generated_exact

def receiptGeneratedBytes (receipt : GeneratedReceipt)
    (dispatchOutput : Array Std.U8 384#usize)
    (digest : Array Std.U8 32#usize) : List Std.U8 :=
  receiptPrefixGeneratedBytes receipt dispatchOutput ++ digest.val

def receiptGeneratedArray (receipt : GeneratedReceipt)
    (dispatchOutput : Array Std.U8 384#usize)
    (digest : Array Std.U8 32#usize) : Array Std.U8 432#usize :=
  ⟨receiptGeneratedBytes receipt dispatchOutput digest, by
    simp [receiptGeneratedBytes, receiptPrefixGeneratedBytes,
      receiptFixedGeneratedBytes, dispatchOutput.property, digest.property,
      core.num.U64.to_le_bytes]⟩

theorem receipt_padded_setSlice_digest
    (receipt : GeneratedReceipt) (dispatchOutput : Array Std.U8 384#usize)
    (digest : Array Std.U8 32#usize) :
    (receiptPrefixPaddedArray receipt dispatchOutput).val.setSlice! 400 digest.val =
      (receiptGeneratedArray receipt dispatchOutput digest).val := by
  change
    (receiptPrefixGeneratedBytes receipt dispatchOutput ++
      List.replicate 32 0#u8).setSlice! 400 digest.val =
      receiptPrefixGeneratedBytes receipt dispatchOutput ++ digest.val
  rw [setSlice_append_replicate_at
    (receiptPrefixGeneratedBytes receipt dispatchOutput) digest.val 0#u8 32 400
    (by simp [receiptPrefixGeneratedBytes, receiptFixedGeneratedBytes,
      dispatchOutput.property, core.num.U64.to_le_bytes])
    (by simp [digest.property])]
  simp [digest.property]

theorem receipt_digest_write_generated_bind {T : Type}
    (receipt : GeneratedReceipt) (dispatchOutput : Array Std.U8 384#usize)
    (digest : Array Std.U8 32#usize)
    (next : Array Std.U8 432#usize → Result T) :
    (do
      let (s10, index_mut_back3) ←
        core.array.Array.index_mut (core.ops.index.IndexMutSlice
          (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8))
          (receiptPrefixPaddedArray receipt dispatchOutput) { start := 400#usize }
      let s11 ← lift (Array.to_slice digest)
      let s12 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s10 s11
      next (index_mut_back3 s12)) =
      next (receiptGeneratedArray receipt dispatchOutput digest) := by
  simp [Std.lift, core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut,
    core.slice.Slice.copy_from_slice, Array.to_slice, Array.from_slice,
    receipt_padded_setSlice_digest, Slice.len, digest.property]

theorem receipt_generated_array_source_exact
    (sha256 : Sha256) (receipt : GeneratedReceipt)
    (dispatchOutput : Array Std.U8 384#usize)
    (digest : Array Std.U8 32#usize)
    (hdispatch : bytesOfGenerated dispatchOutput =
      encodeWireDispatchResult (bindingOfGenerated receipt.binding))
    (hdigest : bytesOfGenerated digest = bytes32List (sha256
      (generatedShaPreimage
        (receiptDigestGeneratedInputs receipt dispatchOutput)))) :
    bytesOfGenerated (receiptGeneratedArray receipt dispatchOutput digest) =
      encodeWireReceipt sha256 (receiptOfGenerated receipt) := by
  have hprefix := receipt_prefix_source_exact receipt dispatchOutput hdispatch
  have hpreimage :=
    receipt_digest_preimage_source_exact receipt dispatchOutput hdispatch
  unfold bytesOfGenerated at hprefix hdigest
  change List.map byteOfGenerated
      (receiptPrefixGeneratedBytes receipt dispatchOutput) =
    wireReceiptPrefixResult (receiptOfGenerated receipt) at hprefix
  simp [bytesOfGenerated, receiptGeneratedArray, receiptGeneratedBytes,
    encodeWireReceipt, List.map_append]
  rw [hprefix, hdigest, hpreimage]

theorem encode_receipt_source_exact
    (sha256 : Sha256)
    (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
    (hhash : GeneratedSha256Matches sha256 hash)
    (receipt : GeneratedReceipt) (output : Array Std.U8 432#usize)
    (hrun :
      pool_v1.authorization_receipt.encode_pool_v1_authorization_receipt_v1
        receipt hash = .ok (.Ok output)) :
    bytesOfGenerated output = encodeWireReceipt sha256 (receiptOfGenerated receipt) := by
  unfold pool_v1.authorization_receipt.encode_pool_v1_authorization_receipt_v1 at hrun
  generalize hdispatch :
      pool_v1.verifier_dispatch.encode_verifier_dispatch_result_v1
        {
          success_code :=
            pool_v1.verifier_dispatch.POOL_V1_VERIFIER_DISPATCH_SUCCESS_CODE,
          binding := receipt.binding
        } = dispatchResult at hrun
  cases dispatchResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
  | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
  | ok dispatchResult =>
      cases dispatchResult with
      | Err error =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            pool_v1.authorization_receipt.PoolV1AuthorizationReceiptError.Insts.CoreConvertFromPoolV1VerifierDispatchFormatError.from,
            Bind.bind, Aeneas.Std.bind] at hrun
      | Ok dispatchOutput =>
          have hdispatchExact :=
            encode_dispatch_result_source_exact receipt.binding dispatchOutput hdispatch
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at hrun
          simp [pool_v1.authorization_receipt.POOL_V1_AUTHORIZATION_RECEIPT_MAGIC,
            pool_v1.authorization_receipt.POOL_V1_AUTHORIZATION_RECEIPT_VERSION,
            pool_v1.authorization_receipt.POOL_V1_AUTHORIZATION_RECEIPT_HASH_SHA256,
            pool_v1.authorization_receipt.POOL_V1_AUTHORIZATION_RECEIPT_STATUS_VERIFIED,
            digestOffset_exact, resultOffset_exact,
            pool_v1.authorization_receipt.receipt_digest_v1,
            pool_v1.authorization_receipt.POOL_V1_AUTHORIZATION_RECEIPT_DIGEST_DOMAIN,
            Std.lift, core.array.Array.index_mut, core.ops.index.IndexMutSlice,
            core.slice.index.Slice.index_mut,
            core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
            core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
            core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut,
            core.slice.index.SliceIndexRangeToUsizeSlice.index,
            core.slice.Slice.copy_from_slice, Array.to_slice, Array.from_slice,
            Array.update, Array.repeat, Array.make, List.setSlice!, Slice.len,
            core.num.U64.to_le_bytes, Bind.bind, Aeneas.Std.bind,
            take392_append_exact, BitVec.toLEBytes] at hrun
          split at hrun
          case h_2 => simp at hrun
          case h_3 => simp at hrun
          case h_1 result digest digestRun =>
            have hdigestRaw := hhash _ digest digestRun
            have hdispatchLength : dispatchOutput.val.length = 384 := by
              simpa using dispatchOutput.property
            have hdigestLength : digest.val.length = 32 := by
              simpa using digest.property
            have htakeDispatch : List.take 384 dispatchOutput.val =
                dispatchOutput.val := by
              exact (List.take_eq_self_iff dispatchOutput.val).2
                hdispatchLength.le
            have htakeDigest : List.take 32 digest.val = digest.val := by
              exact (List.take_eq_self_iff digest.val).2 hdigestLength.le
            simp only [htakeDispatch, htakeDigest] at digestRun hrun
            simp only [htakeDispatch] at hdigestRaw
            have hdigestExact :
                bytesOfGenerated digest = bytes32List (sha256
                  (generatedShaPreimage
                    (receiptDigestGeneratedInputs receipt dispatchOutput))) := by
              simpa [receiptDigestGeneratedInputs, receiptPrefixGeneratedArray,
                receiptPrefixGeneratedBytes, receiptFixedGeneratedBytes,
                Array.to_slice, Array.make, core.num.U64.to_le_bytes,
                BitVec.toLEBytes,
                pool_v1.authorization_receipt.POOL_V1_AUTHORIZATION_RECEIPT_DIGEST_DOMAIN]
                using hdigestRaw
            injection hrun with hgeneratedOutput
            injection hgeneratedOutput with hgeneratedArray
            subst output
            simpa [receiptGeneratedArray, receiptGeneratedBytes,
              receiptPrefixGeneratedBytes, receiptFixedGeneratedBytes,
              core.num.U64.to_le_bytes, BitVec.toLEBytes] using
              (receipt_generated_array_source_exact sha256 receipt
                dispatchOutput digest hdispatchExact hdigestExact)

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
#print axioms resultOffset_exact
#print axioms digestOffset_exact
#print axioms receipt_header_generated_bind
#print axioms receipt_header_extracted_bind
#print axioms receipt_header_initial_bind
#print axioms receipt_header_setSlice_dispatch
#print axioms receipt_prefix_padded_take
#print axioms take392_append_exact
#print axioms receipt_raw_tail_exact
#print axioms receipt_dispatch_generated_bind
#print axioms receipt_digest_generated_inputs
#print axioms receipt_digest_domain_generated_exact
#print axioms receipt_prefix_source_exact
#print axioms receipt_digest_preimage_source_exact
#print axioms receipt_padded_setSlice_digest
#print axioms receipt_digest_write_generated_bind
#print axioms receipt_generated_array_source_exact
#print axioms encode_receipt_source_exact

end AspisPool.AuthorizationReceiptEncoderSourceBridge
