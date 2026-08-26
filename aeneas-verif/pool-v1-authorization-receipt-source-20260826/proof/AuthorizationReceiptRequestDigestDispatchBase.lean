import AuthorizationReceiptRequestDigest.Funs
import AspisFormal.Pool.AuthorizationReceiptAccountWireV1
import Aeneas.Tactic.Step.Step

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisPool.AuthorizationReceiptRequestDigestSourceBridge

open AspisPool.AuthorizationReceiptAccountWireV1
open AuthorizationReceiptRequestDigestGenerated

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

def bytesOfGeneratedSlice (values : Slice Std.U8) : ByteString :=
  values.val.map byteOfGenerated

def generatedShaPreimage (inputs : Slice (Slice Std.U8)) : ByteString :=
  inputs.val.flatMap bytesOfGeneratedSlice

def GeneratedSha256Matches (sha256 : Sha256)
    (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) : Prop :=
  ∀ inputs digest, hash inputs = .ok digest →
    bytesOfGenerated digest = bytes32List (sha256 (generatedShaPreimage inputs))

end AspisPool.AuthorizationReceiptRequestDigestSourceBridge
