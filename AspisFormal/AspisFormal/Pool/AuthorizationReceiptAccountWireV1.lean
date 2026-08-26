import AspisFormal.Pool.AuthorizationReceiptAccountV1

/-!
# Exact ASRA/ASVA/ASVQ byte preimages

This leaf closes the mathematical part of the source-correspondence boundary
for the committed Pool V1 verifier-owned receipt account.  It spells out the
exact successful Rust encodings used by `verifier_dispatch.rs`,
`authorization_receipt.rs`, and `authorization_receipt_account.rs`:

* the fixed 384-byte `ASVS` binding and variable `ASVQ` request;
* all four literal SHA-256 domain prefixes and their concatenated preimages;
* the 432-byte nested `ASVA` receipt;
* pending and verified 688-byte ASRA prefix/body images and 720-byte accounts;
* the only three changed finalization regions; and
* the ordered PDA seed prefix and three dynamic 32-byte seeds.

`sha256` remains an arbitrary function from one concatenated byte string to
32 bytes.  No collision, preimage, or random-oracle property is assumed.  A
finite byte-vector packing equivalence lets the earlier lifecycle module's
abstract `Nat` identifiers carry exact 32-byte values without selecting an
endianness for those identifiers.  All *wire* integer encodings below are the
literal little-endian formula used by Rust.

The final `AeneasSourceEquality` predicate is not used by any theorem.  It is
the exact remaining toolchain statement: successful results of the named
production Rust functions equal the kernel-checked encoders in this file.
-/

set_option autoImplicit false

namespace AspisPool.AuthorizationReceiptAccountWireV1

open AspisPool.AuthorizationReceiptV1

abbrev ByteString := List UInt8
abbrev Bytes32 := Fin 32 → UInt8
abbrev Sha256 := ByteString → Bytes32

noncomputable section

def bytes32List (bytes : Bytes32) : ByteString := List.ofFn bytes

theorem bytes32List_length (bytes : Bytes32) : (bytes32List bytes).length = 32 := by
  simp [bytes32List]

def zero32 : Bytes32 := fun _ => 0

def packedBound : Nat := Fintype.card Bytes32

noncomputable def bytes32Equiv : Bytes32 ≃ Fin packedBound :=
  Fintype.equivFin Bytes32

/-- Abstract lifecycle identifier for one exact 32-byte Rust value. -/
noncomputable def pack32 (bytes : Bytes32) : Nat := (bytes32Equiv bytes).val

/-- Recover the byte vector represented by a lifecycle identifier.  Values
outside the exact 256-bit image are mapped to zero; all identifiers constructed
by this module are in range. -/
noncomputable def unpack32 (value : Nat) : Bytes32 :=
  if inRange : value < packedBound then bytes32Equiv.symm ⟨value, inRange⟩ else zero32

@[simp] theorem unpack32_pack32 (bytes : Bytes32) : unpack32 (pack32 bytes) = bytes := by
  unfold unpack32 pack32
  rw [dif_pos (bytes32Equiv bytes).isLt]
  exact bytes32Equiv.symm_apply_apply bytes

def block32 (value : Nat) : ByteString := bytes32List (unpack32 value)

@[simp] theorem block32_pack32 (bytes : Bytes32) : block32 (pack32 bytes) = bytes32List bytes := by
  simp [block32]

def littleEndianByte (value place : Nat) : UInt8 :=
  UInt8.ofNat ((value / 256 ^ place) % 256)

def u32LE (value : Nat) : ByteString :=
  [littleEndianByte value 0, littleEndianByte value 1,
    littleEndianByte value 2, littleEndianByte value 3]

def u64LE (value : Nat) : ByteString :=
  [littleEndianByte value 0, littleEndianByte value 1,
    littleEndianByte value 2, littleEndianByte value 3,
    littleEndianByte value 4, littleEndianByte value 5,
    littleEndianByte value 6, littleEndianByte value 7]

theorem u32LE_length (value : Nat) : (u32LE value).length = 4 := rfl
theorem u64LE_length (value : Nat) : (u64LE value).length = 8 := rfl

def transitionKindByte : TransitionKind → UInt8
  | .privateTransfer => 1
  | .withdrawal => 2

def asraMagic : ByteString := [0x41, 0x53, 0x52, 0x41]
def asvaMagic : ByteString := [0x41, 0x53, 0x56, 0x41]
def asvqMagic : ByteString := [0x41, 0x53, 0x56, 0x51]
def asvsMagic : ByteString := [0x41, 0x53, 0x56, 0x53]

def accountDigestDomain : ByteString :=
  [97, 115, 112, 105, 115, 47, 112, 111, 111, 108, 45, 118, 49, 47,
    97, 117, 116, 104, 111, 114, 105, 122, 97, 116, 105, 111, 110, 45,
    114, 101, 99, 101, 105, 112, 116, 45, 97, 99, 99, 111, 117, 110,
    116, 47, 118, 49]

def bindingDigestDomain : ByteString :=
  [97, 115, 112, 105, 115, 47, 112, 111, 111, 108, 45, 118, 49, 47,
    97, 117, 116, 104, 111, 114, 105, 122, 97, 116, 105, 111, 110, 45,
    114, 101, 99, 101, 105, 112, 116, 45, 98, 105, 110, 100, 105, 110,
    103, 47, 118, 49]

def requestDigestDomain : ByteString :=
  [97, 115, 112, 105, 115, 47, 112, 111, 111, 108, 45, 118, 49, 47,
    97, 117, 116, 104, 111, 114, 105, 122, 97, 116, 105, 111, 110, 45,
    114, 101, 99, 101, 105, 112, 116, 45, 114, 101, 113, 117, 101, 115,
    116, 47, 118, 49]

def receiptDigestDomain : ByteString :=
  [97, 115, 112, 105, 115, 47, 112, 111, 111, 108, 45, 118, 49, 47,
    97, 117, 116, 104, 111, 114, 105, 122, 97, 116, 105, 111, 110, 45,
    114, 101, 99, 101, 105, 112, 116, 47, 118, 49]

def pdaStaticSeed : ByteString :=
  [97, 115, 112, 105, 115, 45, 118, 101, 114, 105, 102, 121, 45, 114,
    101, 99, 101, 105, 112, 116, 45, 118, 49]

def dispatchVersion : UInt8 := 1
def statementVersion : UInt8 := 1
def sha256Identifier : UInt8 := 1
def statementDigestVersion : UInt8 := 1
def verifyCode : Nat := 1
def successCode : Nat := 0x4153_0001

/-! ## Exact Rust binding inputs -/

structure WireBinding where
  transitionKind : TransitionKind
  verifierProgram : Bytes32
  profileBinding : Bytes32
  releaseBinding : Bytes32
  pool : Bytes32
  deploymentDomain : Bytes32
  anchorSequence : Nat
  anchorRootCanonical : Bytes32
  nullifierCanonical : Bytes32
  statementDigest : Bytes32
  envelopeDigest : Bytes32
  proofAccount : Bytes32
  proofBodyDigest : Bytes32
  proofBodyLength : Nat
  statementPayloadLength : Nat
  deriving DecidableEq

structure WireRequest where
  binding : WireBinding
  statementPayload : ByteString
  deriving DecidableEq

structure WireReceipt where
  pdaBump : Nat
  verifiedSlot : Nat
  binding : WireBinding
  deriving DecidableEq

noncomputable def WireBinding.toTyped (binding : WireBinding) : Binding where
  statementVersion := 1
  transitionKind := binding.transitionKind
  verifierProgram := pack32 binding.verifierProgram
  profileBinding := pack32 binding.profileBinding
  releaseBinding := pack32 binding.releaseBinding
  pool := pack32 binding.pool
  deploymentDomain := pack32 binding.deploymentDomain
  anchorSequence := binding.anchorSequence
  anchorRoot := pack32 binding.anchorRootCanonical
  nullifier := pack32 binding.nullifierCanonical
  statementDigest := pack32 binding.statementDigest
  envelopeDigest := pack32 binding.envelopeDigest
  proofAccount := pack32 binding.proofAccount
  proofBodyDigest := pack32 binding.proofBodyDigest
  proofBodyLength := binding.proofBodyLength
  statementPayloadLength := binding.statementPayloadLength

noncomputable def WireRequest.toTyped (request : WireRequest) :
    AspisPool.AuthorizationReceiptAccountV1.Request where
  binding := request.binding.toTyped
  statementPayload := request.statementPayload

noncomputable def WireReceipt.toTyped (receipt : WireReceipt) : Receipt where
  pdaBump := receipt.pdaBump
  verifiedSlot := receipt.verifiedSlot
  binding := receipt.binding.toTyped

/-! ## Dispatch encoders and SHA preimages -/

def encodeTypedDispatchImage (magic : ByteString) (code : Nat)
    (binding : Binding) : ByteString :=
  magic ++
    [dispatchVersion, UInt8.ofNat binding.statementVersion,
      transitionKindByte binding.transitionKind, sha256Identifier] ++
    u32LE code ++ [statementDigestVersion, 0, 0, 0] ++
    block32 binding.verifierProgram ++ block32 binding.profileBinding ++
    block32 binding.releaseBinding ++ block32 binding.pool ++
    block32 binding.deploymentDomain ++ u64LE binding.anchorSequence ++
    block32 binding.anchorRoot ++ block32 binding.nullifier ++
    block32 binding.statementDigest ++ block32 binding.envelopeDigest ++
    block32 binding.proofAccount ++ block32 binding.proofBodyDigest ++
    u32LE binding.proofBodyLength ++ u32LE binding.statementPayloadLength

def encodeWireDispatchImage (magic : ByteString) (code : Nat)
    (binding : WireBinding) : ByteString :=
  magic ++
    [dispatchVersion, statementVersion, transitionKindByte binding.transitionKind,
      sha256Identifier] ++
    u32LE code ++ [statementDigestVersion, 0, 0, 0] ++
    bytes32List binding.verifierProgram ++ bytes32List binding.profileBinding ++
    bytes32List binding.releaseBinding ++ bytes32List binding.pool ++
    bytes32List binding.deploymentDomain ++ u64LE binding.anchorSequence ++
    bytes32List binding.anchorRootCanonical ++ bytes32List binding.nullifierCanonical ++
    bytes32List binding.statementDigest ++ bytes32List binding.envelopeDigest ++
    bytes32List binding.proofAccount ++ bytes32List binding.proofBodyDigest ++
    u32LE binding.proofBodyLength ++ u32LE binding.statementPayloadLength

def encodeTypedDispatchResult (binding : Binding) : ByteString :=
  encodeTypedDispatchImage asvsMagic successCode binding

def encodeWireDispatchResult (binding : WireBinding) : ByteString :=
  encodeWireDispatchImage asvsMagic successCode binding

def encodeTypedDispatchRequest
    (request : AspisPool.AuthorizationReceiptAccountV1.Request) : ByteString :=
  encodeTypedDispatchImage asvqMagic verifyCode request.binding ++ request.statementPayload

def encodeWireDispatchRequest (request : WireRequest) : ByteString :=
  encodeWireDispatchImage asvqMagic verifyCode request.binding ++ request.statementPayload

def typedBindingDigestPreimage (binding : Binding) : ByteString :=
  bindingDigestDomain ++ encodeTypedDispatchResult binding

def wireBindingDigestPreimage (binding : WireBinding) : ByteString :=
  bindingDigestDomain ++ encodeWireDispatchResult binding

def typedRequestDigestPreimage
    (request : AspisPool.AuthorizationReceiptAccountV1.Request) : ByteString :=
  requestDigestDomain ++ encodeTypedDispatchRequest request

def wireRequestDigestPreimage (request : WireRequest) : ByteString :=
  requestDigestDomain ++ encodeWireDispatchRequest request

theorem encode_typed_dispatch_image_of_wire (magic : ByteString) (code : Nat)
    (binding : WireBinding) :
    encodeTypedDispatchImage magic code binding.toTyped =
      encodeWireDispatchImage magic code binding := by
  simp [encodeTypedDispatchImage, encodeWireDispatchImage, WireBinding.toTyped,
    statementVersion]

theorem encode_typed_dispatch_result_of_wire (binding : WireBinding) :
    encodeTypedDispatchResult binding.toTyped = encodeWireDispatchResult binding := by
  exact encode_typed_dispatch_image_of_wire asvsMagic successCode binding

theorem encode_typed_dispatch_request_of_wire (request : WireRequest) :
    encodeTypedDispatchRequest request.toTyped = encodeWireDispatchRequest request := by
  simp [encodeTypedDispatchRequest, encodeWireDispatchRequest,
    WireRequest.toTyped, encode_typed_dispatch_image_of_wire]

theorem typed_binding_preimage_of_wire (binding : WireBinding) :
    typedBindingDigestPreimage binding.toTyped = wireBindingDigestPreimage binding := by
  simp [typedBindingDigestPreimage, wireBindingDigestPreimage,
    encode_typed_dispatch_result_of_wire]

theorem typed_request_preimage_of_wire (request : WireRequest) :
    typedRequestDigestPreimage request.toTyped = wireRequestDigestPreimage request := by
  simp [typedRequestDigestPreimage, wireRequestDigestPreimage,
    encode_typed_dispatch_request_of_wire]

theorem exact_dispatch_result_length (binding : WireBinding) :
    (encodeWireDispatchResult binding).length = 384 := by
  simp [encodeWireDispatchResult, encodeWireDispatchImage, bytes32List_length,
    u32LE_length, u64LE_length, asvsMagic]

theorem exact_dispatch_request_length (request : WireRequest) :
    (encodeWireDispatchRequest request).length = 384 + request.statementPayload.length := by
  simp [encodeWireDispatchRequest, encodeWireDispatchImage, bytes32List_length,
    u32LE_length, u64LE_length, asvqMagic]
  omega

/-- Shared field boundaries of the 384-byte `ASVS` image and `ASVQ` prefix.
The variable `ASVQ` statement payload begins at the final boundary. -/
theorem exact_dispatch_offsets :
    [0, 4, 5, 6, 7, 8, 12, 13, 16, 48, 80, 112, 144, 176, 184,
      216, 248, 280, 312, 344, 376, 380, 384] =
      [0,
        asvsMagic.length,
        asvsMagic.length + 1,
        asvsMagic.length + 2,
        asvsMagic.length + 3,
        asvsMagic.length + 4,
        asvsMagic.length + 4 + 4,
        asvsMagic.length + 4 + 4 + 1,
        asvsMagic.length + 4 + 4 + 4,
        asvsMagic.length + 4 + 4 + 4 + 32,
        asvsMagic.length + 4 + 4 + 4 + 64,
        asvsMagic.length + 4 + 4 + 4 + 96,
        asvsMagic.length + 4 + 4 + 4 + 128,
        asvsMagic.length + 4 + 4 + 4 + 160,
        asvsMagic.length + 4 + 4 + 4 + 160 + 8,
        asvsMagic.length + 4 + 4 + 4 + 160 + 8 + 32,
        asvsMagic.length + 4 + 4 + 4 + 160 + 8 + 64,
        asvsMagic.length + 4 + 4 + 4 + 160 + 8 + 96,
        asvsMagic.length + 4 + 4 + 4 + 160 + 8 + 128,
        asvsMagic.length + 4 + 4 + 4 + 160 + 8 + 160,
        asvsMagic.length + 4 + 4 + 4 + 160 + 8 + 192,
        asvsMagic.length + 4 + 4 + 4 + 160 + 8 + 192 + 4,
        asvsMagic.length + 4 + 4 + 4 + 160 + 8 + 192 + 8] := by
  decide

theorem exact_digest_domain_lengths :
    accountDigestDomain.length = 46 ∧
      bindingDigestDomain.length = 46 ∧
      requestDigestDomain.length = 46 ∧
      receiptDigestDomain.length = 38 := by
  decide

/-! ## Nested ASVA and ASRA encoders -/

def typedReceiptPrefixResult (receipt : Receipt) : ByteString :=
  asvaMagic ++ [1, 1, 1, UInt8.ofNat receipt.pdaBump] ++
    u64LE receipt.verifiedSlot ++ encodeTypedDispatchResult receipt.binding

def wireReceiptPrefixResult (receipt : WireReceipt) : ByteString :=
  asvaMagic ++ [1, 1, 1, UInt8.ofNat receipt.pdaBump] ++
    u64LE receipt.verifiedSlot ++ encodeWireDispatchResult receipt.binding

def encodeTypedReceipt (sha256 : Sha256) (receipt : Receipt) : ByteString :=
  let prefixResult := typedReceiptPrefixResult receipt
  prefixResult ++ bytes32List (sha256 (receiptDigestDomain ++ prefixResult))

def encodeWireReceipt (sha256 : Sha256) (receipt : WireReceipt) : ByteString :=
  let prefixResult := wireReceiptPrefixResult receipt
  prefixResult ++ bytes32List (sha256 (receiptDigestDomain ++ prefixResult))

def encodeTypedBody (sha256 : Sha256) :
    AspisPool.AuthorizationReceiptAccountV1.ReceiptBody → ByteString
  | .zero => List.replicate 432 0
  | .asva receipt => encodeTypedReceipt sha256 receipt

def statusByte : AspisPool.AuthorizationReceiptAccountV1.Status → UInt8
  | .pending => 0
  | .verified => 1

def encodeTypedAccountCore (sha256 : Sha256)
    (core : AspisPool.AuthorizationReceiptAccountV1.AccountCore) : ByteString :=
  core.magic ++
    [UInt8.ofNat core.formatVersion, UInt8.ofNat core.hashIdentifier,
      statusByte core.status, UInt8.ofNat core.pdaBump] ++
    u64LE core.verifiedSlot ++ block32 core.verifierProgram ++
    block32 core.proofAccount ++ block32 core.statementDigest ++
    block32 core.bindingDigest ++ block32 core.requestDigest ++
    block32 core.proofUploadAuthority ++ block32 core.closeRefundAuthority ++
    core.reserved ++ encodeTypedBody sha256 core.body

def typedPreimageBytes (sha256 : Sha256) :
    AspisPool.AuthorizationReceiptAccountV1.DigestPreimage → ByteString
  | .binding binding => typedBindingDigestPreimage binding
  | .request request => typedRequestDigestPreimage request
  | .wrapper core => accountDigestDomain ++ encodeTypedAccountCore sha256 core

noncomputable def typedHash (sha256 : Sha256) :
    AspisPool.AuthorizationReceiptAccountV1.HashFn :=
  fun preimage => pack32 (sha256 (typedPreimageBytes sha256 preimage))

theorem typed_hash_has_exact_sha256_bytes (sha256 : Sha256)
    (preimage : AspisPool.AuthorizationReceiptAccountV1.DigestPreimage) :
    block32 (typedHash sha256 preimage) =
      bytes32List (sha256 (typedPreimageBytes sha256 preimage)) := by
  simp [typedHash]

theorem typed_binding_hash_bytes_of_wire (sha256 : Sha256)
    (binding : WireBinding) :
    block32 (typedHash sha256 (.binding binding.toTyped)) =
      bytes32List (sha256 (wireBindingDigestPreimage binding)) := by
  rw [typed_hash_has_exact_sha256_bytes, typedPreimageBytes,
    typed_binding_preimage_of_wire]

theorem typed_request_hash_bytes_of_wire (sha256 : Sha256)
    (request : WireRequest) :
    block32 (typedHash sha256 (.request {
      binding := request.binding.toTyped
      statementPayload := request.statementPayload
    })) =
      bytes32List (sha256 (wireRequestDigestPreimage request)) := by
  rw [typed_hash_has_exact_sha256_bytes, typedPreimageBytes]
  have preimageExact :
      typedRequestDigestPreimage {
        binding := request.binding.toTyped
        statementPayload := request.statementPayload
      } = wireRequestDigestPreimage request := by
    simpa only [WireRequest.toTyped] using typed_request_preimage_of_wire request
  rw [preimageExact]

theorem unpack_typed_binding_hash_of_wire (sha256 : Sha256)
    (binding : WireBinding) :
    unpack32 (typedHash sha256 (.binding binding.toTyped)) =
      sha256 (wireBindingDigestPreimage binding) := by
  change unpack32 (pack32 (sha256
    (typedPreimageBytes sha256 (.binding binding.toTyped)))) = _
  rw [unpack32_pack32, typedPreimageBytes, typed_binding_preimage_of_wire]

def encodeTypedAccount (sha256 : Sha256)
    (account : AspisPool.AuthorizationReceiptAccountV1.Account) : ByteString :=
  encodeTypedAccountCore sha256 account.core ++ block32 account.wrapperDigest

def sealedTypedAccountBytes (sha256 : Sha256)
    (core : AspisPool.AuthorizationReceiptAccountV1.AccountCore) : ByteString :=
  let prefixBody := encodeTypedAccountCore sha256 core
  prefixBody ++ bytes32List (sha256 (accountDigestDomain ++ prefixBody))

theorem encode_typed_sealed_account (sha256 : Sha256)
    (core : AspisPool.AuthorizationReceiptAccountV1.AccountCore) :
    encodeTypedAccount sha256
        (AspisPool.AuthorizationReceiptAccountV1.sealAccount (typedHash sha256) core) =
      sealedTypedAccountBytes sha256 core := by
  simp [encodeTypedAccount, AspisPool.AuthorizationReceiptAccountV1.sealAccount,
    sealedTypedAccountBytes,
    typed_hash_has_exact_sha256_bytes, typedPreimageBytes]

theorem typed_receipt_prefix_of_wire (receipt : WireReceipt) :
    typedReceiptPrefixResult receipt.toTyped = wireReceiptPrefixResult receipt := by
  simp [typedReceiptPrefixResult, wireReceiptPrefixResult, WireReceipt.toTyped,
    encode_typed_dispatch_result_of_wire]

theorem encode_typed_receipt_of_wire (sha256 : Sha256) (receipt : WireReceipt) :
    encodeTypedReceipt sha256 {
      pdaBump := receipt.pdaBump
      verifiedSlot := receipt.verifiedSlot
      binding := receipt.binding.toTyped
    } = encodeWireReceipt sha256 receipt := by
  have prefixExact :
      typedReceiptPrefixResult {
        pdaBump := receipt.pdaBump
        verifiedSlot := receipt.verifiedSlot
        binding := receipt.binding.toTyped
      } = wireReceiptPrefixResult receipt := by
    simpa only [WireReceipt.toTyped] using typed_receipt_prefix_of_wire receipt
  simp only [encodeTypedReceipt, encodeWireReceipt]
  rw [prefixExact]

theorem exact_receipt_length (sha256 : Sha256) (receipt : WireReceipt) :
    (encodeWireReceipt sha256 receipt).length = 432 := by
  simp [encodeWireReceipt, wireReceiptPrefixResult, exact_dispatch_result_length,
    bytes32List_length, asvaMagic, u64LE_length]

theorem exact_asva_offsets :
    [0, 4, 5, 6, 7, 8, 16, 400, 432] =
      [0,
        asvaMagic.length,
        asvaMagic.length + 1,
        asvaMagic.length + 2,
        asvaMagic.length + 3,
        asvaMagic.length + 4,
        asvaMagic.length + 4 + 8,
        asvaMagic.length + 4 + 8 + 384,
        asvaMagic.length + 4 + 8 + 384 + 32] := by
  decide

def wireImmutableHeader (sha256 : Sha256) (request : WireRequest)
    (proofUploadAuthority closeRefundAuthority : Bytes32) : ByteString :=
  bytes32List request.binding.verifierProgram ++
    bytes32List request.binding.proofAccount ++
    bytes32List request.binding.statementDigest ++
    bytes32List (sha256 (wireBindingDigestPreimage request.binding)) ++
    bytes32List (sha256 (wireRequestDigestPreimage request)) ++
    bytes32List proofUploadAuthority ++ bytes32List closeRefundAuthority ++
    List.replicate 16 0

def wirePendingCore (sha256 : Sha256) (request : WireRequest) (pdaBump : Nat)
    (proofUploadAuthority closeRefundAuthority : Bytes32) : ByteString :=
  asraMagic ++ [1, 1, 0, UInt8.ofNat pdaBump] ++ u64LE 0 ++
    wireImmutableHeader sha256 request proofUploadAuthority closeRefundAuthority ++
    List.replicate 432 0

def wireFinalizedCore (sha256 : Sha256) (request : WireRequest)
    (receipt : WireReceipt) (proofUploadAuthority closeRefundAuthority : Bytes32) :
    ByteString :=
  asraMagic ++ [1, 1, 1, UInt8.ofNat receipt.pdaBump] ++
    u64LE receipt.verifiedSlot ++
    wireImmutableHeader sha256 request proofUploadAuthority closeRefundAuthority ++
    encodeWireReceipt sha256 receipt

def sealWireAccount (sha256 : Sha256) (prefixBody : ByteString) : ByteString :=
  prefixBody ++ bytes32List (sha256 (accountDigestDomain ++ prefixBody))

def wirePendingAccount (sha256 : Sha256) (request : WireRequest) (pdaBump : Nat)
    (proofUploadAuthority closeRefundAuthority : Bytes32) : ByteString :=
  sealWireAccount sha256
    (wirePendingCore sha256 request pdaBump proofUploadAuthority closeRefundAuthority)

def wireFinalizedAccount (sha256 : Sha256) (request : WireRequest)
    (receipt : WireReceipt) (proofUploadAuthority closeRefundAuthority : Bytes32) :
    ByteString :=
  sealWireAccount sha256
    (wireFinalizedCore sha256 request receipt proofUploadAuthority closeRefundAuthority)

theorem typed_pending_core_of_wire (sha256 : Sha256) (request : WireRequest)
    (pdaBump : Nat) (proofUploadAuthority closeRefundAuthority : Bytes32) :
    encodeTypedAccountCore sha256
        (AspisPool.AuthorizationReceiptAccountV1.pendingCore
          (typedHash sha256) request.toTyped pdaBump
          (pack32 proofUploadAuthority) (pack32 closeRefundAuthority)) =
      wirePendingCore sha256 request pdaBump proofUploadAuthority closeRefundAuthority := by
  simp only [encodeTypedAccountCore,
    AspisPool.AuthorizationReceiptAccountV1.pendingCore, encodeTypedBody,
    wirePendingCore, wireImmutableHeader,
    AspisPool.AuthorizationReceiptAccountV1.accountMagic,
    AspisPool.AuthorizationReceiptAccountV1.accountVersion,
    AspisPool.AuthorizationReceiptAccountV1.sha256Identifier,
    AspisPool.AuthorizationReceiptAccountV1.zeroReserved,
    AspisPool.AuthorizationReceiptAccountV1.reservedBytes,
    WireRequest.toTyped, block32_pack32, statusByte, asraMagic]
  rw [typed_binding_hash_bytes_of_wire, typed_request_hash_bytes_of_wire]
  simp only [WireBinding.toTyped, block32_pack32, List.append_assoc]
  norm_num

theorem typed_pending_account_of_wire (sha256 : Sha256) (request : WireRequest)
    (pdaBump : Nat) (proofUploadAuthority closeRefundAuthority : Bytes32) :
    encodeTypedAccount sha256
        (AspisPool.AuthorizationReceiptAccountV1.pendingAccount
          (typedHash sha256) request.toTyped pdaBump
          (pack32 proofUploadAuthority) (pack32 closeRefundAuthority)) =
      wirePendingAccount sha256 request pdaBump proofUploadAuthority
        closeRefundAuthority := by
  rw [AspisPool.AuthorizationReceiptAccountV1.pendingAccount,
    encode_typed_sealed_account]
  simp only [sealedTypedAccountBytes, wirePendingAccount, sealWireAccount]
  rw [typed_pending_core_of_wire]

theorem typed_finalized_core_of_wire (sha256 : Sha256) (request : WireRequest)
    (receipt : WireReceipt) (proofUploadAuthority closeRefundAuthority : Bytes32) :
    encodeTypedAccountCore sha256
        (AspisPool.AuthorizationReceiptAccountV1.finalizedCore
          (AspisPool.AuthorizationReceiptAccountV1.pendingAccount
            (typedHash sha256) request.toTyped receipt.pdaBump
            (pack32 proofUploadAuthority) (pack32 closeRefundAuthority))
          receipt.toTyped) =
      wireFinalizedCore sha256 request receipt proofUploadAuthority
        closeRefundAuthority := by
  simp only [encodeTypedAccountCore,
    AspisPool.AuthorizationReceiptAccountV1.finalizedCore,
    AspisPool.AuthorizationReceiptAccountV1.pendingAccount,
    AspisPool.AuthorizationReceiptAccountV1.pendingCore,
    AspisPool.AuthorizationReceiptAccountV1.sealAccount, encodeTypedBody,
    wireFinalizedCore, wireImmutableHeader,
    AspisPool.AuthorizationReceiptAccountV1.accountMagic,
    AspisPool.AuthorizationReceiptAccountV1.accountVersion,
    AspisPool.AuthorizationReceiptAccountV1.sha256Identifier,
    AspisPool.AuthorizationReceiptAccountV1.zeroReserved,
    AspisPool.AuthorizationReceiptAccountV1.reservedBytes,
    WireRequest.toTyped, WireReceipt.toTyped, block32_pack32, statusByte,
    asraMagic]
  rw [typed_binding_hash_bytes_of_wire, typed_request_hash_bytes_of_wire,
    encode_typed_receipt_of_wire]
  simp only [WireBinding.toTyped, block32_pack32, List.append_assoc]
  norm_num

theorem typed_finalized_account_of_wire (sha256 : Sha256) (request : WireRequest)
    (receipt : WireReceipt) (proofUploadAuthority closeRefundAuthority : Bytes32) :
    encodeTypedAccount sha256
        (AspisPool.AuthorizationReceiptAccountV1.finalizedAccount (typedHash sha256)
          (AspisPool.AuthorizationReceiptAccountV1.pendingAccount
            (typedHash sha256) request.toTyped receipt.pdaBump
            (pack32 proofUploadAuthority) (pack32 closeRefundAuthority))
          receipt.toTyped) =
      wireFinalizedAccount sha256 request receipt proofUploadAuthority
        closeRefundAuthority := by
  rw [AspisPool.AuthorizationReceiptAccountV1.finalizedAccount,
    encode_typed_sealed_account]
  simp only [sealedTypedAccountBytes, wireFinalizedAccount, sealWireAccount]
  rw [typed_finalized_core_of_wire]

/-- A successful typed initialization is not merely field-equivalent to the
Rust image: encoding its returned account produces the exact sealed ASRA
pending bytes. -/
theorem initialize_success_has_exact_wire_account (sha256 : Sha256)
    (request : WireRequest)
    (observedProofAccount proofUploadAuthority signedUploadAuthority
      closeRefundAuthority : Bytes32)
    (pdaBump : Nat) (account : AspisPool.AuthorizationReceiptAccountV1.Account)
    (success : AspisPool.AuthorizationReceiptAccountV1.initializeAccount
      (typedHash sha256) request.toTyped (pack32 observedProofAccount)
      (pack32 proofUploadAuthority) (some (pack32 signedUploadAuthority))
      (pack32 closeRefundAuthority) pdaBump = some account) :
    encodeTypedAccount sha256 account =
      wirePendingAccount sha256 request pdaBump proofUploadAuthority
        closeRefundAuthority := by
  have accountExact :=
    (AspisPool.AuthorizationReceiptAccountV1.initialize_success_iff
      (typedHash sha256) request.toTyped (pack32 observedProofAccount)
      (pack32 proofUploadAuthority) (some (pack32 signedUploadAuthority))
      (pack32 closeRefundAuthority) pdaBump account).mp success |>.2
  rw [accountExact]
  exact typed_pending_account_of_wire sha256 request pdaBump proofUploadAuthority
    closeRefundAuthority

/-- Starting from the exact wire-induced pending state, every successful typed
finalization encodes as the exact sealed ASRA finalized image.  The success
fact itself supplies the binding-equality check; it is not assumed separately. -/
theorem finalize_success_has_exact_wire_account (sha256 : Sha256)
    (request : WireRequest) (receipt : WireReceipt)
    (proofUploadAuthority closeRefundAuthority : Bytes32)
    (account : AspisPool.AuthorizationReceiptAccountV1.Account)
    (success : AspisPool.AuthorizationReceiptAccountV1.finalizeAccount
      (typedHash sha256)
      (AspisPool.AuthorizationReceiptAccountV1.pendingAccount
        (typedHash sha256) request.toTyped receipt.pdaBump
        (pack32 proofUploadAuthority) (pack32 closeRefundAuthority))
      request.toTyped receipt.toTyped = some account) :
    encodeTypedAccount sha256 account =
      wireFinalizedAccount sha256 request receipt proofUploadAuthority
        closeRefundAuthority := by
  have accountExact :=
    (AspisPool.AuthorizationReceiptAccountV1.finalize_success_iff
      (typedHash sha256)
      (AspisPool.AuthorizationReceiptAccountV1.pendingAccount
        (typedHash sha256) request.toTyped receipt.pdaBump
        (pack32 proofUploadAuthority) (pack32 closeRefundAuthority))
      request.toTyped receipt.toTyped account).mp success |>.2
  rw [accountExact]
  exact typed_finalized_account_of_wire sha256 request receipt
    proofUploadAuthority closeRefundAuthority

theorem exact_pending_account_length (sha256 : Sha256) (request : WireRequest)
    (pdaBump : Nat) (proofUploadAuthority closeRefundAuthority : Bytes32) :
    (wirePendingAccount sha256 request pdaBump proofUploadAuthority
      closeRefundAuthority).length = 720 := by
  simp only [wirePendingAccount, sealWireAccount, List.length_append,
    bytes32List_length]
  have headerLength :
      (wireImmutableHeader sha256 request proofUploadAuthority
        closeRefundAuthority).length = 240 := by
    simp only [wireImmutableHeader, List.length_append, bytes32List_length,
      List.length_replicate]
  simp only [wirePendingCore, List.length_append, List.length_cons,
    List.length_nil, u64LE_length, headerLength, List.length_replicate,
    asraMagic]

theorem exact_finalized_account_length (sha256 : Sha256) (request : WireRequest)
    (receipt : WireReceipt) (proofUploadAuthority closeRefundAuthority : Bytes32) :
    (wireFinalizedAccount sha256 request receipt proofUploadAuthority
      closeRefundAuthority).length = 720 := by
  simp [wireFinalizedAccount, sealWireAccount, wireFinalizedCore,
    wireImmutableHeader, exact_receipt_length, bytes32List_length,
    u64LE_length, asraMagic]

/-- The source transition copies the six-byte magic/version/hash prefix, bump,
and bytes 16..256; it changes only status, slot, body, and wrapper digest.  The
two equations below expose that decomposition without a list-update axiom. -/
theorem pending_and_finalized_exact_sections (sha256 : Sha256)
    (request : WireRequest) (receipt : WireReceipt)
    (proofUploadAuthority closeRefundAuthority : Bytes32) :
    wirePendingCore sha256 request receipt.pdaBump proofUploadAuthority
        closeRefundAuthority =
      asraMagic ++ [1, 1, 0, UInt8.ofNat receipt.pdaBump] ++ u64LE 0 ++
        wireImmutableHeader sha256 request proofUploadAuthority closeRefundAuthority ++
        List.replicate 432 0 ∧
    wireFinalizedCore sha256 request receipt proofUploadAuthority
        closeRefundAuthority =
      asraMagic ++ [1, 1, 1, UInt8.ofNat receipt.pdaBump] ++
        u64LE receipt.verifiedSlot ++
        wireImmutableHeader sha256 request proofUploadAuthority closeRefundAuthority ++
        encodeWireReceipt sha256 receipt := by
  exact ⟨rfl, rfl⟩

/-! ## PDA seed ordering -/

def wirePdaDynamicSeeds (sha256 : Sha256) (binding : WireBinding) : List Bytes32 :=
  [binding.proofAccount, binding.statementDigest,
    sha256 (wireBindingDigestPreimage binding)]

/-- Exact inputs to `Pubkey::find_program_address`, excluding the verifier
program id passed as its separate second argument. -/
def wirePdaAddressSeeds (sha256 : Sha256) (binding : WireBinding) :
    List ByteString :=
  [pdaStaticSeed, bytes32List binding.proofAccount,
    bytes32List binding.statementDigest,
    bytes32List (sha256 (wireBindingDigestPreimage binding))]

/-- Exact `invoke_signed` seed list.  The canonical bump returned by
`find_program_address` is appended only at signing time. -/
def wirePdaSignerSeeds (sha256 : Sha256) (binding : WireBinding) (bump : Nat) :
    List ByteString :=
  wirePdaAddressSeeds sha256 binding ++ [[UInt8.ofNat bump]]

def typedPdaDynamicSeeds
    (inputs : AspisPool.AuthorizationReceiptAccountV1.PdaInputs) : List Bytes32 :=
  [unpack32 inputs.proofAccount, unpack32 inputs.statementDigest,
    unpack32 inputs.bindingDigest]

theorem pending_pda_dynamic_seeds_exact (sha256 : Sha256) (request : WireRequest)
    (pdaBump : Nat) (proofUploadAuthority closeRefundAuthority : Bytes32) :
    typedPdaDynamicSeeds
        (AspisPool.AuthorizationReceiptAccountV1.Account.pdaInputs
          (AspisPool.AuthorizationReceiptAccountV1.pendingAccount
            (typedHash sha256) request.toTyped pdaBump
            (pack32 proofUploadAuthority) (pack32 closeRefundAuthority))) =
      wirePdaDynamicSeeds sha256 request.binding := by
  calc
    typedPdaDynamicSeeds
        (AspisPool.AuthorizationReceiptAccountV1.Account.pdaInputs
          (AspisPool.AuthorizationReceiptAccountV1.pendingAccount
            (typedHash sha256) request.toTyped pdaBump
            (pack32 proofUploadAuthority) (pack32 closeRefundAuthority))) =
      [request.binding.proofAccount, request.binding.statementDigest,
        unpack32 (typedHash sha256 (.binding request.binding.toTyped))] := by
          simp only [typedPdaDynamicSeeds,
            AspisPool.AuthorizationReceiptAccountV1.Account.pdaInputs,
            AspisPool.AuthorizationReceiptAccountV1.pendingAccount,
            AspisPool.AuthorizationReceiptAccountV1.pendingCore,
            AspisPool.AuthorizationReceiptAccountV1.sealAccount,
            WireRequest.toTyped, WireBinding.toTyped, unpack32_pack32]
    _ = [request.binding.proofAccount, request.binding.statementDigest,
        sha256 (wireBindingDigestPreimage request.binding)] := by
          rw [unpack_typed_binding_hash_of_wire]
    _ = wirePdaDynamicSeeds sha256 request.binding := rfl

theorem exact_pda_seed_prefix_and_order (sha256 : Sha256) (binding : WireBinding) :
    pdaStaticSeed =
      [97, 115, 112, 105, 115, 45, 118, 101, 114, 105, 102, 121, 45, 114,
        101, 99, 101, 105, 112, 116, 45, 118, 49] ∧
    wirePdaDynamicSeeds sha256 binding =
      [binding.proofAccount, binding.statementDigest,
        sha256 (wireBindingDigestPreimage binding)] := by
  exact ⟨rfl, rfl⟩

theorem exact_pda_address_and_signer_seed_order (sha256 : Sha256)
    (binding : WireBinding) (bump : Nat) :
    wirePdaAddressSeeds sha256 binding =
      [pdaStaticSeed, bytes32List binding.proofAccount,
        bytes32List binding.statementDigest,
        bytes32List (sha256 (wireBindingDigestPreimage binding))] ∧
    wirePdaSignerSeeds sha256 binding bump =
      [pdaStaticSeed, bytes32List binding.proofAccount,
        bytes32List binding.statementDigest,
        bytes32List (sha256 (wireBindingDigestPreimage binding)),
        [UInt8.ofNat bump]] := by
  exact ⟨rfl, rfl⟩

/-! ## Frozen offsets and explicit Aeneas residual -/

theorem exact_asra_offsets :
    [0, 4, 5, 6, 7, 8, 16, 48, 80, 112, 144, 176, 208, 240, 256, 688, 720] =
      [0,
        asraMagic.length,
        asraMagic.length + 1,
        asraMagic.length + 2,
        asraMagic.length + 3,
        asraMagic.length + 4,
        asraMagic.length + 4 + 8,
        asraMagic.length + 4 + 8 + 32,
        asraMagic.length + 4 + 8 + 64,
        asraMagic.length + 4 + 8 + 96,
        asraMagic.length + 4 + 8 + 128,
        asraMagic.length + 4 + 8 + 160,
        asraMagic.length + 4 + 8 + 192,
        asraMagic.length + 4 + 8 + 224,
        asraMagic.length + 4 + 8 + 240,
        asraMagic.length + 4 + 8 + 240 + 432,
        asraMagic.length + 4 + 8 + 240 + 432 + 32] := by
  decide

structure ExtractedRustEncoders where
  encodeDispatchResult : WireBinding → Option ByteString
  encodeDispatchRequest : WireRequest → Option ByteString
  bindingHashInput : WireBinding → Option ByteString
  requestHashInput : WireRequest → Option ByteString
  encodeReceipt : Sha256 → WireReceipt → Option ByteString
  encodePending : Sha256 → WireRequest → Nat → Bytes32 → Bytes32 → Option ByteString
  encodeFinalized : Sha256 → WireRequest → WireReceipt → Bytes32 → Bytes32 →
    Option ByteString
  pdaDynamicSeeds : Sha256 → WireBinding → Option (List Bytes32)

/-- Exact generated-source goal.  It is intentionally not a field of any
lifecycle theorem and supplies no arbitrary result: every successful returned
value is fixed to the concrete encoder above. -/
def AeneasSourceEquality (rust : ExtractedRustEncoders) : Prop :=
  (∀ binding output, rust.encodeDispatchResult binding = some output →
      output = encodeWireDispatchResult binding) ∧
  (∀ request output, rust.encodeDispatchRequest request = some output →
      output = encodeWireDispatchRequest request) ∧
  (∀ binding output, rust.bindingHashInput binding = some output →
      output = wireBindingDigestPreimage binding) ∧
  (∀ request output, rust.requestHashInput request = some output →
      output = wireRequestDigestPreimage request) ∧
  (∀ sha256 receipt output, rust.encodeReceipt sha256 receipt = some output →
      output = encodeWireReceipt sha256 receipt) ∧
  (∀ sha256 request bump upload close output,
      rust.encodePending sha256 request bump upload close = some output →
        output = wirePendingAccount sha256 request bump upload close) ∧
  (∀ sha256 request receipt upload close output,
      rust.encodeFinalized sha256 request receipt upload close = some output →
        output = wireFinalizedAccount sha256 request receipt upload close) ∧
  (∀ sha256 binding output, rust.pdaDynamicSeeds sha256 binding = some output →
      output = wirePdaDynamicSeeds sha256 binding)

def committedRustRevision : String :=
  "6f1abc0bb514e36d308c37bda56c353edaeeb637"

/-- SHA-256 of each file as stored in `committedRustRevision`, not of a dirty
worktree copy.  The last two integration files pin the four address seeds and
the five signer seeds in addition to the pure crate's `dynamic_seeds`. -/
def committedRustSourcePins : List (String × String) :=
  [("crates/aspis-statement/src/pool_v1/authorization_receipt_account.rs",
      "132b264453c4d3c286b4d39f92b132c8e662495f809ff2ad57559d37098245cf"),
    ("crates/aspis-statement/src/pool_v1/authorization_receipt.rs",
      "512e7a02f3f8718d520e8c9ff4445f0e691039841cc72ade9f02c21d861225f3"),
    ("crates/aspis-statement/src/pool_v1/verifier_dispatch.rs",
      "fbfa90d9d8de5a36b476786132c52f7c64ee7b75a5ec3a89ea0c18d76e77c8bb"),
    ("programs/aspis-pool/src/prepared_settlement.rs",
      "255c45d386d6f36060dbed5c68007fd04d0c8636beaa21f14a2636ca2f72c22f"),
    ("programs/aspis-verifier/src/v7_pool_receipt.rs",
      "1d4992c5cff8a055c5c0fce2e935f392e32d2d3e47fb63bf2fabb3cdb45626c2")]

/-- Inclusive committed-source line ranges carrying the constants, encoders,
hash preimages, state transitions, and PDA calls modeled above. -/
def committedRustSourceRanges : List (String × Nat × Nat) :=
  [("crates/aspis-statement/src/pool_v1/authorization_receipt_account.rs", 53, 82),
    ("crates/aspis-statement/src/pool_v1/authorization_receipt_account.rs", 193, 310),
    ("crates/aspis-statement/src/pool_v1/authorization_receipt_account.rs", 483, 523),
    ("crates/aspis-statement/src/pool_v1/authorization_receipt.rs", 19, 34),
    ("crates/aspis-statement/src/pool_v1/authorization_receipt.rs", 72, 105),
    ("crates/aspis-statement/src/pool_v1/verifier_dispatch.rs", 18, 51),
    ("crates/aspis-statement/src/pool_v1/verifier_dispatch.rs", 240, 270),
    ("crates/aspis-statement/src/pool_v1/verifier_dispatch.rs", 360, 459),
    ("programs/aspis-pool/src/prepared_settlement.rs", 215, 228),
    ("programs/aspis-verifier/src/v7_pool_receipt.rs", 179, 220),
    ("programs/aspis-verifier/src/v7_pool_receipt.rs", 231, 247)]

#print axioms unpack32_pack32
#print axioms encode_typed_dispatch_image_of_wire
#print axioms typed_binding_preimage_of_wire
#print axioms typed_request_preimage_of_wire
#print axioms exact_dispatch_result_length
#print axioms exact_dispatch_request_length
#print axioms exact_dispatch_offsets
#print axioms exact_digest_domain_lengths
#print axioms typed_hash_has_exact_sha256_bytes
#print axioms typed_binding_hash_bytes_of_wire
#print axioms typed_request_hash_bytes_of_wire
#print axioms unpack_typed_binding_hash_of_wire
#print axioms encode_typed_receipt_of_wire
#print axioms exact_receipt_length
#print axioms exact_asva_offsets
#print axioms typed_pending_core_of_wire
#print axioms typed_pending_account_of_wire
#print axioms typed_finalized_core_of_wire
#print axioms typed_finalized_account_of_wire
#print axioms initialize_success_has_exact_wire_account
#print axioms finalize_success_has_exact_wire_account
#print axioms exact_pending_account_length
#print axioms exact_finalized_account_length
#print axioms pending_and_finalized_exact_sections
#print axioms pending_pda_dynamic_seeds_exact
#print axioms exact_pda_seed_prefix_and_order
#print axioms exact_pda_address_and_signer_seed_order
#print axioms exact_asra_offsets

end
end AspisPool.AuthorizationReceiptAccountWireV1
