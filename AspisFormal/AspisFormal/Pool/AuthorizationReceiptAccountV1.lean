import AspisFormal.Pool.AuthorizationReceiptV1

/-!
# Pool V1 verifier-owned authorization-receipt account lifecycle

This module is the pure, typed lifecycle model for the 720-byte `ASRA`
account committed by `authorization_receipt_account.rs`.  The constructors
below retain every semantically live wrapper field.  The three digest domains
are distinct constructors of `DigestPreimage`, so a deterministic hash is
always called on a typed binding, request, or wrapper preimage; identifying
that function with the deployed domain-separated SHA-256 byte encodings is a
separate Rust/Aeneas source-correspondence obligation.

The state transformer itself has no security premise.  Initialization can
succeed only with the exact proof account and the nonzero upload authority
present as a signer.  Finalization consumes only a canonical pending image and
copies every immutable field.  Close authorization returns the original
account alongside an authorization record, making nonmutation explicit.
-/

set_option autoImplicit false

namespace AspisPool.AuthorizationReceiptAccountV1

open AspisPool.AuthorizationReceiptV1

abbrev Digest := Nat
abbrev PublicKey := Nat

def accountMagic : List UInt8 := [0x41, 0x53, 0x52, 0x41]
def accountVersion : Nat := 1
def sha256Identifier : Nat := 1
def receiptPdaSeed : String := "aspis-verify-receipt-v1"

def headerBytes : Nat := 256
def receiptBodyBytes : Nat := 432
def wrapperDigestBytes : Nat := 32
def accountBytes : Nat := 720
def reservedBytes : Nat := 16

def verifiedSlotOffset : Nat := 8
def verifierProgramOffset : Nat := 16
def proofAccountOffset : Nat := 48
def statementDigestOffset : Nat := 80
def bindingDigestOffset : Nat := 112
def requestDigestOffset : Nat := 144
def proofUploadAuthorityOffset : Nat := 176
def closeRefundAuthorityOffset : Nat := 208
def reservedOffset : Nat := 240
def receiptOffset : Nat := 256
def wrapperDigestOffset : Nat := 688

def zeroReserved : List UInt8 := List.replicate reservedBytes 0

inductive Status where
  | pending
  | verified
  deriving DecidableEq, Repr

/-- A typed distinction between the exact 432 zero bytes in a pending account
and the exact nested ASVA encoding in a finalized account. -/
inductive ReceiptBody where
  | zero
  | asva (receipt : Receipt)
  deriving DecidableEq, Repr

def ReceiptBody.bytes (encodeASVA : Receipt → List UInt8) : ReceiptBody → List UInt8
  | .zero => List.replicate receiptBodyBytes 0
  | .asva receipt => encodeASVA receipt

/-- The exact ASVQ request information relevant to the pure wrapper.  Keeping
the payload in the request makes the request digest commit more than the outer
binding alone. -/
structure Request where
  binding : Binding
  statementPayload : List UInt8
  deriving DecidableEq, Repr

/-- All bytes covered by the wrapper digest, represented by their typed
meaning.  `wrapperDigest` itself is deliberately absent to avoid circularity. -/
structure AccountCore where
  magic : List UInt8
  formatVersion : Nat
  hashIdentifier : Nat
  status : Status
  pdaBump : Nat
  verifiedSlot : Nat
  verifierProgram : PublicKey
  proofAccount : PublicKey
  statementDigest : Digest
  bindingDigest : Digest
  requestDigest : Digest
  proofUploadAuthority : PublicKey
  closeRefundAuthority : PublicKey
  reserved : List UInt8
  body : ReceiptBody
  deriving DecidableEq, Repr

/-- Typed, disjoint domains for all three SHA-256 calls made by ASRA. -/
inductive DigestPreimage where
  | binding (binding : Binding)
  | request (request : Request)
  | wrapper (core : AccountCore)
  deriving DecidableEq, Repr

abbrev HashFn := DigestPreimage → Digest

structure Account where
  core : AccountCore
  wrapperDigest : Digest
  deriving DecidableEq, Repr

structure ImmutableFields where
  magic : List UInt8
  formatVersion : Nat
  hashIdentifier : Nat
  pdaBump : Nat
  verifierProgram : PublicKey
  proofAccount : PublicKey
  statementDigest : Digest
  bindingDigest : Digest
  requestDigest : Digest
  proofUploadAuthority : PublicKey
  closeRefundAuthority : PublicKey
  reserved : List UInt8
  deriving DecidableEq, Repr

structure PdaInputs where
  staticSeed : String
  proofAccount : PublicKey
  statementDigest : Digest
  bindingDigest : Digest
  bump : Nat
  deriving DecidableEq, Repr

structure CloseAuthorization where
  closeAuthority : PublicKey
  refundDestination : PublicKey
  deriving DecidableEq, Repr

def AccountCore.immutableFields (core : AccountCore) : ImmutableFields where
  magic := core.magic
  formatVersion := core.formatVersion
  hashIdentifier := core.hashIdentifier
  pdaBump := core.pdaBump
  verifierProgram := core.verifierProgram
  proofAccount := core.proofAccount
  statementDigest := core.statementDigest
  bindingDigest := core.bindingDigest
  requestDigest := core.requestDigest
  proofUploadAuthority := core.proofUploadAuthority
  closeRefundAuthority := core.closeRefundAuthority
  reserved := core.reserved

def Account.pdaInputs (account : Account) : PdaInputs where
  staticSeed := receiptPdaSeed
  proofAccount := account.core.proofAccount
  statementDigest := account.core.statementDigest
  bindingDigest := account.core.bindingDigest
  bump := account.core.pdaBump

def sealAccount (hash : HashFn) (core : AccountCore) : Account where
  core := core
  wrapperDigest := hash (.wrapper core)

def pendingCore (hash : HashFn) (request : Request) (pdaBump : Nat)
    (proofUploadAuthority closeRefundAuthority : PublicKey) : AccountCore where
  magic := accountMagic
  formatVersion := accountVersion
  hashIdentifier := sha256Identifier
  status := .pending
  pdaBump := pdaBump
  verifiedSlot := 0
  verifierProgram := request.binding.verifierProgram
  proofAccount := request.binding.proofAccount
  statementDigest := request.binding.statementDigest
  bindingDigest := hash (.binding request.binding)
  requestDigest := hash (.request request)
  proofUploadAuthority := proofUploadAuthority
  closeRefundAuthority := closeRefundAuthority
  reserved := zeroReserved
  body := .zero

def pendingAccount (hash : HashFn) (request : Request) (pdaBump : Nat)
    (proofUploadAuthority closeRefundAuthority : PublicKey) : Account :=
  sealAccount hash (pendingCore hash request pdaBump proofUploadAuthority closeRefundAuthority)

def CanonicalHeader (core : AccountCore) : Prop :=
  core.magic = accountMagic ∧
    core.formatVersion = accountVersion ∧
    core.hashIdentifier = sha256Identifier ∧
    core.proofUploadAuthority ≠ 0 ∧
    core.closeRefundAuthority ≠ 0 ∧
    core.reserved = zeroReserved

def Sealed (hash : HashFn) (account : Account) : Prop :=
  account.wrapperDigest = hash (.wrapper account.core)

def CanonicalPending (hash : HashFn) (account : Account) : Prop :=
  CanonicalHeader account.core ∧
    Sealed hash account ∧
    account.core.status = .pending ∧
    account.core.verifiedSlot = 0 ∧
    account.core.body = .zero

/-- Exact request-to-account binding checked before finalization. -/
def ExactRequestBinding (hash : HashFn) (account : Account) (request : Request) : Prop :=
  account.core.verifierProgram = request.binding.verifierProgram ∧
    account.core.proofAccount = request.binding.proofAccount ∧
    account.core.statementDigest = request.binding.statementDigest ∧
    account.core.bindingDigest = hash (.binding request.binding) ∧
    account.core.requestDigest = hash (.request request)

/-- The nested-ASVA checks made when a verified wrapper is decoded. -/
def CanonicalFinalized (hash : HashFn) (account : Account) : Prop :=
  CanonicalHeader account.core ∧
    Sealed hash account ∧
    match account.core.body with
    | .zero => False
    | .asva receipt =>
      account.core.status = .verified ∧
        account.core.verifiedSlot = receipt.verifiedSlot ∧
        receipt.pdaBump = account.core.pdaBump ∧
        receipt.binding.verifierProgram = account.core.verifierProgram ∧
        receipt.binding.proofAccount = account.core.proofAccount ∧
        receipt.binding.statementDigest = account.core.statementDigest ∧
        hash (.binding receipt.binding) = account.core.bindingDigest

def CanonicalAccount (hash : HashFn) (account : Account) : Prop :=
  CanonicalPending hash account ∨ CanonicalFinalized hash account

/-- All signer/proof-header facts required to prevent deterministic-PDA
preinitialization by an unrelated caller. -/
def PreinitAuthorized (request : Request) (observedProofAccount : PublicKey)
    (proofHeaderUploadAuthority : PublicKey)
    (signedUploadAuthority : Option PublicKey)
    (closeRefundAuthority : PublicKey) : Prop :=
  observedProofAccount = request.binding.proofAccount ∧
    signedUploadAuthority = some proofHeaderUploadAuthority ∧
    proofHeaderUploadAuthority ≠ 0 ∧
    closeRefundAuthority ≠ 0

instance instDecidablePreinitAuthorized (request : Request)
    (observedProofAccount proofHeaderUploadAuthority : PublicKey)
    (signedUploadAuthority : Option PublicKey)
    (closeRefundAuthority : PublicKey) :
    Decidable (PreinitAuthorized request observedProofAccount
      proofHeaderUploadAuthority signedUploadAuthority closeRefundAuthority) := by
  unfold PreinitAuthorized
  infer_instance

def initializeAccount (hash : HashFn) (request : Request)
    (observedProofAccount proofHeaderUploadAuthority : PublicKey)
    (signedUploadAuthority : Option PublicKey)
    (closeRefundAuthority : PublicKey) (pdaBump : Nat) : Option Account :=
  if PreinitAuthorized request observedProofAccount proofHeaderUploadAuthority
      signedUploadAuthority closeRefundAuthority then
    some (pendingAccount hash request pdaBump proofHeaderUploadAuthority
      closeRefundAuthority)
  else
    none

theorem exact_account_layout :
    headerBytes = receiptOffset ∧
      receiptOffset + receiptBodyBytes = wrapperDigestOffset ∧
      wrapperDigestOffset + wrapperDigestBytes = accountBytes ∧
      reservedOffset + reservedBytes = receiptOffset := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem zero_body_is_exact_432_bytes (encodeASVA : Receipt → List UInt8) :
    ReceiptBody.bytes encodeASVA .zero = List.replicate 432 0 ∧
      (ReceiptBody.bytes encodeASVA .zero).length = 432 := by
  constructor
  · rfl
  · change (List.replicate 432 (0 : UInt8)).length = 432
    exact List.length_replicate

theorem initialize_success_iff (hash : HashFn) (request : Request)
    (observedProofAccount proofHeaderUploadAuthority : PublicKey)
    (signedUploadAuthority : Option PublicKey)
    (closeRefundAuthority : PublicKey) (pdaBump : Nat) (account : Account) :
    initializeAccount hash request observedProofAccount proofHeaderUploadAuthority
        signedUploadAuthority closeRefundAuthority pdaBump = some account ↔
      PreinitAuthorized request observedProofAccount proofHeaderUploadAuthority
          signedUploadAuthority closeRefundAuthority ∧
        account = pendingAccount hash request pdaBump proofHeaderUploadAuthority
          closeRefundAuthority := by
  by_cases authorized : PreinitAuthorized request observedProofAccount
    proofHeaderUploadAuthority signedUploadAuthority closeRefundAuthority
  · simp only [initializeAccount, authorized, if_true, Option.some.injEq, true_and]
    exact eq_comm
  · simp [initializeAccount, authorized]

theorem initialize_success_binds_preinitialization_authority
    (hash : HashFn) (request : Request)
    (observedProofAccount proofHeaderUploadAuthority : PublicKey)
    (signedUploadAuthority : Option PublicKey)
    (closeRefundAuthority : PublicKey) (pdaBump : Nat) (account : Account)
    (success : initializeAccount hash request observedProofAccount proofHeaderUploadAuthority
      signedUploadAuthority closeRefundAuthority pdaBump = some account) :
    observedProofAccount = request.binding.proofAccount ∧
      signedUploadAuthority = some proofHeaderUploadAuthority ∧
      proofHeaderUploadAuthority ≠ 0 ∧ closeRefundAuthority ≠ 0 := by
  exact (initialize_success_iff hash request observedProofAccount
    proofHeaderUploadAuthority signedUploadAuthority closeRefundAuthority pdaBump
    account).mp success |>.1

theorem initialize_success_has_exact_pending_fields
    (hash : HashFn) (request : Request)
    (observedProofAccount proofHeaderUploadAuthority : PublicKey)
    (signedUploadAuthority : Option PublicKey)
    (closeRefundAuthority : PublicKey) (pdaBump : Nat) (account : Account)
    (success : initializeAccount hash request observedProofAccount proofHeaderUploadAuthority
      signedUploadAuthority closeRefundAuthority pdaBump = some account) :
    account.core.magic = accountMagic ∧
      account.core.formatVersion = accountVersion ∧
      account.core.hashIdentifier = sha256Identifier ∧
      account.core.status = .pending ∧
      account.core.pdaBump = pdaBump ∧
      account.core.verifiedSlot = 0 ∧
      account.core.verifierProgram = request.binding.verifierProgram ∧
      account.core.proofAccount = request.binding.proofAccount ∧
      account.core.statementDigest = request.binding.statementDigest ∧
      account.core.bindingDigest = hash (.binding request.binding) ∧
      account.core.requestDigest = hash (.request request) ∧
      account.core.proofUploadAuthority = proofHeaderUploadAuthority ∧
      account.core.closeRefundAuthority = closeRefundAuthority ∧
      account.core.reserved = List.replicate 16 0 ∧
      account.core.body = .zero ∧
      account.wrapperDigest = hash (.wrapper account.core) := by
  rcases (initialize_success_iff hash request observedProofAccount
    proofHeaderUploadAuthority signedUploadAuthority closeRefundAuthority pdaBump
    account).mp success with ⟨_, rfl⟩
  simp [pendingAccount, pendingCore, sealAccount, zeroReserved, reservedBytes, Sealed]

theorem initialize_success_is_canonical_pending
    (hash : HashFn) (request : Request)
    (observedProofAccount proofHeaderUploadAuthority : PublicKey)
    (signedUploadAuthority : Option PublicKey)
    (closeRefundAuthority : PublicKey) (pdaBump : Nat) (account : Account)
    (success : initializeAccount hash request observedProofAccount proofHeaderUploadAuthority
      signedUploadAuthority closeRefundAuthority pdaBump = some account) :
    CanonicalPending hash account := by
  rcases (initialize_success_iff hash request observedProofAccount
    proofHeaderUploadAuthority signedUploadAuthority closeRefundAuthority pdaBump
    account).mp success with ⟨authorized, rfl⟩
  rcases authorized with ⟨_, _, uploadNonzero, closeNonzero⟩
  simp [CanonicalPending, CanonicalHeader, Sealed, pendingAccount, pendingCore,
    sealAccount, uploadNonzero, closeNonzero]

theorem initialize_success_binds_exact_pda_inputs
    (hash : HashFn) (request : Request)
    (observedProofAccount proofHeaderUploadAuthority : PublicKey)
    (signedUploadAuthority : Option PublicKey)
    (closeRefundAuthority : PublicKey) (pdaBump : Nat) (account : Account)
    (success : initializeAccount hash request observedProofAccount proofHeaderUploadAuthority
      signedUploadAuthority closeRefundAuthority pdaBump = some account) :
    account.pdaInputs = {
      staticSeed := receiptPdaSeed
      proofAccount := request.binding.proofAccount
      statementDigest := request.binding.statementDigest
      bindingDigest := hash (.binding request.binding)
      bump := pdaBump
    } := by
  rcases (initialize_success_iff hash request observedProofAccount
    proofHeaderUploadAuthority signedUploadAuthority closeRefundAuthority pdaBump
    account).mp success with ⟨_, rfl⟩
  rfl

def CanFinalize (hash : HashFn) (pending : Account) (request : Request)
    (receipt : Receipt) : Prop :=
  CanonicalPending hash pending ∧
    ExactRequestBinding hash pending request ∧
    receipt.binding = request.binding ∧
    receipt.pdaBump = pending.core.pdaBump

instance instDecidableCanFinalize (hash : HashFn) (pending : Account)
    (request : Request) (receipt : Receipt) :
    Decidable (CanFinalize hash pending request receipt) := by
  unfold CanFinalize CanonicalPending CanonicalHeader Sealed ExactRequestBinding
  infer_instance

def finalizedCore (pending : Account) (receipt : Receipt) : AccountCore :=
  { pending.core with
    status := .verified
    verifiedSlot := receipt.verifiedSlot
    body := .asva receipt }

def finalizedAccount (hash : HashFn) (pending : Account) (receipt : Receipt) : Account :=
  sealAccount hash (finalizedCore pending receipt)

def finalizeAccount (hash : HashFn) (pending : Account) (request : Request)
    (receipt : Receipt) : Option Account :=
  if CanFinalize hash pending request receipt then
    some (finalizedAccount hash pending receipt)
  else
    none

theorem finalize_success_iff (hash : HashFn) (pending : Account)
    (request : Request) (receipt : Receipt) (finalized : Account) :
    finalizeAccount hash pending request receipt = some finalized ↔
      CanFinalize hash pending request receipt ∧
        finalized = finalizedAccount hash pending receipt := by
  by_cases allowed : CanFinalize hash pending request receipt
  · simp only [finalizeAccount, allowed, if_true, Option.some.injEq, true_and]
    exact eq_comm
  · simp [finalizeAccount, allowed]

theorem finalize_success_is_one_way_and_nested_exact
    (hash : HashFn) (pending : Account) (request : Request)
    (receipt : Receipt) (finalized : Account)
    (success : finalizeAccount hash pending request receipt = some finalized) :
    pending.core.status = .pending ∧
      finalized.core.status = .verified ∧
      finalized.core.verifiedSlot = receipt.verifiedSlot ∧
      finalized.core.body = .asva receipt ∧
      receipt.binding = request.binding ∧
      receipt.pdaBump = finalized.core.pdaBump := by
  rcases (finalize_success_iff hash pending request receipt finalized).mp success with
    ⟨allowed, rfl⟩
  rcases allowed with ⟨canonical, _, bindingExact, bumpExact⟩
  refine ⟨canonical.2.2.1, ?_⟩
  simp [finalizedAccount, finalizedCore, sealAccount, bindingExact, bumpExact]

theorem finalize_success_preserves_every_immutable_field
    (hash : HashFn) (pending : Account) (request : Request)
    (receipt : Receipt) (finalized : Account)
    (success : finalizeAccount hash pending request receipt = some finalized) :
    finalized.core.immutableFields = pending.core.immutableFields := by
  rcases (finalize_success_iff hash pending request receipt finalized).mp success with
    ⟨_, rfl⟩
  simp [AccountCore.immutableFields, finalizedAccount, finalizedCore, sealAccount]

theorem finalize_success_is_canonical_and_request_exact
    (hash : HashFn) (pending : Account) (request : Request)
    (receipt : Receipt) (finalized : Account)
    (success : finalizeAccount hash pending request receipt = some finalized) :
    CanonicalFinalized hash finalized ∧
      ExactRequestBinding hash finalized request ∧
      receipt.binding = request.binding := by
  rcases (finalize_success_iff hash pending request receipt finalized).mp success with
    ⟨allowed, rfl⟩
  rcases allowed with
    ⟨⟨header, _, _, _, _⟩, requestExact, bindingExact, bumpExact⟩
  rcases requestExact with
    ⟨verifierExact, proofExact, statementExact, bindingDigestExact,
      requestDigestExact⟩
  have headerFinal : CanonicalHeader (finalizedAccount hash pending receipt).core := by
    simpa [CanonicalHeader, finalizedAccount, finalizedCore, sealAccount] using header
  have requestFinal :
      ExactRequestBinding hash (finalizedAccount hash pending receipt) request := by
    simpa [ExactRequestBinding, finalizedAccount, finalizedCore, sealAccount] using
      (show ExactRequestBinding hash pending request from
        ⟨verifierExact, proofExact, statementExact, bindingDigestExact,
          requestDigestExact⟩)
  refine ⟨?_, requestFinal, bindingExact⟩
  refine ⟨headerFinal, ?_, ?_⟩
  · rfl
  · change
      (finalizedAccount hash pending receipt).core.status = .verified ∧
        (finalizedAccount hash pending receipt).core.verifiedSlot = receipt.verifiedSlot ∧
        receipt.pdaBump = (finalizedAccount hash pending receipt).core.pdaBump ∧
        receipt.binding.verifierProgram =
          (finalizedAccount hash pending receipt).core.verifierProgram ∧
        receipt.binding.proofAccount =
          (finalizedAccount hash pending receipt).core.proofAccount ∧
        receipt.binding.statementDigest =
          (finalizedAccount hash pending receipt).core.statementDigest ∧
        hash (.binding receipt.binding) =
          (finalizedAccount hash pending receipt).core.bindingDigest
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [finalizedAccount, finalizedCore, sealAccount]
    · simp [finalizedAccount, finalizedCore, sealAccount]
    · simpa [finalizedAccount, finalizedCore, sealAccount] using bumpExact
    · change receipt.binding.verifierProgram = pending.core.verifierProgram
      rw [bindingExact]
      exact verifierExact.symm
    · change receipt.binding.proofAccount = pending.core.proofAccount
      rw [bindingExact]
      exact proofExact.symm
    · change receipt.binding.statementDigest = pending.core.statementDigest
      rw [bindingExact]
      exact statementExact.symm
    · change hash (.binding receipt.binding) = pending.core.bindingDigest
      rw [bindingExact]
      exact bindingDigestExact.symm

theorem verified_account_cannot_finalize (hash : HashFn) (account : Account)
    (request : Request) (receipt : Receipt)
    (verified : account.core.status = .verified) :
    finalizeAccount hash account request receipt = none := by
  have rejected : ¬ CanFinalize hash account request receipt := by
    intro allowed
    have pendingStatus := allowed.1.2.2.1
    rw [verified] at pendingStatus
    cases pendingStatus
  simp [finalizeAccount, rejected]

theorem finalize_success_cannot_finalize_again
    (hash : HashFn) (pending : Account) (request nextRequest : Request)
    (receipt nextReceipt : Receipt) (finalized : Account)
    (success : finalizeAccount hash pending request receipt = some finalized) :
    finalizeAccount hash finalized nextRequest nextReceipt = none := by
  apply verified_account_cannot_finalize
  exact (finalize_success_is_one_way_and_nested_exact hash pending request receipt
    finalized success).2.1

def CanClose (hash : HashFn) (account : Account)
    (signedCloseAuthority : Option PublicKey) (refundDestination : PublicKey) : Prop :=
  CanonicalAccount hash account ∧
    signedCloseAuthority = some account.core.closeRefundAuthority ∧
    refundDestination = account.core.closeRefundAuthority

instance instDecidableCanonicalAccount (hash : HashFn) (account : Account) :
    Decidable (CanonicalAccount hash account) := by
  unfold CanonicalAccount CanonicalPending CanonicalFinalized CanonicalHeader Sealed
  cases bodyExact : account.core.body <;> simp only [bodyExact] <;> infer_instance

instance instDecidableCanClose (hash : HashFn) (account : Account)
    (signedCloseAuthority : Option PublicKey) (refundDestination : PublicKey) :
    Decidable (CanClose hash account signedCloseAuthority refundDestination) := by
  unfold CanClose
  infer_instance

def authorizeClose (hash : HashFn) (account : Account)
    (signedCloseAuthority : Option PublicKey)
    (refundDestination : PublicKey) : Option CloseAuthorization :=
  if CanClose hash account signedCloseAuthority refundDestination then
    some {
      closeAuthority := account.core.closeRefundAuthority
      refundDestination := refundDestination
    }
  else
    none

theorem canonical_account_close_authorized (hash : HashFn) (account : Account)
    (canonical : CanonicalAccount hash account) :
    authorizeClose hash account (some account.core.closeRefundAuthority)
        account.core.closeRefundAuthority =
      some {
        closeAuthority := account.core.closeRefundAuthority
        refundDestination := account.core.closeRefundAuthority
      } := by
  simp [authorizeClose, CanClose, canonical]

theorem authorize_close_success_binds_authority_and_refund
    (hash : HashFn) (account : Account)
    (signedCloseAuthority : Option PublicKey) (refundDestination : PublicKey)
    (authorization : CloseAuthorization)
    (success : authorizeClose hash account signedCloseAuthority refundDestination =
      some authorization) :
    CanonicalAccount hash account ∧
      signedCloseAuthority = some account.core.closeRefundAuthority ∧
      refundDestination = account.core.closeRefundAuthority ∧
      authorization.closeAuthority = account.core.closeRefundAuthority ∧
      authorization.refundDestination = refundDestination := by
  unfold authorizeClose at success
  by_cases allowed : CanClose hash account signedCloseAuthority refundDestination
  · have authorizationExact :
        ({ closeAuthority := account.core.closeRefundAuthority
           refundDestination := refundDestination } : CloseAuthorization) = authorization := by
      exact Option.some.inj (by simpa [allowed] using success)
    rw [← authorizationExact]
    exact ⟨allowed.1, allowed.2.1, allowed.2.2, rfl, rfl⟩
  · simp [allowed] at success

/-- The close gate returns the original account rather than a rewritten
account.  Deletion/refund is deliberately outside this pure state machine. -/
def closeAuthorizationStep (hash : HashFn) (account : Account)
    (signedCloseAuthority : Option PublicKey)
    (refundDestination : PublicKey) : Option (CloseAuthorization × Account) :=
  match authorizeClose hash account signedCloseAuthority refundDestination with
  | none => none
  | some authorization => some (authorization, account)

theorem close_authorization_does_not_mutate
    (hash : HashFn) (account after : Account)
    (signedCloseAuthority : Option PublicKey) (refundDestination : PublicKey)
    (authorization : CloseAuthorization)
    (success : closeAuthorizationStep hash account signedCloseAuthority
      refundDestination = some (authorization, after)) :
    after = account := by
  cases accepted : authorizeClose hash account signedCloseAuthority refundDestination with
  | none =>
      simp [closeAuthorizationStep, accepted] at success
  | some acceptedAuthorization =>
      have pairExact : (acceptedAuthorization, account) = (authorization, after) := by
        exact Option.some.inj (by simpa [closeAuthorizationStep, accepted] using success)
      exact (congrArg Prod.snd pairExact).symm

#print axioms exact_account_layout
#print axioms zero_body_is_exact_432_bytes
#print axioms initialize_success_iff
#print axioms initialize_success_binds_preinitialization_authority
#print axioms initialize_success_has_exact_pending_fields
#print axioms initialize_success_is_canonical_pending
#print axioms initialize_success_binds_exact_pda_inputs
#print axioms finalize_success_iff
#print axioms finalize_success_is_one_way_and_nested_exact
#print axioms finalize_success_preserves_every_immutable_field
#print axioms finalize_success_is_canonical_and_request_exact
#print axioms verified_account_cannot_finalize
#print axioms finalize_success_cannot_finalize_again
#print axioms canonical_account_close_authorized
#print axioms authorize_close_success_binds_authority_and_refund
#print axioms close_authorization_does_not_mutate

end AspisPool.AuthorizationReceiptAccountV1
