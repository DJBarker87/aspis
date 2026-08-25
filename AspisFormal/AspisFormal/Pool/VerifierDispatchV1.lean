import Mathlib.Data.Nat.Basic

/-!
# Pool V1 authenticated verifier dispatch

Pure P3d/P3e model of the variable-length `ASVQ` request, fixed `ASVS` result
and read-only clear/invoke/capture control flow.
The request is a 384-byte binding prefix followed by the complete canonical
profile-specific statement payload. The Pool derives the statement digest from
the selected profile/release and exact payload; `ASVS` echoes the digest and
payload length, but not the payload bytes.

Payload substitution is not ruled out by assuming SHA-256 injective. Instead,
the theorem below proves that one success result authenticating two distinct
payloads implies an explicit approved-hash collision (and equal payload
length). SHA-256 collision resistance, Rust/source refinement, profile-specific
payload parsing, CPI and Solana return-data authenticity remain named external
boundaries.
-/

set_option autoImplicit false

namespace AspisPool.VerifierDispatchV1

def bindingPrefixBytes : Nat := 384
def maxPayloadBytes : Nat := 640
def maxRequestBytes : Nat := 1024
def resultBytes : Nat := 384
def solanaReturnDataMaxBytes : Nat := 1024
def successCode : Nat := 0x41530001

inductive TransitionKind where
  | privateTransfer
  | withdrawal
  deriving DecidableEq, Repr

/-- Full semantic inventory repeated between the request prefix and result. -/
structure Binding (Program Profile Release Digest Account Pool Domain : Type) where
  statementVersion : Nat
  transitionKind : TransitionKind
  verifierProgram : Program
  profile : Profile
  release : Release
  pool : Pool
  deploymentDomain : Domain
  anchorSequence : Nat
  anchorRoot : Digest
  nullifier : Digest
  statementDigest : Digest
  envelopeDigest : Digest
  proofAccount : Account
  proofBodyDigest : Digest
  proofBodyLength : Nat
  statementPayloadLength : Nat
  deriving DecidableEq, Repr

structure Request (BindingType Payload : Type) where
  binding : BindingType
  payload : Payload
  deriving DecidableEq, Repr

structure Result (BindingType : Type) where
  code : Nat
  binding : BindingType
  deriving DecidableEq, Repr

def validPayloadLength {Payload : Type} (length : Payload → Nat) (payload : Payload) : Prop :=
  0 < length payload ∧ length payload ≤ maxPayloadBytes

def requestBytes {Payload : Type} (length : Payload → Nat) (payload : Payload) : Nat :=
  bindingPrefixBytes + length payload

theorem valid_payload_fits_request_cap {Payload : Type}
    (length : Payload → Nat) (payload : Payload)
    (valid : validPayloadLength length payload) :
    requestBytes length payload ≤ maxRequestBytes := by
  calc
    requestBytes length payload = 384 + length payload := rfl
    _ ≤ 384 + 640 := Nat.add_le_add_left valid.2 384
    _ = maxRequestBytes := rfl

theorem result_contract_fits_return_data :
    resultBytes ≤ solanaReturnDataMaxBytes := by
  decide

/-- Digest and length fields derived from the exact payload under the selected
profile/release context. `hash` abstracts the frozen domain-separated SHA-256
preimage used by Rust. -/
structure PayloadBinding (Profile Release Digest : Type) where
  statementVersion : Nat
  profile : Profile
  release : Release
  statementDigest : Digest
  statementPayloadLength : Nat
  deriving DecidableEq, Repr

def derivePayloadBinding {Profile Release Digest Payload : Type}
    (hash : Nat → Profile → Release → Payload → Digest)
    (length : Payload → Nat) (statementVersion : Nat)
    (profile : Profile) (release : Release) (payload : Payload) :
    PayloadBinding Profile Release Digest :=
  { statementVersion
    profile
    release
    statementDigest := hash statementVersion profile release payload
    statementPayloadLength := length payload }

def PayloadCollision {Profile Release Digest Payload : Type}
    (hash : Nat → Profile → Release → Payload → Digest)
    (statementVersion : Nat) (profile : Profile) (release : Release)
    (left right : Payload) : Prop :=
  left ≠ right ∧
    hash statementVersion profile release left =
      hash statementVersion profile release right

/-- Pure model after exact-size parsing and returning-program-id validation. -/
def accepts {Program BindingType : Type}
    (returningProgram selectedProgram : Program)
    (expectedBinding : BindingType) (returned : Result BindingType) : Prop :=
  returningProgram = selectedProgram ∧
    returned.code = successCode ∧
    returned.binding = expectedBinding

theorem accepted_result_binds_program_code_and_request
    {Program BindingType : Type}
    (returningProgram selectedProgram : Program)
    (expectedBinding : BindingType) (returned : Result BindingType)
    (accepted : accepts returningProgram selectedProgram expectedBinding returned) :
    returningProgram = selectedProgram ∧
      returned.code = successCode ∧
      returned.binding = expectedBinding := by
  exact accepted

/-- One exact result cannot authenticate two distinct recomputed payload
bindings unless the frozen profile-selected hash collides. Equality also forces
the echoed payload lengths to match. -/
theorem distinct_payloads_one_result_implies_collision
    {Program Profile Release Digest Payload : Type}
    (hash : Nat → Profile → Release → Payload → Digest)
    (length : Payload → Nat) (statementVersion : Nat)
    (profile : Profile) (release : Release)
    (original substituted : Payload)
    (different : original ≠ substituted)
    (returningProgram selectedProgram : Program)
    (returned : Result (PayloadBinding Profile Release Digest))
    (originalAccepted : accepts returningProgram selectedProgram
      (derivePayloadBinding hash length statementVersion profile release original) returned)
    (substitutedAccepted : accepts returningProgram selectedProgram
      (derivePayloadBinding hash length statementVersion profile release substituted) returned) :
    PayloadCollision hash statementVersion profile release original substituted ∧
      length original = length substituted := by
  have bindingsEqual :
      derivePayloadBinding hash length statementVersion profile release original =
        derivePayloadBinding hash length statementVersion profile release substituted :=
    originalAccepted.2.2.symm.trans substitutedAccepted.2.2
  constructor
  · constructor
    · exact different
    · exact congrArg PayloadBinding.statementDigest bindingsEqual
  · exact congrArg PayloadBinding.statementPayloadLength bindingsEqual

theorem payload_substitution_rejected_without_collision
    {Program Profile Release Digest Payload : Type}
    (hash : Nat → Profile → Release → Payload → Digest)
    (length : Payload → Nat) (statementVersion : Nat)
    (profile : Profile) (release : Release)
    (original substituted : Payload)
    (different : original ≠ substituted)
    (noCollision : ¬ PayloadCollision hash statementVersion profile release original substituted)
    (returningProgram selectedProgram : Program)
    (returned : Result (PayloadBinding Profile Release Digest)) :
    ¬ (accepts returningProgram selectedProgram
        (derivePayloadBinding hash length statementVersion profile release original) returned ∧
      accepts returningProgram selectedProgram
        (derivePayloadBinding hash length statementVersion profile release substituted) returned) := by
  intro bothAccepted
  exact noCollision
    (distinct_payloads_one_result_implies_collision hash length statementVersion profile release
      original substituted different returningProgram selectedProgram returned
      bothAccepted.1 bothAccepted.2).1

/-! ## P3e read-only runtime control flow -/

inductive DispatchEvent where
  | clearReturnData
  | invokeSelectedVerifier
  | captureReturnData
  deriving DecidableEq, Repr

/-- There is no event between the selected CPI and return-data capture. -/
def successfulDispatchTrace : List DispatchEvent :=
  [.clearReturnData, .invokeSelectedVerifier, .captureReturnData]

theorem clear_invoke_capture_order_exact :
    successfulDispatchTrace =
      [.clearReturnData, .invokeSelectedVerifier, .captureReturnData] := by
  rfl

/-- Abstract return-data buffer after the Pool explicitly clears it and the
callee either supplies a new result or supplies nothing. -/
def capturedAfterClear {ResultData : Type}
    (_stale : Option ResultData) (calleeResult : Option ResultData) : Option ResultData :=
  calleeResult

theorem missing_callee_result_cannot_reuse_stale {ResultData : Type}
    (stale : Option ResultData) :
    capturedAfterClear stale none = none := by
  rfl

inductive DispatchOutcome (Program ResultData : Type) where
  | cpiError
  | missingReturnData
  | captured (program : Program) (data : ResultData)
  deriving DecidableEq, Repr

/-- P3e has no Pool-state transition: success and every error outcome return
the identical abstract Pool state. -/
def readonlyDispatchState {PoolState Program ResultData : Type}
    (state : PoolState) (_outcome : DispatchOutcome Program ResultData) : PoolState :=
  state

theorem readonly_dispatch_never_writes_pool_state
    {PoolState Program ResultData : Type}
    (state : PoolState) (outcome : DispatchOutcome Program ResultData) :
    readonlyDispatchState state outcome = state := by
  rfl

/-- Named obligations for connecting Rust/profile parsing and Solana execution
to the pure collision-explicit model. -/
structure SourceRuntimeBoundary where
  domainSeparatedSha256MatchesRuntime : Prop
  approvedSha256CollisionBound : Prop
  poolComputesDigestFromExactPayload : Prop
  selectedVerifierRecomputesDigestFromExactPayload : Prop
  selectedProfileParsesCompleteCanonicalStatement : Prop
  registryEnvelopeAndProofRustParsingMatchesModel : Prop
  supportedLoaderImpliesIntendedExecutable : Prop
  productionSourceMatchesClearInvokeCaptureTrace : Prop
  emptySetReturnDataClearsRuntimeBuffer : Prop
  cpiInvokesOnlySelectedVerifier : Prop
  readonlyMetaPreventsVerifierAccountWrites : Prop
  returnDataSnapshotIsImmediateAfterCpi : Prop
  returnDataProgramIdAndExact384BytesChecked : Prop
  acceptedResultComposedAtomicallyWithPoolWrites : Prop

#print axioms valid_payload_fits_request_cap
#print axioms result_contract_fits_return_data
#print axioms accepted_result_binds_program_code_and_request
#print axioms distinct_payloads_one_result_implies_collision
#print axioms payload_substitution_rejected_without_collision
#print axioms clear_invoke_capture_order_exact
#print axioms missing_callee_result_cannot_reuse_stale
#print axioms readonly_dispatch_never_writes_pool_state

end AspisPool.VerifierDispatchV1
