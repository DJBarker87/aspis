import AspisFormal.Pool.VerifierDispatchV1

/-!
# Frozen Tag-73 read-only ASVQ profile

Small P3f grammar model for the opt-in selected-verifier handler.  This fixes
the profile payload length and every verifier-call policy input, binds all
duplicated outer/payload/account fields, and keeps statement/body substitution
behind explicit digest-collision predicates.  It does not model or claim the
future Pool historical-anchor or 1-to-2 relation.

Concrete byte parsing, SHA-256, sealed-ASPU parsing, the Rust verifier call and
Solana return-data behavior remain named source/runtime boundaries.
-/

set_option autoImplicit false

namespace AspisPool.V7Tag73ReadOnlyProfileV1

def bindingPrefixBytes : Nat := 384
def profilePayloadBytes : Nat := 392
def completeRequestBytes : Nat := 776
def atomicStatementBytes : Nat := 216
def proofBodyBytes : Nat := 30_504
def proofAccountHeaderBytes : Nat := 40
def exactProofAccountBytes : Nat := 30_544
def frontierNodes : Nat := 203
def profileVersion : Nat := 1
def proofSourceSealedAspu : Nat := 1
def checkAllWork : Nat := 1
def atomicStatementVersion : Nat := 4
def profileMagic : List Nat := [0x41, 0x37, 0x50, 0x31]

theorem exact_request_size :
    completeRequestBytes = bindingPrefixBytes + profilePayloadBytes := by
  decide

theorem exact_request_fits_dispatch_cap :
    completeRequestBytes ≤ AspisPool.VerifierDispatchV1.maxRequestBytes := by
  decide

theorem exact_proof_account_size :
    exactProofAccountBytes = proofAccountHeaderBytes + proofBodyBytes := by
  decide

/-- Fields already authenticated by the fixed ASVQ binding prefix. -/
structure OuterBinding (Program Release Account Digest : Type) where
  verifierProgram : Program
  release : Release
  proofAccount : Account
  proofBodyDigest : Digest
  proofBodyLength : Nat
  deriving DecidableEq, Repr

/-- The exact semantic inventory of the 392-byte P3f payload. -/
structure Payload (Program Release Account Digest Statement : Type) where
  magic : List Nat
  version : Nat
  proofSource : Nat
  workPolicy : Nat
  statementVersion : Nat
  frontierCount : Nat
  reserved : Nat
  proofBodyLength : Nat
  proofBodyDigest : Digest
  verifierProgram : Program
  release : Release
  attempt : Account
  atomicStatementDigest : Digest
  statement : Statement
  deriving DecidableEq, Repr

/-- The only account visible to the verifier-side ASVQ instruction. -/
structure ProofAccount (Program Account Body : Type) where
  key : Account
  owner : Program
  signer : Bool
  writable : Bool
  executable : Bool
  sealed : Bool
  totalDataBytes : Nat
  declaredBodyBytes : Nat
  body : Body
  deriving DecidableEq, Repr

/-- Non-cryptographic P3f grammar and duplication checks.  The two digest
equalities represent recomputation from the exact canonical statement/body;
they do not assume either hash is injective. -/
def Accepted
    {Program Release Account Digest Statement Body : Type}
    (frozenRelease : Release)
    (canonicalStatement : Statement → Prop)
    (atomicDigest : Statement → Digest)
    (bodyLength : Body → Nat)
    (bodyDigest : Body → Digest)
    (outer : OuterBinding Program Release Account Digest)
    (payload : Payload Program Release Account Digest Statement)
    (proof : ProofAccount Program Account Body) : Prop :=
  payload.magic = profileMagic ∧
  payload.version = profileVersion ∧
  payload.proofSource = proofSourceSealedAspu ∧
  payload.workPolicy = checkAllWork ∧
  payload.statementVersion = atomicStatementVersion ∧
  payload.frontierCount = frontierNodes ∧
  payload.reserved = 0 ∧
  payload.proofBodyLength = proofBodyBytes ∧
  payload.release = frozenRelease ∧
  canonicalStatement payload.statement ∧
  payload.atomicStatementDigest = atomicDigest payload.statement ∧
  payload.verifierProgram = outer.verifierProgram ∧
  payload.release = outer.release ∧
  payload.attempt = outer.proofAccount ∧
  payload.proofBodyDigest = outer.proofBodyDigest ∧
  payload.proofBodyLength = outer.proofBodyLength ∧
  proof.key = outer.proofAccount ∧
  proof.owner = outer.verifierProgram ∧
  proof.signer = false ∧
  proof.writable = false ∧
  proof.executable = false ∧
  proof.sealed = true ∧
  proof.totalDataBytes = exactProofAccountBytes ∧
  proof.declaredBodyBytes = proofBodyBytes ∧
  bodyLength proof.body = proofBodyBytes ∧
  bodyDigest proof.body = payload.proofBodyDigest

/-- Acceptance fixes the exact frozen verifier arguments and all duplicated
program/release/attempt/proof fields. -/
theorem accepted_fixes_frozen_call_and_account
    {Program Release Account Digest Statement Body : Type}
    (frozenRelease : Release)
    (canonicalStatement : Statement → Prop)
    (atomicDigest : Statement → Digest)
    (bodyLength : Body → Nat)
    (bodyDigest : Body → Digest)
    (outer : OuterBinding Program Release Account Digest)
    (payload : Payload Program Release Account Digest Statement)
    (proof : ProofAccount Program Account Body)
    (accepted : Accepted frozenRelease canonicalStatement atomicDigest bodyLength bodyDigest
      outer payload proof) :
    payload.frontierCount = 203 ∧
      payload.workPolicy = 1 ∧
      payload.release = frozenRelease ∧
      payload.verifierProgram = outer.verifierProgram ∧
      payload.attempt = proof.key ∧
      payload.proofBodyDigest = outer.proofBodyDigest ∧
      outer.proofBodyDigest = bodyDigest proof.body ∧
      proof.owner = outer.verifierProgram ∧
      proof.totalDataBytes = 30_544 ∧
      proof.signer = false ∧ proof.writable = false ∧ proof.executable = false := by
  rcases accepted with
    ⟨_, _, _, hWork, _, hFrontier, _, _, hRelease, _, _, hProgram, _, hAttempt,
      hProofDigest, _, hProofKey, hOwner, hSigner, hWritable, hExecutable, _, hTotal,
      _, _, hBodyDigest⟩
  exact ⟨hFrontier, hWork, hRelease, hProgram, hAttempt.trans hProofKey.symm,
    hProofDigest, hProofDigest.symm.trans hBodyDigest.symm, hOwner, hTotal, hSigner,
    hWritable, hExecutable⟩

def DigestCollision {Message Digest : Type}
    (hash : Message → Digest) (left right : Message) : Prop :=
  left ≠ right ∧ hash left = hash right

/-- A changed canonical statement cannot retain one recomputed inner digest
without crossing the approved atomic-statement SHA-256 collision boundary. -/
theorem distinct_statements_one_inner_digest_implies_collision
    {Statement Digest : Type}
    (hash : Statement → Digest) (left right : Statement) (claimed : Digest)
    (different : left ≠ right)
    (leftAccepted : claimed = hash left)
    (rightAccepted : claimed = hash right) :
    DigestCollision hash left right := by
  exact ⟨different, leftAccepted.symm.trans rightAccepted⟩

/-- The same explicit boundary is retained for substitution of the exact
30,504-byte proof body. -/
theorem distinct_bodies_one_digest_implies_collision
    {Body Digest : Type}
    (hash : Body → Digest) (left right : Body) (claimed : Digest)
    (different : left ≠ right)
    (leftAccepted : claimed = hash left)
    (rightAccepted : claimed = hash right) :
    DigestCollision hash left right := by
  exact ⟨different, leftAccepted.symm.trans rightAccepted⟩

/-- Named refinement and runtime obligations intentionally not manufactured as
Lean theorems by this byte-grammar model. -/
structure SourceRuntimeBoundary where
  rustPayloadParserMatchesExact392ByteGrammar : Prop
  rustAtomicStatementParserMatchesCanonical216Bytes : Prop
  sha256SyscallMatchesDigestModel : Prop
  sealedAspuParserMatchesExactAccountModel : Prop
  frozenTag73VerifierSourceMatchesAcceptedProofPredicate : Prop
  frozenTag73CryptographicSecurityInterfacesHold : Prop
  solanaProgramIdentityAndReadonlyAccountSemanticsHold : Prop
  returnDataIsSetOnlyAfterFullVerifierAcceptance : Prop

#print axioms exact_request_size
#print axioms exact_request_fits_dispatch_cap
#print axioms exact_proof_account_size
#print axioms accepted_fixes_frozen_call_and_account
#print axioms distinct_statements_one_inner_digest_implies_collision
#print axioms distinct_bodies_one_digest_implies_collision

end AspisPool.V7Tag73ReadOnlyProfileV1
