import AspisFormal.K1.V7Tag73FutureFreeFullControl
import AspisFormal.K1.V7Tag73RawProverMessages
import AspisFormal.K1.V7Tag73FixedFieldMessageBridge

/-!
# Raw same-tape source for the Tag-73 compiler

The older operational replay stack lets the adversary return a
`ParsedTag73Proof` containing a completed `ConcreteDagInstance`.  That is a
useful record for checking one already completed fixed-table execution, but it
is not the result type of a noninteractive prover: the DAG contains verifier-
derived challenges, sampler stopping points, circle points and q16 search
data.  Carrying that object through a rewind freezes precisely the future data
that may change after lambda or chi is reprogrammed.

This module gives the same-tape black box its correct result type.  The result
contains the public instance, opaque raw proof/payload, and only the
prover-controlled Tag-73 messages.  The future-free verifier reconstructs all
coins and query schedules from its own oracle replies.  No verifier result,
acceptance fact, restoration function, DAG, or extraction conclusion is a
field.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73RawSameTapeSource

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73RawProverMessages
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73ResumeDerivedReplayNode
open AspisK1.V7Tag73FixedFieldMessageBridge
open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-! ## The actual prover return -/

/-- Parsed prover-owned bytes.  `messages` contains neither challenges nor a
query DAG; `rawProof` and `auxiliary` retain the application parser's opaque
result without giving K1.6 any conclusion-shaped projection from it. -/
structure RawTag73ParsedProof (Proof Payload : Type*) where
  rawProof : Proof
  auxiliary : Payload
  messages : RawTag73ProverMessages

/-- One public raw Tag-73 result returned by the black-box prover. -/
structure RawTag73AdversaryReturnedValue
    (Statement Proof Payload : Type*) where
  publicProof : PublicProof Statement (RawTag73ParsedProof Proof Payload)

/-- The parser-side public-instance check.  It is executable and fixes the
program, release, statement, attempt and proof-account context before any
verifier-derived challenge exists. -/
def contextFieldsMatch (left right : Context) : Bool :=
  decide (left.programId = right.programId) &&
    decide (left.releaseBinding = right.releaseBinding) &&
    decide (left.statementDigest = right.statementDigest) &&
    decide (left.attemptId = right.attemptId)

private theorem context_eq_of_fields {left right : Context}
    (program : left.programId = right.programId)
    (release : left.releaseBinding = right.releaseBinding)
    (statement : left.statementDigest = right.statementDigest)
    (attempt : left.attemptId = right.attemptId) : left = right := by
  cases left
  cases right
  simp_all

def rawReturnedValueContextMatches
    {Statement Proof Payload : Type*}
    (value : RawTag73AdversaryReturnedValue Statement Proof Payload) : Bool :=
  contextFieldsMatch value.publicProof.proof.messages.context
    value.publicProof.publicInstance.context

abbrev CheckedRawTag73AdversaryReturnedValue
    (Statement Proof Payload : Type*) :=
  {value : RawTag73AdversaryReturnedValue Statement Proof Payload //
    rawReturnedValueContextMatches value = true ∧
      ∃ decoded : Fin 641 → QM31Exact,
        FixedFieldDecodeExact value.publicProof.proof.messages decoded}

theorem checked_raw_return_context_is_exact
    {Statement Proof Payload : Type*}
    (value : CheckedRawTag73AdversaryReturnedValue Statement Proof Payload) :
    value.1.publicProof.proof.messages.context =
      value.1.publicProof.publicInstance.context := by
  have checked := value.2.1
  simp only [rawReturnedValueContextMatches, contextFieldsMatch,
    Bool.and_eq_true, decide_eq_true_eq] at checked
  have program := checked.1.1.1
  have release := checked.1.1.2
  have statement := checked.1.2
  have attempt := checked.2
  exact context_eq_of_fields program release statement attempt

/-- Every value admitted by the checked raw-prover interface has the exact
canonical 641-field decoding performed by the deployed packed reader.  This
is a parser refinement, not a knowledge or soundness assumption: the
current-source Aeneas bridge constructs it from literal reader success. -/
theorem checked_raw_return_has_exact_fixed_field_decode
    {Statement Proof Payload : Type*}
    (value : CheckedRawTag73AdversaryReturnedValue Statement Proof Payload) :
    ∃ decoded : Fin 641 → QM31Exact,
      FixedFieldDecodeExact value.1.publicProof.proof.messages decoded := by
  exact value.2.2

/-- There is no projection from the raw result to verifier-derived values.
This positive theorem records the complete prover-controlled projection used
by the future-free interpreter. -/
def CheckedRawTag73AdversaryReturnedValue.rawMessages
    {Statement Proof Payload : Type*}
    (value : CheckedRawTag73AdversaryReturnedValue Statement Proof Payload) :
    RawTag73ProverMessages :=
  value.1.publicProof.proof.messages

/-! ## Same-hidden-tape source -/

structure RawTag73SameTapeSource
    (HiddenTape TapeIdentity Observation Statement Proof Payload : Type*) where
  blackBox : SameTapeBlackBox HiddenTape Observation
    (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload)
  hiddenTape : HiddenTape
  tapeIdentity : TapeIdentity
  observation : Observation
  controller : AdaptiveController
  oracleLimits : OracleLimits
  firstRunFuel : Nat
  initialOracle : OracleState

def RawTag73SameTapeSource.capability
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload) :
    SameTapeStartCapability TapeIdentity Observation
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload) :=
  closeSameTapeStart source.blackBox source.hiddenTape source.tapeIdentity

def RawTag73SameTapeSource.firstExecution
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload) :
    MachineRun (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload) :=
  runMachine source.controller source.oracleLimits .adversary
    source.firstRunFuel source.initialOracle
      (source.capability.start source.observation)

/-- The generic same-tape origin generated from the raw source.  The forgery
projection is the actually returned public raw proof; it does not inspect or
assume a verifier decision. -/
def RawTag73SameTapeSource.toOriginSource
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload) :
    AspisK1.V7Tag73ConcreteKnowledgeInsertion.SameTapeOriginSource
      HiddenTape TapeIdentity Observation Statement
      (RawTag73ParsedProof Proof Payload)
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload) where
  blackBox := source.blackBox
  hiddenTape := source.hiddenTape
  tapeIdentity := source.tapeIdentity
  observation := source.observation
  controller := source.controller
  oracleLimits := source.oracleLimits
  firstRunFuel := source.firstRunFuel
  initialOracle := source.initialOracle
  forgeryOf value := some value.1.publicProof

@[simp] theorem raw_origin_first_execution_is_source_execution
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload) :
    source.toOriginSource.origin.firstExecution = source.firstExecution := by
  rfl

@[simp] theorem raw_origin_forgery_of_returned_value
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (value : CheckedRawTag73AdversaryReturnedValue Statement Proof Payload) :
    source.toOriginSource.forgeryOf value = some value.1.publicProof := by
  rfl

@[simp] theorem raw_source_capability_uses_same_hidden_tape
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload) :
    source.capability.start source.observation =
      source.blackBox.start source.hiddenTape source.observation := by
  rfl

@[simp] theorem raw_source_capability_identity
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload) :
    source.capability.tapeIdentity = source.tapeIdentity := by
  rfl

/-! ## Raw messages drive prover-owned future-free slots -/

def rawPayloadAt (raw : RawTag73ProverMessages) :
    FutureFreePayloadSite → Payload
  | .initialMaskClaim => .initialMaskClaim raw.initialClaim
  | .semanticRound round => .semanticRound round (raw.semanticSent round)
  | .pointClaims => .pointClaims raw.pointClaims
  | .inactiveClaim => .inactiveClaim raw.inactiveClaim
  | .circleOodValue sample => .circleOodValue sample (raw.oodValue sample)
  | .relationRound round => .relationRound round (raw.relationSent round)
  | .final256 => .final256 raw.finalValues
  | .queryBatchClaim => .queryBatchClaim raw.queryBatchClaim

@[simp] theorem raw_payload_matches_its_exact_site
    (raw : RawTag73ProverMessages) (site : FutureFreePayloadSite) :
    payloadMatchesSite site (rawPayloadAt raw site) = true := by
  cases site <;> simp [rawPayloadAt, payloadMatchesSite]

def rawWorkNonceAt (raw : RawTag73ProverMessages) : WorkStage → NonceBytes
  | .batch => raw.batchNonce
  | .fold => raw.foldNonce
  | .final => raw.finalNonce

@[simp] theorem raw_work_nonce_payload_is_exact
    (raw : RawTag73ProverMessages) (stage : WorkStage) :
    workNoncePayload stage (rawWorkNonceAt raw stage) =
      match stage with
      | .batch => .batchNonce raw.batchNonce
      | .fold => .foldNonce raw.foldNonce
      | .final => .finalNonce raw.finalNonce := by
  cases stage <;> rfl

def rawC1Root (raw : RawTag73ProverMessages) :
    TypedMerkleRoot .initialC1 :=
  ⟨raw.c1Root⟩

@[simp] theorem raw_c1_root_value (raw : RawTag73ProverMessages) :
    (rawC1Root raw).value = raw.c1Root := by
  rfl

/-- C2 is indexed only when the live verifier has decoded its current pair.
Changing either live challenge never requires transporting a whole future
proof value. -/
theorem raw_c2_submission_is_live_pair_indexed
    (raw : RawTag73ProverMessages)
    (lambda chi : Qm31Bytes) :
    (raw.c2Commitment lambda chi).root = raw.c2Root := by
  rfl

/-! ## The only prover-driven transitions -/

/-- A raw result can act only when the future-free verifier is explicitly
waiting for a prover-owned value.  All challenge and q16 states return
`none`; those steps belong to the verifier/public-coin machine. -/
def submitNextRawMessage (raw : RawTag73ProverMessages)
    (state : FutureFreeVerifierState) : Option FutureFreeVerifierState :=
  match controlEq : state.current.control with
  | .adaptive .awaitingC1 =>
      submitFutureFreeC1 state (rawC1Root raw)
  | .adaptive (.awaitingC2 lambda chi) =>
      some (submitFutureFreeC2 state lambda chi
        (raw.c2Commitment lambda chi) controlEq)
  | .linear (.payload site :: _) =>
      submitFutureFreePayload state (rawPayloadAt raw site)
  | .linear (.work stage :: _) =>
      submitFutureFreeWorkNonce state (rawWorkNonceAt raw stage)
  | _ => none

/-- Every raw prover submission retains the fixed public instance carried by
the live verifier snapshot. -/
theorem successful_raw_submission_preserves_bindings
    (raw : RawTag73ProverMessages)
    (state next : FutureFreeVerifierState)
    (submitted : submitNextRawMessage raw state = some next) :
    next.current.bindings = state.current.bindings := by
  unfold submitNextRawMessage at submitted
  split at submitted <;>
    simp_all [submitFutureFreeC1, submitFutureFreeC2,
      submitFutureFreePayload, submitFutureFreeWorkNonce,
      appendFutureFreeSnapshot]
  all_goals subst next <;> rfl

private theorem successful_submit_c1_is_complete_append
    (state next : FutureFreeVerifierState)
    (root : TypedMerkleRoot .initialC1)
    (submitted : submitFutureFreeC1 state root = some next) :
    ∃ snapshot,
      next = appendFutureFreeSnapshot state (.proverC1 root) snapshot := by
  unfold submitFutureFreeC1 at submitted
  split at submitted
  next controlEq =>
    refine ⟨_, (Option.some.inj submitted).symm⟩
  all_goals simp at submitted

private theorem successful_submit_payload_is_complete_append
    (state next : FutureFreeVerifierState) (payload : Payload)
    (submitted : submitFutureFreePayload state payload = some next) :
    ∃ snapshot,
      next = appendFutureFreeSnapshot state (.proverPayload payload) snapshot := by
  unfold submitFutureFreePayload at submitted
  split at submitted
  next site remaining controlEq =>
    split at submitted
    next matched =>
      refine ⟨_, (Option.some.inj submitted).symm⟩
    all_goals simp at submitted
  all_goals simp at submitted

private theorem successful_submit_work_is_complete_append
    (state next : FutureFreeVerifierState) (nonce : NonceBytes)
    (submitted : submitFutureFreeWorkNonce state nonce = some next) :
    ∃ stage snapshot,
      next = appendFutureFreeSnapshot state
        (.proverWorkNonce stage nonce) snapshot := by
  unfold submitFutureFreeWorkNonce at submitted
  split at submitted
  next stage remaining controlEq =>
    exact ⟨stage, _, (Option.some.inj submitted).symm⟩
  all_goals simp at submitted

/-- Successful raw submission is always one literal complete-state append.
This exposes the operational shape used by history/restoration invariants. -/
theorem successful_raw_submission_is_complete_append
    (raw : RawTag73ProverMessages)
    (state next : FutureFreeVerifierState)
    (submitted : submitNextRawMessage raw state = some next) :
    ∃ event snapshot,
      next = appendFutureFreeSnapshot state event snapshot := by
  unfold submitNextRawMessage at submitted
  split at submitted
  next controlEq =>
    obtain ⟨snapshot, nextEq⟩ :=
      successful_submit_c1_is_complete_append state next (rawC1Root raw)
        submitted
    exact ⟨.proverC1 (rawC1Root raw), snapshot, nextEq⟩
  next lambda chi controlEq =>
    exact ⟨.proverC2 lambda chi (raw.c2Commitment lambda chi), _,
      (Option.some.inj submitted).symm⟩
  next site remaining controlEq =>
    obtain ⟨snapshot, nextEq⟩ :=
      successful_submit_payload_is_complete_append state next
        (rawPayloadAt raw site) submitted
    exact ⟨.proverPayload (rawPayloadAt raw site), snapshot, nextEq⟩
  next stage remaining controlEq =>
    obtain ⟨actualStage, snapshot, nextEq⟩ :=
      successful_submit_work_is_complete_append state next
        (rawWorkNonceAt raw stage) submitted
    exact ⟨.proverWorkNonce actualStage (rawWorkNonceAt raw stage),
      snapshot, nextEq⟩
  all_goals simp at submitted

/-! ## Fixed bindings are raw and challenge independent -/

theorem checked_raw_return_preserves_public_bindings
    {Statement Proof Payload : Type*}
    (value : CheckedRawTag73AdversaryReturnedValue Statement Proof Payload) :
    let bindings := FixedBindings.ofContext value.rawMessages.context
    bindings.programId = value.1.publicProof.publicInstance.context.programId ∧
      bindings.releaseBinding =
        value.1.publicProof.publicInstance.context.releaseBinding ∧
      bindings.statementDigest =
        value.1.publicProof.publicInstance.context.statementDigest ∧
      bindings.attemptId =
        value.1.publicProof.publicInstance.context.attemptId ∧
      bindings.proofAccountId =
        value.1.publicProof.publicInstance.context.attemptId := by
  unfold CheckedRawTag73AdversaryReturnedValue.rawMessages
  rw [checked_raw_return_context_is_exact value]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

#print axioms checked_raw_return_context_is_exact
#print axioms checked_raw_return_has_exact_fixed_field_decode
#print axioms raw_source_capability_uses_same_hidden_tape
#print axioms raw_source_capability_identity
#print axioms raw_origin_first_execution_is_source_execution
#print axioms raw_origin_forgery_of_returned_value
#print axioms raw_payload_matches_its_exact_site
#print axioms raw_work_nonce_payload_is_exact
#print axioms raw_c1_root_value
#print axioms raw_c2_submission_is_live_pair_indexed
#print axioms successful_raw_submission_preserves_bindings
#print axioms successful_raw_submission_is_complete_append
#print axioms checked_raw_return_preserves_public_bindings

end

end AspisK1.V7Tag73RawSameTapeSource
