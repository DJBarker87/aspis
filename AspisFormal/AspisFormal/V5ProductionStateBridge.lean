import AspisFormal.V5TheftStateTransitionReduction

/-!
# Production V5 account and state bridge

This file makes the deterministic, security-relevant projection of the
production V5 state transition explicit.  It records the exact five-account
order used by the spend, the two-account prefix used by the later proof close,
and the pool, marker, and proof-lifecycle fields changed on success.  It also
keeps the mainnet source and the current source separate:
the mainnet source checked the canonical marker address, while the current
source additionally rejects a canonical derivation whose numeric bump is not
255.

The functions below are executable Lean models of a selected projection of the
source control flow.  They do not model payer debits, marker rent/ownership
during the System Program CPI, raw account byte arrays, or every Rust error.
They are not a translation of Solana's `AccountInfo`, the System Program, or
the runtime.  Equality between the selected Rust and these projections, PDA
and System Program behavior, account locking, transaction rollback,
persistence, and finality remain individually named boundaries at the end of
the file.
-/

namespace AspisV5ProductionStateBridge

open AspisV5NullifierMarkerReplay
open AspisV5TheftStateTransitionReduction

/-! ## Exact account positions -/

/-- The five roles read by
`verify_and_apply_atomic_payment_state_traced_inner`. -/
inductive SpendAccountRole where
  | proof
  | pool
  | marker
  | payer
  | systemProgram
  deriving DecidableEq, Fintype

def spendAccountOrder : List SpendAccountRole :=
  [.proof, .pool, .marker, .payer, .systemProgram]

theorem spend_account_order_length : spendAccountOrder.length = 5 := by
  rfl

theorem spend_account_roles_are_exactly_once :
    spendAccountOrder.Nodup ∧
      ∀ role : SpendAccountRole, role ∈ spendAccountOrder := by
  decide

/-- The two roles consumed, in order, by `close_proof`.  The Rust close
handler reads this prefix and does not reject additional account metas. -/
inductive CloseAccountRole where
  | proof
  | refund
  deriving DecidableEq, Fintype

def closeAccountPrefix : List CloseAccountRole := [.proof, .refund]

theorem close_account_prefix_length : closeAccountPrefix.length = 2 := by
  rfl

theorem close_account_roles_are_exactly_once :
    closeAccountPrefix.Nodup ∧
      ∀ role : CloseAccountRole, role ∈ closeAccountPrefix := by
  decide

/-- Account metadata used by the deterministic validation model. -/
structure RawAccount (Address : Type*) where
  address : Address
  owner : AccountOwner
  signer : Bool
  writable : Bool
  executable : Bool
  deriving DecidableEq

/-- A successful spend decoder exists only for exactly five accounts. -/
def decodeSpendAccounts {Address : Type*}
    (accounts : List (RawAccount Address)) :
    Option (V5AccountView Address) :=
  match accounts with
  | [proof, pool, marker, payer, systemProgram] =>
      some
        { proofAddress := proof.address
          poolAddress := pool.address
          markerAddress := marker.address
          payerAddress := payer.address
          systemProgramAddress := systemProgram.address
          proofOwner := proof.owner
          poolOwner := pool.owner
          payerOwner := payer.owner
          proofWritable := proof.writable
          poolWritable := pool.writable
          markerWritable := marker.writable
          payerWritable := payer.writable
          payerSigner := payer.signer
          systemProgramExecutable := systemProgram.executable }
  | _ => none

/-- The close handler consumes the first two accounts and deliberately ignores
the remaining account metas, matching its two `next_account_info` calls. -/
def decodeCloseAccountPrefix {Address : Type*}
    (accounts : List (RawAccount Address)) :
    Option (CloseAccountView Address) :=
  match accounts with
  | proof :: refund :: _ =>
      some
        { proofAddress := proof.address
          refundAddress := refund.address
          proofOwner := proof.owner
          refundOwner := refund.owner
          proofSigner := proof.signer
          refundSigner := refund.signer
          proofWritable := proof.writable
          refundWritable := refund.writable }
  | _ => none

theorem decode_spend_accounts_requires_exactly_five
    {Address : Type*} {accounts : List (RawAccount Address)}
    {view : V5AccountView Address}
    (decoded : decodeSpendAccounts accounts = some view) :
    accounts.length = 5 := by
  cases accounts with
  | nil => simp [decodeSpendAccounts] at decoded
  | cons a rest =>
      cases rest with
      | nil => simp [decodeSpendAccounts] at decoded
      | cons b rest =>
          cases rest with
          | nil => simp [decodeSpendAccounts] at decoded
          | cons c rest =>
              cases rest with
              | nil => simp [decodeSpendAccounts] at decoded
              | cons d rest =>
                  cases rest with
                  | nil => simp [decodeSpendAccounts] at decoded
                  | cons e rest =>
                      cases rest with
                      | nil => rfl
                      | cons f rest => simp [decodeSpendAccounts] at decoded

theorem decode_close_prefix_requires_at_least_two
    {Address : Type*} {accounts : List (RawAccount Address)}
    {view : CloseAccountView Address}
    (decoded : decodeCloseAccountPrefix accounts = some view) :
    2 ≤ accounts.length := by
  cases accounts with
  | nil => simp [decodeCloseAccountPrefix] at decoded
  | cons proof rest =>
      cases rest with
      | nil => simp [decodeCloseAccountPrefix] at decoded
      | cons refund tail => simp

/-- The refund recipient is supplied by account position one (the second
account).  It is not a constant embedded in the close handler. -/
theorem decoded_close_refund_is_supplied_second_account
    {Address : Type*} {rawAccounts : List (RawAccount Address)}
    {view : CloseAccountView Address}
    (decoded : decodeCloseAccountPrefix rawAccounts = some view) :
    ∃ proof refund tail,
      rawAccounts = proof :: refund :: tail ∧
      view.refundAddress = refund.address := by
  cases rawAccounts with
  | nil => simp [decodeCloseAccountPrefix] at decoded
  | cons proof rest =>
      cases rest with
      | nil => simp [decodeCloseAccountPrefix] at decoded
      | cons refund tail =>
          refine ⟨proof, refund, tail, rfl, ?_⟩
          simp [decodeCloseAccountPrefix] at decoded
          subst view
          rfl

/-- The source operations in the retained-proof path, including operations
that the production callback trace intentionally combines into `StateApplied`.
This is a source-order model, not a claim that these events were emitted by the
deployed program. -/
inductive ProductionSpendOperationEvent where
  | fiveAccountsDecoded
  | accountsValidatedProgramOwned
  | accountsValidatedSystemOwned
  | statementDigestDone
  | proofVerified
  | programOwnedMarkerReady
  | systemOwnedMarkerCreated
  | mutableStateRechecked
  | nextPoolValuePrepared
  | markerValuePrepared
  | nextPoolImageEncoded
  | markerImageEncoded
  | markerWritten
  | poolWritten
  | stateAppliedCallback
  deriving DecidableEq

/-- Exact callback events exposed by
`verify_and_apply_atomic_payment_state_traced_inner`.  The callback fires once
after both fixed-size state copies; it does not separately observe the marker
and pool writes. -/
def productionSpendCallbackTrace
    {Address Nullifier Anchor : Type*}
    (accounts : V5AccountView Address)
    (state : SourceState Address Nullifier Anchor) :
    List ProductionSpendOperationEvent :=
  (match state.markers accounts.markerAddress with
  | .systemOwnedEmpty => [.accountsValidatedSystemOwned]
  | _ => [.accountsValidatedProgramOwned]) ++
  [.statementDigestDone, .proofVerified] ++
  (match state.markers accounts.markerAddress with
  | .systemOwnedEmpty => [.systemOwnedMarkerCreated]
  | _ => [.programOwnedMarkerReady]) ++
  [.mutableStateRechecked, .stateAppliedCallback]

/-- Source line order for a successful retained-proof spend.  In particular,
the marker bytes are copied before the pool bytes, and neither close nor refund
is part of this instruction. -/
def productionRetainedSpendOperationTrace
    {Address Nullifier Anchor : Type*}
    (accounts : V5AccountView Address)
    (state : SourceState Address Nullifier Anchor) :
    List ProductionSpendOperationEvent :=
  [.fiveAccountsDecoded] ++
  (match state.markers accounts.markerAddress with
  | .systemOwnedEmpty => [.accountsValidatedSystemOwned]
  | _ => [.accountsValidatedProgramOwned]) ++
  [.statementDigestDone, .proofVerified] ++
  (match state.markers accounts.markerAddress with
  | .systemOwnedEmpty => [.systemOwnedMarkerCreated]
  | _ => [.programOwnedMarkerReady]) ++
  [.mutableStateRechecked, .nextPoolValuePrepared, .markerValuePrepared,
    .nextPoolImageEncoded, .markerImageEncoded, .markerWritten, .poolWritten,
    .stateAppliedCallback]

theorem retained_spend_source_order_ends_with_marker_then_pool_then_callback
    {Address Nullifier Anchor : Type*}
    (accounts : V5AccountView Address)
    (state : SourceState Address Nullifier Anchor) :
    ∃ tracePrefix,
      productionRetainedSpendOperationTrace accounts state =
        tracePrefix ++ [.markerWritten, .poolWritten, .stateAppliedCallback] := by
  refine ⟨[.fiveAccountsDecoded] ++
    (match state.markers accounts.markerAddress with
    | .systemOwnedEmpty => [.accountsValidatedSystemOwned]
    | _ => [.accountsValidatedProgramOwned]) ++
    [.statementDigestDone, .proofVerified] ++
    (match state.markers accounts.markerAddress with
    | .systemOwnedEmpty => [.systemOwnedMarkerCreated]
    | _ => [.programOwnedMarkerReady]) ++
    [.mutableStateRechecked, .nextPoolValuePrepared, .markerValuePrepared,
      .nextPoolImageEncoded, .markerImageEncoded], ?_⟩
  simp [productionRetainedSpendOperationTrace, List.append_assoc]

/-- Forget statement construction, byte-image preparation, and the combined
callback to recover the smaller trace used by the theft/replay state model. -/
def projectSpendSecurityEvent {Address : Type*} :
    ProductionSpendOperationEvent → Option (SourceTraceEvent Address)
  | .fiveAccountsDecoded => none
  | .accountsValidatedProgramOwned => some .accountsValidated
  | .accountsValidatedSystemOwned => some .accountsValidated
  | .statementDigestDone => none
  | .proofVerified => some .proofVerified
  | .programOwnedMarkerReady => some .programOwnedMarkerReady
  | .systemOwnedMarkerCreated => some .systemOwnedMarkerPrepared
  | .mutableStateRechecked => some .mutableStateRechecked
  | .nextPoolValuePrepared => none
  | .markerValuePrepared => none
  | .nextPoolImageEncoded => none
  | .markerImageEncoded => none
  | .markerWritten => some .markerWritten
  | .poolWritten => some .poolWritten
  | .stateAppliedCallback => none

theorem retained_spend_operation_trace_projects_to_security_trace
    {Address Nullifier Anchor : Type*}
    (accounts : V5AccountView Address)
    (state : SourceState Address Nullifier Anchor) :
    (productionRetainedSpendOperationTrace accounts state).filterMap
        projectSpendSecurityEvent =
      v5SuccessTrace accounts state := by
  cases marker : state.markers accounts.markerAddress <;>
    simp [productionRetainedSpendOperationTrace, projectSpendSecurityEvent,
      v5SuccessTrace, marker]

/-! ## Source execution after account decoding -/

/-- Current source: exact five-account decoding followed by the bump-255
transition. -/
noncomputable def runCurrentProductionSpend
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (derive : Nullifier → Address × Fin 256)
    (canonicalSystemProgram : Address)
    (rawAccounts : List (RawAccount Address))
    (state : SourceState Address Nullifier Anchor)
    (request : V5SourceRequest Nullifier Anchor)
    (proofAccepted mutableStateRechecked : Prop) :
    SourceOutcome (SourceState Address Nullifier Anchor) Address :=
  match decodeSpendAccounts rawAccounts with
  | none => .rejected .spendRejected []
  | some accounts =>
      runV5SourceTransition derive canonicalSystemProgram accounts state
        request proofAccepted mutableStateRechecked

/-- Recorded mainnet source: the same exact account decoding and canonical
address check, without a separate numeric-bump rejection. -/
noncomputable def runRecordedProductionSpend
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (derive : Nullifier → Address × Fin 256)
    (canonicalSystemProgram : Address)
    (rawAccounts : List (RawAccount Address))
    (state : SourceState Address Nullifier Anchor)
    (request : V5SourceRequest Nullifier Anchor)
    (proofAccepted mutableStateRechecked : Prop) :
    SourceOutcome (SourceState Address Nullifier Anchor) Address :=
  match decodeSpendAccounts rawAccounts with
  | none => .rejected .spendRejected []
  | some accounts =>
      runRecordedDeployedV5SourceTransition derive canonicalSystemProgram
        accounts state request proofAccepted mutableStateRechecked

theorem current_production_success_exposes_decoded_accounts
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (derive : Nullifier → Address × Fin 256)
    (canonicalSystemProgram : Address)
    (rawAccounts : List (RawAccount Address))
    (state nextState : SourceState Address Nullifier Anchor)
    (request : V5SourceRequest Nullifier Anchor)
    (proofAccepted mutableStateRechecked : Prop)
    (trace : List (SourceTraceEvent Address))
    (success : runCurrentProductionSpend derive canonicalSystemProgram
      rawAccounts state request proofAccepted mutableStateRechecked =
        .committed nextState trace) :
    ∃ accounts,
      decodeSpendAccounts rawAccounts = some accounts ∧
      V5SourceSuccessRequirements derive canonicalSystemProgram accounts state
        request proofAccepted mutableStateRechecked := by
  unfold runCurrentProductionSpend at success
  split at success
  · simp at success
  · rename_i accounts decoded
    exact ⟨accounts, decoded,
      v5_source_success_implies_requirements derive canonicalSystemProgram
        accounts state nextState request proofAccepted mutableStateRechecked
        trace success⟩

theorem recorded_production_success_exposes_decoded_accounts
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (derive : Nullifier → Address × Fin 256)
    (canonicalSystemProgram : Address)
    (rawAccounts : List (RawAccount Address))
    (state nextState : SourceState Address Nullifier Anchor)
    (request : V5SourceRequest Nullifier Anchor)
    (proofAccepted mutableStateRechecked : Prop)
    (trace : List (SourceTraceEvent Address))
    (success : runRecordedProductionSpend derive canonicalSystemProgram
      rawAccounts state request proofAccepted mutableStateRechecked =
        .committed nextState trace) :
    ∃ accounts,
      decodeSpendAccounts rawAccounts = some accounts ∧
      V5SourceCoreSuccessRequirements derive canonicalSystemProgram accounts
        state request proofAccepted mutableStateRechecked := by
  unfold runRecordedProductionSpend at success
  split at success
  · simp at success
  · rename_i accounts decoded
    exact ⟨accounts, decoded,
      recorded_deployed_v5_success_implies_core_requirements derive
        canonicalSystemProgram accounts state nextState request proofAccepted
        mutableStateRechecked trace success⟩

theorem current_production_success_has_bump_255
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (derive : Nullifier → Address × Fin 256)
    (canonicalSystemProgram : Address)
    (rawAccounts : List (RawAccount Address))
    (state nextState : SourceState Address Nullifier Anchor)
    (request : V5SourceRequest Nullifier Anchor)
    (proofAccepted mutableStateRechecked : Prop)
    (trace : List (SourceTraceEvent Address))
    (success : runCurrentProductionSpend derive canonicalSystemProgram
      rawAccounts state request proofAccepted mutableStateRechecked =
        .committed nextState trace) :
    (derive request.nullifier).2 = 255 := by
  obtain ⟨accounts, _decoded, requirements⟩ :=
    current_production_success_exposes_decoded_accounts derive
      canonicalSystemProgram rawAccounts state nextState request proofAccepted
      mutableStateRechecked trace success
  exact requirements.bumpIs255

/-- A current-source success fixes the complete state image and event order,
in addition to exposing the exact decoded account view. -/
theorem current_production_success_is_exact
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (derive : Nullifier → Address × Fin 256)
    (canonicalSystemProgram : Address)
    (rawAccounts : List (RawAccount Address))
    (state nextState : SourceState Address Nullifier Anchor)
    (request : V5SourceRequest Nullifier Anchor)
    (proofAccepted mutableStateRechecked : Prop)
    (trace : List (SourceTraceEvent Address))
    (success : runCurrentProductionSpend derive canonicalSystemProgram
      rawAccounts state request proofAccepted mutableStateRechecked =
        .committed nextState trace) :
    ∃ accounts,
      decodeSpendAccounts rawAccounts = some accounts ∧
      V5SourceSuccessRequirements derive canonicalSystemProgram accounts state
        request proofAccepted mutableStateRechecked ∧
      nextState.poolAnchor = request.outputAnchor ∧
      nextState.poolSequence = state.poolSequence + 1 ∧
      nextState.poolDeploymentDomain = state.poolDeploymentDomain ∧
      nextState.markers ((derive request.nullifier).1) =
        .spent accounts.poolAddress request.nullifier ∧
      nextState.proofClosed = state.proofClosed ∧
      nextState.proofLamports = state.proofLamports ∧
      nextState.lastRefund = state.lastRefund ∧
      trace = v5SuccessTrace accounts state := by
  unfold runCurrentProductionSpend at success
  split at success
  · simp at success
  · rename_i accounts decoded
    have requirements := v5_source_success_implies_requirements derive
      canonicalSystemProgram accounts state nextState request proofAccepted
      mutableStateRechecked trace success
    have stateFacts := v5_source_success_exact_state derive
      canonicalSystemProgram accounts state nextState request proofAccepted
      mutableStateRechecked trace success
    have traceFact := v5_source_success_exact_trace derive
      canonicalSystemProgram accounts state nextState request proofAccepted
      mutableStateRechecked trace success
    have stateEq : nextState = applyV5Success accounts state request := by
      have modeled : runV5SourceTransition derive canonicalSystemProgram
          accounts state request proofAccepted mutableStateRechecked =
          .committed (applyV5Success accounts state request)
            (v5SuccessTrace accounts state) := by
        simp [runV5SourceTransition, requirements]
      rw [modeled] at success
      injection success with exactState _exactTrace
      exact exactState.symm
    exact ⟨accounts, decoded, requirements, stateFacts.1, stateFacts.2.1,
      by simpa [stateEq, applyV5Success], stateFacts.2.2.1,
      stateFacts.2.2.2.1, stateFacts.2.2.2.2.1,
      stateFacts.2.2.2.2.2, traceFact⟩

/-! ## Exact deployed/current bump distinction -/

theorem current_requirements_iff_core_and_bump_255
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (derive : Nullifier → Address × Fin 256)
    (canonicalSystemProgram : Address)
    (accounts : V5AccountView Address)
    (state : SourceState Address Nullifier Anchor)
    (request : V5SourceRequest Nullifier Anchor)
    (proofAccepted mutableStateRechecked : Prop) :
    V5SourceSuccessRequirements derive canonicalSystemProgram accounts state
        request proofAccepted mutableStateRechecked ↔
      V5SourceCoreSuccessRequirements derive canonicalSystemProgram accounts
          state request proofAccepted mutableStateRechecked ∧
        (derive request.nullifier).2 = 255 := by
  constructor
  · intro requirements
    exact ⟨requirements.toV5SourceCoreSuccessRequirements,
      requirements.bumpIs255⟩
  · rintro ⟨core, bump⟩
    exact { core with bumpIs255 := bump }

theorem current_and_recorded_models_agree_at_bump_255
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (derive : Nullifier → Address × Fin 256)
    (canonicalSystemProgram : Address)
    (accounts : V5AccountView Address)
    (state : SourceState Address Nullifier Anchor)
    (request : V5SourceRequest Nullifier Anchor)
    (proofAccepted mutableStateRechecked : Prop)
    (bump : (derive request.nullifier).2 = 255) :
    runV5SourceTransition derive canonicalSystemProgram accounts state request
        proofAccepted mutableStateRechecked =
      runRecordedDeployedV5SourceTransition derive canonicalSystemProgram
        accounts state request proofAccepted mutableStateRechecked := by
  classical
  unfold runV5SourceTransition runRecordedDeployedV5SourceTransition
  by_cases core : V5SourceCoreSuccessRequirements derive
      canonicalSystemProgram accounts state request proofAccepted
      mutableStateRechecked
  · have current : V5SourceSuccessRequirements derive canonicalSystemProgram
        accounts state request proofAccepted mutableStateRechecked :=
      (current_requirements_iff_core_and_bump_255 derive
        canonicalSystemProgram accounts state request proofAccepted
        mutableStateRechecked).2 ⟨core, bump⟩
    simp [core, current]
  · have current : ¬ V5SourceSuccessRequirements derive
        canonicalSystemProgram accounts state request proofAccepted
        mutableStateRechecked := by
      intro requirements
      exact core requirements.toV5SourceCoreSuccessRequirements
    simp [core, current]

theorem recorded_can_accept_below_255_while_current_rejects
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (derive : Nullifier → Address × Fin 256)
    (canonicalSystemProgram : Address)
    (accounts : V5AccountView Address)
    (state : SourceState Address Nullifier Anchor)
    (request : V5SourceRequest Nullifier Anchor)
    (proofAccepted mutableStateRechecked : Prop)
    (core : V5SourceCoreSuccessRequirements derive canonicalSystemProgram
      accounts state request proofAccepted mutableStateRechecked)
    (not255 : (derive request.nullifier).2 ≠ 255) :
    runRecordedDeployedV5SourceTransition derive canonicalSystemProgram
        accounts state request proofAccepted mutableStateRechecked =
        .committed (applyV5Success accounts state request)
          (v5SuccessTrace accounts state) ∧
      runV5SourceTransition derive canonicalSystemProgram accounts state
        request proofAccepted mutableStateRechecked =
        .rejected .spendRejected [] := by
  classical
  have noCurrent : ¬ V5SourceSuccessRequirements derive
      canonicalSystemProgram accounts state request proofAccepted
      mutableStateRechecked := by
    intro requirements
    exact not255 requirements.bumpIs255
  simp [runRecordedDeployedV5SourceTransition, runV5SourceTransition, core,
    noCurrent]

/-! ## Sequential replay after the exact state write -/

theorem exact_replay_rejects_after_current_success
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (derive : Nullifier → Address × Fin 256)
    (canonicalSystemProgram : Address)
    (accounts : V5AccountView Address)
    (before after : SourceState Address Nullifier Anchor)
    (request replayRequest : V5SourceRequest Nullifier Anchor)
    (proofAccepted mutableStateRechecked replayProofAccepted
      replayStateRechecked : Prop)
    (trace : List (SourceTraceEvent Address))
    (sameNullifier : replayRequest.nullifier = request.nullifier)
    (success : runV5SourceTransition derive canonicalSystemProgram accounts
      before request proofAccepted mutableStateRechecked =
        .committed after trace) :
    ¬ ∃ replayState replayTrace,
      runV5SourceTransition derive canonicalSystemProgram accounts after
        replayRequest replayProofAccepted replayStateRechecked =
          .committed replayState replayTrace := by
  have requirements := v5_source_success_implies_requirements derive
    canonicalSystemProgram accounts before after request proofAccepted
    mutableStateRechecked trace success
  have exactState := v5_source_success_exact_state derive
    canonicalSystemProgram accounts before after request proofAccepted
    mutableStateRechecked trace success
  have occupied : after.markers accounts.markerAddress =
      .spent accounts.poolAddress request.nullifier := by
    rw [requirements.expectedMarkerAddress]
    exact exactState.2.2.1
  rw [← sameNullifier] at occupied
  exact v5_source_rejects_preexisting_marker derive canonicalSystemProgram
    accounts after replayRequest replayProofAccepted replayStateRechecked
    accounts.poolAddress replayRequest.nullifier occupied

/-! ## Exact later close and refund in the source model -/

/-- Extra deterministic values checked by the separate tag-64 close before it
mutates lamports or proof data. -/
structure CloseDataChecks where
  uploadedProofBoundsValid : Prop
  proofFinalized : Prop

/-- State needed to say which balance received the refund. -/
structure CloseLedgerState (Address Nullifier Anchor : Type*) where
  spend : SourceState Address Nullifier Anchor
  balances : Address → Nat

structure ProductionCloseRequirements
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (accounts : CloseAccountView Address)
    (state : CloseLedgerState Address Nullifier Anchor)
    (checks : CloseDataChecks) : Prop where
  accountChecks : CloseSuccessRequirements accounts state.spend
  uploadedProofBoundsValid : checks.uploadedProofBoundsValid
  proofFinalized : checks.proofFinalized
  refundDoesNotOverflow :
    state.balances accounts.refundAddress + state.spend.proofLamports < 2 ^ 64

def applyProductionClose
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (accounts : CloseAccountView Address)
    (state : CloseLedgerState Address Nullifier Anchor) :
    CloseLedgerState Address Nullifier Anchor :=
  { spend := applyCloseSuccess accounts state.spend
    balances := Function.update state.balances accounts.refundAddress
      (state.balances accounts.refundAddress + state.spend.proofLamports) }

noncomputable def runProductionClose
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (rawAccounts : List (RawAccount Address))
    (state : CloseLedgerState Address Nullifier Anchor)
    (checks : CloseDataChecks) :
    SourceOutcome (CloseLedgerState Address Nullifier Anchor) Address :=
  match decodeCloseAccountPrefix rawAccounts with
  | none => .rejected .closeRejected []
  | some accounts =>
      letI : Decidable (ProductionCloseRequirements accounts state checks) :=
        Classical.propDecidable _
      if _requirements : ProductionCloseRequirements accounts state checks then
        .committed (applyProductionClose accounts state)
          (closeSuccessTrace accounts)
      else
        .rejected .closeRejected []

theorem production_close_success_is_exact
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (rawAccounts : List (RawAccount Address))
    (state nextState : CloseLedgerState Address Nullifier Anchor)
    (checks : CloseDataChecks)
    (trace : List (SourceTraceEvent Address))
    (success : runProductionClose rawAccounts state checks =
      .committed nextState trace) :
    ∃ accounts,
      decodeCloseAccountPrefix rawAccounts = some accounts ∧
      ProductionCloseRequirements accounts state checks ∧
      nextState.spend.proofClosed = true ∧
      nextState.spend.proofLamports = 0 ∧
      nextState.spend.lastRefund =
        some (accounts.refundAddress, state.spend.proofLamports) ∧
      nextState.balances accounts.refundAddress =
        state.balances accounts.refundAddress + state.spend.proofLamports ∧
      (∀ address, address ≠ accounts.refundAddress →
        nextState.balances address = state.balances address) ∧
      nextState.spend.poolAnchor = state.spend.poolAnchor ∧
      nextState.spend.poolSequence = state.spend.poolSequence ∧
      nextState.spend.markers = state.spend.markers ∧
      trace = [.proofInvalidated, .refundCredited accounts.refundAddress,
        .proofBalanceZeroed] := by
  unfold runProductionClose at success
  split at success
  · simp at success
  · rename_i accounts decoded
    split at success
    · rename_i requirements
      cases success
      refine ⟨accounts, decoded, requirements, ?_⟩
      simp [applyProductionClose, applyCloseSuccess, closeSuccessTrace]
      intro address notRefund
      simp [notRefund]
    · simp at success

/-! ## Rust/source projection equality predicates -/

/-- The lifecycle bit carried by the Lean projection must agree with a
successful read of the real proof bytes.  The retained state handler does not
itself inspect a `proofClosed` Boolean: that check happens while the production
proof verifier parses the proof account. -/
def RetainedProofProjectionConsistent
    {Address Nullifier Anchor : Type*}
    (state : SourceState Address Nullifier Anchor)
    (proofAccepted : Prop) : Prop :=
  proofAccepted → state.proofClosed = false

/-- Universal correspondence obligation for the security-relevant projection
of the current retained-proof spend handler.  This is not equality of complete
Solana account state: payer debits, marker rent/owner changes, raw bytes, and
runtime effects are outside the codomain.  A Charon/Aeneas extraction of this
account handler is not present in the repository, so this predicate is not
asserted below. -/
def ExactCurrentRustStateEquality
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (derive : Nullifier → Address × Fin 256)
    (canonicalSystemProgram : Address)
    (rustRun : List (RawAccount Address) →
      SourceState Address Nullifier Anchor →
      V5SourceRequest Nullifier Anchor → Prop → Prop →
      SourceOutcome (SourceState Address Nullifier Anchor) Address) : Prop :=
  ∀ rawAccounts state request proofAccepted mutableStateRechecked,
    RetainedProofProjectionConsistent state proofAccepted →
    rustRun rawAccounts state request proofAccepted mutableStateRechecked =
      runCurrentProductionSpend derive canonicalSystemProgram rawAccounts
        state request proofAccepted mutableStateRechecked

/-- The corresponding projected equality for the source recorded for the
mainnet program.  It intentionally targets the no-numeric-bump model. -/
def ExactRecordedRustStateEquality
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (derive : Nullifier → Address × Fin 256)
    (canonicalSystemProgram : Address)
    (rustRun : List (RawAccount Address) →
      SourceState Address Nullifier Anchor →
      V5SourceRequest Nullifier Anchor → Prop → Prop →
      SourceOutcome (SourceState Address Nullifier Anchor) Address) : Prop :=
  ∀ rawAccounts state request proofAccepted mutableStateRechecked,
    RetainedProofProjectionConsistent state proofAccepted →
    rustRun rawAccounts state request proofAccepted mutableStateRechecked =
      runRecordedProductionSpend derive canonicalSystemProgram rawAccounts
        state request proofAccepted mutableStateRechecked

/-- Exact source equality needed for the later proof-close instruction. -/
def ExactRustCloseEquality
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (rustClose : List (RawAccount Address) →
      CloseLedgerState Address Nullifier Anchor → CloseDataChecks →
      SourceOutcome (CloseLedgerState Address Nullifier Anchor) Address) : Prop :=
  ∀ rawAccounts state checks,
    rustClose rawAccounts state checks =
      runProductionClose rawAccounts state checks

/-- Once the exact current-Rust equality is supplied, a successful Rust run
inherits the account order, bump, state image, proof retention, and write
ordering proved above. -/
theorem current_rust_success_is_exact
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (derive : Nullifier → Address × Fin 256)
    (canonicalSystemProgram : Address)
    (rustRun : List (RawAccount Address) →
      SourceState Address Nullifier Anchor →
      V5SourceRequest Nullifier Anchor → Prop → Prop →
      SourceOutcome (SourceState Address Nullifier Anchor) Address)
    (equality : ExactCurrentRustStateEquality derive canonicalSystemProgram
      rustRun)
    (rawAccounts : List (RawAccount Address))
    (state nextState : SourceState Address Nullifier Anchor)
    (request : V5SourceRequest Nullifier Anchor)
    (proofAccepted mutableStateRechecked : Prop)
    (projectionConsistent :
      RetainedProofProjectionConsistent state proofAccepted)
    (trace : List (SourceTraceEvent Address))
    (success : rustRun rawAccounts state request proofAccepted
      mutableStateRechecked = .committed nextState trace) :
    ∃ accounts,
      decodeSpendAccounts rawAccounts = some accounts ∧
      V5SourceSuccessRequirements derive canonicalSystemProgram accounts state
        request proofAccepted mutableStateRechecked ∧
      nextState.poolAnchor = request.outputAnchor ∧
      nextState.poolSequence = state.poolSequence + 1 ∧
      nextState.poolDeploymentDomain = state.poolDeploymentDomain ∧
      nextState.markers ((derive request.nullifier).1) =
        .spent accounts.poolAddress request.nullifier ∧
      nextState.proofClosed = state.proofClosed ∧
      nextState.proofLamports = state.proofLamports ∧
      nextState.lastRefund = state.lastRefund ∧
      trace = v5SuccessTrace accounts state := by
  apply current_production_success_is_exact derive canonicalSystemProgram
    rawAccounts state nextState request proofAccepted mutableStateRechecked
    trace
  rw [← equality rawAccounts state request proofAccepted mutableStateRechecked
    projectionConsistent]
  exact success

/-- Mainnet-facing recorded-source result.  The recorded Rust path itself
checked the canonical marker address but not the numeric bump.  Exact
recorded-Rust/source equality and the separately observed bump value together
recover the full bump-255 requirements and the complete successful state
image. -/
theorem recorded_mainnet_rust_success_is_exact_at_observed_bump_255
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (derive : Nullifier → Address × Fin 256)
    (canonicalSystemProgram : Address)
    (rustRun : List (RawAccount Address) →
      SourceState Address Nullifier Anchor →
      V5SourceRequest Nullifier Anchor → Prop → Prop →
      SourceOutcome (SourceState Address Nullifier Anchor) Address)
    (equality : ExactRecordedRustStateEquality derive canonicalSystemProgram
      rustRun)
    (rawAccounts : List (RawAccount Address))
    (state nextState : SourceState Address Nullifier Anchor)
    (request : V5SourceRequest Nullifier Anchor)
    (proofAccepted mutableStateRechecked : Prop)
    (projectionConsistent :
      RetainedProofProjectionConsistent state proofAccepted)
    (trace : List (SourceTraceEvent Address))
    (observedBump : (derive request.nullifier).2 = 255)
    (success : rustRun rawAccounts state request proofAccepted
      mutableStateRechecked = .committed nextState trace) :
    ∃ accounts,
      decodeSpendAccounts rawAccounts = some accounts ∧
      rawAccounts.length = 5 ∧
      V5SourceSuccessRequirements derive canonicalSystemProgram accounts state
        request proofAccepted mutableStateRechecked ∧
      nextState.poolAnchor = request.outputAnchor ∧
      nextState.poolSequence = state.poolSequence + 1 ∧
      nextState.poolDeploymentDomain = state.poolDeploymentDomain ∧
      nextState.markers ((derive request.nullifier).1) =
        .spent accounts.poolAddress request.nullifier ∧
      nextState.proofClosed = state.proofClosed ∧
      nextState.proofLamports = state.proofLamports ∧
      nextState.lastRefund = state.lastRefund ∧
      trace = v5SuccessTrace accounts state := by
  have sourceSuccess : runRecordedProductionSpend derive
      canonicalSystemProgram rawAccounts state request proofAccepted
        mutableStateRechecked = .committed nextState trace := by
    rw [← equality rawAccounts state request proofAccepted
      mutableStateRechecked projectionConsistent]
    exact success
  unfold runRecordedProductionSpend at sourceSuccess
  split at sourceSuccess
  · simp at sourceSuccess
  · rename_i accounts decoded
    have core := recorded_deployed_v5_success_implies_core_requirements derive
      canonicalSystemProgram accounts state nextState request proofAccepted
      mutableStateRechecked trace sourceSuccess
    have requirements : V5SourceSuccessRequirements derive
        canonicalSystemProgram accounts state request proofAccepted
        mutableStateRechecked :=
      { core with bumpIs255 := observedBump }
    have modeled : runRecordedDeployedV5SourceTransition derive
        canonicalSystemProgram accounts state request proofAccepted
          mutableStateRechecked =
        .committed (applyV5Success accounts state request)
          (v5SuccessTrace accounts state) := by
      simp [runRecordedDeployedV5SourceTransition, core]
    rw [modeled] at sourceSuccess
    injection sourceSuccess with stateEq traceEq
    subst nextState
    refine ⟨accounts, decoded,
      decode_spend_accounts_requires_exactly_five decoded, requirements, ?_⟩
    simp [applyV5Success, core.expectedMarkerAddress, traceEq]

/-- Once exact close-source equality is supplied, the Rust close sends the
whole proof balance to the account in position one and nowhere else. -/
theorem rust_close_success_is_exact
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (rustClose : List (RawAccount Address) →
      CloseLedgerState Address Nullifier Anchor → CloseDataChecks →
      SourceOutcome (CloseLedgerState Address Nullifier Anchor) Address)
    (equality : ExactRustCloseEquality rustClose)
    (rawAccounts : List (RawAccount Address))
    (state nextState : CloseLedgerState Address Nullifier Anchor)
    (checks : CloseDataChecks)
    (trace : List (SourceTraceEvent Address))
    (success : rustClose rawAccounts state checks =
      .committed nextState trace) :
    ∃ accounts,
      decodeCloseAccountPrefix rawAccounts = some accounts ∧
      ProductionCloseRequirements accounts state checks ∧
      nextState.spend.proofClosed = true ∧
      nextState.spend.proofLamports = 0 ∧
      nextState.spend.lastRefund =
        some (accounts.refundAddress, state.spend.proofLamports) ∧
      nextState.balances accounts.refundAddress =
        state.balances accounts.refundAddress + state.spend.proofLamports ∧
      (∀ address, address ≠ accounts.refundAddress →
        nextState.balances address = state.balances address) ∧
      nextState.spend.poolAnchor = state.spend.poolAnchor ∧
      nextState.spend.poolSequence = state.spend.poolSequence ∧
      nextState.spend.markers = state.spend.markers ∧
      trace = [.proofInvalidated, .refundCredited accounts.refundAddress,
        .proofBalanceZeroed] := by
  apply production_close_success_is_exact rawAccounts state nextState checks
    trace
  rw [← equality rawAccounts state checks]
  exact success

/-! ## Explicit source/runtime boundaries -/

/-- The boundaries needed to carry the deterministic theorems above to an
observed Solana execution.  They are separated so no proof about the Lean
model is misreported as a proof about the runtime. -/
structure ProductionRuntimePremises where
  selectedRustEqualsSourceModel : Prop
  canonicalPdaAndSystemProgramMatch : Prop
  writablePoolAndMarkerLocksSerialize : Prop
  rejectedTransactionsRollBack : Prop
  committedMarkerAndPoolPersist : Prop
  finalizedObservationMatchesCommit : Prop
  proofCloseAndRefundMatchModel : Prop

/-- The runtime premise list is exactly the seven failure fields already used
by the theft reduction, stated outside those failures. -/
def RuntimePremisesHoldOutside
    {Coins : Type*} (failures : RuntimeFailurePredicates Coins)
    (coins : Coins) : Prop :=
  ¬ failures.rustStateModelMismatch coins ∧
  ¬ failures.systemProgramOrPdaMismatch coins ∧
  ¬ failures.writableAccountLockFailure coins ∧
  ¬ failures.rejectedTransactionRollbackFailure coins ∧
  ¬ failures.committedMarkerPersistenceFailure coins ∧
  ¬ failures.finalizedStateObservationFailure coins ∧
  ¬ failures.closeOrRefundModelMismatch coins

theorem runtime_premises_hold_outside_iff_no_named_failure
    {Coins : Type*} (failures : RuntimeFailurePredicates Coins)
    (coins : Coins) :
    RuntimePremisesHoldOutside failures coins ↔
      ¬ NamedRuntimeFailureEvent failures coins := by
  simp [RuntimePremisesHoldOutside, NamedRuntimeFailureEvent]

#print axioms spend_account_roles_are_exactly_once
#print axioms decode_spend_accounts_requires_exactly_five
#print axioms decoded_close_refund_is_supplied_second_account
#print axioms retained_spend_source_order_ends_with_marker_then_pool_then_callback
#print axioms retained_spend_operation_trace_projects_to_security_trace
#print axioms current_production_success_exposes_decoded_accounts
#print axioms current_production_success_has_bump_255
#print axioms current_production_success_is_exact
#print axioms current_and_recorded_models_agree_at_bump_255
#print axioms recorded_can_accept_below_255_while_current_rejects
#print axioms exact_replay_rejects_after_current_success
#print axioms production_close_success_is_exact
#print axioms current_rust_success_is_exact
#print axioms recorded_mainnet_rust_success_is_exact_at_observed_bump_255
#print axioms rust_close_success_is_exact
#print axioms runtime_premises_hold_outside_iff_no_named_failure

end AspisV5ProductionStateBridge
