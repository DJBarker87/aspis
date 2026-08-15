import AspisFormal.V5RecordedCloseBytes

/-!
# Current bump check and proof-account refund

This file keeps two different claims separate.

* The source recorded for the mainnet transaction checked the derived spent-
  marker address, but it did not contain a separate numeric bump check.
* The current source routes instruction 67 through a wrapper that passes 255
  to the account validator, which rejects any different derived bump.

The later proof-account close is also separate from the spend instruction.
It takes the proof account first and the refund account second, then credits
the complete live proof balance to that supplied second account.

The replay script pins all four current Rust files, checks the call sites, runs
the bump and refund tests, and translates the plain-value bump/refund
projection with Charon and Aeneas.  Aeneas still cannot translate Solana's
`AccountInfo` mutable `Rc<RefCell<&mut _>>` fields.  Equality between those
fields and the proved plain values therefore remains the one named wrapper
condition below.  Solana rollback, locking, atomic commit, account removal,
and finality remain runtime assumptions, not Lean theorems.
-/

namespace AspisV5CurrentInstructionAndClose

open AspisV5TheftStateTransitionReduction
open AspisV5ProductionStateBridge
open AspisV5RecordedCloseBytes

/-! ## Exact current-source files checked by the replay -/

def currentAtomicPaymentBlob : String :=
  "53e44db042f6035d06dbddb08f80a76c67b25b80"

def currentLifecycleBlob : String :=
  "560466bb84c85dde599b4b918f95b3015bf6b52a"

def currentV5InstructionWrapperBlob : String :=
  "9318294b41ec8b5572075bfd919b8f1c24172525"

def currentDispatcherBlob : String :=
  "d3687ed3b689b311f174b95a1f4137ced6784633"

theorem current_source_file_identities_are_exact :
    currentAtomicPaymentBlob =
        "53e44db042f6035d06dbddb08f80a76c67b25b80" ∧
      currentLifecycleBlob =
        "560466bb84c85dde599b4b918f95b3015bf6b52a" ∧
      currentV5InstructionWrapperBlob =
        "9318294b41ec8b5572075bfd919b8f1c24172525" ∧
      currentDispatcherBlob =
        "d3687ed3b689b311f174b95a1f4137ced6784633" := by
  simp [currentAtomicPaymentBlob, currentLifecycleBlob,
    currentV5InstructionWrapperBlob, currentDispatcherBlob]

/-- The close wrapper itself is unchanged between the recorded mainnet tree
and the current tree.  The replay also compares the refund helper text even
though the surrounding atomic-payment file changed for the bump check. -/
theorem current_and_recorded_lifecycle_files_are_identical :
    currentLifecycleBlob = recordedLifecycleBlob := by
  rfl

theorem current_and_recorded_atomic_payment_files_are_different :
    currentAtomicPaymentBlob ≠ recordedAtomicPaymentBlob := by
  decide

/-! ## The current instruction requires bump 255 -/

def currentRequiredNullifierBump : Fin 256 := 255

def currentBumpAccepted (derivedBump : Fin 256) : Prop :=
  derivedBump = currentRequiredNullifierBump

theorem current_required_nullifier_bump_is_255 :
    currentRequiredNullifierBump = 255 := by
  rfl

theorem current_bump_is_accepted_iff_255 (derivedBump : Fin 256) :
    currentBumpAccepted derivedBump ↔ derivedBump = 255 := by
  rfl

/-- An accepted current-source model run cannot have any derived bump other
than 255.  This includes exact five-account decoding and the account checks in
`runCurrentProductionSpend`; it does not describe the older recorded binary. -/
theorem current_instruction_model_success_requires_bump_255
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
  exact current_production_success_has_bump_255 derive canonicalSystemProgram
    rawAccounts state nextState request proofAccepted mutableStateRechecked
    trace success

/-- This is the remaining connection from the actual current Rust handler to
the executable account/state model.  The translated pure bump gate proves
that its accepted value is exactly 255; this condition additionally says that
the real dispatcher, wrapper, account decoding, PDA result, and validator feed
that gate exactly the values modeled here. -/
def ExactCurrentInstructionAccountInfoEquality
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (derive : Nullifier → Address × Fin 256)
    (canonicalSystemProgram : Address)
    (rustRun : List (RawAccount Address) →
      SourceState Address Nullifier Anchor →
      V5SourceRequest Nullifier Anchor → Prop → Prop →
      SourceOutcome (SourceState Address Nullifier Anchor) Address) : Prop :=
  ExactCurrentRustStateEquality derive canonicalSystemProgram rustRun

theorem current_rust_success_requires_bump_255
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (derive : Nullifier → Address × Fin 256)
    (canonicalSystemProgram : Address)
    (rustRun : List (RawAccount Address) →
      SourceState Address Nullifier Anchor →
      V5SourceRequest Nullifier Anchor → Prop → Prop →
      SourceOutcome (SourceState Address Nullifier Anchor) Address)
    (equality : ExactCurrentInstructionAccountInfoEquality derive
      canonicalSystemProgram rustRun)
    (rawAccounts : List (RawAccount Address))
    (state nextState : SourceState Address Nullifier Anchor)
    (request : V5SourceRequest Nullifier Anchor)
    (proofAccepted mutableStateRechecked : Prop)
    (projectionConsistent :
      RetainedProofProjectionConsistent state proofAccepted)
    (trace : List (SourceTraceEvent Address))
    (success : rustRun rawAccounts state request proofAccepted
      mutableStateRechecked = .committed nextState trace) :
    (derive request.nullifier).2 = 255 := by
  apply current_instruction_model_success_requires_bump_255 derive
    canonicalSystemProgram rawAccounts state nextState request proofAccepted
    mutableStateRechecked trace
  rw [← equality rawAccounts state request proofAccepted
    mutableStateRechecked projectionConsistent]
  exact success

/-! ## The current close sends the full balance to the supplied account -/

/-- The relevant current close wrapper and helper have the same source as the
recorded close.  This definition gives that unchanged code its current-source
name while preserving the recorded/mainnet distinction for the spend path. -/
noncomputable def runCurrentProofClose
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (rawAccounts : List (RawAccount Address))
    (state : RecordedCloseState Address Nullifier Anchor)
    (checks : CloseDataChecks) :
    RecordedCloseOutcome (RecordedCloseState Address Nullifier Anchor)
      Address :=
  runRecordedClose rawAccounts state checks

theorem current_close_model_equals_recorded_close_model
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (rawAccounts : List (RawAccount Address))
    (state : RecordedCloseState Address Nullifier Anchor)
    (checks : CloseDataChecks) :
    runCurrentProofClose rawAccounts state checks =
      runRecordedClose rawAccounts state checks := by
  rfl

/-- Every successful current close credits the complete live proof balance to
the second supplied account, writes `ASPC`, and zeros the proof balance. -/
theorem current_close_success_refunds_full_balance_to_second_account
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (rawAccounts : List (RawAccount Address))
    (state nextState : RecordedCloseState Address Nullifier Anchor)
    (checks : CloseDataChecks)
    (trace : List (RecordedCloseOperation Address))
    (success : runCurrentProofClose rawAccounts state checks =
      .committed nextState trace) :
    ∃ proof refund tail,
      rawAccounts = proof :: refund :: tail ∧
      nextState.ledger.balances refund.address =
        state.ledger.balances refund.address +
          state.ledger.spend.proofLamports ∧
      nextState.ledger.spend.proofLamports = 0 ∧
      nextState.proofData.take 4 = closedProofMagic := by
  have recordedSuccess : runRecordedClose rawAccounts state checks =
      .committed nextState trace := by
    simpa [runCurrentProofClose] using success
  obtain ⟨accounts, proof, refund, tail, _decoded, rawEq, refundEq,
    _requirements, _dataEq, prefixFact, _suffix, _length, _closed, zero,
    _lastRefund, credited, _others, _anchor, _sequence, _domain, _markers,
    _trace⟩ := recorded_close_success_is_exact rawAccounts state nextState
      checks trace recordedSuccess
  refine ⟨proof, refund, tail, rawEq, ?_, zero, prefixFact⟩
  simpa [refundEq] using credited

theorem current_close_success_includes_inbound_dust
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (rawAccounts : List (RawAccount Address))
    (state nextState : RecordedCloseState Address Nullifier Anchor)
    (checks : CloseDataChecks)
    (trace : List (RecordedCloseOperation Address))
    (baseBalance inboundDust : Nat)
    (balanceAtClose : state.ledger.spend.proofLamports =
      baseBalance + inboundDust)
    (success : runCurrentProofClose rawAccounts state checks =
      .committed nextState trace) :
    ∃ refundAddress,
      nextState.ledger.balances refundAddress =
        state.ledger.balances refundAddress + baseBalance + inboundDust := by
  apply successful_close_includes_inbound_dust rawAccounts state nextState
    checks trace baseBalance inboundDust balanceAtClose
  simpa [runCurrentProofClose] using success

/-- The exact remaining source connection for the close.  Charon extracts the
real function, but pinned Aeneas stops at the nested mutable `AccountInfo`
projection.  The translated plain-value function already proves the address,
byte, and balance result once these reads and borrows are connected. -/
def ExactCurrentCloseAccountInfoWrapperEquality
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (rustClose : List (RawAccount Address) →
      RecordedCloseState Address Nullifier Anchor → CloseDataChecks →
      RecordedCloseOutcome (RecordedCloseState Address Nullifier Anchor)
        Address) : Prop :=
  ∀ rawAccounts state checks,
    rustClose rawAccounts state checks =
      runCurrentProofClose rawAccounts state checks

theorem current_account_info_close_success_has_exact_refund
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (rustClose : List (RawAccount Address) →
      RecordedCloseState Address Nullifier Anchor → CloseDataChecks →
      RecordedCloseOutcome (RecordedCloseState Address Nullifier Anchor)
        Address)
    (equality : ExactCurrentCloseAccountInfoWrapperEquality rustClose)
    (rawAccounts : List (RawAccount Address))
    (state nextState : RecordedCloseState Address Nullifier Anchor)
    (checks : CloseDataChecks)
    (trace : List (RecordedCloseOperation Address))
    (success : rustClose rawAccounts state checks =
      .committed nextState trace) :
    ∃ proof refund tail,
      rawAccounts = proof :: refund :: tail ∧
      nextState.ledger.balances refund.address =
        state.ledger.balances refund.address +
          state.ledger.spend.proofLamports ∧
      nextState.ledger.spend.proofLamports = 0 ∧
      nextState.proofData.take 4 = closedProofMagic := by
  apply current_close_success_refunds_full_balance_to_second_account
    rawAccounts state nextState checks trace
  rw [← equality rawAccounts state checks]
  exact success

/-! ## Runtime assumptions kept outside the source proofs -/

structure CurrentSpendRuntimeAssumptions where
  pdaDerivationMatchesSolana : Prop
  writablePoolAndMarkerLocksSerialize : Prop
  rejectedInstructionWritesRollBack : Prop
  successfulInstructionWritesCommitAtomically : Prop
  finalizedObservationMatchesCommit : Prop

structure CurrentCloseRuntimeAssumptions where
  accountInfoReadsAndBorrowsMatchProjection : Prop
  rejectedInstructionWritesRollBack : Prop
  successfulInstructionWritesCommitAtomically : Prop
  zeroLamportProgramAccountIsRemovedAtCommit : Prop
  finalizedObservationMatchesCommit : Prop

#print axioms current_source_file_identities_are_exact
#print axioms current_and_recorded_lifecycle_files_are_identical
#print axioms current_and_recorded_atomic_payment_files_are_different
#print axioms current_required_nullifier_bump_is_255
#print axioms current_bump_is_accepted_iff_255
#print axioms current_instruction_model_success_requires_bump_255
#print axioms current_rust_success_requires_bump_255
#print axioms current_close_model_equals_recorded_close_model
#print axioms current_close_success_refunds_full_balance_to_second_account
#print axioms current_close_success_includes_inbound_dust
#print axioms current_account_info_close_success_has_exact_refund

end AspisV5CurrentInstructionAndClose
