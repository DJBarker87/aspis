import AspisFormal.V5ProductionStateBridge

/-!
# Recorded proof-account close, including bytes and the full refund

This file refines the close model in `V5ProductionStateBridge` with the raw
proof-account bytes and the exact successful source order.  It targets the
source tree recorded for the mainnet build.  That source selected the refund
recipient from the second instruction account, overwrote the first four proof
bytes with `ASPC`, credited the entire proof-account balance to that recipient,
and then set the proof-account balance to zero.

This is still a model of the successful Rust path.  Charon can extract the
recorded function while leaving the Solana `AccountInfo` methods opaque, but
the pinned Aeneas version cannot translate the resulting mutable
`Rc<RefCell<&mut _>>` projections.  Therefore equality between the extracted
Rust and `runRecordedClose` remains a named source-level obligation below.
Solana account borrowing, commit/rollback, zero-lamport account removal, and
finality are separate runtime obligations; none is silently treated as a Lean
theorem.
-/

namespace AspisV5RecordedCloseBytes

open AspisV5TheftStateTransitionReduction
open AspisV5ProductionStateBridge

/-! ## Exact source identity -/

def recordedMainnetSourceCommit : String :=
  "06788d44d30ea8cbd391899dddaf6f0acc6e4a3f"

def recordedMainnetSourceTree : String :=
  "9b6bdfddb3c213addc2bb705c8130cce4fb2c351"

def recordedAtomicPaymentBlob : String :=
  "dca4626b5b49da6aa48076fad748dc838ce9c7d6"

def recordedLifecycleBlob : String :=
  "560466bb84c85dde599b4b918f95b3015bf6b52a"

/-- The later current-source change is intentionally pinned separately.  The
recorded mainnet source checked the derived marker address but did not contain
the additional numeric-bump argument/check. -/
def currentAtomicPaymentBlobWithNumericBumpCheck : String :=
  "53e44db042f6035d06dbddb08f80a76c67b25b80"

theorem recorded_source_identities_are_exact :
    recordedMainnetSourceCommit =
        "06788d44d30ea8cbd391899dddaf6f0acc6e4a3f" ∧
      recordedMainnetSourceTree =
        "9b6bdfddb3c213addc2bb705c8130cce4fb2c351" ∧
      recordedAtomicPaymentBlob =
        "dca4626b5b49da6aa48076fad748dc838ce9c7d6" ∧
      recordedLifecycleBlob =
        "560466bb84c85dde599b4b918f95b3015bf6b52a" := by
  simp [recordedMainnetSourceCommit, recordedMainnetSourceTree,
    recordedAtomicPaymentBlob, recordedLifecycleBlob]

/-! ## Raw close state and exact mutation -/

/-- Decimal bytes for the production constant `*b"ASPC"`. -/
def closedProofMagic : List UInt8 := [65, 83, 80, 67]

theorem closed_proof_magic_is_ASPC :
    closedProofMagic = [65, 83, 80, 67] := by
  rfl

/-- Rust's `proof_data[..4].copy_from_slice(&PROOF_ACCOUNT_CLOSED_MAGIC)`:
replace exactly the first four bytes and retain the complete suffix. -/
def overwriteClosedProofMagic (data : List UInt8) : List UInt8 :=
  closedProofMagic ++ data.drop 4

theorem overwritten_prefix_is_exact_magic (data : List UInt8) :
    (overwriteClosedProofMagic data).take 4 = closedProofMagic := by
  simp [overwriteClosedProofMagic, closedProofMagic]

theorem overwritten_suffix_is_unchanged (data : List UInt8) :
    (overwriteClosedProofMagic data).drop 4 = data.drop 4 := by
  simp [overwriteClosedProofMagic, closedProofMagic]

theorem overwrite_preserves_length_when_source_check_passes
    (data : List UInt8) (longEnough : 4 ≤ data.length) :
    (overwriteClosedProofMagic data).length = data.length := by
  simp [overwriteClosedProofMagic, closedProofMagic]
  omega

/-- The ledger projection from `V5ProductionStateBridge`, plus the actual
proof bytes mutated by the recorded close helper.  `proofData` belongs to the
proof account selected at instruction position zero. -/
structure RecordedCloseState (Address Nullifier Anchor : Type*) where
  ledger : CloseLedgerState Address Nullifier Anchor
  proofData : List UInt8

/-- Every deterministic condition needed for the successful path.  The first
field contains the exact owner, signer, writable, distinct-address,
open-proof, positive-balance, finalized-proof, and u64-addition checks from the
coarser model.  The second field is the later mutable-data length check. -/
structure RecordedCloseSuccessRequirements
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (accounts : CloseAccountView Address)
    (state : RecordedCloseState Address Nullifier Anchor)
    (checks : CloseDataChecks) : Prop where
  ledgerChecks : ProductionCloseRequirements accounts state.ledger checks
  proofDataHasFourBytes : 4 ≤ state.proofData.length

/-- Successful source operations in their exact order across `close_proof`,
`close_finalized_proof_account`, and
`refund_program_owned_proof_account`. -/
inductive RecordedCloseOperation (Address : Type*) where
  | proofAccountSelected
  | refundAccountSelected
  | proofDataBorrowedForLifecycle
  | uploadedBoundsChecked
  | finalizedBitChecked
  | lifecycleDataBorrowReleased
  | proofOwnerChecked
  | proofSignerChecked
  | refundSignerChecked
  | proofWritableChecked
  | refundWritableChecked
  | distinctAddressChecked
  | refundOwnerChecked
  | proofBalanceRead
  | positiveProofBalanceChecked
  | refundBalanceRead
  | refundAdditionChecked
  | proofDataMutablyBorrowed
  | proofDataLengthChecked
  | proofLamportsMutablyBorrowed
  | refundLamportsMutablyBorrowed
  | proofMagicWritten
  | refundBalanceWritten (recipient : Address)
  | proofBalanceZeroed
  deriving DecidableEq

def recordedCloseSuccessTrace {Address : Type*}
    (accounts : CloseAccountView Address) :
    List (RecordedCloseOperation Address) :=
  [.proofAccountSelected,
    .refundAccountSelected,
    .proofDataBorrowedForLifecycle,
    .uploadedBoundsChecked,
    .finalizedBitChecked,
    .lifecycleDataBorrowReleased,
    .proofOwnerChecked,
    .proofSignerChecked,
    .refundSignerChecked,
    .proofWritableChecked,
    .refundWritableChecked,
    .distinctAddressChecked,
    .refundOwnerChecked,
    .proofBalanceRead,
    .positiveProofBalanceChecked,
    .refundBalanceRead,
    .refundAdditionChecked,
    .proofDataMutablyBorrowed,
    .proofDataLengthChecked,
    .proofLamportsMutablyBorrowed,
    .refundLamportsMutablyBorrowed,
    .proofMagicWritten,
    .refundBalanceWritten accounts.refundAddress,
    .proofBalanceZeroed]

def applyRecordedClose
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (accounts : CloseAccountView Address)
    (state : RecordedCloseState Address Nullifier Anchor) :
    RecordedCloseState Address Nullifier Anchor :=
  { ledger := applyProductionClose accounts state.ledger
    proofData := overwriteClosedProofMagic state.proofData }

inductive RecordedCloseOutcome (State Address : Type*) where
  | rejected
  | committed (state : State) (trace : List (RecordedCloseOperation Address))

/-- Executable successful/rejected model of the recorded source.  The source
reads only the first two accounts, so additional account metas remain ignored
exactly as in `decodeCloseAccountPrefix`. -/
noncomputable def runRecordedClose
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (rawAccounts : List (RawAccount Address))
    (state : RecordedCloseState Address Nullifier Anchor)
    (checks : CloseDataChecks) :
    RecordedCloseOutcome (RecordedCloseState Address Nullifier Anchor) Address :=
  match decodeCloseAccountPrefix rawAccounts with
  | none => .rejected
  | some accounts =>
      letI : Decidable (RecordedCloseSuccessRequirements accounts state checks) :=
        Classical.propDecidable _
      if _requirements : RecordedCloseSuccessRequirements accounts state checks then
        .committed (applyRecordedClose accounts state)
          (recordedCloseSuccessTrace accounts)
      else
        .rejected

/-! ## Consequences of a successful close -/

theorem recorded_close_success_is_exact
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (rawAccounts : List (RawAccount Address))
    (state nextState : RecordedCloseState Address Nullifier Anchor)
    (checks : CloseDataChecks)
    (trace : List (RecordedCloseOperation Address))
    (success : runRecordedClose rawAccounts state checks =
      .committed nextState trace) :
    ∃ accounts proof refund tail,
      decodeCloseAccountPrefix rawAccounts = some accounts ∧
      rawAccounts = proof :: refund :: tail ∧
      accounts.refundAddress = refund.address ∧
      RecordedCloseSuccessRequirements accounts state checks ∧
      nextState.proofData = closedProofMagic ++ state.proofData.drop 4 ∧
      nextState.proofData.take 4 = closedProofMagic ∧
      nextState.proofData.drop 4 = state.proofData.drop 4 ∧
      nextState.proofData.length = state.proofData.length ∧
      nextState.ledger.spend.proofClosed = true ∧
      nextState.ledger.spend.proofLamports = 0 ∧
      nextState.ledger.spend.lastRefund =
        some (accounts.refundAddress, state.ledger.spend.proofLamports) ∧
      nextState.ledger.balances accounts.refundAddress =
        state.ledger.balances accounts.refundAddress +
          state.ledger.spend.proofLamports ∧
      (∀ address, address ≠ accounts.refundAddress →
        nextState.ledger.balances address = state.ledger.balances address) ∧
      nextState.ledger.spend.poolAnchor = state.ledger.spend.poolAnchor ∧
      nextState.ledger.spend.poolSequence = state.ledger.spend.poolSequence ∧
      nextState.ledger.spend.poolDeploymentDomain =
        state.ledger.spend.poolDeploymentDomain ∧
      nextState.ledger.spend.markers = state.ledger.spend.markers ∧
      trace = recordedCloseSuccessTrace accounts := by
  unfold runRecordedClose at success
  split at success
  · simp at success
  · rename_i accounts decoded
    split at success
    · rename_i requirements
      cases success
      obtain ⟨proof, refund, tail, rawEq, refundEq⟩ :=
        decoded_close_refund_is_supplied_second_account decoded
      have dataEq : (applyRecordedClose accounts state).proofData =
          closedProofMagic ++ state.proofData.drop 4 := by
        rfl
      have prefixFact : (applyRecordedClose accounts state).proofData.take 4 =
          closedProofMagic := overwritten_prefix_is_exact_magic state.proofData
      have suffixFact : (applyRecordedClose accounts state).proofData.drop 4 =
          state.proofData.drop 4 := overwritten_suffix_is_unchanged state.proofData
      have lengthFact : (applyRecordedClose accounts state).proofData.length =
          state.proofData.length :=
        overwrite_preserves_length_when_source_check_passes state.proofData
          requirements.proofDataHasFourBytes
      have otherBalances : ∀ address, address ≠ accounts.refundAddress →
          (applyRecordedClose accounts state).ledger.balances address =
            state.ledger.balances address := by
        intro address notRefund
        simp [applyRecordedClose, applyProductionClose, notRefund]
      refine ⟨accounts, proof, refund, tail, decoded, rawEq, refundEq,
        requirements, dataEq, prefixFact, suffixFact, lengthFact, ?_⟩
      simp [applyRecordedClose, applyProductionClose, applyCloseSuccess]
      simpa [applyRecordedClose, applyProductionClose] using otherBalances
    · simp at success

/-- The close never uses a hardcoded refund wallet.  On every successful run,
the credited address is the second supplied account. -/
theorem successful_refund_recipient_is_second_account
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (rawAccounts : List (RawAccount Address))
    (state nextState : RecordedCloseState Address Nullifier Anchor)
    (checks : CloseDataChecks)
    (trace : List (RecordedCloseOperation Address))
    (success : runRecordedClose rawAccounts state checks =
      .committed nextState trace) :
    ∃ proof refund tail,
      rawAccounts = proof :: refund :: tail ∧
      nextState.ledger.balances refund.address =
        state.ledger.balances refund.address +
          state.ledger.spend.proofLamports := by
  obtain ⟨accounts, proof, refund, tail, _decoded, rawEq, refundEq,
    _requirements, _dataEq, _prefix, _suffix, _length, _closed, _zero,
    _lastRefund, credited, _others, _anchor, _sequence, _domain, _markers,
    _trace⟩ := recorded_close_success_is_exact rawAccounts state nextState
      checks trace success
  refine ⟨proof, refund, tail, rawEq, ?_⟩
  simpa [refundEq] using credited

/-- Any lamports present at close time are included.  This is why an inbound
dust transfer cannot redirect or strand the refund in this model: the source
reads the live proof balance and credits that whole value. -/
theorem successful_close_includes_inbound_dust
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (rawAccounts : List (RawAccount Address))
    (state nextState : RecordedCloseState Address Nullifier Anchor)
    (checks : CloseDataChecks)
    (trace : List (RecordedCloseOperation Address))
    (baseBalance inboundDust : Nat)
    (balanceAtClose : state.ledger.spend.proofLamports =
      baseBalance + inboundDust)
    (success : runRecordedClose rawAccounts state checks =
      .committed nextState trace) :
    ∃ refundAddress,
      nextState.ledger.balances refundAddress =
        state.ledger.balances refundAddress + baseBalance + inboundDust := by
  obtain ⟨accounts, _proof, _refund, _tail, _decoded, _rawEq, _refundEq,
    _requirements, _dataEq, _prefix, _suffix, _length, _closed, _zero,
    _lastRefund, credited, _others, _anchor, _sequence, _domain, _markers,
    _trace⟩ := recorded_close_success_is_exact rawAccounts state nextState
      checks trace success
  refine ⟨accounts.refundAddress, ?_⟩
  rw [credited, balanceAtClose]
  omega

/-! ## Exact source-equality and runtime boundaries -/

/-- The remaining universal source-level equality.  Its codomain includes the
exact bytes and balances, unlike the earlier coarse close predicate. -/
def ExactRecordedRustRawCloseEquality
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (rustClose : List (RawAccount Address) →
      RecordedCloseState Address Nullifier Anchor → CloseDataChecks →
      RecordedCloseOutcome (RecordedCloseState Address Nullifier Anchor)
        Address) : Prop :=
  ∀ rawAccounts state checks,
    rustClose rawAccounts state checks = runRecordedClose rawAccounts state checks

theorem rust_close_success_inherits_exact_bytes_and_refund
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (rustClose : List (RawAccount Address) →
      RecordedCloseState Address Nullifier Anchor → CloseDataChecks →
      RecordedCloseOutcome (RecordedCloseState Address Nullifier Anchor)
        Address)
    (equality : ExactRecordedRustRawCloseEquality rustClose)
    (rawAccounts : List (RawAccount Address))
    (state nextState : RecordedCloseState Address Nullifier Anchor)
    (checks : CloseDataChecks)
    (trace : List (RecordedCloseOperation Address))
    (success : rustClose rawAccounts state checks =
      .committed nextState trace) :
    ∃ (accounts : CloseAccountView Address)
      (proof refund : RawAccount Address) (tail : List (RawAccount Address)),
      rawAccounts = proof :: refund :: tail ∧
      accounts.refundAddress = refund.address ∧
      nextState.proofData.take 4 = closedProofMagic ∧
      nextState.proofData.drop 4 = state.proofData.drop 4 ∧
      nextState.ledger.spend.proofLamports = 0 ∧
      nextState.ledger.balances accounts.refundAddress =
        state.ledger.balances accounts.refundAddress +
          state.ledger.spend.proofLamports ∧
      nextState.ledger.spend.poolAnchor = state.ledger.spend.poolAnchor ∧
      nextState.ledger.spend.poolSequence = state.ledger.spend.poolSequence ∧
      nextState.ledger.spend.markers = state.ledger.spend.markers := by
  have modeled : runRecordedClose rawAccounts state checks =
      .committed nextState trace := by
    rw [← equality rawAccounts state checks]
    exact success
  obtain ⟨accounts, proof, refund, tail, _decoded, rawEq, refundEq,
    _requirements, _dataEq, prefixFact, suffixFact, _length, _closed, zero,
    _lastRefund, credited, _others, anchor, sequence, _domain, markers,
    _trace⟩ := recorded_close_success_is_exact rawAccounts state nextState
      checks trace modeled
  exact ⟨accounts, proof, refund, tail, rawEq, refundEq, prefixFact, suffixFact, zero,
    credited, anchor, sequence, markers⟩

/-- External library facts needed before the extracted Rust body can be
identified with the executable Lean state.  These are narrower than Solana
transaction-runtime assumptions. -/
structure RecordedAccountInfoSemantics where
  publicFieldsMatchAccountMetadata : Prop
  lamportsReadReturnsLiveBalance : Prop
  mutableDataBorrowTargetsProofBytes : Prop
  mutableProofLamportsBorrowTargetsProofBalance : Prop
  mutableRefundLamportsBorrowTargetsRefundBalance : Prop
  sliceCopyWritesExactlyFirstFourBytes : Prop

/-- Solana behavior still needed after source equality and `AccountInfo`
semantics have been supplied. -/
structure RecordedCloseRuntimeSemantics where
  failedInstructionWritesRollBack : Prop
  successfulInstructionWritesCommitAtomically : Prop
  zeroLamportProgramAccountIsRemovedAtCommit : Prop
  finalizedRpcObservationMatchesCommittedState : Prop

#print axioms overwritten_prefix_is_exact_magic
#print axioms overwritten_suffix_is_unchanged
#print axioms overwrite_preserves_length_when_source_check_passes
#print axioms recorded_close_success_is_exact
#print axioms successful_refund_recipient_is_second_account
#print axioms successful_close_includes_inbound_dust
#print axioms rust_close_success_inherits_exact_bytes_and_refund

end AspisV5RecordedCloseBytes
