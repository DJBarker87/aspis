import Mathlib
import AspisFormal.Pool.TransferOneToTwoV1
import AspisFormal.Pool.WithdrawalV1

/-!
# Pool V1 atomic settlement

Pure composition of proof authorization, nullifier freshness and the custody
ledger transitions.  A failed authorization, duplicate marker or failed
runtime-effect flag selects the byte-identical pre-state; a successful branch
appends the exact marker and delegates conservation to the transfer/withdrawal
ledger theorems.

The flag recording completion of fallible Solana CPIs is a model input.  The
Rust/source bridge and Solana's transactional rollback semantics must prove
that the production entrypoint implements this selection.
-/

set_option autoImplicit false

namespace AspisPool.AtomicSettlementV1

open AspisPool.DepositV1

structure State (Note Root Marker : Type) where
  ledger : Ledger Note Root
  consumedNullifiers : List Marker
  deriving DecidableEq, Repr

def transferCandidate {Note Root Marker : Type}
    (before : State Note Root Marker)
    (relation : AspisPool.TransferOneToTwoV1.Relation)
    (outputs : AspisPool.TransferOneToTwoV1.OrderedOutputs Note)
    (rootAfterFirst rootAfterSecond : Root) (marker : Marker) :
    State Note Root Marker where
  ledger := AspisPool.TransferOneToTwoV1.transfer before.ledger relation outputs
    rootAfterFirst rootAfterSecond
  consumedNullifiers := before.consumedNullifiers ++ [marker]

def withdrawalCandidate {Note Root Marker : Type}
    (before : State Note Root Marker)
    (relation : AspisPool.WithdrawalV1.Relation)
    (changeNote : Note) (rootAfterChange : Root) (marker : Marker) :
    State Note Root Marker where
  ledger := AspisPool.WithdrawalV1.withdraw before.ledger relation changeNote
    rootAfterChange
  consumedNullifiers := before.consumedNullifiers ++ [marker]

/-- The two booleans separate proof/registry/anchor authorization from the
completion of every fallible account/CPI effect that precedes persistence. -/
def settleTransfer {Note Root Marker : Type} [DecidableEq Marker]
    (before : State Note Root Marker) (authorized effectsComplete : Bool)
    (relation : AspisPool.TransferOneToTwoV1.Relation)
    (outputs : AspisPool.TransferOneToTwoV1.OrderedOutputs Note)
    (rootAfterFirst rootAfterSecond : Root) (marker : Marker) :
    State Note Root Marker :=
  if authorized = true ∧ effectsComplete = true ∧
      marker ∉ before.consumedNullifiers then
    transferCandidate before relation outputs rootAfterFirst rootAfterSecond marker
  else
    before

def settleWithdrawal {Note Root Marker : Type} [DecidableEq Marker]
    (before : State Note Root Marker) (authorized effectsComplete : Bool)
    (relation : AspisPool.WithdrawalV1.Relation)
    (changeNote : Note) (rootAfterChange : Root) (marker : Marker) :
    State Note Root Marker :=
  if authorized = true ∧ effectsComplete = true ∧
      marker ∉ before.consumedNullifiers then
    withdrawalCandidate before relation changeNote rootAfterChange marker
  else
    before

theorem rejected_transfer_is_exact_prestate
    {Note Root Marker : Type} [DecidableEq Marker]
    (before : State Note Root Marker)
    (relation : AspisPool.TransferOneToTwoV1.Relation)
    (outputs : AspisPool.TransferOneToTwoV1.OrderedOutputs Note)
    (firstRoot secondRoot : Root) (marker : Marker)
    (authorized effectsComplete : Bool)
    (rejected : ¬ (authorized = true ∧ effectsComplete = true ∧
      marker ∉ before.consumedNullifiers)) :
    settleTransfer before authorized effectsComplete relation outputs firstRoot
      secondRoot marker = before := by
  simp [settleTransfer, rejected]

theorem rejected_withdrawal_is_exact_prestate
    {Note Root Marker : Type} [DecidableEq Marker]
    (before : State Note Root Marker)
    (relation : AspisPool.WithdrawalV1.Relation)
    (changeNote : Note) (rootAfterChange : Root) (marker : Marker)
    (authorized effectsComplete : Bool)
    (rejected : ¬ (authorized = true ∧ effectsComplete = true ∧
      marker ∉ before.consumedNullifiers)) :
    settleWithdrawal before authorized effectsComplete relation changeNote
      rootAfterChange marker = before := by
  simp [settleWithdrawal, rejected]

theorem duplicate_transfer_nullifier_rejects
    {Note Root Marker : Type} [DecidableEq Marker]
    (before : State Note Root Marker)
    (relation : AspisPool.TransferOneToTwoV1.Relation)
    (outputs : AspisPool.TransferOneToTwoV1.OrderedOutputs Note)
    (firstRoot secondRoot : Root) (marker : Marker)
    (duplicate : marker ∈ before.consumedNullifiers) :
    settleTransfer before true true relation outputs firstRoot secondRoot marker =
      before := by
  apply rejected_transfer_is_exact_prestate
  simp [duplicate]

theorem duplicate_withdrawal_nullifier_rejects
    {Note Root Marker : Type} [DecidableEq Marker]
    (before : State Note Root Marker)
    (relation : AspisPool.WithdrawalV1.Relation)
    (changeNote : Note) (rootAfterChange : Root) (marker : Marker)
    (duplicate : marker ∈ before.consumedNullifiers) :
    settleWithdrawal before true true relation changeNote rootAfterChange marker =
      before := by
  apply rejected_withdrawal_is_exact_prestate
  simp [duplicate]

theorem successful_transfer_is_exact_and_conserved
    {Note Root Marker : Type} [DecidableEq Marker]
    (before : State Note Root Marker)
    (relation : AspisPool.TransferOneToTwoV1.Relation)
    (outputs : AspisPool.TransferOneToTwoV1.OrderedOutputs Note)
    (firstRoot secondRoot : Root) (marker : Marker) (reserve : Nat)
    (fresh : marker ∉ before.consumedNullifiers)
    (conserved : VaultConserved reserve before.ledger)
    (inputBacked : relation.inputValue ≤ before.ledger.unspentValue) :
    let after := settleTransfer before true true relation outputs firstRoot
      secondRoot marker
    after = transferCandidate before relation outputs firstRoot secondRoot marker ∧
      after.consumedNullifiers = before.consumedNullifiers ++ [marker] ∧
      after.ledger.notes = before.ledger.notes ++ [outputs.first, outputs.second] ∧
      after.ledger.roots = before.ledger.roots ++ [firstRoot, secondRoot] ∧
      VaultConserved reserve after.ledger := by
  have ledgerResult :=
    AspisPool.TransferOneToTwoV1.private_transfer_preserves_vault_invariant
      before.ledger relation outputs firstRoot secondRoot reserve conserved inputBacked
  simp only [settleTransfer, fresh, not_false_eq_true, true_and,
    transferCandidate]
  exact ⟨rfl, rfl, ledgerResult.2.2.1, ledgerResult.2.2.2.1,
    ledgerResult.2.2.2.2.2.2⟩

theorem successful_withdrawal_is_exact_and_conserved
    {Note Root Marker : Type} [DecidableEq Marker]
    (before : State Note Root Marker)
    (relation : AspisPool.WithdrawalV1.Relation)
    (changeNote : Note) (rootAfterChange : Root) (marker : Marker)
    (reserve : Nat) (fresh : marker ∉ before.consumedNullifiers)
    (conserved : VaultConserved reserve before.ledger)
    (inputBacked : relation.inputValue ≤ before.ledger.unspentValue) :
    let after := settleWithdrawal before true true relation changeNote
      rootAfterChange marker
    after = withdrawalCandidate before relation changeNote rootAfterChange marker ∧
      after.consumedNullifiers = before.consumedNullifiers ++ [marker] ∧
      after.ledger.notes = before.ledger.notes ++ [changeNote] ∧
      after.ledger.roots = before.ledger.roots ++ [rootAfterChange] ∧
      VaultConserved reserve after.ledger := by
  have ledgerResult :=
    AspisPool.WithdrawalV1.private_withdrawal_preserves_vault_invariant
      before.ledger relation changeNote rootAfterChange reserve conserved inputBacked
  simp only [settleWithdrawal, fresh, not_false_eq_true, true_and,
    withdrawalCandidate]
  exact ⟨rfl, rfl, ledgerResult.2.2.1, ledgerResult.2.2.2.1,
    ledgerResult.2.2.2.2.2.2⟩

#print axioms rejected_transfer_is_exact_prestate
#print axioms rejected_withdrawal_is_exact_prestate
#print axioms duplicate_transfer_nullifier_rejects
#print axioms duplicate_withdrawal_nullifier_rejects
#print axioms successful_transfer_is_exact_and_conserved
#print axioms successful_withdrawal_is_exact_and_conserved

end AspisPool.AtomicSettlementV1
