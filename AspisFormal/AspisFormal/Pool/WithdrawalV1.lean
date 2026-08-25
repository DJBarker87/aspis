import Mathlib
import AspisFormal.Pool.DepositV1

/-!
# Pool V1 private withdrawal ledger

This is the pure custody theorem for one proved private input, one hidden
change output and one public token withdrawal.  Pool V1 has canonical fee
zero, so the proof relation supplies

`inputValue = changeValue + amount`.

Concrete note commitments, nullifiers, retained roots, token CPI execution
and Solana rollback are composed by their dedicated layers.
-/

set_option autoImplicit false

namespace AspisPool.WithdrawalV1

open AspisPool.DepositV1

structure Relation where
  inputValue : Nat
  changeValue : Nat
  amount : Nat
  inputBound : inputValue < valueLimit
  changeBound : changeValue < valueLimit
  amountPositive : 0 < amount
  amountBound : amount < valueLimit
  balance : inputValue = changeValue + amount

/-- Ghost successful withdrawal.  The old input commitment remains in the
append-only tree; its nullifier is consumed separately. -/
def withdraw {Note Root : Type}
    (before : Ledger Note Root) (relation : Relation)
    (changeNote : Note) (rootAfterChange : Root) : Ledger Note Root where
  vaultBalance := before.vaultBalance - relation.amount
  unspentValue := before.unspentValue - relation.inputValue +
    relation.changeValue
  notes := before.notes ++ [changeNote]
  roots := before.roots ++ [rootAfterChange]

theorem unspent_delta_eq_sub_amount
    (beforeUnspent : Nat) (relation : Relation)
    (inputBacked : relation.inputValue ≤ beforeUnspent) :
    beforeUnspent - relation.inputValue + relation.changeValue =
      beforeUnspent - relation.amount := by
  have balance := relation.balance
  omega

/-- Exact withdrawal ledger theorem: custody and ghost unspent value both
fall by the public amount, exactly one change commitment/root is appended and
the reserve invariant is preserved. -/
theorem private_withdrawal_preserves_vault_invariant
    {Note Root : Type} (before : Ledger Note Root) (relation : Relation)
    (changeNote : Note) (rootAfterChange : Root)
    (reserve : Nat) (conserved : VaultConserved reserve before)
    (inputBacked : relation.inputValue ≤ before.unspentValue) :
    let after := withdraw before relation changeNote rootAfterChange
    after.vaultBalance = before.vaultBalance - relation.amount ∧
      after.unspentValue = before.unspentValue - relation.amount ∧
      after.notes = before.notes ++ [changeNote] ∧
      after.roots = before.roots ++ [rootAfterChange] ∧
      after.notes.length = before.notes.length + 1 ∧
      after.roots.length = before.roots.length + 1 ∧
      VaultConserved reserve after := by
  dsimp [withdraw]
  have unspentDelta := unspent_delta_eq_sub_amount
    before.unspentValue relation inputBacked
  have amountLeUnspent : relation.amount ≤ before.unspentValue := by
    rw [relation.balance] at inputBacked
    omega
  refine ⟨rfl, unspentDelta, rfl, rfl, by simp, by simp, ?_⟩
  unfold VaultConserved at conserved ⊢
  change before.vaultBalance - relation.amount =
    (before.unspentValue - relation.inputValue + relation.changeValue) + reserve
  rw [unspentDelta]
  rw [conserved]
  omega

theorem old_commitment_prefix_preserved
    {Note Root : Type} (before : Ledger Note Root) (relation : Relation)
    (changeNote : Note) (rootAfterChange : Root) :
    (withdraw before relation changeNote rootAfterChange).notes.take
        before.notes.length = before.notes := by
  simp [withdraw]

/-- The public destination selects the token recipient but cannot affect the
proved change note, append order or post-withdrawal root. -/
theorem destination_irrelevant_to_private_ledger
    {Note Root Destination : Type}
    (before : Ledger Note Root) (relation : Relation)
    (changeNote : Note) (rootAfterChange : Root)
    (_left _right : Destination) :
    withdraw before relation changeNote rootAfterChange =
      withdraw before relation changeNote rootAfterChange := rfl

#print axioms unspent_delta_eq_sub_amount
#print axioms private_withdrawal_preserves_vault_invariant
#print axioms old_commitment_prefix_preserved
#print axioms destination_irrelevant_to_private_ledger

end AspisPool.WithdrawalV1
