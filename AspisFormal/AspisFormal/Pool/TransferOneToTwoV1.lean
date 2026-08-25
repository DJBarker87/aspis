import Mathlib
import AspisFormal.Pool.DepositV1

/-!
# Pool V1 one-input/two-output transfer ledger

This is the pure P4 conservation theorem.  The proof relation supplies one
hidden input value, two hidden output values and one public fee satisfying

`input = output0 + output1 + fee`.

The Pool keeps old commitments forever, appends the two ordered output
commitments and charges the public fee from both the token vault and the ghost
unspent-value ledger.  Nullifier reservation, verifier dispatch, concrete
commitments, tree roots and Solana atomicity are composed in later source and
state-transition modules.
-/

set_option autoImplicit false

namespace AspisPool.TransferOneToTwoV1

open AspisPool.DepositV1

structure Relation where
  inputValue : Nat
  output0Value : Nat
  output1Value : Nat
  fee : Nat
  inputBound : inputValue < valueLimit
  output0Bound : output0Value < valueLimit
  output1Bound : output1Value < valueLimit
  feeBound : fee < valueLimit
  balance : inputValue = output0Value + output1Value + fee

/-- The proof may name recipient and change internally, but their public
commitment order is independently randomized by the wallet.  The state
machine consumes only this ordered pair. -/
structure OrderedOutputs (Note : Type) where
  first : Note
  second : Note
  deriving DecidableEq, Repr

/-- Ghost successful transition.  Commitments are append-only; spending is
represented by the separately consumed nullifier rather than leaf deletion. -/
def transfer {Note Root : Type}
    (before : Ledger Note Root) (relation : Relation)
    (outputs : OrderedOutputs Note) (rootAfterFirst rootAfterSecond : Root) :
    Ledger Note Root where
  vaultBalance := before.vaultBalance - relation.fee
  unspentValue := before.unspentValue - relation.inputValue +
    relation.output0Value + relation.output1Value
  notes := before.notes ++ [outputs.first, outputs.second]
  roots := before.roots ++ [rootAfterFirst, rootAfterSecond]

/-- Removing the proved input and adding the two proved outputs charges
exactly the public fee in the ghost ledger. -/
theorem unspent_delta_eq_sub_fee
    (beforeUnspent : Nat) (relation : Relation)
    (inputBacked : relation.inputValue ≤ beforeUnspent) :
    beforeUnspent - relation.inputValue + relation.output0Value +
        relation.output1Value =
      beforeUnspent - relation.fee := by
  have recoverInput :
      beforeUnspent - relation.inputValue + relation.inputValue =
        beforeUnspent := Nat.sub_add_cancel inputBacked
  have balance := relation.balance
  have recoverWithOutputs :
      (beforeUnspent - relation.inputValue + relation.output0Value +
          relation.output1Value) + relation.fee = beforeUnspent := by
    omega
  exact Nat.eq_sub_of_add_eq recoverWithOutputs

/-- Exact P4 ledger theorem: two commitments and two chronological roots are
appended in their supplied order, the vault and ghost unspent value both fall
by the same fee, and conservation is preserved. -/
theorem private_transfer_preserves_vault_invariant
    {Note Root : Type} (before : Ledger Note Root) (relation : Relation)
    (outputs : OrderedOutputs Note) (rootAfterFirst rootAfterSecond : Root)
    (reserve : Nat) (conserved : VaultConserved reserve before)
    (inputBacked : relation.inputValue ≤ before.unspentValue) :
    let after := transfer before relation outputs rootAfterFirst rootAfterSecond
    after.vaultBalance = before.vaultBalance - relation.fee ∧
      after.unspentValue = before.unspentValue - relation.fee ∧
      after.notes = before.notes ++ [outputs.first, outputs.second] ∧
      after.roots = before.roots ++ [rootAfterFirst, rootAfterSecond] ∧
      after.notes.length = before.notes.length + 2 ∧
      after.roots.length = before.roots.length + 2 ∧
      VaultConserved reserve after := by
  dsimp [transfer]
  have unspentDelta := unspent_delta_eq_sub_fee
    before.unspentValue relation inputBacked
  have feeLeUnspent : relation.fee ≤ before.unspentValue := by
    rw [relation.balance] at inputBacked
    omega
  have feeLeVault : relation.fee ≤ before.vaultBalance := by
    unfold VaultConserved at conserved
    rw [conserved]
    omega
  refine ⟨rfl, unspentDelta, rfl, rfl, by simp, by simp, ?_⟩
  unfold VaultConserved
  change before.vaultBalance - relation.fee =
    (before.unspentValue - relation.inputValue + relation.output0Value +
      relation.output1Value) + reserve
  rw [unspentDelta]
  unfold VaultConserved at conserved
  rw [conserved]
  exact Nat.sub_add_comm feeLeUnspent

/-- Appending the two outputs never rewrites or removes any prior commitment. -/
theorem old_commitment_prefix_preserved
    {Note Root : Type} (before : Ledger Note Root) (relation : Relation)
    (outputs : OrderedOutputs Note) (rootAfterFirst rootAfterSecond : Root) :
    (transfer before relation outputs rootAfterFirst rootAfterSecond).notes.take
        before.notes.length = before.notes := by
  simp [transfer]

/-- A failed proof/dispatch/marker stage selects the byte-identical pre-state
in the pure transactional model. -/
def settleAfterAuthorization {State : Type} (before candidate : State) :
    Bool → State
  | false => before
  | true => candidate

theorem failed_authorization_no_state_change {State : Type}
    (before candidate : State) :
    settleAfterAuthorization before candidate false = before := rfl

/-- Swapping the ordered commitments swaps their public leaf order.  No
theorem identifies either position as recipient or change. -/
theorem output_order_is_exact
    {Note Root : Type} (before : Ledger Note Root) (relation : Relation)
    (first second : Note) (rootAfterFirst rootAfterSecond : Root) :
    (transfer before relation ⟨first, second⟩ rootAfterFirst rootAfterSecond).notes =
      before.notes ++ [first, second] := rfl

#print axioms unspent_delta_eq_sub_fee
#print axioms private_transfer_preserves_vault_invariant
#print axioms old_commitment_prefix_preserved
#print axioms failed_authorization_no_state_change
#print axioms output_order_is_exact

end AspisPool.TransferOneToTwoV1
