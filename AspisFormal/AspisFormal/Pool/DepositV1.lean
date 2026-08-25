import Mathlib

/-!
# Pool V1 vault-backed deposit

This is the small pure ledger theorem for P2.  The note constructor and Merkle
root are parameters: production refinement instantiates the former with the
frozen Poseidon note commitment and obtains the latter from the already-proved
incremental-tree append kernel. Legacy SPL Token CPI execution, account-data
refresh and Solana transaction rollback are explicit external source/runtime
boundaries.
-/

set_option autoImplicit false

namespace AspisPool.DepositV1

def valueLimit : Nat := 2 ^ 30
def receiptBytes : Nat := 224
def payloadMaxBytes : Nat := 512
def returnMaxBytes : Nat := receiptBytes + payloadMaxBytes

structure DepositInput (Owner Asset Salt Payload : Type) where
  ownerKey : Owner
  amount : Nat
  asset : Asset
  salt : Salt
  payload : Payload

def ValidAmount (amount : Nat) : Prop := 0 < amount ∧ amount < valueLimit

/-- Abstract economic state. `unspentValue` is ghost accounting: the on-chain
program cannot reveal or sum private note values. -/
structure Ledger (Note Root : Type) where
  vaultBalance : Nat
  unspentValue : Nat
  notes : List Note
  roots : List Root
  deriving DecidableEq, Repr

def VaultConserved {Note Root : Type} (reserve : Nat)
    (state : Ledger Note Root) : Prop :=
  state.vaultBalance = state.unspentValue + reserve

/-- Pure successful deposit. The source bridge must establish that the token
CPI increased the canonical vault by exactly `amount` before selecting this
branch. -/
def deposit {Owner Asset Salt Payload Note Root : Type}
    (commit : Owner → Nat → Asset → Salt → Note)
    (before : Ledger Note Root)
    (input : DepositInput Owner Asset Salt Payload)
    (newRoot : Root) : Ledger Note Root where
  vaultBalance := before.vaultBalance + input.amount
  unspentValue := before.unspentValue + input.amount
  notes := before.notes ++
    [commit input.ownerKey input.amount input.asset input.salt]
  roots := before.roots ++ [newRoot]

/-- One exact successful deposit adds the same public amount to custody and
the ghost unspent ledger, appends exactly its deterministic commitment, and
records exactly one chronological post-append root. -/
theorem deposit_appends_and_backs_note
    {Owner Asset Salt Payload Note Root : Type}
    (commit : Owner → Nat → Asset → Salt → Note)
    (before : Ledger Note Root)
    (input : DepositInput Owner Asset Salt Payload)
    (newRoot : Root) (reserve : Nat)
    (conserved : VaultConserved reserve before) :
    let after := deposit commit before input newRoot
    after.vaultBalance = before.vaultBalance + input.amount ∧
      after.unspentValue = before.unspentValue + input.amount ∧
      after.notes = before.notes ++
        [commit input.ownerKey input.amount input.asset input.salt] ∧
      after.roots = before.roots ++ [newRoot] ∧
      VaultConserved reserve after := by
  dsimp [deposit]
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  unfold VaultConserved at conserved ⊢
  change before.vaultBalance + input.amount =
    before.unspentValue + input.amount + reserve
  rw [conserved]
  omega

theorem deposit_preserves_vault_conservation
    {Owner Asset Salt Payload Note Root : Type}
    (commit : Owner → Nat → Asset → Salt → Note)
    (before : Ledger Note Root)
    (input : DepositInput Owner Asset Salt Payload)
    (newRoot : Root) (reserve : Nat)
    (conserved : VaultConserved reserve before) :
    VaultConserved reserve (deposit commit before input newRoot) := by
  unfold VaultConserved at conserved ⊢
  dsimp [deposit]
  rw [conserved]
  omega

/-- Delivery bytes cannot change the note, vault delta, leaf ordering or root
history. They are emitted alongside the receipt, never trusted as commitment
input. -/
theorem opaque_payload_irrelevant
    {Owner Asset Salt Payload Note Root : Type}
    (commit : Owner → Nat → Asset → Salt → Note)
    (before : Ledger Note Root)
    (owner : Owner) (amount : Nat) (asset : Asset) (salt : Salt)
    (leftPayload rightPayload : Payload) (newRoot : Root) :
    deposit commit before
        ⟨owner, amount, asset, salt, leftPayload⟩ newRoot =
      deposit commit before
        ⟨owner, amount, asset, salt, rightPayload⟩ newRoot := rfl

/-- Fail-closed transactional model: without an exact successful transfer,
the candidate append is not selected. Solana rollback/source refinement must
show that the Rust error path realizes this branch byte-for-byte. -/
def settleAfterTransfer {State : Type} (before candidate : State) :
    Bool → State
  | false => before
  | true => candidate

theorem failed_transfer_no_state_change {State : Type}
    (before candidate : State) :
    settleAfterTransfer before candidate false = before := rfl

theorem exact_format_bounds :
    valueLimit = 1_073_741_824 ∧
      receiptBytes = 224 ∧ payloadMaxBytes = 512 ∧ returnMaxBytes = 736 := by
  norm_num [valueLimit, receiptBytes, payloadMaxBytes, returnMaxBytes]

#print axioms deposit_appends_and_backs_note
#print axioms deposit_preserves_vault_conservation
#print axioms opaque_payload_irrelevant
#print axioms failed_transfer_no_state_change
#print axioms exact_format_bounds

end AspisPool.DepositV1
