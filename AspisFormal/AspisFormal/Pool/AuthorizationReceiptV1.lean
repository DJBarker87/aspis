import Mathlib
import AspisFormal.Pool.AtomicSettlementV1
import AspisFormal.Pool.VerifierRegistryV1

/-!
# Pool V1 verifier authorization receipts

Pure composition boundary for splitting the expensive Tag-73 verification
transaction from the atomic custody settlement transaction.  The receipt
copies the complete verifier binding; it does not replace proof soundness or
registry authorization.  Its implementation-side authenticity consists of
the canonical bytes, verifier ownership and exact verifier-derived PDA.

The only new premise is `IssuerSound`: an account accepted as an authentic
receipt was issued only after the named verifier accepted that exact binding.
The Rust/Aeneas bridge must discharge this premise for the production
entrypoint.  Once it does, receipt settlement reconstructs the same direct
verification fact and delegates to the unchanged atomic nullifier/custody
transition.
-/

set_option autoImplicit false

namespace AspisPool.AuthorizationReceiptV1

open AspisPool.AtomicSettlementV1

inductive TransitionKind where
  | privateTransfer
  | withdrawal
  deriving DecidableEq, Repr

/-- Typed abstraction of every field copied by the exact ASVS/ASVA wire. -/
structure Binding where
  statementVersion : Nat
  transitionKind : TransitionKind
  verifierProgram : Nat
  profileBinding : Nat
  releaseBinding : Nat
  pool : Nat
  deploymentDomain : Nat
  anchorSequence : Nat
  anchorRoot : Nat
  nullifier : Nat
  statementDigest : Nat
  envelopeDigest : Nat
  proofAccount : Nat
  proofBodyDigest : Nat
  proofBodyLength : Nat
  statementPayloadLength : Nat
  deriving DecidableEq, Repr

structure Receipt where
  pdaBump : Nat
  verifiedSlot : Nat
  binding : Binding
  deriving DecidableEq, Repr

def Binding.selection (binding : Binding) :
    AspisPool.VerifierRegistryV1.Selection where
  verifierProgram := binding.verifierProgram
  profileBinding := binding.profileBinding
  releaseBinding := binding.releaseBinding
  statementVersion := binding.statementVersion

/-- Settlement must recover exactly the expected binding and may not consume a
receipt apparently issued in a future slot. -/
def ExactFor (receipt : Receipt) (expected : Binding) (settlementSlot : Nat) : Prop :=
  receipt.binding = expected ∧ receipt.verifiedSlot ≤ settlementSlot

/-- Full receipt-side authorization excluding proof soundness itself. -/
def AcceptedReceipt
    (AuthenticAccount : Receipt → Prop)
    (policy : AspisPool.VerifierRegistryV1.Policy)
    (registry : AspisPool.VerifierRegistryV1.Registry)
    (entry : AspisPool.VerifierRegistryV1.Entry)
    (receipt : Receipt) (expected : Binding) (settlementSlot : Nat) : Prop :=
  AuthenticAccount receipt ∧
    ExactFor receipt expected settlementSlot ∧
    AspisPool.VerifierRegistryV1.Authorized expected.pool policy registry entry
      expected.selection settlementSlot

/-- Exact trust obligation for the verifier-owned receipt instruction. -/
def IssuerSound (AuthenticAccount : Receipt → Prop)
    (DirectVerified : Binding → Prop) : Prop :=
  ∀ receipt, AuthenticAccount receipt → DirectVerified receipt.binding

theorem accepted_receipt_reconstructs_exact_direct_verification
    (AuthenticAccount : Receipt → Prop) (DirectVerified : Binding → Prop)
    (policy : AspisPool.VerifierRegistryV1.Policy)
    (registry : AspisPool.VerifierRegistryV1.Registry)
    (entry : AspisPool.VerifierRegistryV1.Entry)
    (receipt : Receipt) (expected : Binding) (settlementSlot : Nat)
    (issuerSound : IssuerSound AuthenticAccount DirectVerified)
    (accepted : AcceptedReceipt AuthenticAccount policy registry entry receipt
      expected settlementSlot) :
    DirectVerified expected ∧
      receipt.binding = expected ∧
      receipt.verifiedSlot ≤ settlementSlot ∧
      AspisPool.VerifierRegistryV1.Authorized expected.pool policy registry entry
        expected.selection settlementSlot := by
  rcases accepted with ⟨authentic, ⟨exactBinding, notFuture⟩, authorized⟩
  have verifiedReceipt := issuerSound receipt authentic
  subst exactBinding
  exact ⟨verifiedReceipt, rfl, notFuture, authorized⟩

theorem accepted_receipt_binds_exact_active_release
    (AuthenticAccount : Receipt → Prop)
    (policy : AspisPool.VerifierRegistryV1.Policy)
    (registry : AspisPool.VerifierRegistryV1.Registry)
    (entry : AspisPool.VerifierRegistryV1.Entry)
    (receipt : Receipt) (expected : Binding) (settlementSlot : Nat)
    (accepted : AcceptedReceipt AuthenticAccount policy registry entry receipt
      expected settlementSlot) :
    entry.verifierProgram = expected.verifierProgram ∧
      entry.profileBinding = expected.profileBinding ∧
      entry.releaseBinding = expected.releaseBinding ∧
      entry.statementVersion = expected.statementVersion ∧
      AspisPool.VerifierRegistryV1.ActiveAt entry settlementSlot := by
  exact AspisPool.VerifierRegistryV1.accepted_entry_is_exact_and_active
    expected.pool policy registry entry expected.selection settlementSlot accepted.2.2

/-- Replacing direct verifier-CPI authorization by an authentic exact receipt
does not change the atomic state transformer once both gates represent the
same proof-acceptance fact. -/
theorem receipt_and_direct_transfer_gates_are_state_identical
    {Note Root Marker : Type} [DecidableEq Marker]
    (before : State Note Root Marker)
    (relation : AspisPool.TransferOneToTwoV1.Relation)
    (outputs : AspisPool.TransferOneToTwoV1.OrderedOutputs Note)
    (firstRoot secondRoot : Root) (marker : Marker)
    (receiptAuthorized directAuthorized effectsComplete : Bool)
    (sameAuthorization : receiptAuthorized = directAuthorized) :
    settleTransfer before receiptAuthorized effectsComplete relation outputs
        firstRoot secondRoot marker =
      settleTransfer before directAuthorized effectsComplete relation outputs
        firstRoot secondRoot marker := by
  rw [sameAuthorization]

theorem receipt_and_direct_withdrawal_gates_are_state_identical
    {Note Root Marker : Type} [DecidableEq Marker]
    (before : State Note Root Marker)
    (relation : AspisPool.WithdrawalV1.Relation)
    (changeNote : Note) (rootAfterChange : Root) (marker : Marker)
    (receiptAuthorized directAuthorized effectsComplete : Bool)
    (sameAuthorization : receiptAuthorized = directAuthorized) :
    settleWithdrawal before receiptAuthorized effectsComplete relation changeNote
        rootAfterChange marker =
      settleWithdrawal before directAuthorized effectsComplete relation changeNote
        rootAfterChange marker := by
  rw [sameAuthorization]

/-- An immutable receipt can be replayed as input, but the already consumed
nullifier makes the second custody transition the exact pre-state. -/
theorem replayed_transfer_receipt_cannot_repeat_settlement
    {Note Root Marker : Type} [DecidableEq Marker]
    (before : State Note Root Marker)
    (relation : AspisPool.TransferOneToTwoV1.Relation)
    (outputs : AspisPool.TransferOneToTwoV1.OrderedOutputs Note)
    (firstRoot secondRoot : Root) (marker : Marker)
    (duplicate : marker ∈ before.consumedNullifiers) :
    settleTransfer before true true relation outputs firstRoot secondRoot marker = before := by
  exact duplicate_transfer_nullifier_rejects before relation outputs firstRoot
    secondRoot marker duplicate

theorem replayed_withdrawal_receipt_cannot_repeat_settlement
    {Note Root Marker : Type} [DecidableEq Marker]
    (before : State Note Root Marker)
    (relation : AspisPool.WithdrawalV1.Relation)
    (changeNote : Note) (rootAfterChange : Root) (marker : Marker)
    (duplicate : marker ∈ before.consumedNullifiers) :
    settleWithdrawal before true true relation changeNote rootAfterChange marker = before := by
  exact duplicate_withdrawal_nullifier_rejects before relation changeNote rootAfterChange
    marker duplicate

#print axioms accepted_receipt_reconstructs_exact_direct_verification
#print axioms accepted_receipt_binds_exact_active_release
#print axioms receipt_and_direct_transfer_gates_are_state_identical
#print axioms receipt_and_direct_withdrawal_gates_are_state_identical
#print axioms replayed_transfer_receipt_cannot_repeat_settlement
#print axioms replayed_withdrawal_receipt_cannot_repeat_settlement

end AspisPool.AuthorizationReceiptV1
