import Mathlib
import AspisFormal.Pool.TransferOneToTwoV1

/-!
# Pool V1 payment proof relation

This file fixes the application-level relation that a production Pool proof
profile must compile.  It is deliberately independent of the PCS: Poseidon,
Merkle evaluation and owner/nullifier derivation are explicit function
parameters, while every public state-transition field is represented in the
typed statement.

The existing Tag-73 read-only `AtomicPaymentStatementV4` profile proves a
one-input/one-output relation and is not silently treated as this relation.

The frozen Pool V1 transition ABI has no fee field: transfer bytes reserve the
only spare `u32` as zero and withdrawal bytes use it for the public amount.
Consequently this V1 relation has canonical fee zero.  A nonzero in-note fee
requires a new statement/profile version.
-/

set_option autoImplicit false

namespace AspisPool.PaymentRelationV1

open AspisPool.DepositV1

inductive TransitionKind where
  | privateTransfer
  | withdrawal
  deriving DecidableEq, Repr

/-- Fields common to both proof-authorized Pool transitions.  Pool identity,
deployment domain and anchor sequence are transcript-bound public data even
though they are not private witness values. -/
structure CommonPublic (Pool Domain Root Digest Asset : Type) where
  pool : Pool
  deploymentDomain : Domain
  anchorSequence : Nat
  anchorRoot : Root
  nullifier : Digest
  asset : Asset
  deriving DecidableEq, Repr

structure NoteOpening (Owner Asset Salt : Type) where
  owner : Owner
  value : Nat
  asset : Asset
  salt : Salt
  deriving DecidableEq, Repr

structure InputWitness (Key Salt Asset Path : Type) where
  nullifierKey : Key
  inputSalt : Salt
  inputAsset : Asset
  inputValue : Nat
  path : Path
  deriving DecidableEq, Repr

structure PrivateTransferPublic
    (Pool Domain Root Digest Asset : Type) where
  common : CommonPublic Pool Domain Root Digest Asset
  firstOutputCommitment : Digest
  secondOutputCommitment : Digest
  deriving DecidableEq, Repr

structure PrivateTransferWitness
    (Key Salt Asset Path Owner : Type) where
  input : InputWitness Key Salt Asset Path
  firstOutput : NoteOpening Owner Asset Salt
  secondOutput : NoteOpening Owner Asset Salt
  deriving DecidableEq, Repr

structure WithdrawalPublic
    (Pool Domain Root Digest Asset Destination : Type) where
  common : CommonPublic Pool Domain Root Digest Asset
  amount : Nat
  destination : Destination
  changeCommitment : Digest
  deriving DecidableEq, Repr

structure WithdrawalWitness
    (Key Salt Asset Path Owner : Type) where
  input : InputWitness Key Salt Asset Path
  change : NoteOpening Owner Asset Salt
  deriving DecidableEq, Repr

structure Primitives
    (Key Salt Asset Path Owner Root Digest : Type) where
  ownerKey : Key → Owner
  nullifier : Key → Salt → Digest
  noteCommitment : Owner → Nat → Asset → Salt → Digest
  merkleRoot : Digest → Path → Root

def ValidValue (value : Nat) : Prop := value < valueLimit

/-- Exact one-private-input/two-private-output relation.  The output ordering
is public and is the ordering consumed by the append-only Pool tree; neither
position is semantically labelled recipient or change. -/
def ValidPrivateTransfer
    {Pool Domain Root Digest Asset Key Salt Path Owner : Type}
    [DecidableEq Root] [DecidableEq Digest] [DecidableEq Asset]
    (primitives : Primitives Key Salt Asset Path Owner Root Digest)
    (statement : PrivateTransferPublic Pool Domain Root Digest Asset)
    (witness : PrivateTransferWitness Key Salt Asset Path Owner) : Prop :=
  ValidValue witness.input.inputValue ∧
  ValidValue witness.firstOutput.value ∧
  ValidValue witness.secondOutput.value ∧
  witness.input.inputAsset = statement.common.asset ∧
  witness.firstOutput.asset = statement.common.asset ∧
  witness.secondOutput.asset = statement.common.asset ∧
  primitives.merkleRoot
      (primitives.noteCommitment
        (primitives.ownerKey witness.input.nullifierKey)
        witness.input.inputValue witness.input.inputAsset
        witness.input.inputSalt)
      witness.input.path = statement.common.anchorRoot ∧
  primitives.nullifier witness.input.nullifierKey witness.input.inputSalt =
    statement.common.nullifier ∧
  primitives.noteCommitment witness.firstOutput.owner
      witness.firstOutput.value witness.firstOutput.asset
      witness.firstOutput.salt = statement.firstOutputCommitment ∧
  primitives.noteCommitment witness.secondOutput.owner
      witness.secondOutput.value witness.secondOutput.asset
      witness.secondOutput.salt = statement.secondOutputCommitment ∧
  witness.input.inputValue = witness.firstOutput.value +
    witness.secondOutput.value

/-- Exact private withdrawal relation.  The public token destination and
amount are proof-bound alongside one hidden change note. -/
def ValidWithdrawal
    {Pool Domain Root Digest Asset Destination Key Salt Path Owner : Type}
    [DecidableEq Root] [DecidableEq Digest] [DecidableEq Asset]
    (primitives : Primitives Key Salt Asset Path Owner Root Digest)
    (statement : WithdrawalPublic Pool Domain Root Digest Asset Destination)
    (witness : WithdrawalWitness Key Salt Asset Path Owner) : Prop :=
  ValidValue witness.input.inputValue ∧
  ValidValue witness.change.value ∧
  0 < statement.amount ∧ ValidValue statement.amount ∧
  witness.input.inputAsset = statement.common.asset ∧
  witness.change.asset = statement.common.asset ∧
  primitives.merkleRoot
      (primitives.noteCommitment
        (primitives.ownerKey witness.input.nullifierKey)
        witness.input.inputValue witness.input.inputAsset
        witness.input.inputSalt)
      witness.input.path = statement.common.anchorRoot ∧
  primitives.nullifier witness.input.nullifierKey witness.input.inputSalt =
    statement.common.nullifier ∧
  primitives.noteCommitment witness.change.owner witness.change.value
      witness.change.asset witness.change.salt = statement.changeCommitment ∧
  witness.input.inputValue = witness.change.value + statement.amount

theorem valid_private_transfer_yields_ledger_relation
    {Pool Domain Root Digest Asset Key Salt Path Owner : Type}
    [DecidableEq Root] [DecidableEq Digest] [DecidableEq Asset]
    (primitives : Primitives Key Salt Asset Path Owner Root Digest)
    (statement : PrivateTransferPublic Pool Domain Root Digest Asset)
    (witness : PrivateTransferWitness Key Salt Asset Path Owner)
    (valid : ValidPrivateTransfer primitives statement witness) :
    ∃ relation : AspisPool.TransferOneToTwoV1.Relation,
      relation.inputValue = witness.input.inputValue ∧
      relation.output0Value = witness.firstOutput.value ∧
      relation.output1Value = witness.secondOutput.value ∧
      relation.fee = 0 := by
  rcases valid with ⟨inputBound, firstBound, secondBound, _, _, _, _,
    _, _, _, balance⟩
  exact ⟨{
    inputValue := witness.input.inputValue
    output0Value := witness.firstOutput.value
    output1Value := witness.secondOutput.value
    fee := 0
    inputBound := inputBound
    output0Bound := firstBound
    output1Bound := secondBound
    feeBound := by norm_num [valueLimit]
    balance := by simpa using balance }, rfl, rfl, rfl, rfl⟩

theorem valid_withdrawal_conserves_value
    {Pool Domain Root Digest Asset Destination Key Salt Path Owner : Type}
    [DecidableEq Root] [DecidableEq Digest] [DecidableEq Asset]
    (primitives : Primitives Key Salt Asset Path Owner Root Digest)
    (statement : WithdrawalPublic Pool Domain Root Digest Asset Destination)
    (witness : WithdrawalWitness Key Salt Asset Path Owner)
    (valid : ValidWithdrawal primitives statement witness) :
    witness.input.inputValue = witness.change.value + statement.amount := by
  exact valid.2.2.2.2.2.2.2.2.2

/-- One fixed private-transfer witness determines every proof-relevant public
anchor/nullifier/output field.  Pool identity, deployment domain and
anchor sequence are separately transcript-bound statement fields. -/
theorem same_transfer_witness_public_projection_unique
    {Pool Domain Root Digest Asset Key Salt Path Owner : Type}
    [DecidableEq Root] [DecidableEq Digest] [DecidableEq Asset]
    (primitives : Primitives Key Salt Asset Path Owner Root Digest)
    (left right : PrivateTransferPublic Pool Domain Root Digest Asset)
    (witness : PrivateTransferWitness Key Salt Asset Path Owner)
    (leftValid : ValidPrivateTransfer primitives left witness)
    (rightValid : ValidPrivateTransfer primitives right witness) :
    left.common.anchorRoot = right.common.anchorRoot ∧
      left.common.nullifier = right.common.nullifier ∧
      left.firstOutputCommitment = right.firstOutputCommitment ∧
      left.secondOutputCommitment = right.secondOutputCommitment := by
  rcases leftValid with ⟨_, _, _, _, _, _, leftAnchor, leftNullifier,
    leftFirst, leftSecond, leftBalance⟩
  rcases rightValid with ⟨_, _, _, _, _, _, rightAnchor, rightNullifier,
    rightFirst, rightSecond, rightBalance⟩
  refine ⟨leftAnchor.symm.trans rightAnchor, leftNullifier.symm.trans rightNullifier,
    leftFirst.symm.trans rightFirst, leftSecond.symm.trans rightSecond⟩

/-- For one fixed withdrawal witness the public amount is determined by value
conservation.  The destination, Pool identity and deployment data are instead
bound by the public statement and Fiat--Shamir transcript. -/
theorem same_withdrawal_witness_amount_determined
    {Pool Domain Root Digest Asset Destination Key Salt Path Owner : Type}
    [DecidableEq Root] [DecidableEq Digest] [DecidableEq Asset]
    (primitives : Primitives Key Salt Asset Path Owner Root Digest)
    (left right : WithdrawalPublic Pool Domain Root Digest Asset Destination)
    (witness : WithdrawalWitness Key Salt Asset Path Owner)
    (leftValid : ValidWithdrawal primitives left witness)
    (rightValid : ValidWithdrawal primitives right witness) :
    left.amount = right.amount := by
  have leftBalance := valid_withdrawal_conserves_value primitives left witness leftValid
  have rightBalance := valid_withdrawal_conserves_value primitives right witness rightValid
  omega

#print axioms valid_private_transfer_yields_ledger_relation
#print axioms valid_withdrawal_conserves_value
#print axioms same_transfer_witness_public_projection_unique
#print axioms same_withdrawal_witness_amount_determined

end AspisPool.PaymentRelationV1
