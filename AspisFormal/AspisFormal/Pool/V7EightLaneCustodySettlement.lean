import AspisFormal.Pool.TransferOneToTwoV1
import AspisFormal.Pool.WithdrawalV1
import AspisFormal.Pool.V7EightLaneDeposit

/-!
# Custody composition for one-transaction eight-lane spends

This file joins the exact forest state transition to the existing transfer and
withdrawal value-conservation relations.  A private transfer appends one
two-output pair and charges only its public fee.  A withdrawal appends one
change commitment plus an algebraically empty second slot and removes exactly
the public withdrawal amount from custody.  In both cases the lane update and
nullifier insertion remain the same single terminal state transition.
-/

set_option autoImplicit false

namespace AspisPool.V7EightLaneCustodySettlement

open AspisPool.V7PairLeafOccupancy
open AspisPool.V7EightLaneForestGeometry
open AspisPool.V7EightLaneForestRelation
open AspisPool.V7EightLaneForestTerminal
open AspisPool.V7EightLaneCheckpointSettlement
open AspisPool.V7EightLaneDeposit

structure ForestPrivateTransferAccepted
    {K Nullifier : Type} [CommRing K]
    (parent : ForestDigest K → ForestDigest K → ForestDigest K)
    (emptyLeaf : ForestDigest K)
    (compressPair : ForestPairLeaf K → ForestDigest K)
    (depth : Nat)
    (laneOfNullifier : Nullifier → Lane)
    (baseRelation :
      ForestTerminalStatement K Nullifier →
        ForestTerminalProof K parent → Prop)
    (state : ForestVaultState K Nullifier)
    (statement : ForestTerminalStatement K Nullifier)
    (proof : ForestTerminalProof K parent) where
  poolAccepted : ForestPoolAccepted parent emptyLeaf compressPair depth
    laneOfNullifier baseRelation state.pool statement proof
  relation : AspisPool.TransferOneToTwoV1.Relation
  inputBacked : relation.inputValue ≤ state.unspentValue
  recipientCommitment : ForestDigest K
  changeCommitment : ForestDigest K
  changeSentinelInverse : K
  changeSentinelInverseCorrect :
    changeCommitment ⟨7, by decide⟩ * changeSentinelInverse = 1
  outputPairExact : proof.outputPair =
    twoOutputPair recipientCommitment changeCommitment changeSentinelInverse

def applyPrivateTransfer
    {K Nullifier : Type}
    (state : ForestVaultState K Nullifier)
    (statement : ForestTerminalStatement K Nullifier)
    (relation : AspisPool.TransferOneToTwoV1.Relation) :
    ForestVaultState K Nullifier where
  pool := applyTerminal state.pool statement
  vaultBalance := state.vaultBalance - relation.fee
  unspentValue := state.unspentValue - relation.inputValue +
    relation.output0Value + relation.output1Value

structure ForestWithdrawalAccepted
    {K Nullifier : Type} [CommRing K]
    (parent : ForestDigest K → ForestDigest K → ForestDigest K)
    (emptyLeaf : ForestDigest K)
    (compressPair : ForestPairLeaf K → ForestDigest K)
    (depth : Nat)
    (laneOfNullifier : Nullifier → Lane)
    (baseRelation :
      ForestTerminalStatement K Nullifier →
        ForestTerminalProof K parent → Prop)
    (state : ForestVaultState K Nullifier)
    (statement : ForestTerminalStatement K Nullifier)
    (proof : ForestTerminalProof K parent) where
  poolAccepted : ForestPoolAccepted parent emptyLeaf compressPair depth
    laneOfNullifier baseRelation state.pool statement proof
  relation : AspisPool.WithdrawalV1.Relation
  inputBacked : relation.inputValue ≤ state.unspentValue
  changeCommitment : ForestDigest K
  outputPairExact : proof.outputPair = singleOutputPair changeCommitment

def applyWithdrawal
    {K Nullifier : Type}
    (state : ForestVaultState K Nullifier)
    (statement : ForestTerminalStatement K Nullifier)
    (relation : AspisPool.WithdrawalV1.Relation) :
    ForestVaultState K Nullifier where
  pool := applyTerminal state.pool statement
  vaultBalance := state.vaultBalance - relation.amount
  unspentValue := state.unspentValue - relation.inputValue + relation.changeValue

theorem accepted_transfer_pair_has_two_occupied_outputs
    {K Nullifier : Type} [CommRing K]
    (parent : ForestDigest K → ForestDigest K → ForestDigest K)
    (emptyLeaf : ForestDigest K)
    (compressPair : ForestPairLeaf K → ForestDigest K)
    (depth : Nat)
    (laneOfNullifier : Nullifier → Lane)
    (baseRelation :
      ForestTerminalStatement K Nullifier →
        ForestTerminalProof K parent → Prop)
    (state : ForestVaultState K Nullifier)
    (statement : ForestTerminalStatement K Nullifier)
    (proof : ForestTerminalProof K parent)
    (accepted : ForestPrivateTransferAccepted parent emptyLeaf compressPair
      depth laneOfNullifier baseRelation state statement proof) :
    proof.outputPair.Valid ∧ proof.outputPair.secondOccupied = 1 := by
  rw [accepted.outputPairExact]
  exact ⟨twoOutputPair_valid accepted.recipientCommitment
      accepted.changeCommitment accepted.changeSentinelInverse
      accepted.changeSentinelInverseCorrect, rfl⟩

theorem accepted_withdrawal_pair_has_one_output_and_empty_second
    {K Nullifier : Type} [CommRing K]
    (parent : ForestDigest K → ForestDigest K → ForestDigest K)
    (emptyLeaf : ForestDigest K)
    (compressPair : ForestPairLeaf K → ForestDigest K)
    (depth : Nat)
    (laneOfNullifier : Nullifier → Lane)
    (baseRelation :
      ForestTerminalStatement K Nullifier →
        ForestTerminalProof K parent → Prop)
    (state : ForestVaultState K Nullifier)
    (statement : ForestTerminalStatement K Nullifier)
    (proof : ForestTerminalProof K parent)
    (accepted : ForestWithdrawalAccepted parent emptyLeaf compressPair depth
      laneOfNullifier baseRelation state statement proof) :
    proof.outputPair.Valid ∧ proof.outputPair.secondOccupied = 0 ∧
      proof.outputPair.secondCommitment = fun _ => 0 := by
  rw [accepted.outputPairExact]
  exact ⟨singleOutputPair_valid accepted.changeCommitment, rfl, rfl⟩

theorem private_transfer_preserves_forest_vault_conservation
    {K Nullifier : Type} [CommRing K]
    (parent : ForestDigest K → ForestDigest K → ForestDigest K)
    (emptyLeaf : ForestDigest K)
    (compressPair : ForestPairLeaf K → ForestDigest K)
    (depth : Nat)
    (laneOfNullifier : Nullifier → Lane)
    (baseRelation :
      ForestTerminalStatement K Nullifier →
        ForestTerminalProof K parent → Prop)
    (state : ForestVaultState K Nullifier)
    (statement : ForestTerminalStatement K Nullifier)
    (proof : ForestTerminalProof K parent)
    (accepted : ForestPrivateTransferAccepted parent emptyLeaf compressPair
      depth laneOfNullifier baseRelation state statement proof)
    (reserve : Nat) (conserved : VaultConserved reserve state) :
    VaultConserved reserve
      (applyPrivateTransfer state statement accepted.relation) := by
  have unspentDelta := AspisPool.TransferOneToTwoV1.unspent_delta_eq_sub_fee
    state.unspentValue accepted.relation accepted.inputBacked
  have feeLeUnspent : accepted.relation.fee ≤ state.unspentValue := by
    have inputBacked := accepted.inputBacked
    rw [accepted.relation.balance] at inputBacked
    omega
  unfold VaultConserved at conserved ⊢
  simp only [applyPrivateTransfer]
  rw [unspentDelta, conserved]
  exact Nat.sub_add_comm feeLeUnspent

theorem withdrawal_preserves_forest_vault_conservation
    {K Nullifier : Type} [CommRing K]
    (parent : ForestDigest K → ForestDigest K → ForestDigest K)
    (emptyLeaf : ForestDigest K)
    (compressPair : ForestPairLeaf K → ForestDigest K)
    (depth : Nat)
    (laneOfNullifier : Nullifier → Lane)
    (baseRelation :
      ForestTerminalStatement K Nullifier →
        ForestTerminalProof K parent → Prop)
    (state : ForestVaultState K Nullifier)
    (statement : ForestTerminalStatement K Nullifier)
    (proof : ForestTerminalProof K parent)
    (accepted : ForestWithdrawalAccepted parent emptyLeaf compressPair depth
      laneOfNullifier baseRelation state statement proof)
    (reserve : Nat) (conserved : VaultConserved reserve state) :
    VaultConserved reserve
      (applyWithdrawal state statement accepted.relation) := by
  have unspentDelta := AspisPool.WithdrawalV1.unspent_delta_eq_sub_amount
    state.unspentValue accepted.relation accepted.inputBacked
  have amountLeUnspent : accepted.relation.amount ≤ state.unspentValue := by
    have inputBacked := accepted.inputBacked
    rw [accepted.relation.balance] at inputBacked
    omega
  unfold VaultConserved at conserved ⊢
  simp only [applyWithdrawal]
  rw [unspentDelta, conserved]
  exact Nat.sub_add_comm amountLeUnspent

@[simp] theorem private_transfer_and_withdrawal_each_insert_nullifier
    {K Nullifier : Type}
    (state : ForestVaultState K Nullifier)
    (statement : ForestTerminalStatement K Nullifier)
    (transferRelation : AspisPool.TransferOneToTwoV1.Relation)
    (withdrawalRelation : AspisPool.WithdrawalV1.Relation) :
    statement.nullifier ∈
        (applyPrivateTransfer state statement transferRelation).pool.atomic.spentNullifiers ∧
      statement.nullifier ∈
        (applyWithdrawal state statement withdrawalRelation).pool.atomic.spentNullifiers := by
  exact ⟨accepted_terminal_marks_nullifier state.pool.atomic statement,
    accepted_terminal_marks_nullifier state.pool.atomic statement⟩

#print axioms accepted_transfer_pair_has_two_occupied_outputs
#print axioms accepted_withdrawal_pair_has_one_output_and_empty_second
#print axioms private_transfer_preserves_forest_vault_conservation
#print axioms withdrawal_preserves_forest_vault_conservation
#print axioms private_transfer_and_withdrawal_each_insert_nullifier

end AspisPool.V7EightLaneCustodySettlement
