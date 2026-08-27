import AspisFormal.Pool.V7EightLaneCompactDispatch

/-!
# Compact-dispatch to atomic-settlement composition

This module joins the reconstructed ASQ8/ASR8 transport object to the exact
one-transaction forest and custody theorems.  It is deliberately independent
of byte parsing: the Rust/Aeneas source bridge must provide the authentication
and snapshot hypotheses below.
-/

set_option autoImplicit false

namespace AspisPool.V7EightLaneCompactSettlement

open AspisPool.IncrementalMerkleV1
open AspisPool.V7EightLaneForestGeometry
open AspisPool.V7EightLaneForestRelation
open AspisPool.V7EightLaneForestTerminal
open AspisPool.V7EightLaneCheckpointChronology
open AspisPool.V7EightLaneCheckpointSettlement
open AspisPool.V7EightLaneDeposit
open AspisPool.V7EightLaneCustodySettlement
open AspisPool.V7EightLaneCompactDispatch

structure CompactSnapshotMatches
    {K Nullifier Profile Release PoolProgram Payment
      ProofAccount MasterAccount CheckpointAccount LaneAccount : Type}
    (request : CompactRequest Profile Release PoolProgram Payment)
    (snapshot : ForestAccountSnapshot ProofAccount MasterAccount
      CheckpointAccount LaneAccount ForestCheckpointMaster
      (ForestCheckpoint (Digest K)) (ForestPairLiveState K))
    (state : ForestVaultState K Nullifier)
    (statement : ForestTerminalStatement K Nullifier) : Prop where
  masterExact : snapshot.master = state.pool.checkpointMaster
  checkpointAnchorExact : snapshot.checkpoint.globalRoot =
    statement.membershipAnchor
  laneExact : snapshot.lane = state.pool.atomic.lanes statement.outputLane

structure CompactTransferAccepted
    {K Nullifier Profile Release PoolProgram Payment
      ProofAccount MasterAccount CheckpointAccount LaneAccount : Type}
    [CommRing K]
    (parent : Digest K → Digest K → Digest K)
    (emptyLeaf : Digest K)
    (compressPair : PairLeaf K → Digest K)
    (depth : Nat)
    (laneOfNullifier : Nullifier → Lane)
    (baseRelation : ForestTerminalStatement K Nullifier →
      ForestTerminalProof K parent → Prop)
    (request : CompactRequest Profile Release PoolProgram Payment)
    (snapshot : ForestAccountSnapshot ProofAccount MasterAccount
      CheckpointAccount LaneAccount ForestCheckpointMaster
      (ForestCheckpoint (Digest K)) (ForestPairLiveState K))
    (state : ForestVaultState K Nullifier)
    (statement : ForestTerminalStatement K Nullifier)
    (proof : ForestTerminalProof K parent)
    (result : CompactResult MasterAccount LaneAccount Nullifier
      (ForestPairLiveState K)) where
  snapshotMatches : CompactSnapshotMatches request snapshot state statement
  resultAuthenticates : ResultAuthenticates snapshot.masterAccount
    snapshot.laneAccount statement.nullifier statement.laneResult result
  transferAccepted : ForestPrivateTransferAccepted parent emptyLeaf
    compressPair depth laneOfNullifier baseRelation state statement proof

structure CompactWithdrawalAccepted
    {K Nullifier Profile Release PoolProgram Payment
      ProofAccount MasterAccount CheckpointAccount LaneAccount : Type}
    [CommRing K]
    (parent : Digest K → Digest K → Digest K)
    (emptyLeaf : Digest K)
    (compressPair : PairLeaf K → Digest K)
    (depth : Nat)
    (laneOfNullifier : Nullifier → Lane)
    (baseRelation : ForestTerminalStatement K Nullifier →
      ForestTerminalProof K parent → Prop)
    (request : CompactRequest Profile Release PoolProgram Payment)
    (snapshot : ForestAccountSnapshot ProofAccount MasterAccount
      CheckpointAccount LaneAccount ForestCheckpointMaster
      (ForestCheckpoint (Digest K)) (ForestPairLiveState K))
    (state : ForestVaultState K Nullifier)
    (statement : ForestTerminalStatement K Nullifier)
    (proof : ForestTerminalProof K parent)
    (result : CompactResult MasterAccount LaneAccount Nullifier
      (ForestPairLiveState K)) where
  snapshotMatches : CompactSnapshotMatches request snapshot state statement
  resultAuthenticates : ResultAuthenticates snapshot.masterAccount
    snapshot.laneAccount statement.nullifier statement.laneResult result
  withdrawalAccepted : ForestWithdrawalAccepted parent emptyLeaf
    compressPair depth laneOfNullifier baseRelation state statement proof

/-- A compactly dispatched transfer reconstructs one semantic statement and
inherits the complete atomic Pool postcondition and custody conservation. -/
theorem compact_transfer_has_exact_atomic_custody_postcondition
    {K Nullifier Profile Release PoolProgram Payment
      ProofAccount MasterAccount CheckpointAccount LaneAccount : Type}
    [CommRing K] [NoZeroDivisors K]
    (parent : Digest K → Digest K → Digest K)
    (emptyLeaf : Digest K)
    (compressPair : PairLeaf K → Digest K)
    (depth : Nat)
    (laneOfNullifier : Nullifier → Lane)
    (baseRelation : ForestTerminalStatement K Nullifier →
      ForestTerminalProof K parent → Prop)
    (request : CompactRequest Profile Release PoolProgram Payment)
    (snapshot : ForestAccountSnapshot ProofAccount MasterAccount
      CheckpointAccount LaneAccount ForestCheckpointMaster
      (ForestCheckpoint (Digest K)) (ForestPairLiveState K))
    (state : ForestVaultState K Nullifier)
    (statement : ForestTerminalStatement K Nullifier)
    (proof : ForestTerminalProof K parent)
    (result : CompactResult MasterAccount LaneAccount Nullifier
      (ForestPairLiveState K))
    (accepted : CompactTransferAccepted parent emptyLeaf compressPair depth
      laneOfNullifier baseRelation request snapshot state statement proof result)
    (reserve : Nat) (conserved : VaultConserved reserve state) :
    reconstructSemanticStatement request snapshot statement.laneResult =
        reconstructSemanticStatement request snapshot result.candidate ∧
      snapshot.master = state.pool.checkpointMaster ∧
      snapshot.checkpoint.globalRoot = statement.membershipAnchor ∧
      snapshot.lane = state.pool.atomic.lanes statement.outputLane ∧
      ForestOneTransactionPostcondition parent laneOfNullifier state.pool
        statement proof ∧
      VaultConserved reserve
        (applyPrivateTransfer state statement
          accepted.transferAccepted.relation) := by
  refine ⟨authenticated_result_gives_identical_semantic_reconstruction request
      snapshot statement.nullifier statement.laneResult result
      accepted.resultAuthenticates, accepted.snapshotMatches.masterExact,
      accepted.snapshotMatches.checkpointAnchorExact,
      accepted.snapshotMatches.laneExact, ?_, ?_⟩
  · exact accepted_pool_spend_has_exact_one_transaction_postcondition parent
      emptyLeaf compressPair depth laneOfNullifier baseRelation state.pool
      statement proof accepted.transferAccepted.poolAccepted
  · exact private_transfer_preserves_forest_vault_conservation parent emptyLeaf
      compressPair depth laneOfNullifier baseRelation state statement proof
      accepted.transferAccepted reserve conserved

/-- The withdrawal path has the same authenticated reconstruction and atomic
state postcondition, with withdrawal-specific custody conservation. -/
theorem compact_withdrawal_has_exact_atomic_custody_postcondition
    {K Nullifier Profile Release PoolProgram Payment
      ProofAccount MasterAccount CheckpointAccount LaneAccount : Type}
    [CommRing K] [NoZeroDivisors K]
    (parent : Digest K → Digest K → Digest K)
    (emptyLeaf : Digest K)
    (compressPair : PairLeaf K → Digest K)
    (depth : Nat)
    (laneOfNullifier : Nullifier → Lane)
    (baseRelation : ForestTerminalStatement K Nullifier →
      ForestTerminalProof K parent → Prop)
    (request : CompactRequest Profile Release PoolProgram Payment)
    (snapshot : ForestAccountSnapshot ProofAccount MasterAccount
      CheckpointAccount LaneAccount ForestCheckpointMaster
      (ForestCheckpoint (Digest K)) (ForestPairLiveState K))
    (state : ForestVaultState K Nullifier)
    (statement : ForestTerminalStatement K Nullifier)
    (proof : ForestTerminalProof K parent)
    (result : CompactResult MasterAccount LaneAccount Nullifier
      (ForestPairLiveState K))
    (accepted : CompactWithdrawalAccepted parent emptyLeaf compressPair depth
      laneOfNullifier baseRelation request snapshot state statement proof result)
    (reserve : Nat) (conserved : VaultConserved reserve state) :
    reconstructSemanticStatement request snapshot statement.laneResult =
        reconstructSemanticStatement request snapshot result.candidate ∧
      snapshot.master = state.pool.checkpointMaster ∧
      snapshot.checkpoint.globalRoot = statement.membershipAnchor ∧
      snapshot.lane = state.pool.atomic.lanes statement.outputLane ∧
      ForestOneTransactionPostcondition parent laneOfNullifier state.pool
        statement proof ∧
      VaultConserved reserve
        (applyWithdrawal state statement
          accepted.withdrawalAccepted.relation) := by
  refine ⟨authenticated_result_gives_identical_semantic_reconstruction request
      snapshot statement.nullifier statement.laneResult result
      accepted.resultAuthenticates, accepted.snapshotMatches.masterExact,
      accepted.snapshotMatches.checkpointAnchorExact,
      accepted.snapshotMatches.laneExact, ?_, ?_⟩
  · exact accepted_pool_spend_has_exact_one_transaction_postcondition parent
      emptyLeaf compressPair depth laneOfNullifier baseRelation state.pool
      statement proof accepted.withdrawalAccepted.poolAccepted
  · exact withdrawal_preserves_forest_vault_conservation parent emptyLeaf
      compressPair depth laneOfNullifier baseRelation state statement proof
      accepted.withdrawalAccepted reserve conserved

#print axioms compact_transfer_has_exact_atomic_custody_postcondition
#print axioms compact_withdrawal_has_exact_atomic_custody_postcondition

end AspisPool.V7EightLaneCompactSettlement
