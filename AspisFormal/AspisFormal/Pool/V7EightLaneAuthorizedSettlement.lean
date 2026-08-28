import AspisFormal.Pool.V7EightLaneCompactSettlement

/-!
# Versioned-registry authorization to compact atomic settlement

The selected verifier is not chosen by unauthenticated instruction bytes.
This module composes the exact active registry-entry theorem with the compact
ASQ8/ASR8 reconstruction and one-transaction custody postcondition.
-/

set_option autoImplicit false

namespace AspisPool.V7EightLaneAuthorizedSettlement

open AspisPool.VerifierRegistryV1
open AspisPool.IncrementalMerkleV1
open AspisPool.V7EightLaneForestGeometry
open AspisPool.V7EightLaneForestRelation
open AspisPool.V7EightLaneForestTerminal
open AspisPool.V7EightLaneCheckpointChronology
open AspisPool.V7EightLaneCheckpointSettlement
open AspisPool.V7EightLaneDeposit
open AspisPool.V7EightLaneCustodySettlement
open AspisPool.V7EightLaneCompactDispatch
open AspisPool.V7EightLaneCompactSettlement

structure AuthorizedCompactTransfer
    {K Nullifier Payment ProofAccount MasterAccount CheckpointAccount
      LaneAccount : Type} [CommRing K]
    (parent : Digest K → Digest K → Digest K)
    (emptyLeaf : Digest K)
    (compressPair : PairLeaf K → Digest K)
    (depth : Nat)
    (laneOfNullifier : Nullifier → Lane)
    (baseRelation : ForestTerminalStatement K Nullifier →
      ForestTerminalProof K parent → Prop)
    (pool : Nat) (policy : Policy) (registry : Registry) (entry : Entry)
    (selection : Selection) (slot : Nat)
    (request : CompactRequest Nat Nat Nat Payment)
    (snapshot : ForestAccountSnapshot ProofAccount MasterAccount
      CheckpointAccount LaneAccount ForestCheckpointMaster
      (ForestCheckpoint (Digest K)) (ForestPairLiveState K))
    (state : ForestVaultState K Nullifier)
    (statement : ForestTerminalStatement K Nullifier)
    (proof : ForestTerminalProof K parent)
    (result : CompactResult MasterAccount LaneAccount Nullifier
      (ForestPairLiveState K)) where
  registryAuthorized : Authorized pool policy registry entry selection slot
  requestProfileExact : request.profile = selection.profileBinding
  requestReleaseExact : request.release = selection.releaseBinding
  requestPoolExact : request.poolProgram = pool
  compactAccepted : CompactTransferAccepted parent emptyLeaf compressPair depth
    laneOfNullifier baseRelation request snapshot state statement proof result

structure AuthorizedCompactWithdrawal
    {K Nullifier Payment ProofAccount MasterAccount CheckpointAccount
      LaneAccount : Type} [CommRing K]
    (parent : Digest K → Digest K → Digest K)
    (emptyLeaf : Digest K)
    (compressPair : PairLeaf K → Digest K)
    (depth : Nat)
    (laneOfNullifier : Nullifier → Lane)
    (baseRelation : ForestTerminalStatement K Nullifier →
      ForestTerminalProof K parent → Prop)
    (pool : Nat) (policy : Policy) (registry : Registry) (entry : Entry)
    (selection : Selection) (slot : Nat)
    (request : CompactRequest Nat Nat Nat Payment)
    (snapshot : ForestAccountSnapshot ProofAccount MasterAccount
      CheckpointAccount LaneAccount ForestCheckpointMaster
      (ForestCheckpoint (Digest K)) (ForestPairLiveState K))
    (state : ForestVaultState K Nullifier)
    (statement : ForestTerminalStatement K Nullifier)
    (proof : ForestTerminalProof K parent)
    (result : CompactResult MasterAccount LaneAccount Nullifier
      (ForestPairLiveState K)) where
  registryAuthorized : Authorized pool policy registry entry selection slot
  requestProfileExact : request.profile = selection.profileBinding
  requestReleaseExact : request.release = selection.releaseBinding
  requestPoolExact : request.poolProgram = pool
  compactAccepted : CompactWithdrawalAccepted parent emptyLeaf compressPair
    depth laneOfNullifier baseRelation request snapshot state statement proof
    result

theorem authorized_compact_transfer_closes_registry_transport_and_custody
    {K Nullifier Payment ProofAccount MasterAccount CheckpointAccount
      LaneAccount : Type} [CommRing K] [NoZeroDivisors K]
    (parent : Digest K → Digest K → Digest K)
    (emptyLeaf : Digest K)
    (compressPair : PairLeaf K → Digest K)
    (depth : Nat)
    (laneOfNullifier : Nullifier → Lane)
    (baseRelation : ForestTerminalStatement K Nullifier →
      ForestTerminalProof K parent → Prop)
    (pool : Nat) (policy : Policy) (registry : Registry) (entry : Entry)
    (selection : Selection) (slot : Nat)
    (request : CompactRequest Nat Nat Nat Payment)
    (snapshot : ForestAccountSnapshot ProofAccount MasterAccount
      CheckpointAccount LaneAccount ForestCheckpointMaster
      (ForestCheckpoint (Digest K)) (ForestPairLiveState K))
    (state : ForestVaultState K Nullifier)
    (statement : ForestTerminalStatement K Nullifier)
    (proof : ForestTerminalProof K parent)
    (result : CompactResult MasterAccount LaneAccount Nullifier
      (ForestPairLiveState K))
    (accepted : AuthorizedCompactTransfer parent emptyLeaf compressPair depth
      laneOfNullifier baseRelation pool policy registry entry selection slot
      request snapshot state statement proof result)
    (reserve : Nat) (conserved : VaultConserved reserve state) :
    entry.verifierProgram = selection.verifierProgram ∧
      entry.profileBinding = request.profile ∧
      entry.releaseBinding = request.release ∧
      entry.statementVersion = selection.statementVersion ∧
      ActiveAt entry slot ∧
      reconstructSemanticStatement request snapshot statement.laneResult =
        reconstructSemanticStatement request snapshot result.candidate ∧
      snapshot.master = state.pool.checkpointMaster ∧
      snapshot.checkpoint.globalRoot = statement.membershipAnchor ∧
      snapshot.lane = state.pool.atomic.lanes statement.outputLane ∧
      ForestOneTransactionPostcondition parent laneOfNullifier state.pool
        statement proof ∧
      VaultConserved reserve
        (applyPrivateTransfer state statement
          accepted.compactAccepted.transferAccepted.relation) := by
  have registryExact := accepted_entry_is_exact_and_active pool policy registry
    entry selection slot accepted.registryAuthorized
  have settlement := compact_transfer_has_exact_atomic_custody_postcondition
    parent emptyLeaf compressPair depth laneOfNullifier baseRelation request
    snapshot state statement proof result accepted.compactAccepted reserve conserved
  exact ⟨registryExact.1,
    registryExact.2.1.trans accepted.requestProfileExact.symm,
    registryExact.2.2.1.trans accepted.requestReleaseExact.symm,
    registryExact.2.2.2.1, registryExact.2.2.2.2,
    settlement.1, settlement.2.1, settlement.2.2.1,
    settlement.2.2.2.1, settlement.2.2.2.2.1,
    settlement.2.2.2.2.2⟩

theorem authorized_compact_withdrawal_closes_registry_transport_and_custody
    {K Nullifier Payment ProofAccount MasterAccount CheckpointAccount
      LaneAccount : Type} [CommRing K] [NoZeroDivisors K]
    (parent : Digest K → Digest K → Digest K)
    (emptyLeaf : Digest K)
    (compressPair : PairLeaf K → Digest K)
    (depth : Nat)
    (laneOfNullifier : Nullifier → Lane)
    (baseRelation : ForestTerminalStatement K Nullifier →
      ForestTerminalProof K parent → Prop)
    (pool : Nat) (policy : Policy) (registry : Registry) (entry : Entry)
    (selection : Selection) (slot : Nat)
    (request : CompactRequest Nat Nat Nat Payment)
    (snapshot : ForestAccountSnapshot ProofAccount MasterAccount
      CheckpointAccount LaneAccount ForestCheckpointMaster
      (ForestCheckpoint (Digest K)) (ForestPairLiveState K))
    (state : ForestVaultState K Nullifier)
    (statement : ForestTerminalStatement K Nullifier)
    (proof : ForestTerminalProof K parent)
    (result : CompactResult MasterAccount LaneAccount Nullifier
      (ForestPairLiveState K))
    (accepted : AuthorizedCompactWithdrawal parent emptyLeaf compressPair depth
      laneOfNullifier baseRelation pool policy registry entry selection slot
      request snapshot state statement proof result)
    (reserve : Nat) (conserved : VaultConserved reserve state) :
    entry.verifierProgram = selection.verifierProgram ∧
      entry.profileBinding = request.profile ∧
      entry.releaseBinding = request.release ∧
      entry.statementVersion = selection.statementVersion ∧
      ActiveAt entry slot ∧
      reconstructSemanticStatement request snapshot statement.laneResult =
        reconstructSemanticStatement request snapshot result.candidate ∧
      snapshot.master = state.pool.checkpointMaster ∧
      snapshot.checkpoint.globalRoot = statement.membershipAnchor ∧
      snapshot.lane = state.pool.atomic.lanes statement.outputLane ∧
      ForestOneTransactionPostcondition parent laneOfNullifier state.pool
        statement proof ∧
      VaultConserved reserve
        (applyWithdrawal state statement
          accepted.compactAccepted.withdrawalAccepted.relation) := by
  have registryExact := accepted_entry_is_exact_and_active pool policy registry
    entry selection slot accepted.registryAuthorized
  have settlement := compact_withdrawal_has_exact_atomic_custody_postcondition
    parent emptyLeaf compressPair depth laneOfNullifier baseRelation request
    snapshot state statement proof result accepted.compactAccepted reserve conserved
  exact ⟨registryExact.1,
    registryExact.2.1.trans accepted.requestProfileExact.symm,
    registryExact.2.2.1.trans accepted.requestReleaseExact.symm,
    registryExact.2.2.2.1, registryExact.2.2.2.2,
    settlement.1, settlement.2.1, settlement.2.2.1,
    settlement.2.2.2.1, settlement.2.2.2.2.1,
    settlement.2.2.2.2.2⟩

#print axioms authorized_compact_transfer_closes_registry_transport_and_custody
#print axioms authorized_compact_withdrawal_closes_registry_transport_and_custody

end AspisPool.V7EightLaneAuthorizedSettlement
