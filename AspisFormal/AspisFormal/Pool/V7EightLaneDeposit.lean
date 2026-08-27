import AspisFormal.Pool.DepositV1
import AspisFormal.Pool.V7EightLaneCheckpointSettlement

/-!
# Vault-backed deposits into the eight-lane forest

A deposit routes from its canonical commitment to one public lane, transfers
the public amount into custody, and appends exactly one pair whose first slot
is occupied and whose second slot is algebraically empty.  It changes no
nullifier or retained checkpoint.  The newly deposited note joins the global
anonymity set at the next permissionless checkpoint.
-/

set_option autoImplicit false

namespace AspisPool.V7EightLaneDeposit

open AspisPool.DepositV1
open AspisPool.IncrementalMerkleV1
open AspisPool.V7PairLeafOccupancy
open AspisPool.V7PairAppendAfterstateCorrect
open AspisPool.V7EightLaneForestGeometry
open AspisPool.V7EightLaneForestRelation
open AspisPool.V7EightLaneForestTerminal
open AspisPool.V7EightLaneCheckpointChronology
open AspisPool.V7EightLaneCheckpointSettlement

abbrev ForestDigest (K : Type) :=
  AspisPool.V7EightLaneForestRelation.Digest K
abbrev ForestPairLeaf (K : Type) :=
  AspisPool.V7PairLeafOccupancy.PairLeaf K

structure ForestVaultState (K Nullifier : Type) where
  pool : ForestPoolState K Nullifier
  vaultBalance : Nat
  unspentValue : Nat

def VaultConserved {K Nullifier : Type}
    (reserve : Nat) (state : ForestVaultState K Nullifier) : Prop :=
  state.vaultBalance = state.unspentValue + reserve

structure ForestDepositStatement (K : Type) where
  amount : Nat
  commitment : ForestDigest K
  outputLane : Lane
  laneSource : ForestPairLiveState K
  laneResult : ForestPairLiveState K

structure ForestDepositAccepted
    {K Nullifier : Type} [CommRing K]
    (parent : ForestDigest K → ForestDigest K → ForestDigest K)
    (emptyLeaf : ForestDigest K)
    (compressPair : ForestPairLeaf K → ForestDigest K)
    (depth : Nat)
    (laneOfCommitment : ForestDigest K → Lane)
    (state : ForestVaultState K Nullifier)
    (statement : ForestDepositStatement K) : Prop where
  amountValid : ValidAmount statement.amount
  outputLaneExact :
    statement.outputLane = laneOfCommitment statement.commitment
  sourceIsLockedLiveLane :
    statement.laneSource = state.pool.atomic.lanes statement.outputLane
  appendExact : ExactPairAppendTransition parent emptyLeaf compressPair depth
    (singleOutputPair statement.commitment)
    statement.laneSource statement.laneResult

def applyDeposit
    {K Nullifier : Type}
    (state : ForestVaultState K Nullifier)
    (statement : ForestDepositStatement K) : ForestVaultState K Nullifier where
  pool := {
    atomic := {
      lanes := updateLane state.pool.atomic.lanes statement.outputLane
        statement.laneResult
      spentNullifiers := state.pool.atomic.spentNullifiers
    }
    checkpointMaster := state.pool.checkpointMaster
    retainedAnchors := state.pool.retainedAnchors
  }
  vaultBalance := state.vaultBalance + statement.amount
  unspentValue := state.unspentValue + statement.amount

theorem accepted_deposit_pair_is_valid_and_empty_second
    {K Nullifier : Type} [CommRing K]
    (parent : ForestDigest K → ForestDigest K → ForestDigest K)
    (emptyLeaf : ForestDigest K)
    (compressPair : ForestPairLeaf K → ForestDigest K)
    (depth : Nat)
    (laneOfCommitment : ForestDigest K → Lane)
    (state : ForestVaultState K Nullifier)
    (statement : ForestDepositStatement K)
    (accepted : ForestDepositAccepted parent emptyLeaf compressPair depth
      laneOfCommitment state statement) :
    (singleOutputPair statement.commitment).Valid ∧
      (singleOutputPair statement.commitment).secondOccupied = 0 ∧
      (singleOutputPair statement.commitment).secondCommitment = fun _ => 0 := by
  exact ⟨accepted.appendExact.1, rfl, rfl⟩

theorem accepted_deposit_empty_slot_is_unspendable
    {K Nullifier : Type} [CommRing K] [Nontrivial K]
    (parent : ForestDigest K → ForestDigest K → ForestDigest K)
    (emptyLeaf : ForestDigest K)
    (compressPair : ForestPairLeaf K → ForestDigest K)
    (depth : Nat)
    (laneOfCommitment : ForestDigest K → Lane)
    (state : ForestVaultState K Nullifier)
    (statement : ForestDepositStatement K)
    (_accepted : ForestDepositAccepted parent emptyLeaf compressPair depth
      laneOfCommitment state statement) :
    ¬ (singleOutputPair statement.commitment).SelectedSlotIsSpendable true := by
  exact canonical_empty_second_slot_not_spendable statement.commitment

@[simp] theorem deposit_writes_exactly_selected_lane
    {K Nullifier : Type}
    (state : ForestVaultState K Nullifier)
    (statement : ForestDepositStatement K) :
    (applyDeposit state statement).pool.atomic.lanes statement.outputLane =
      statement.laneResult := by
  simp [applyDeposit, updateLane]

theorem deposit_preserves_every_other_lane
    {K Nullifier : Type}
    (state : ForestVaultState K Nullifier)
    (statement : ForestDepositStatement K)
    (lane : Lane) (different : lane ≠ statement.outputLane) :
    (applyDeposit state statement).pool.atomic.lanes lane =
      state.pool.atomic.lanes lane := by
  simp [applyDeposit, updateLane, different]

@[simp] theorem deposit_preserves_nullifiers_and_checkpoint_history
    {K Nullifier : Type}
    (state : ForestVaultState K Nullifier)
    (statement : ForestDepositStatement K) :
    (applyDeposit state statement).pool.atomic.spentNullifiers =
        state.pool.atomic.spentNullifiers ∧
      (applyDeposit state statement).pool.checkpointMaster =
        state.pool.checkpointMaster ∧
      (applyDeposit state statement).pool.retainedAnchors =
        state.pool.retainedAnchors :=
  ⟨rfl, rfl, rfl⟩

theorem deposit_preserves_vault_conservation
    {K Nullifier : Type}
    (reserve : Nat)
    (state : ForestVaultState K Nullifier)
    (statement : ForestDepositStatement K)
    (conserved : VaultConserved reserve state) :
    VaultConserved reserve (applyDeposit state statement) := by
  unfold VaultConserved at conserved ⊢
  simp only [applyDeposit]
  omega

/-- At the next checkpoint the exact deposited lane result is one leaf of the
new global root and has its canonical private three-level authentication path. -/
theorem deposited_lane_enters_next_global_checkpoint
    {K Nullifier : Type}
    (parent : ForestDigest K → ForestDigest K → ForestDigest K)
    (state : ForestVaultState K Nullifier)
    (statement : ForestDepositStatement K) :
    foldThreeForestLevels parent statement.laneResult.root
        (forestSuperSibling parent
          (observedLaneRoots (applyDeposit state statement).pool.atomic.lanes)
          statement.outputLane)
        (forestSuperDirection statement.outputLane) =
      (checkpointFromState parent (applyDeposit state statement).pool).globalRoot := by
  rw [← deposit_writes_exactly_selected_lane state statement]
  exact checkpoint_gives_every_lane_one_global_anonymity_root parent
    (applyDeposit state statement).pool.checkpointMaster
    (observedLaneSequences (applyDeposit state statement).pool.atomic.lanes)
    (observedLaneRoots (applyDeposit state statement).pool.atomic.lanes)
    statement.outputLane

#print axioms accepted_deposit_pair_is_valid_and_empty_second
#print axioms accepted_deposit_empty_slot_is_unspendable
#print axioms deposit_writes_exactly_selected_lane
#print axioms deposit_preserves_every_other_lane
#print axioms deposit_preserves_nullifiers_and_checkpoint_history
#print axioms deposit_preserves_vault_conservation
#print axioms deposited_lane_enters_next_global_checkpoint

end AspisPool.V7EightLaneDeposit
