import AspisFormal.Pool.V7EightLaneDeposit

/-!
# Inductive validity of Pool-owned V7 pair-forest lanes

The production fast decoder may omit the expensive active-root reconstruction
only for canonical Pool-owned lane PDAs whose state is reachable from genesis
through the Pool's checked writers.  This file makes that boundary explicit.

`PairLiveStateInvariant` contains the exact chronological frontier witness and
the root/cursor/sequence equalities checked by the strict decoder.  Genesis
establishes it; an exact Tag-73 terminal append and an accepted deposit preserve
it; a permissionless checkpoint cannot change it.  Thus the omitted active-root
check is recovered from an inductive state invariant, not from an unverified
instruction or proof-account hint.
-/

set_option autoImplicit false

namespace AspisPool.V7PairForestLaneInvariant

open AspisPool.IncrementalMerkleV1
open AspisPool.V7PairLeafOccupancy
open AspisPool.V7PairAppendAfterstateCorrect
open AspisPool.V7EightLaneForestGeometry
open AspisPool.V7EightLaneForestRelation
open AspisPool.V7EightLaneForestTerminal
open AspisPool.V7EightLaneCheckpointSettlement
open AspisPool.V7EightLaneDeposit

abbrev LaneDigest := AspisPool.V7EightLaneDeposit.ForestDigest
abbrev LanePairLeaf := AspisPool.V7EightLaneDeposit.ForestPairLeaf

/-- Complete mathematical invariant behind the strict active-lane decoder. -/
def PairLiveStateInvariant
    {D : Type}
    (parent : D → D → D)
    (emptyLeaf : D)
    (depth : Nat)
    (state : PairLiveState D) : Prop :=
  ∃ leaves : List D,
    FrontierInvariant parent emptyLeaf depth leaves state.frontier ∧
      state.sequence = leaves.length ∧
      state.nextPairIndex = leaves.length ∧
      state.root = reconstructRoot parent emptyLeaf state.frontier

/-- Canonical empty live lane used when a fresh Pool forest is initialized. -/
def pairGenesis {D : Type}
    (parent : D → D → D)
    (emptyLeaf : D)
    (depth : Nat) : PairLiveState D where
  sequence := 0
  nextPairIndex := 0
  root := reconstructRoot parent emptyLeaf
    (List.replicate depth (Option.none : Option D))
  frontier := List.replicate depth (Option.none : Option D)

theorem pairGenesis_invariant
    {D : Type}
    (parent : D → D → D)
    (emptyLeaf : D)
    (depth : Nat) :
    PairLiveStateInvariant parent emptyLeaf depth
      (pairGenesis parent emptyLeaf depth) := by
  refine ⟨[], genesis_invariant parent emptyLeaf depth, rfl, rfl, rfl⟩

/-- In particular, the invariant supplies the root/frontier equality omitted
by the Pool-owned fast decoder. -/
theorem invariant_supplies_active_root_check
    {D : Type}
    (parent : D → D → D)
    (emptyLeaf : D)
    (depth : Nat)
    (state : PairLiveState D)
    (invariant : PairLiveStateInvariant parent emptyLeaf depth state) :
    state.root = reconstructRoot parent emptyLeaf state.frontier := by
  rcases invariant with ⟨_leaves, _frontier, _sequence, _index, root⟩
  exact root

/-- The exact append relation emitted by the selected Tag-73 verifier preserves
all strict-decoder facts, including the authenticated frontier witness. -/
theorem exact_append_preserves_pair_live_state_invariant
    {K D : Type} [CommRing K]
    (parent : D → D → D)
    (emptyLeaf : D)
    (compressPair : LanePairLeaf K → D)
    (depth : Nat)
    (leaf : LanePairLeaf K)
    (source result : PairLiveState D)
    (sourceInvariant :
      PairLiveStateInvariant parent emptyLeaf depth source)
    (exact : ExactPairAppendTransition parent emptyLeaf compressPair depth
      leaf source result) :
    PairLiveStateInvariant parent emptyLeaf depth result := by
  rcases sourceInvariant with
    ⟨leaves, frontierValid, sourceSequence, sourceIndex, _sourceRoot⟩
  rcases exact with
    ⟨_validLeaf, _sourceSeqIndex, _sourceIndexCount, _sourceDepth,
      _exactSourceRoot, carry, resultSequence, resultIndex, _resultCount,
      resultRoot⟩
  have resultFrontierValid :=
    FrontierInvariant.append_preserves parent emptyLeaf (compressPair leaf)
      depth leaves source.frontier result.frontier frontierValid carry
  refine ⟨leaves ++ [compressPair leaf], resultFrontierValid, ?_, ?_, resultRoot⟩
  · rw [resultSequence, sourceSequence]
    simp
  · rw [resultIndex, sourceIndex]
    simp

/-- Every one of the eight live lane accounts satisfies the same canonical
frontier/root invariant. -/
def ForestLaneInvariant
    {K : Type}
    (parent : LaneDigest K → LaneDigest K → LaneDigest K)
    (emptyLeaf : LaneDigest K)
    (depth : Nat)
    (lanes : ForestLiveLanes K) : Prop :=
  ∀ lane, PairLiveStateInvariant parent emptyLeaf depth (lanes lane)

theorem genesis_forest_lane_invariant
    {K : Type}
    (parent : LaneDigest K → LaneDigest K → LaneDigest K)
    (emptyLeaf : LaneDigest K)
    (depth : Nat) :
    ForestLaneInvariant parent emptyLeaf depth
      (fun _lane => pairGenesis parent emptyLeaf depth) := by
  intro _lane
  exact pairGenesis_invariant parent emptyLeaf depth

/-- Updating one lane with an exact append preserves the invariant for the
selected lane and leaves all seven other witnesses unchanged. -/
theorem exact_update_preserves_forest_lane_invariant
    {K : Type} [CommRing K]
    (parent : LaneDigest K → LaneDigest K → LaneDigest K)
    (emptyLeaf : LaneDigest K)
    (compressPair : LanePairLeaf K → LaneDigest K)
    (depth : Nat)
    (lanes : ForestLiveLanes K)
    (written : Lane)
    (leaf : LanePairLeaf K)
    (result : ForestPairLiveState K)
    (forestInvariant : ForestLaneInvariant parent emptyLeaf depth lanes)
    (exact : ExactPairAppendTransition parent emptyLeaf compressPair depth
      leaf (lanes written) result) :
    ForestLaneInvariant parent emptyLeaf depth
      (updateLane lanes written result) := by
  intro lane
  by_cases same : lane = written
  · subst lane
    simpa [updateLane] using
      exact_append_preserves_pair_live_state_invariant parent emptyLeaf
        compressPair depth leaf (lanes written) result
        (forestInvariant written) exact
  · simpa [updateLane, same] using forestInvariant lane

/-- The only lane write in an accepted private transfer is the exact result
authenticated by the terminal relation, so application preserves all lanes. -/
theorem accepted_terminal_preserves_forest_lane_invariant
    {K Nullifier : Type} [CommRing K]
    (parent : LaneDigest K → LaneDigest K → LaneDigest K)
    (emptyLeaf : LaneDigest K)
    (compressPair : LanePairLeaf K → LaneDigest K)
    (depth : Nat)
    (laneOfNullifier : Nullifier → Lane)
    (retained : LaneDigest K → Prop)
    (baseRelation :
      ForestTerminalStatement K Nullifier →
        ForestTerminalProof K parent → Prop)
    (state : ForestAtomicState K Nullifier)
    (statement : ForestTerminalStatement K Nullifier)
    (proof : ForestTerminalProof K parent)
    (forestInvariant :
      ForestLaneInvariant parent emptyLeaf depth state.lanes)
    (accepted : ForestAtomicAccepted parent emptyLeaf compressPair depth
      laneOfNullifier retained baseRelation state statement proof) :
    ForestLaneInvariant parent emptyLeaf depth
      (applyAcceptedTerminal state statement).lanes := by
  have exactLive :
      ExactPairAppendTransition parent emptyLeaf compressPair depth
        proof.outputPair (state.lanes statement.outputLane)
          statement.laneResult := by
    simpa [accepted.terminal.publicSourceExact,
      accepted.terminal.publicResultExact,
      accepted.terminal.sourceIsLockedLiveLane] using
        accepted.terminal.appendExact
  simpa [applyAcceptedTerminal] using
    exact_update_preserves_forest_lane_invariant parent emptyLeaf compressPair
      depth state.lanes statement.outputLane proof.outputPair
      statement.laneResult forestInvariant exactLive

/-- Deposits use the same checked carry relation and therefore preserve the
inductive lane invariant as well. -/
theorem accepted_deposit_preserves_forest_lane_invariant
    {K Nullifier : Type} [CommRing K]
    (parent : ForestDigest K → ForestDigest K → ForestDigest K)
    (emptyLeaf : ForestDigest K)
    (compressPair : ForestPairLeaf K → ForestDigest K)
    (depth : Nat)
    (laneOfCommitment : ForestDigest K → Lane)
    (state : ForestVaultState K Nullifier)
    (statement : ForestDepositStatement K)
    (forestInvariant : ForestLaneInvariant parent emptyLeaf depth
      state.pool.atomic.lanes)
    (accepted : ForestDepositAccepted parent emptyLeaf compressPair depth
      laneOfCommitment state statement) :
    ForestLaneInvariant parent emptyLeaf depth
      (applyDeposit state statement).pool.atomic.lanes := by
  have exactLive :
      ExactPairAppendTransition parent emptyLeaf compressPair depth
        (singleOutputPair statement.commitment)
        (state.pool.atomic.lanes statement.outputLane) statement.laneResult := by
    simpa [accepted.sourceIsLockedLiveLane] using accepted.appendExact
  simpa [applyDeposit] using
    exact_update_preserves_forest_lane_invariant parent emptyLeaf compressPair
      depth state.pool.atomic.lanes statement.outputLane
      (singleOutputPair statement.commitment) statement.laneResult
      forestInvariant exactLive

/-- Permissionless checkpointing observes roots but cannot write a lane. -/
theorem checkpoint_preserves_forest_lane_invariant
    {K Nullifier : Type}
    (parent : LaneDigest K → LaneDigest K → LaneDigest K)
    (emptyLeaf : LaneDigest K)
    (depth : Nat)
    (state : ForestPoolState K Nullifier)
    (forestInvariant : ForestLaneInvariant parent emptyLeaf depth
      state.atomic.lanes) :
    ForestLaneInvariant parent emptyLeaf depth
      (applyCheckpoint parent state).atomic.lanes := by
  simpa [applyCheckpoint] using forestInvariant

#print axioms pairGenesis_invariant
#print axioms invariant_supplies_active_root_check
#print axioms exact_append_preserves_pair_live_state_invariant
#print axioms genesis_forest_lane_invariant
#print axioms exact_update_preserves_forest_lane_invariant
#print axioms accepted_terminal_preserves_forest_lane_invariant
#print axioms accepted_deposit_preserves_forest_lane_invariant
#print axioms checkpoint_preserves_forest_lane_invariant

end AspisPool.V7PairForestLaneInvariant
