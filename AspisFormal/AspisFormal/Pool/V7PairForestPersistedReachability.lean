import AspisFormal.Pool.V7PairForestLaneInvariant

/-!
# Reachability closure for persisted V7 pair-forest lanes

The runtime fast path may use the active root/frontier relation only for lane
states introduced by strict genesis initialization and then advanced by the
two authenticated Pool writers.  This file makes that induction explicit in
the mathematical model.  Checkpointing needs no constructor because it never
writes a lane.

The separate Aeneas/source bridge proves that the production persistence
surface has exactly these constructors and that every successful mutation is
persisted through the byte-exact strict lane codec.
-/

set_option autoImplicit false

namespace AspisPool.V7PairForestPersistedReachability

open AspisPool.IncrementalMerkleV1
open AspisPool.V7PairLeafOccupancy
open AspisPool.V7PairAppendAfterstateCorrect
open AspisPool.V7EightLaneForestGeometry
open AspisPool.V7EightLaneForestRelation
open AspisPool.V7EightLaneForestTerminal
open AspisPool.V7EightLaneDeposit
open AspisPool.V7PairForestLaneInvariant

abbrev LaneDigest := AspisPool.V7EightLaneDeposit.ForestDigest
abbrev LanePairLeaf := AspisPool.V7EightLaneDeposit.ForestPairLeaf

/-- The two Pool-authenticated ways to advance one persisted lane.  A public
deposit obtains its exact append from the checked Pool construction; a
terminal transition obtains it from the accepted Tag-73/ASR8 relation. -/
inductive AuthenticatedPoolLaneTransition
    {K : Type} [CommRing K]
    (parent : LaneDigest K → LaneDigest K → LaneDigest K)
    (emptyLeaf : LaneDigest K)
    (compressPair : LanePairLeaf K → LaneDigest K)
    (depth : Nat) :
    ForestPairLiveState K → ForestPairLiveState K → Prop where
  | checkedDeposit
      (commitment : LaneDigest K)
      {source result : ForestPairLiveState K}
      (exact : ExactPairAppendTransition parent emptyLeaf compressPair depth
        (singleOutputPair commitment) source result) :
      AuthenticatedPoolLaneTransition parent emptyLeaf compressPair depth
        source result
  | authenticatedTerminal
      (outputPair : LanePairLeaf K)
      {source result : ForestPairLiveState K}
      (exact : ExactPairAppendTransition parent emptyLeaf compressPair depth
        outputPair source result) :
      AuthenticatedPoolLaneTransition parent emptyLeaf compressPair depth
        source result

theorem authenticated_transition_preserves_invariant
    {K : Type} [CommRing K]
    (parent : LaneDigest K → LaneDigest K → LaneDigest K)
    (emptyLeaf : LaneDigest K)
    (compressPair : LanePairLeaf K → LaneDigest K)
    (depth : Nat)
    (source result : ForestPairLiveState K)
    (sourceInvariant :
      PairLiveStateInvariant parent emptyLeaf depth source)
    (transition : AuthenticatedPoolLaneTransition parent emptyLeaf
      compressPair depth source result) :
    PairLiveStateInvariant parent emptyLeaf depth result := by
  cases transition with
  | checkedDeposit commitment exact =>
      exact exact_append_preserves_pair_live_state_invariant parent emptyLeaf
        compressPair depth (singleOutputPair commitment) source result
        sourceInvariant exact
  | authenticatedTerminal outputPair exact =>
      exact exact_append_preserves_pair_live_state_invariant parent emptyLeaf
        compressPair depth outputPair source result sourceInvariant exact

/-- Per-lane persisted reachability under the closed Pool writer surface.
Transactions selecting another lane are stuttering steps and do not introduce
a new state. -/
inductive PersistedLaneReachable
    {K : Type} [CommRing K]
    (parent : LaneDigest K → LaneDigest K → LaneDigest K)
    (emptyLeaf : LaneDigest K)
    (compressPair : LanePairLeaf K → LaneDigest K)
    (depth : Nat) : ForestPairLiveState K → Prop where
  | genesis : PersistedLaneReachable parent emptyLeaf compressPair depth
      (pairGenesis parent emptyLeaf depth)
  | authenticated
      {source result : ForestPairLiveState K}
      (sourceReachable : PersistedLaneReachable parent emptyLeaf compressPair
        depth source)
      (transition : AuthenticatedPoolLaneTransition parent emptyLeaf
        compressPair depth source result) :
      PersistedLaneReachable parent emptyLeaf compressPair depth result

/-- Every reachable persisted lane has the root/frontier relation used by the
default-off invariant decoder. -/
theorem persisted_lane_reachable_has_invariant
    {K : Type} [CommRing K]
    (parent : LaneDigest K → LaneDigest K → LaneDigest K)
    (emptyLeaf : LaneDigest K)
    (compressPair : LanePairLeaf K → LaneDigest K)
    (depth : Nat)
    {state : ForestPairLiveState K}
    (reachable : PersistedLaneReachable parent emptyLeaf compressPair depth
      state) :
    PairLiveStateInvariant parent emptyLeaf depth state := by
  induction reachable with
  | genesis => exact pairGenesis_invariant parent emptyLeaf depth
  | authenticated sourceReachable transition sourceInvariant =>
      exact authenticated_transition_preserves_invariant parent emptyLeaf
        compressPair depth _ _ sourceInvariant transition

/-- Exact induction classification consumed by the source closure: a
reachable persisted lane is the strict genesis state or the output of one of
the two authenticated writers applied to an already reachable predecessor. -/
theorem persisted_lane_reachable_is_genesis_or_authenticated_output
    {K : Type} [CommRing K]
    (parent : LaneDigest K → LaneDigest K → LaneDigest K)
    (emptyLeaf : LaneDigest K)
    (compressPair : LanePairLeaf K → LaneDigest K)
    (depth : Nat)
    {state : ForestPairLiveState K}
    (reachable : PersistedLaneReachable parent emptyLeaf compressPair depth
      state) :
    state = pairGenesis parent emptyLeaf depth ∨
      ∃ source,
        PersistedLaneReachable parent emptyLeaf compressPair depth source ∧
        AuthenticatedPoolLaneTransition parent emptyLeaf compressPair depth
          source state := by
  cases reachable with
  | genesis => exact Or.inl rfl
  | authenticated sourceReachable transition =>
      exact Or.inr ⟨_, sourceReachable, transition⟩

/-- An accepted public deposit supplies exactly the checked-deposit
constructor; no fixture root or unverified afterstate enters reachability. -/
theorem accepted_deposit_yields_authenticated_lane_transition
    {K Nullifier : Type} [CommRing K]
    (parent : LaneDigest K → LaneDigest K → LaneDigest K)
    (emptyLeaf : LaneDigest K)
    (compressPair : LanePairLeaf K → LaneDigest K)
    (depth : Nat)
    (laneOfCommitment : LaneDigest K → Lane)
    (state : ForestVaultState K Nullifier)
    (statement : ForestDepositStatement K)
    (accepted : ForestDepositAccepted parent emptyLeaf compressPair depth
      laneOfCommitment state statement) :
    AuthenticatedPoolLaneTransition parent emptyLeaf compressPair depth
      (state.pool.atomic.lanes statement.outputLane) statement.laneResult := by
  apply AuthenticatedPoolLaneTransition.checkedDeposit statement.commitment
  simpa only [accepted.sourceIsLockedLiveLane] using accepted.appendExact

theorem accepted_deposit_extends_persisted_reachability
    {K Nullifier : Type} [CommRing K]
    (parent : LaneDigest K → LaneDigest K → LaneDigest K)
    (emptyLeaf : LaneDigest K)
    (compressPair : LanePairLeaf K → LaneDigest K)
    (depth : Nat)
    (laneOfCommitment : LaneDigest K → Lane)
    (state : ForestVaultState K Nullifier)
    (statement : ForestDepositStatement K)
    (sourceReachable : PersistedLaneReachable parent emptyLeaf compressPair
      depth (state.pool.atomic.lanes statement.outputLane))
    (accepted : ForestDepositAccepted parent emptyLeaf compressPair depth
      laneOfCommitment state statement) :
    PersistedLaneReachable parent emptyLeaf compressPair depth
      statement.laneResult :=
  .authenticated sourceReachable
    (accepted_deposit_yields_authenticated_lane_transition parent emptyLeaf
      compressPair depth laneOfCommitment state statement accepted)

/-- An accepted terminal transition supplies exactly the authenticated-ASR8
constructor for the currently selected live lane. -/
theorem accepted_terminal_yields_authenticated_lane_transition
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
    (accepted : ForestAtomicAccepted parent emptyLeaf compressPair depth
      laneOfNullifier retained baseRelation state statement proof) :
    AuthenticatedPoolLaneTransition parent emptyLeaf compressPair depth
      (state.lanes statement.outputLane) statement.laneResult := by
  apply AuthenticatedPoolLaneTransition.authenticatedTerminal proof.outputPair
  simpa [accepted.terminal.publicSourceExact,
    accepted.terminal.publicResultExact,
    accepted.terminal.sourceIsLockedLiveLane] using
      accepted.terminal.appendExact

theorem accepted_terminal_extends_persisted_reachability
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
    (sourceReachable : PersistedLaneReachable parent emptyLeaf compressPair
      depth (state.lanes statement.outputLane))
    (accepted : ForestAtomicAccepted parent emptyLeaf compressPair depth
      laneOfNullifier retained baseRelation state statement proof) :
    PersistedLaneReachable parent emptyLeaf compressPair depth
      statement.laneResult :=
  .authenticated sourceReachable
    (accepted_terminal_yields_authenticated_lane_transition parent emptyLeaf
      compressPair depth laneOfNullifier retained baseRelation state statement
      proof accepted)

#print axioms authenticated_transition_preserves_invariant
#print axioms persisted_lane_reachable_has_invariant
#print axioms persisted_lane_reachable_is_genesis_or_authenticated_output
#print axioms accepted_deposit_yields_authenticated_lane_transition
#print axioms accepted_deposit_extends_persisted_reachability
#print axioms accepted_terminal_yields_authenticated_lane_transition
#print axioms accepted_terminal_extends_persisted_reachability

end AspisPool.V7PairForestPersistedReachability
