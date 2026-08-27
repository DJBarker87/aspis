import AspisFormal.Pool.V7EightLaneCheckpointChronology

/-!
# Checkpoint/settlement composition for the eight-lane Pool

This module gives the state-machine theorem joining the permissionless forest
checkpoint with the one-transaction private spend.  A checkpoint observes all
eight lane states, retains their exact seven-parent global root, and changes no
lane or nullifier state.  A spend changes one deterministic live lane and the
nullifier set, while leaving the retained historical-root set and checkpoint
master untouched.  Thus the membership anchor and the append tip have the
separate roles required for concurrency.
-/

set_option autoImplicit false

namespace AspisPool.V7EightLaneCheckpointSettlement

open AspisPool.V7EightLaneForestGeometry
open AspisPool.V7EightLaneForestRelation
open AspisPool.V7EightLaneForestTerminal
open AspisPool.V7EightLaneCheckpointChronology

def observedLaneSequences {K : Type}
    (lanes : ForestLiveLanes K) : LaneSequences :=
  fun lane => (lanes lane).sequence

def observedLaneRoots {K : Type}
    (lanes : ForestLiveLanes K) : LaneVector (Digest K) :=
  fun lane => (lanes lane).root

structure ForestPoolState (K Nullifier : Type) where
  atomic : ForestAtomicState K Nullifier
  checkpointMaster : ForestCheckpointMaster
  retainedAnchors : Set (Digest K)

def checkpointFromState {K Nullifier : Type}
    (parent : Digest K → Digest K → Digest K)
    (state : ForestPoolState K Nullifier) : ForestCheckpoint (Digest K) :=
  makeCheckpoint parent state.checkpointMaster
    (observedLaneSequences state.atomic.lanes)
    (observedLaneRoots state.atomic.lanes)

def applyCheckpoint {K Nullifier : Type}
    (parent : Digest K → Digest K → Digest K)
    (state : ForestPoolState K Nullifier) : ForestPoolState K Nullifier where
  atomic := state.atomic
  checkpointMaster := advanceMaster state.checkpointMaster
    (observedLaneSequences state.atomic.lanes)
  retainedAnchors := Set.insert (checkpointFromState parent state).globalRoot
    state.retainedAnchors

def applyTerminal {K Nullifier : Type}
    (state : ForestPoolState K Nullifier)
    (statement : ForestTerminalStatement K Nullifier) :
    ForestPoolState K Nullifier where
  atomic := applyAcceptedTerminal state.atomic statement
  checkpointMaster := state.checkpointMaster
  retainedAnchors := state.retainedAnchors

@[simp] theorem checkpoint_retains_exact_observed_global_root
    {K Nullifier : Type}
    (parent : Digest K → Digest K → Digest K)
    (state : ForestPoolState K Nullifier) :
    (checkpointFromState parent state).globalRoot ∈
      (applyCheckpoint parent state).retainedAnchors := by
  exact Set.mem_insert _ _

@[simp] theorem checkpoint_preserves_atomic_spend_state
    {K Nullifier : Type}
    (parent : Digest K → Digest K → Digest K)
    (state : ForestPoolState K Nullifier) :
    (applyCheckpoint parent state).atomic = state.atomic :=
  rfl

theorem checkpoint_preserves_every_existing_anchor
    {K Nullifier : Type}
    (parent : Digest K → Digest K → Digest K)
    (state : ForestPoolState K Nullifier)
    (anchor : Digest K)
    (retained : anchor ∈ state.retainedAnchors) :
    anchor ∈ (applyCheckpoint parent state).retainedAnchors := by
  exact Set.mem_insert_of_mem _ retained

@[simp] theorem terminal_preserves_checkpoint_master
    {K Nullifier : Type}
    (state : ForestPoolState K Nullifier)
    (statement : ForestTerminalStatement K Nullifier) :
    (applyTerminal state statement).checkpointMaster =
      state.checkpointMaster :=
  rfl

@[simp] theorem terminal_preserves_retained_anchor_set
    {K Nullifier : Type}
    (state : ForestPoolState K Nullifier)
    (statement : ForestTerminalStatement K Nullifier) :
    (applyTerminal state statement).retainedAnchors = state.retainedAnchors :=
  rfl

theorem terminal_preserves_historical_membership_anchor
    {K Nullifier : Type}
    (state : ForestPoolState K Nullifier)
    (statement : ForestTerminalStatement K Nullifier)
    (retained : statement.membershipAnchor ∈ state.retainedAnchors) :
    statement.membershipAnchor ∈
      (applyTerminal state statement).retainedAnchors := by
  exact retained

@[simp] theorem post_terminal_observed_output_lane_root
    {K Nullifier : Type}
    (state : ForestPoolState K Nullifier)
    (statement : ForestTerminalStatement K Nullifier) :
    observedLaneRoots (applyTerminal state statement).atomic.lanes
        statement.outputLane = statement.laneResult.root := by
  simp [observedLaneRoots, applyTerminal]

/-- After the next permissionless checkpoint, the newly written output lane
has its canonical private three-level path into the new global anchor. -/
theorem output_lane_enters_next_global_checkpoint
    {K Nullifier : Type}
    (parent : Digest K → Digest K → Digest K)
    (state : ForestPoolState K Nullifier)
    (statement : ForestTerminalStatement K Nullifier) :
    foldThreeForestLevels parent statement.laneResult.root
        (forestSuperSibling parent
          (observedLaneRoots (applyTerminal state statement).atomic.lanes)
          statement.outputLane)
        (forestSuperDirection statement.outputLane) =
      (checkpointFromState parent
        (applyTerminal state statement)).globalRoot := by
  rw [← post_terminal_observed_output_lane_root state statement]
  exact checkpoint_gives_every_lane_one_global_anonymity_root parent
    (applyTerminal state statement).checkpointMaster
    (observedLaneSequences (applyTerminal state statement).atomic.lanes)
    (observedLaneRoots (applyTerminal state statement).atomic.lanes)
    statement.outputLane

/-- Two atomic state updates to distinct lanes commute.  Solana may serialize
their landing order, but neither result depends on that order; only same-lane
writers contend. -/
theorem distinct_lane_terminal_updates_commute
    {K Nullifier : Type} [DecidableEq Nullifier]
    (state : ForestAtomicState K Nullifier)
    (first second : ForestTerminalStatement K Nullifier)
    (different : first.outputLane ≠ second.outputLane) :
    applyAcceptedTerminal (applyAcceptedTerminal state first) second =
      applyAcceptedTerminal (applyAcceptedTerminal state second) first := by
  cases state with
  | mk lanes nullifiers =>
      cases first with
      | mk firstAnchor firstNullifier firstLane firstSource firstResult =>
          cases second with
          | mk secondAnchor secondNullifier secondLane secondSource secondResult =>
              simp only [applyAcceptedTerminal]
              congr 1
              · exact Function.update_comm different firstResult secondResult lanes
              · exact (Set.insert_comm firstNullifier secondNullifier nullifiers).symm

#print axioms checkpoint_retains_exact_observed_global_root
#print axioms checkpoint_preserves_atomic_spend_state
#print axioms checkpoint_preserves_every_existing_anchor
#print axioms terminal_preserves_checkpoint_master
#print axioms terminal_preserves_retained_anchor_set
#print axioms terminal_preserves_historical_membership_anchor
#print axioms post_terminal_observed_output_lane_root
#print axioms output_lane_enters_next_global_checkpoint
#print axioms distinct_lane_terminal_updates_commute

end AspisPool.V7EightLaneCheckpointSettlement
