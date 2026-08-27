import AspisFormal.Pool.V7EightLaneForestRelation
import AspisFormal.Pool.V7PairAppendAfterstateCorrect

/-!
# One-terminal-transaction contract for the V7 eight-lane forest

This file composes the forest membership relation with the already proved
exact pair append.  It states the semantic contract which the Tag-73 terminal
and Pool source bridges must implement:

* the historical input path ends at one retained global checkpoint root;
* the public output lane is the deterministic image of the nullifier;
* the proof-carried source is exactly the currently locked state of that one
  output lane;
* the proof-carried result is the exact depth-20 pair append; and
* one accepted settlement updates that lane and inserts the nullifier in the
  same state transition.

The checkpoint transaction is not part of settlement.  It only creates a
retained historical membership anchor.  This module therefore models one
terminal spend transaction, and proves that a change to another lane does not
stale its completed proof.
-/

set_option autoImplicit false

namespace AspisPool.V7EightLaneForestTerminal

open AspisPool.IncrementalMerkleV1
open AspisPool.V7EightLaneForestGeometry
open AspisPool.V7EightLaneForestRelation
open AspisPool.V7PairAppendAfterstateCorrect

abbrev PairLeaf := AspisPool.V7PairLeafOccupancy.PairLeaf

abbrev ForestPairLiveState (K : Type) := PairLiveState (Digest K)
abbrev ForestLiveLanes (K : Type) := LaneVector (ForestPairLiveState K)

/-- Exact public data needed by the terminal.  `membershipAnchor` is stable
and historical. `laneSource` and `laneResult` concern only `outputLane`. -/
structure ForestTerminalStatement (K Nullifier : Type) where
  membershipAnchor : Digest K
  nullifier : Nullifier
  outputLane : Lane
  laneSource : ForestPairLiveState K
  laneResult : ForestPairLiveState K

/-- Cryptographic witness components relevant to the forest extension.  The
pre-existing spend relation remains the separate `baseRelation` predicate in
`ForestTerminalAccepted`. -/
structure ForestTerminalProof
    (K : Type) [CommRing K]
    (parent : Digest K → Digest K → Digest K) where
  membershipTrace : ThreeLevelForestTrace K parent
  outputPair : PairLeaf K
  source : ForestPairLiveState K
  result : ForestPairLiveState K

/-- Intended semantic terminal acceptance.  Every field is a concrete check
that must later be discharged from the Rust terminal and Pool caller. -/
structure ForestTerminalAccepted
    {K Nullifier : Type} [CommRing K]
    (parent : Digest K → Digest K → Digest K)
    (emptyLeaf : Digest K)
    (compressPair : PairLeaf K → Digest K)
    (depth : Nat)
    (laneOfNullifier : Nullifier → Lane)
    (retained : Digest K → Prop)
    (baseRelation :
      ForestTerminalStatement K Nullifier →
        ForestTerminalProof K parent → Prop)
    (live : ForestLiveLanes K)
    (statement : ForestTerminalStatement K Nullifier)
    (proof : ForestTerminalProof K parent) : Prop where
  baseValid : baseRelation statement proof
  retainedAnchor : retained statement.membershipAnchor
  outputLaneExact : statement.outputLane = laneOfNullifier statement.nullifier
  membershipAnchorExact :
    proof.membershipTrace.anchor = statement.membershipAnchor
  publicSourceExact : proof.source = statement.laneSource
  publicResultExact : proof.result = statement.laneResult
  sourceIsLockedLiveLane : statement.laneSource = live statement.outputLane
  appendExact : ExactPairAppendTransition parent emptyLeaf compressPair depth
    proof.outputPair proof.source proof.result

/-- Accepted terminal evidence extracts an actual private input lane and a
three-parent path to the public historical checkpoint root. -/
theorem accepted_extracts_private_input_lane
    {K Nullifier : Type} [CommRing K] [NoZeroDivisors K]
    (parent : Digest K → Digest K → Digest K)
    (emptyLeaf : Digest K)
    (compressPair : PairLeaf K → Digest K)
    (depth : Nat)
    (laneOfNullifier : Nullifier → Lane)
    (retained : Digest K → Prop)
    (baseRelation :
      ForestTerminalStatement K Nullifier →
        ForestTerminalProof K parent → Prop)
    (live : ForestLiveLanes K)
    (statement : ForestTerminalStatement K Nullifier)
    (proof : ForestTerminalProof K parent)
    (accepted : ForestTerminalAccepted parent emptyLeaf compressPair depth
      laneOfNullifier retained baseRelation live statement proof) :
    ∃ inputLane : Lane, ∃ directions : Fin 3 → Bool,
      (∀ level, directions level = forestSuperDirection inputLane level) ∧
      foldThreeForestLevels parent proof.membershipTrace.laneRoot
          (fun level => (proof.membershipTrace.levels level).sibling)
          directions = statement.membershipAnchor := by
  rcases three_level_forest_trace_extracts_private_lane parent
      proof.membershipTrace with ⟨lane, directions, laneBits, path⟩
  exact ⟨lane, directions, laneBits,
    path.trans accepted.membershipAnchorExact⟩

theorem accepted_output_lane_is_nullifier_lane
    {K Nullifier : Type} [CommRing K]
    (parent : Digest K → Digest K → Digest K)
    (emptyLeaf : Digest K)
    (compressPair : PairLeaf K → Digest K)
    (depth : Nat)
    (laneOfNullifier : Nullifier → Lane)
    (retained : Digest K → Prop)
    (baseRelation :
      ForestTerminalStatement K Nullifier →
        ForestTerminalProof K parent → Prop)
    (live : ForestLiveLanes K)
    (statement : ForestTerminalStatement K Nullifier)
    (proof : ForestTerminalProof K parent)
    (accepted : ForestTerminalAccepted parent emptyLeaf compressPair depth
      laneOfNullifier retained baseRelation live statement proof) :
    statement.outputLane = laneOfNullifier statement.nullifier :=
  accepted.outputLaneExact

/-- The terminal binds the proof source to exactly one currently locked lane. -/
theorem accepted_source_is_exact_locked_lane
    {K Nullifier : Type} [CommRing K]
    (parent : Digest K → Digest K → Digest K)
    (emptyLeaf : Digest K)
    (compressPair : PairLeaf K → Digest K)
    (depth : Nat)
    (laneOfNullifier : Nullifier → Lane)
    (retained : Digest K → Prop)
    (baseRelation :
      ForestTerminalStatement K Nullifier →
        ForestTerminalProof K parent → Prop)
    (live : ForestLiveLanes K)
    (statement : ForestTerminalStatement K Nullifier)
    (proof : ForestTerminalProof K parent)
    (accepted : ForestTerminalAccepted parent emptyLeaf compressPair depth
      laneOfNullifier retained baseRelation live statement proof) :
    proof.source = live statement.outputLane := by
  exact accepted.publicSourceExact.trans accepted.sourceIsLockedLiveLane

/-- A completed proof remains source-valid after a different lane changes. -/
theorem other_lane_update_does_not_stale_completed_proof
    {K Nullifier : Type} [CommRing K]
    (parent : Digest K → Digest K → Digest K)
    (emptyLeaf : Digest K)
    (compressPair : PairLeaf K → Digest K)
    (depth : Nat)
    (laneOfNullifier : Nullifier → Lane)
    (retained : Digest K → Prop)
    (baseRelation :
      ForestTerminalStatement K Nullifier →
        ForestTerminalProof K parent → Prop)
    (live : ForestLiveLanes K)
    (statement : ForestTerminalStatement K Nullifier)
    (proof : ForestTerminalProof K parent)
    (accepted : ForestTerminalAccepted parent emptyLeaf compressPair depth
      laneOfNullifier retained baseRelation live statement proof)
    (written : Lane) (next : ForestPairLiveState K)
    (different : written ≠ statement.outputLane) :
    proof.source =
      updateLane live written next statement.outputLane := by
  rw [update_other_lane_preserves_state live written statement.outputLane next
    different]
  exact accepted_source_is_exact_locked_lane parent emptyLeaf compressPair depth
    laneOfNullifier retained baseRelation live statement proof accepted

/-- Changing the same lane to a state different from the proof source makes
the source equality fail. -/
theorem changed_output_lane_stales_completed_proof
    {K Nullifier : Type} [CommRing K]
    (parent : Digest K → Digest K → Digest K)
    (emptyLeaf : Digest K)
    (compressPair : PairLeaf K → Digest K)
    (depth : Nat)
    (laneOfNullifier : Nullifier → Lane)
    (retained : Digest K → Prop)
    (baseRelation :
      ForestTerminalStatement K Nullifier →
        ForestTerminalProof K parent → Prop)
    (live : ForestLiveLanes K)
    (statement : ForestTerminalStatement K Nullifier)
    (proof : ForestTerminalProof K parent)
    (_accepted : ForestTerminalAccepted parent emptyLeaf compressPair depth
      laneOfNullifier retained baseRelation live statement proof)
    (next : ForestPairLiveState K)
    (changed : next ≠ proof.source) :
    proof.source ≠
      updateLane live statement.outputLane next statement.outputLane := by
  simpa [updateLane] using changed.symm

/-- State updated by one accepted terminal transaction. -/
structure ForestAtomicState (K Nullifier : Type) where
  lanes : ForestLiveLanes K
  spentNullifiers : Set Nullifier

def applyAcceptedTerminal
    {K Nullifier : Type}
    (state : ForestAtomicState K Nullifier)
    (statement : ForestTerminalStatement K Nullifier) :
    ForestAtomicState K Nullifier where
  lanes := updateLane state.lanes statement.outputLane statement.laneResult
  spentNullifiers := Set.insert statement.nullifier state.spentNullifiers

/-- Complete stateful acceptance for the one terminal transaction.  The
cryptographic terminal contract is paired with the Pool's literal replay
precondition: the public nullifier must not already be present in the atomic
state consumed by this transaction. -/
structure ForestAtomicAccepted
    {K Nullifier : Type} [CommRing K]
    (parent : Digest K → Digest K → Digest K)
    (emptyLeaf : Digest K)
    (compressPair : PairLeaf K → Digest K)
    (depth : Nat)
    (laneOfNullifier : Nullifier → Lane)
    (retained : Digest K → Prop)
    (baseRelation :
      ForestTerminalStatement K Nullifier →
        ForestTerminalProof K parent → Prop)
    (state : ForestAtomicState K Nullifier)
    (statement : ForestTerminalStatement K Nullifier)
    (proof : ForestTerminalProof K parent) : Prop where
  terminal : ForestTerminalAccepted parent emptyLeaf compressPair depth
    laneOfNullifier retained baseRelation state.lanes statement proof
  nullifierFresh : statement.nullifier ∉ state.spentNullifiers

@[simp] theorem accepted_terminal_marks_nullifier
    {K Nullifier : Type}
    (state : ForestAtomicState K Nullifier)
    (statement : ForestTerminalStatement K Nullifier) :
    statement.nullifier ∈
      (applyAcceptedTerminal state statement).spentNullifiers := by
  exact Set.mem_insert statement.nullifier state.spentNullifiers

/-- Atomic application makes the exact accepted statement ineligible for a
second application, independent of every cryptographic detail. -/
theorem applied_terminal_rejects_identical_nullifier
    {K Nullifier : Type}
    (state : ForestAtomicState K Nullifier)
    (statement : ForestTerminalStatement K Nullifier) :
    ¬ statement.nullifier ∉
      (applyAcceptedTerminal state statement).spentNullifiers := by
  exact fun absent => absent (accepted_terminal_marks_nullifier state statement)

/-- Therefore no complete stateful acceptance witness for the same statement
can exist against the post-state of an accepted atomic application. -/
theorem identical_statement_cannot_be_accepted_after_application
    {K Nullifier : Type} [CommRing K]
    (parent : Digest K → Digest K → Digest K)
    (emptyLeaf : Digest K)
    (compressPair : PairLeaf K → Digest K)
    (depth : Nat)
    (laneOfNullifier : Nullifier → Lane)
    (retained : Digest K → Prop)
    (baseRelation :
      ForestTerminalStatement K Nullifier →
        ForestTerminalProof K parent → Prop)
    (state : ForestAtomicState K Nullifier)
    (statement : ForestTerminalStatement K Nullifier)
    (proof : ForestTerminalProof K parent) :
    ¬ ForestAtomicAccepted parent emptyLeaf compressPair depth
      laneOfNullifier retained baseRelation
      (applyAcceptedTerminal state statement) statement proof := by
  intro acceptedAgain
  exact applied_terminal_rejects_identical_nullifier state statement
    acceptedAgain.nullifierFresh

@[simp] theorem accepted_terminal_writes_output_lane
    {K Nullifier : Type}
    (state : ForestAtomicState K Nullifier)
    (statement : ForestTerminalStatement K Nullifier) :
    (applyAcceptedTerminal state statement).lanes statement.outputLane =
      statement.laneResult := by
  simp [applyAcceptedTerminal, updateLane]

theorem accepted_terminal_preserves_every_other_lane
    {K Nullifier : Type}
    (state : ForestAtomicState K Nullifier)
    (statement : ForestTerminalStatement K Nullifier)
    (lane : Lane) (different : lane ≠ statement.outputLane) :
    (applyAcceptedTerminal state statement).lanes lane = state.lanes lane := by
  simp [applyAcceptedTerminal, updateLane, different]

/-- The exact transition still supplies the original one-pair cursor and
sequence increment inside the selected lane. -/
theorem accepted_terminal_increments_selected_lane_once
    {K Nullifier : Type} [CommRing K]
    (parent : Digest K → Digest K → Digest K)
    (emptyLeaf : Digest K)
    (compressPair : PairLeaf K → Digest K)
    (depth : Nat)
    (laneOfNullifier : Nullifier → Lane)
    (retained : Digest K → Prop)
    (baseRelation :
      ForestTerminalStatement K Nullifier →
        ForestTerminalProof K parent → Prop)
    (live : ForestLiveLanes K)
    (statement : ForestTerminalStatement K Nullifier)
    (proof : ForestTerminalProof K parent)
    (accepted : ForestTerminalAccepted parent emptyLeaf compressPair depth
      laneOfNullifier retained baseRelation live statement proof) :
    statement.laneResult.sequence = statement.laneSource.sequence + 1 ∧
      statement.laneResult.nextPairIndex =
        statement.laneSource.nextPairIndex + 1 := by
  have indices := exact_transition_indices parent emptyLeaf compressPair depth
    proof.outputPair proof.source proof.result accepted.appendExact
  simpa [accepted.publicSourceExact, accepted.publicResultExact] using indices

#print axioms accepted_extracts_private_input_lane
#print axioms accepted_output_lane_is_nullifier_lane
#print axioms accepted_source_is_exact_locked_lane
#print axioms other_lane_update_does_not_stale_completed_proof
#print axioms changed_output_lane_stales_completed_proof
#print axioms accepted_terminal_marks_nullifier
#print axioms applied_terminal_rejects_identical_nullifier
#print axioms identical_statement_cannot_be_accepted_after_application
#print axioms accepted_terminal_writes_output_lane
#print axioms accepted_terminal_preserves_every_other_lane
#print axioms accepted_terminal_increments_selected_lane_once

end AspisPool.V7EightLaneForestTerminal
