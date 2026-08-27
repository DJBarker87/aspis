import AspisFormal.Pool.V7EightLaneForestTerminal

/-!
# Eight-lane checkpoint chronology and anonymity-set completeness

This is the pure state theorem behind the versioned `ASM8`/`ASL8`/`ASC8`
account plan.  A checkpoint observes all eight lane sequences and roots in one
state vector, rejects rollback and duplicate snapshots after genesis, assigns
the master's next checkpoint sequence, and advances that sequence exactly
once.  Its global root is the seven-parent tree over the eight observed lane
roots, so every lane has a canonical private three-level membership path.

The Solana/Aeneas bridge still has to prove that the program obtains this
vector from the eight canonical lane PDAs in one instruction and writes the
master and immutable checkpoint atomically.
-/

set_option autoImplicit false

namespace AspisPool.V7EightLaneCheckpointChronology

open AspisPool.V7EightLaneForestGeometry
open AspisPool.V7EightLaneForestRelation

abbrev LaneSequences := LaneVector Nat

def ComponentwiseNondecreasing
    (previous current : LaneSequences) : Prop :=
  ∀ lane, previous lane ≤ current lane

def SomeLaneProgressed
    (previous current : LaneSequences) : Prop :=
  ∃ lane, previous lane < current lane

structure ForestCheckpointMaster where
  hasCheckpoint : Bool
  nextCheckpointSequence : Nat
  lastLaneSequences : LaneSequences

/-- Genesis may checkpoint the all-zero forest.  Every later checkpoint must
be componentwise monotone and must advance at least one lane. -/
def CanCreateCheckpoint
    (master : ForestCheckpointMaster)
    (current : LaneSequences) : Prop :=
  if master.hasCheckpoint then
    ComponentwiseNondecreasing master.lastLaneSequences current ∧
      SomeLaneProgressed master.lastLaneSequences current
  else
    master.nextCheckpointSequence = 0 ∧
      master.lastLaneSequences = fun _ => 0

structure ForestCheckpoint (Root : Type) where
  checkpointSequence : Nat
  laneSequences : LaneSequences
  laneRoots : LaneVector Root
  globalRoot : Root

def makeCheckpoint
    {Root : Type}
    (parent : Root → Root → Root)
    (master : ForestCheckpointMaster)
    (currentSequences : LaneSequences)
    (currentRoots : LaneVector Root) : ForestCheckpoint Root where
  checkpointSequence := master.nextCheckpointSequence
  laneSequences := currentSequences
  laneRoots := currentRoots
  globalRoot := forestSuperRoot parent currentRoots

def advanceMaster
    (master : ForestCheckpointMaster)
    (current : LaneSequences) : ForestCheckpointMaster where
  hasCheckpoint := true
  nextCheckpointSequence := master.nextCheckpointSequence + 1
  lastLaneSequences := current

@[simp] theorem checkpoint_uses_exact_master_sequence
    {Root : Type}
    (parent : Root → Root → Root)
    (master : ForestCheckpointMaster)
    (currentSequences : LaneSequences)
    (currentRoots : LaneVector Root) :
    (makeCheckpoint parent master currentSequences currentRoots).checkpointSequence =
      master.nextCheckpointSequence :=
  rfl

@[simp] theorem checkpoint_binds_exact_observed_lane_vector
    {Root : Type}
    (parent : Root → Root → Root)
    (master : ForestCheckpointMaster)
    (currentSequences : LaneSequences)
    (currentRoots : LaneVector Root) :
    (makeCheckpoint parent master currentSequences currentRoots).laneSequences =
        currentSequences ∧
      (makeCheckpoint parent master currentSequences currentRoots).laneRoots =
        currentRoots :=
  ⟨rfl, rfl⟩

@[simp] theorem checkpoint_global_root_is_exact_seven_parent_tree
    {Root : Type}
    (parent : Root → Root → Root)
    (master : ForestCheckpointMaster)
    (currentSequences : LaneSequences)
    (currentRoots : LaneVector Root) :
    (makeCheckpoint parent master currentSequences currentRoots).globalRoot =
      forestSuperRoot parent currentRoots :=
  rfl

@[simp] theorem advance_master_increments_checkpoint_sequence_once
    (master : ForestCheckpointMaster)
    (current : LaneSequences) :
    (advanceMaster master current).nextCheckpointSequence =
        master.nextCheckpointSequence + 1 ∧
      (advanceMaster master current).hasCheckpoint = true ∧
      (advanceMaster master current).lastLaneSequences = current :=
  ⟨rfl, rfl, rfl⟩

theorem later_checkpoint_rejects_identical_lane_sequences
    (master : ForestCheckpointMaster)
    (current : LaneSequences)
    (hasCheckpoint : master.hasCheckpoint = true)
    (canCreate : CanCreateCheckpoint master current) :
    current ≠ master.lastLaneSequences := by
  intro equal
  have progressed : SomeLaneProgressed master.lastLaneSequences current := by
    have reduced := canCreate
    simp [CanCreateCheckpoint, hasCheckpoint] at reduced
    exact reduced.2
  rcases progressed with ⟨lane, strict⟩
  rw [equal] at strict
  exact (Nat.lt_irrefl _ strict)

theorem later_checkpoint_rejects_any_lane_rollback
    (master : ForestCheckpointMaster)
    (current : LaneSequences)
    (hasCheckpoint : master.hasCheckpoint = true)
    (canCreate : CanCreateCheckpoint master current)
    (lane : Lane) :
    master.lastLaneSequences lane ≤ current lane := by
  have monotone :
      ComponentwiseNondecreasing master.lastLaneSequences current := by
    have reduced := canCreate
    simp [CanCreateCheckpoint, hasCheckpoint] at reduced
    exact reduced.1
  exact monotone lane

theorem componentwise_nondecreasing_trans
    (first second third : LaneSequences)
    (left : ComponentwiseNondecreasing first second)
    (right : ComponentwiseNondecreasing second third) :
    ComponentwiseNondecreasing first third := by
  intro lane
  exact Nat.le_trans (left lane) (right lane)

/-- Every one of the eight lanes in one checkpoint contributes to the same
public anonymity anchor and has its canonical private path to that anchor. -/
theorem checkpoint_gives_every_lane_one_global_anonymity_root
    {Root : Type}
    (parent : Root → Root → Root)
    (master : ForestCheckpointMaster)
    (currentSequences : LaneSequences)
    (currentRoots : LaneVector Root)
    (lane : Lane) :
    foldThreeForestLevels parent (currentRoots lane)
        (forestSuperSibling parent currentRoots lane)
        (forestSuperDirection lane) =
      (makeCheckpoint parent master currentSequences currentRoots).globalRoot := by
  exact canonical_checkpoint_path_complete parent currentRoots lane

/-- Updating one lane changes only its sequence component before the next
coherent checkpoint; the remaining seven observed sequences are preserved. -/
theorem update_one_lane_preserves_other_sequence_components
    (sequences : LaneSequences)
    (written other : Lane)
    (next : Nat)
    (different : written ≠ other) :
    updateLane sequences written next other = sequences other := by
  exact update_other_lane_preserves_state sequences written other next different

#print axioms checkpoint_uses_exact_master_sequence
#print axioms checkpoint_binds_exact_observed_lane_vector
#print axioms checkpoint_global_root_is_exact_seven_parent_tree
#print axioms advance_master_increments_checkpoint_sequence_once
#print axioms later_checkpoint_rejects_identical_lane_sequences
#print axioms later_checkpoint_rejects_any_lane_rollback
#print axioms componentwise_nondecreasing_trans
#print axioms checkpoint_gives_every_lane_one_global_anonymity_root
#print axioms update_one_lane_preserves_other_sequence_components

end AspisPool.V7EightLaneCheckpointChronology
