import AspisFormal.Pool.V7PoolOneTxPreChallengeCommitment

/-!
# Eight-lane one-transaction Pool concurrency gate

This module is a production-inactive arithmetic and state-separation gate for
replacing one globally mutable pair-tree tip by eight independently writable
depth-20 pair-tree lanes under one depth-three historical super-root.

The three additional historical-membership parents occupy the exact three
sixteen-row blocks left by the frozen pair relation.  The corresponding three
private direction bits occupy the three unused slots in the sixth path
auxiliary block.  No trace-domain, PCS-width, fixed-claim, or proof-wire
parameter changes.

This module does not assume that eight lanes eliminate contention.  It proves
the precise state-separation property: an update to a different lane preserves
a completed proof's bound source state, while an update to the same lane may
make it stale.  Coherent global checkpoints are defined from one complete
eight-lane snapshot; the eventual Solana source bridge must prove that all
eight lane accounts are read in the same checkpoint transaction.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace AspisPool.V7EightLaneForestGeometry

open AspisPool.V7PairTreeTraceGeometry
open AspisPool.V7PoolOneTxPreChallengeCommitment

def laneCount : Nat := 8
def laneIndexBits : Nat := 3
def laneTreeDepth : Nat := 20
def superRootDepth : Nat := laneIndexBits
def superRootPoseidonBlocks : Nat := superRootDepth
def superRootPoseidonRows : Nat := superRootPoseidonBlocks * blockRows

def forestPrivateDirections : Nat :=
  pairMembershipHashBlocks + laneTreeDepth + superRootDepth

def availablePrivateDirectionSlots : Nat :=
  membershipAuxBlocks * directionsPerAuxBlock

def forestPoseidonBlocks : Nat := poseidonBlocks + superRootPoseidonBlocks
def forestAllocatedRows : Nat := allocatedRows + superRootPoseidonRows
def forestRemainingRows : Nat := traceRows - forestAllocatedRows

theorem exact_eight_lane_geometry :
    laneCount = 2 ^ laneIndexBits ∧
      superRootDepth = 3 ∧
      superRootPoseidonBlocks = 3 ∧
      superRootPoseidonRows = 48 := by
  decide

theorem exact_private_direction_capacity :
    forestPrivateDirections = 24 ∧
      availablePrivateDirectionSlots = 24 ∧
      forestPrivateDirections = availablePrivateDirectionSlots := by
  decide

theorem exact_forest_fills_trace :
    forestPoseidonBlocks = 57 ∧
      forestAllocatedRows = 1024 ∧
      forestRemainingRows = 0 := by
  decide

/-! A literal placement of the three new parents in blocks `61..63` loses four
raw-opening masking dimensions.  The exact forest layout therefore permutes
the same ten-block tail without changing any logical relation or wire shape:
blocks `0..53` retain the old Poseidon schedule, blocks `54..56` are the three
new stable super-root parents, blocks `57..62` carry all 24 private direction
gadgets, and block `63` carries the old value/occupancy auxiliaries. -/

def superRootPhysicalBlock (level : Fin 3) : Nat := 54 + level.val
def superRootRowStart (level : Fin 3) : Nat :=
  superRootPhysicalBlock level * blockRows
def superRootRowEnd (level : Fin 3) : Nat :=
  superRootRowStart level + blockRows

def forestPathAuxBlockStart : Nat := 57
def forestPathAuxRowStart : Nat := forestPathAuxBlockStart * blockRows
def forestPathAuxRowEnd : Nat := forestPathAuxRowStart + membershipAuxBlocks * blockRows
def forestValueAuxBlock : Nat := 63
def forestValueAuxRowStart : Nat := forestValueAuxBlock * blockRows

theorem exact_permuted_tail_blocks :
    (superRootPhysicalBlock ⟨0, by decide⟩,
      superRootPhysicalBlock ⟨1, by decide⟩,
      superRootPhysicalBlock ⟨2, by decide⟩) = (54, 55, 56) ∧
    (superRootRowStart ⟨0, by decide⟩,
      superRootRowStart ⟨1, by decide⟩,
      superRootRowStart ⟨2, by decide⟩) = (864, 880, 896) ∧
    superRootRowEnd ⟨2, by decide⟩ = forestPathAuxRowStart ∧
    forestPathAuxRowStart = 912 ∧
    forestPathAuxRowEnd = forestValueAuxRowStart ∧
    forestValueAuxRowStart = 1008 ∧
    forestValueAuxRowStart + blockRows = traceRows := by
  decide

def existingPoseidonRows : Finset Nat := Finset.Icc 0 863
def superRootRows : Finset Nat := Finset.Icc 864 911
def forestPathAuxRows : Finset Nat := Finset.Icc 912 1007
def forestValueAuxRows : Finset Nat := Finset.Icc 1008 1023

theorem permuted_tail_partitions_trace :
    existingPoseidonRows ∪ superRootRows ∪ forestPathAuxRows ∪ forestValueAuxRows =
      Finset.Icc 0 1023 ∧
    superRootRows.card = 48 ∧
    forestPathAuxRows.card = 96 ∧
    forestValueAuxRows.card = 16 := by
  constructor
  · ext row
    simp [existingPoseidonRows, superRootRows, forestPathAuxRows, forestValueAuxRows]
    omega
  · simp [superRootRows, forestPathAuxRows, forestValueAuxRows]

/-! ## Exact reuse of the three unused direction slots -/

def forestPathBaseRow (level : Fin 24) : Nat :=
  (forestPathAuxBlockStart + level.val / directionsPerAuxBlock) * blockRows +
    1 + 4 * (level.val % directionsPerAuxBlock)

def forestPathSuccessorRow (level : Fin 24) : Nat :=
  forestPathBaseRow level + 1

def forestPathSiblingRow (level : Fin 24) : Nat :=
  forestPathBaseRow level + 2

theorem exact_four_direction_rows_per_aux_block :
    ∀ block : Fin 6,
      (forestPathBaseRow ⟨4 * block.val, by omega⟩ % blockRows,
        forestPathBaseRow ⟨4 * block.val + 1, by omega⟩ % blockRows,
        forestPathBaseRow ⟨4 * block.val + 2, by omega⟩ % blockRows,
        forestPathBaseRow ⟨4 * block.val + 3, by omega⟩ % blockRows) =
        (1, 5, 9, 13) := by
  decide

theorem exact_three_new_direction_slots :
    (forestPathBaseRow ⟨21, by decide⟩,
      forestPathBaseRow ⟨22, by decide⟩,
      forestPathBaseRow ⟨23, by decide⟩) = (997, 1001, 1005) ∧
    (forestPathSuccessorRow ⟨21, by decide⟩,
      forestPathSuccessorRow ⟨22, by decide⟩,
      forestPathSuccessorRow ⟨23, by decide⟩) = (998, 1002, 1006) ∧
    (forestPathSiblingRow ⟨21, by decide⟩,
      forestPathSiblingRow ⟨22, by decide⟩,
      forestPathSiblingRow ⟨23, by decide⟩) = (999, 1003, 1007) := by
  decide

theorem all_twenty_four_direction_rows_stay_in_forest_aux_region :
    ∀ level : Fin 24,
      forestPathAuxRowStart ≤ forestPathBaseRow level ∧
      forestPathBaseRow level < forestPathAuxRowEnd ∧
      forestPathAuxRowStart ≤ forestPathSuccessorRow level ∧
      forestPathSuccessorRow level < forestPathAuxRowEnd ∧
      forestPathAuxRowStart ≤ forestPathSiblingRow level ∧
      forestPathSiblingRow level < forestPathAuxRowEnd := by
  decide

/-! Logical direction zero selects the occupied slot inside its pair leaf,
directions `1..20` select the depth-20 lane path, and directions `21..23`
select the private lane inside the historical eight-root checkpoint. -/

inductive ForestDirectionRole where
  | pairSlot
  | laneTree (level : Fin 20)
  | superRoot (level : Fin 3)
  deriving DecidableEq

def forestDirectionRole (direction : Fin 24) : ForestDirectionRole :=
  if h0 : direction.val = 0 then .pairSlot
  else if h1 : direction.val ≤ 20 then
    .laneTree ⟨direction.val - 1, by omega⟩
  else .superRoot ⟨direction.val - 21, by omega⟩

theorem final_three_directions_are_exact_super_root_path :
    forestDirectionRole ⟨21, by decide⟩ = .superRoot ⟨0, by decide⟩ ∧
      forestDirectionRole ⟨22, by decide⟩ = .superRoot ⟨1, by decide⟩ ∧
      forestDirectionRole ⟨23, by decide⟩ = .superRoot ⟨2, by decide⟩ := by
  decide

def membershipHashBlock (direction : Fin 24) : Nat :=
  if direction.val ≤ 20 then 4 + direction.val
  else 33 + direction.val

def membershipPreviousOutputRow (direction : Fin 24) : Nat :=
  if h : direction.val = 0 then 3 * blockRows + 11
  else membershipHashBlock ⟨direction.val - 1, by omega⟩ * blockRows + 11

def membershipTargetPreRow (direction : Fin 24) : Nat :=
  membershipHashBlock direction * blockRows

def membershipTargetAbsorptionRow (direction : Fin 24) : Nat :=
  membershipTargetPreRow direction + 12

theorem exact_super_root_copy_endpoints :
    (membershipPreviousOutputRow ⟨21, by decide⟩,
      membershipPreviousOutputRow ⟨22, by decide⟩,
      membershipPreviousOutputRow ⟨23, by decide⟩) = (395, 875, 891) ∧
    (membershipTargetPreRow ⟨21, by decide⟩,
      membershipTargetPreRow ⟨22, by decide⟩,
      membershipTargetPreRow ⟨23, by decide⟩) = (864, 880, 896) ∧
    (membershipTargetAbsorptionRow ⟨21, by decide⟩,
      membershipTargetAbsorptionRow ⟨22, by decide⟩,
      membershipTargetAbsorptionRow ⟨23, by decide⟩) = (876, 892, 908) := by
  decide

def existingCopyLinks : Nat := 127
def additionalSuperRootCopyLinks : Nat := 3 * superRootDepth
def forestCopyLinks : Nat := existingCopyLinks + additionalSuperRootCopyLinks

theorem exact_copy_link_delta :
    additionalSuperRootCopyLinks = 9 ∧ forestCopyLinks = 136 := by
  decide

/-! ## Degree and wire invariants -/

def superRootIntrinsicDegree : Nat := 25
def superRootDeployedDegree : Nat :=
  superRootIntrinsicDegree + selectorDegreeOverhead + outerZerocheckDegreeOverhead

theorem super_root_path_retains_degree_27 :
    superRootIntrinsicDegree = intrinsicDegree .twoRoundPoseidon ∧
      superRootDeployedDegree = 27 := by
  decide

theorem forest_retains_frozen_pcs_and_wire :
    c1Columns = 26 ∧
      c2Columns = 3 ∧
      logicalGammaColumns = 29 ∧
      fixedQM31Values = 641 ∧
      maximumBodyBytes = 30504 := by
  decide

/-! ## One global root for all eight lanes -/

abbrev Lane := Fin 8
abbrev LaneVector (State : Type) := Lane → State

def forestSuperRoot {Node : Type}
    (parent : Node → Node → Node) (roots : LaneVector Node) : Node :=
  parent
    (parent (parent (roots 0) (roots 1)) (parent (roots 2) (roots 3)))
    (parent (parent (roots 4) (roots 5)) (parent (roots 6) (roots 7)))

def forestLeftHalf {Node : Type}
    (parent : Node → Node → Node) (roots : LaneVector Node) : Node :=
  parent (parent (roots 0) (roots 1)) (parent (roots 2) (roots 3))

def forestRightHalf {Node : Type}
    (parent : Node → Node → Node) (roots : LaneVector Node) : Node :=
  parent (parent (roots 4) (roots 5)) (parent (roots 6) (roots 7))

def forestSuperSibling {Node : Type}
    (parent : Node → Node → Node) (roots : LaneVector Node)
    (lane : Lane) (level : Fin 3) : Node :=
  if lane.val = 0 then
    if level.val = 0 then roots 1
    else if level.val = 1 then parent (roots 2) (roots 3)
    else forestRightHalf parent roots
  else if lane.val = 1 then
    if level.val = 0 then roots 0
    else if level.val = 1 then parent (roots 2) (roots 3)
    else forestRightHalf parent roots
  else if lane.val = 2 then
    if level.val = 0 then roots 3
    else if level.val = 1 then parent (roots 0) (roots 1)
    else forestRightHalf parent roots
  else if lane.val = 3 then
    if level.val = 0 then roots 2
    else if level.val = 1 then parent (roots 0) (roots 1)
    else forestRightHalf parent roots
  else if lane.val = 4 then
    if level.val = 0 then roots 5
    else if level.val = 1 then parent (roots 6) (roots 7)
    else forestLeftHalf parent roots
  else if lane.val = 5 then
    if level.val = 0 then roots 4
    else if level.val = 1 then parent (roots 6) (roots 7)
    else forestLeftHalf parent roots
  else if lane.val = 6 then
    if level.val = 0 then roots 7
    else if level.val = 1 then parent (roots 4) (roots 5)
    else forestLeftHalf parent roots
  else
    if level.val = 0 then roots 6
    else if level.val = 1 then parent (roots 4) (roots 5)
    else forestLeftHalf parent roots

def forestSuperDirection (lane : Lane) (level : Fin 3) : Bool :=
  decide ((lane.val / (2 ^ level.val)) % 2 = 1)

def orderedParent {Node : Type}
    (parent : Node → Node → Node) (right : Bool)
    (current sibling : Node) : Node :=
  if right then parent sibling current else parent current sibling

def reconstructForestSuperRoot {Node : Type}
    (parent : Node → Node → Node) (roots : LaneVector Node)
    (lane : Lane) : Node :=
  let level0 := orderedParent parent (forestSuperDirection lane 0)
    (roots lane) (forestSuperSibling parent roots lane 0)
  let level1 := orderedParent parent (forestSuperDirection lane 1)
    level0 (forestSuperSibling parent roots lane 1)
  orderedParent parent (forestSuperDirection lane 2)
    level1 (forestSuperSibling parent roots lane 2)

/-- Each privately selected lane root and its exact three sibling subtrees
reconstruct the same public global root.  Thus the statement need not expose
which lane contained the input note. -/
theorem every_lane_reconstructs_same_global_root
    {Node : Type} (parent : Node → Node → Node) (roots : LaneVector Node)
    (lane : Lane) :
    reconstructForestSuperRoot parent roots lane = forestSuperRoot parent roots := by
  fin_cases lane <;>
    simp [reconstructForestSuperRoot, forestSuperDirection,
      forestSuperSibling, forestSuperRoot, forestLeftHalf, forestRightHalf,
      orderedParent]

/-! ## Coherent checkpoint and exact concurrency boundary -/

def updateLane {State : Type}
    (states : LaneVector State) (lane : Lane) (next : State) : LaneVector State :=
  Function.update states lane next

theorem update_other_lane_preserves_state
    {State : Type} [DecidableEq Lane]
    (states : LaneVector State) (written proofLane : Lane) (next : State)
    (different : written ≠ proofLane) :
    updateLane states written next proofLane = states proofLane := by
  simp [updateLane, Ne.symm different]

structure LaneBoundProof (State : Type) where
  lane : Lane
  source : State

def LaneAccepts {State : Type}
    (live : LaneVector State) (proof : LaneBoundProof State) : Prop :=
  live proof.lane = proof.source

theorem different_lane_update_preserves_completed_proof
    {State : Type} [DecidableEq Lane]
    (live : LaneVector State) (proof : LaneBoundProof State)
    (written : Lane) (next : State)
    (accepted : LaneAccepts live proof)
    (different : written ≠ proof.lane) :
    LaneAccepts (updateLane live written next) proof := by
  simpa [LaneAccepts, updateLane, Ne.symm different] using accepted

theorem same_lane_changed_source_rejects_completed_proof
    {State : Type} [DecidableEq State] [DecidableEq Lane]
    (live : LaneVector State) (proof : LaneBoundProof State) (next : State)
    (accepted : LaneAccepts live proof)
    (changed : next ≠ proof.source) :
    ¬ LaneAccepts (updateLane live proof.lane next) proof := by
  simpa [LaneAccepts, updateLane] using changed

/-- A checkpoint is formed from one complete eight-lane state vector.  The
eventual program proof must establish that `observed` came from the eight
specific lane PDAs in one Solana instruction, rather than from separately
timed RPC reads. -/
structure CoherentCheckpoint (State Root : Type)
    (laneRoot : State → Root) (superRoot : (Lane → Root) → Root) where
  observed : LaneVector State

def checkpointComponentRoots
    {State Root : Type}
    (laneRoot : State → Root) (superRoot : (Lane → Root) → Root)
    (checkpoint : CoherentCheckpoint State Root laneRoot superRoot) : Lane → Root :=
  fun lane => laneRoot (checkpoint.observed lane)

def checkpointRoot
    {State Root : Type}
    (laneRoot : State → Root) (superRoot : (Lane → Root) → Root)
    (checkpoint : CoherentCheckpoint State Root laneRoot superRoot) : Root :=
  superRoot (checkpointComponentRoots laneRoot superRoot checkpoint)

theorem checkpoint_component_is_from_same_observed_vector
    {State Root : Type}
    (laneRoot : State → Root) (superRoot : (Lane → Root) → Root)
    (checkpoint : CoherentCheckpoint State Root laneRoot superRoot)
    (lane : Lane) :
    checkpointComponentRoots laneRoot superRoot checkpoint lane =
      laneRoot (checkpoint.observed lane) := by
  rfl

/-- The public *output* lane is a deterministic image of the proof-bound
public nullifier.  This is distinct from the private input lane encoded by
directions 21--23.  The concrete source contract will use the low three bits
of the canonical first nullifier limb and derive the writable lane PDA from
it. -/
structure DeterministicOutputLaneBinding (Nullifier : Type)
    (laneOf : Nullifier → Lane) where
  nullifier : Nullifier
  lane : Lane
  exact_lane : lane = laneOf nullifier

theorem output_lane_binding_is_functional
    {Nullifier : Type} (laneOf : Nullifier → Lane)
    (left right : DeterministicOutputLaneBinding Nullifier laneOf)
    (sameNullifier : left.nullifier = right.nullifier) :
    left.lane = right.lane := by
  rw [left.exact_lane, right.exact_lane, sameNullifier]

#print axioms exact_eight_lane_geometry
#print axioms exact_private_direction_capacity
#print axioms exact_forest_fills_trace
#print axioms exact_permuted_tail_blocks
#print axioms permuted_tail_partitions_trace
#print axioms exact_four_direction_rows_per_aux_block
#print axioms exact_three_new_direction_slots
#print axioms all_twenty_four_direction_rows_stay_in_forest_aux_region
#print axioms exact_super_root_copy_endpoints
#print axioms exact_copy_link_delta
#print axioms super_root_path_retains_degree_27
#print axioms forest_retains_frozen_pcs_and_wire
#print axioms every_lane_reconstructs_same_global_root
#print axioms different_lane_update_preserves_completed_proof
#print axioms same_lane_changed_source_rejects_completed_proof
#print axioms checkpoint_component_is_from_same_observed_vector
#print axioms output_lane_binding_is_functional

end AspisPool.V7EightLaneForestGeometry
