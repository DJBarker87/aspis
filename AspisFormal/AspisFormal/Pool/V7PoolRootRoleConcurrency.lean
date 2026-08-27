import AspisFormal.Pool.V7PairTreeTraceGeometry

/-!
# Historical membership roots versus live append roots

This file makes the concurrency boundary of the proposed one-transaction Pool
path explicit.

The expensive Stage-A artifact is indexed only by a retained membership anchor
and stable spend/output data. It includes the output-pair compression. After
the Stage-A root has fixed that data and `lambda, chi` have been sampled, the
prover reads the live append snapshot and constructs the twenty-node append
tail in Stage B. A stale Stage-B tail is rejected and exposes no after-state;
rebasing reuses Stage A exactly but necessarily rebuilds Stage B and the proof
suffix.

This is a candidate Pool transcript contract, not a claim about the currently
frozen Tag-73 source. The frozen schedule has no post-`chi` live-snapshot
absorption and its Stage-B message has only the three existing helper QM31
lanes. Production integration therefore remains gated on implementing and
source-bridging this schedule, expanding Stage B by four QM31 lanes, and
measuring the rebuild window.
-/

set_option autoImplicit false

namespace AspisPool.V7PoolRootRoleConcurrency

open AspisPool.V7PairLeafOccupancy
open AspisPool.V7PairTreeTraceGeometry

structure HistoricalMembershipAnchor (Root : Type) where
  sequence : Nat
  root : Root
  deriving DecidableEq

structure LiveAppendState (Root Frontier : Type) where
  sequence : Nat
  nextPairIndex : Nat
  root : Root
  frontier : Frontier
  deriving DecidableEq

/-- Data whose expensive proof can be prepared without choosing the current
append state. -/
structure StableSpendStatement (Root Nullifier K : Type) where
  membershipAnchor : HistoricalMembershipAnchor Root
  nullifier : Nullifier
  outputPair : PairLeaf K

/-- Abstract Stage-A certificate. Its type contains no live append root,
cursor, sequence or frontier. -/
structure PreparedStageA
    {Root Nullifier K StageARoot : Type}
    (statement : StableSpendStatement Root Nullifier K)
    (stableRelation : StableSpendStatement Root Nullifier K → Prop) : Type where
  root : StageARoot
  valid : stableRelation statement

/-- The late-bound append tail. `transitionValid` is the transparent
twenty-node pair-tree relation proved for exactly this source and result. -/
structure LateAppendTail
    {Root Frontier K : Type}
    (outputPair : PairLeaf K)
    (transitionValid : PairLeaf K → LiveAppendState Root Frontier →
      LiveAppendState Root Frontier → Prop) : Type where
  source : LiveAppendState Root Frontier
  result : LiveAppendState Root Frontier
  valid : transitionValid outputPair source result

/-- Stage B and every remaining Fiat--Shamir/proximity message must be rebuilt
for the chosen live tail. -/
structure StageBContinuation
    {Root Frontier Nullifier K StageARoot StageBRoot : Type}
    {statement : StableSpendStatement Root Nullifier K}
    {stableRelation : StableSpendStatement Root Nullifier K → Prop}
    {transitionValid : PairLeaf K → LiveAppendState Root Frontier →
      LiveAppendState Root Frontier → Prop}
    (stageA : PreparedStageA (StageARoot := StageARoot) statement stableRelation)
    (tail : LateAppendTail statement.outputPair transitionValid)
    (continuationValid :
      PreparedStageA (StageARoot := StageARoot) statement stableRelation →
      LateAppendTail statement.outputPair transitionValid → StageBRoot → Prop) : Type where
  root : StageBRoot
  valid : continuationValid stageA tail root

/-- The completed proof keeps reusable Stage A and snapshot-specific Stage B
as separate typed components. -/
structure StagedLateBoundSpendProof
    {Root Frontier Nullifier K StageARoot StageBRoot : Type}
    (statement : StableSpendStatement Root Nullifier K)
    (stableRelation : StableSpendStatement Root Nullifier K → Prop)
    (transitionValid : PairLeaf K → LiveAppendState Root Frontier →
      LiveAppendState Root Frontier → Prop)
    (continuationValid :
      PreparedStageA (StageARoot := StageARoot) statement stableRelation →
      LateAppendTail statement.outputPair transitionValid → StageBRoot → Prop) : Type where
  stageA : PreparedStageA (StageARoot := StageARoot) statement stableRelation
  tail : LateAppendTail statement.outputPair transitionValid
  stageB : StageBContinuation stageA tail continuationValid

/-- Acceptance keeps root roles separate. Historical membership is retained
independently; only the Stage-B append source must equal live account state. -/
def Accepts
    {Root Frontier Nullifier K StageARoot StageBRoot : Type}
    [DecidableEq Root] [DecidableEq Frontier]
    (retained : HistoricalMembershipAnchor Root → Prop)
    (statement : StableSpendStatement Root Nullifier K)
    (stableRelation : StableSpendStatement Root Nullifier K → Prop)
    (transitionValid : PairLeaf K → LiveAppendState Root Frontier →
      LiveAppendState Root Frontier → Prop)
    (continuationValid :
      PreparedStageA (StageARoot := StageARoot) statement stableRelation →
      LateAppendTail statement.outputPair transitionValid → StageBRoot → Prop)
    (live : LiveAppendState Root Frontier)
    (proof : StagedLateBoundSpendProof statement stableRelation transitionValid
      continuationValid) : Prop :=
  retained statement.membershipAnchor ∧ proof.tail.source = live

/-- Atomic settlement exposes the proposed after-state only on acceptance. -/
noncomputable def settle
    {Root Frontier Nullifier K StageARoot StageBRoot : Type}
    [DecidableEq Root] [DecidableEq Frontier]
    (retained : HistoricalMembershipAnchor Root → Prop)
    (statement : StableSpendStatement Root Nullifier K)
    (stableRelation : StableSpendStatement Root Nullifier K → Prop)
    (transitionValid : PairLeaf K → LiveAppendState Root Frontier →
      LiveAppendState Root Frontier → Prop)
    (continuationValid :
      PreparedStageA (StageARoot := StageARoot) statement stableRelation →
      LateAppendTail statement.outputPair transitionValid → StageBRoot → Prop)
    (live : LiveAppendState Root Frontier)
    (proof : StagedLateBoundSpendProof statement stableRelation transitionValid
      continuationValid) : Option (LiveAppendState Root Frontier) := by
  classical
  exact if Accepts retained statement stableRelation transitionValid
      continuationValid live proof then some proof.tail.result else none

theorem acceptance_uses_retained_membership_anchor
    {Root Frontier Nullifier K StageARoot StageBRoot : Type}
    [DecidableEq Root] [DecidableEq Frontier]
    {retained : HistoricalMembershipAnchor Root → Prop}
    {statement : StableSpendStatement Root Nullifier K}
    {stableRelation : StableSpendStatement Root Nullifier K → Prop}
    {transitionValid : PairLeaf K → LiveAppendState Root Frontier →
      LiveAppendState Root Frontier → Prop}
    {continuationValid :
      PreparedStageA (StageARoot := StageARoot) statement stableRelation →
      LateAppendTail statement.outputPair transitionValid → StageBRoot → Prop}
    {live : LiveAppendState Root Frontier}
    {proof : StagedLateBoundSpendProof statement stableRelation transitionValid
      continuationValid}
    (accepted : Accepts retained statement stableRelation transitionValid
      continuationValid live proof) : retained statement.membershipAnchor :=
  accepted.1

theorem acceptance_binds_exact_live_append_state
    {Root Frontier Nullifier K StageARoot StageBRoot : Type}
    [DecidableEq Root] [DecidableEq Frontier]
    {retained : HistoricalMembershipAnchor Root → Prop}
    {statement : StableSpendStatement Root Nullifier K}
    {stableRelation : StableSpendStatement Root Nullifier K → Prop}
    {transitionValid : PairLeaf K → LiveAppendState Root Frontier →
      LiveAppendState Root Frontier → Prop}
    {continuationValid :
      PreparedStageA (StageARoot := StageARoot) statement stableRelation →
      LateAppendTail statement.outputPair transitionValid → StageBRoot → Prop}
    {live : LiveAppendState Root Frontier}
    {proof : StagedLateBoundSpendProof statement stableRelation transitionValid
      continuationValid}
    (accepted : Accepts retained statement stableRelation transitionValid
      continuationValid live proof) : proof.tail.source = live :=
  accepted.2

theorem stale_source_rejected
    {Root Frontier Nullifier K StageARoot StageBRoot : Type}
    [DecidableEq Root] [DecidableEq Frontier]
    (retained : HistoricalMembershipAnchor Root → Prop)
    (statement : StableSpendStatement Root Nullifier K)
    (stableRelation : StableSpendStatement Root Nullifier K → Prop)
    (transitionValid : PairLeaf K → LiveAppendState Root Frontier →
      LiveAppendState Root Frontier → Prop)
    (continuationValid :
      PreparedStageA (StageARoot := StageARoot) statement stableRelation →
      LateAppendTail statement.outputPair transitionValid → StageBRoot → Prop)
    (live : LiveAppendState Root Frontier)
    (proof : StagedLateBoundSpendProof statement stableRelation transitionValid
      continuationValid)
    (stale : proof.tail.source ≠ live) :
    ¬ Accepts retained statement stableRelation transitionValid
      continuationValid live proof := by
  intro accepted
  exact stale accepted.2

theorem stale_source_settlement_returns_none
    {Root Frontier Nullifier K StageARoot StageBRoot : Type}
    [DecidableEq Root] [DecidableEq Frontier]
    (retained : HistoricalMembershipAnchor Root → Prop)
    (statement : StableSpendStatement Root Nullifier K)
    (stableRelation : StableSpendStatement Root Nullifier K → Prop)
    (transitionValid : PairLeaf K → LiveAppendState Root Frontier →
      LiveAppendState Root Frontier → Prop)
    (continuationValid :
      PreparedStageA (StageARoot := StageARoot) statement stableRelation →
      LateAppendTail statement.outputPair transitionValid → StageBRoot → Prop)
    (live : LiveAppendState Root Frontier)
    (proof : StagedLateBoundSpendProof statement stableRelation transitionValid
      continuationValid)
    (stale : proof.tail.source ≠ live) :
    settle retained statement stableRelation transitionValid continuationValid
      live proof = none := by
  rw [settle]
  simp [stale_source_rejected retained statement stableRelation transitionValid
    continuationValid live proof stale]

/-- Recompletion takes the same Stage-A artifact but requires a new tail and a
new Stage-B/suffix certificate. It does not claim that old final proof bytes
remain valid. -/
def recomplete
    {Root Frontier Nullifier K StageARoot StageBRoot : Type}
    {statement : StableSpendStatement Root Nullifier K}
    {stableRelation : StableSpendStatement Root Nullifier K → Prop}
    {transitionValid : PairLeaf K → LiveAppendState Root Frontier →
      LiveAppendState Root Frontier → Prop}
    {continuationValid :
      PreparedStageA (StageARoot := StageARoot) statement stableRelation →
      LateAppendTail statement.outputPair transitionValid → StageBRoot → Prop}
    (stageA : PreparedStageA (StageARoot := StageARoot) statement stableRelation)
    (freshTail : LateAppendTail statement.outputPair transitionValid)
    (freshStageB : StageBContinuation stageA freshTail continuationValid) :
    StagedLateBoundSpendProof statement stableRelation transitionValid
      continuationValid :=
  ⟨stageA, freshTail, freshStageB⟩

@[simp] theorem recomplete_preserves_stageA_exactly
    {Root Frontier Nullifier K StageARoot StageBRoot : Type}
    {statement : StableSpendStatement Root Nullifier K}
    {stableRelation : StableSpendStatement Root Nullifier K → Prop}
    {transitionValid : PairLeaf K → LiveAppendState Root Frontier →
      LiveAppendState Root Frontier → Prop}
    {continuationValid :
      PreparedStageA (StageARoot := StageARoot) statement stableRelation →
      LateAppendTail statement.outputPair transitionValid → StageBRoot → Prop}
    (stageA : PreparedStageA (StageARoot := StageARoot) statement stableRelation)
    (freshTail : LateAppendTail statement.outputPair transitionValid)
    (freshStageB : StageBContinuation stageA freshTail continuationValid) :
    (recomplete stageA freshTail freshStageB).stageA = stageA :=
  rfl

@[simp] theorem recomplete_uses_fresh_append_source
    {Root Frontier Nullifier K StageARoot StageBRoot : Type}
    {statement : StableSpendStatement Root Nullifier K}
    {stableRelation : StableSpendStatement Root Nullifier K → Prop}
    {transitionValid : PairLeaf K → LiveAppendState Root Frontier →
      LiveAppendState Root Frontier → Prop}
    {continuationValid :
      PreparedStageA (StageARoot := StageARoot) statement stableRelation →
      LateAppendTail statement.outputPair transitionValid → StageBRoot → Prop}
    (stageA : PreparedStageA (StageARoot := StageARoot) statement stableRelation)
    (freshTail : LateAppendTail statement.outputPair transitionValid)
    (freshStageB : StageBContinuation stageA freshTail continuationValid) :
    (recomplete stageA freshTail freshStageB).tail.source = freshTail.source :=
  rfl

/-! ## Exact commitment schedule and lane cost -/

inductive TranscriptStep where
  | stableStatement
  | stageARoot
  | lambda
  | chi
  | liveAppendSnapshot
  | stageBRoot
  | batchingChallenges
  deriving DecidableEq

def frozenTag73Prefix : List TranscriptStep :=
  [.stableStatement, .stageARoot, .lambda, .chi, .stageBRoot,
    .batchingChallenges]

def stagedPoolPrefix : List TranscriptStep :=
  [.stableStatement, .stageARoot, .lambda, .chi, .liveAppendSnapshot,
    .stageBRoot, .batchingChallenges]

theorem staged_pool_prefix_fixes_live_snapshot_after_stageA_before_stageB :
    stagedPoolPrefix =
      [.stableStatement, .stageARoot, .lambda, .chi, .liveAppendSnapshot,
        .stageBRoot, .batchingChallenges] :=
  rfl

theorem frozen_tag73_prefix_has_no_late_snapshot :
    TranscriptStep.liveAppendSnapshot ∉ frozenTag73Prefix := by
  decide

theorem staged_pool_prefix_is_not_the_frozen_tag73_prefix :
    stagedPoolPrefix ≠ frozenTag73Prefix := by
  decide

def existingStageBHelperQM31Lanes : Nat := 3
def m31CoordinatesPerQM31 : Nat := 4
def lateAppendM31Columns : Nat := traceColumns
def lateAppendQM31Lanes : Nat :=
  lateAppendM31Columns / m31CoordinatesPerQM31
def stagedPoolStageBQM31Lanes : Nat :=
  existingStageBHelperQM31Lanes + lateAppendQM31Lanes

theorem exact_stageB_lane_expansion :
    lateAppendM31Columns = 16 ∧
      lateAppendQM31Lanes = 4 ∧
      stagedPoolStageBQM31Lanes = 7 := by
  decide

inductive SemanticRowOwner where
  | stableStageA
  | liveStageB
  | unused
  deriving DecidableEq

/-- Blocks 0..33 and all auxiliary rows are stable. Blocks 34..53 are the
late append tail. The final 48 rows remain unused. -/
def semanticRowOwner (row : Fin 1024) : SemanticRowOwner :=
  if row.val < stableStagePoseidonRowEnd then .stableStageA
  else if row.val < lateStagePoseidonRowEnd then .liveStageB
  else if row.val < untouchedRowStart then .stableStageA
  else .unused

set_option maxRecDepth 10000 in
theorem exact_semantic_row_owner_cardinalities :
    (Finset.univ.filter (fun row : Fin 1024 =>
      semanticRowOwner row = .stableStageA)).card = 656 ∧
    (Finset.univ.filter (fun row : Fin 1024 =>
      semanticRowOwner row = .liveStageB)).card = 320 ∧
    (Finset.univ.filter (fun row : Fin 1024 =>
      semanticRowOwner row = .unused)).card = 48 := by
  decide

#print axioms stale_source_rejected
#print axioms stale_source_settlement_returns_none
#print axioms recomplete_preserves_stageA_exactly
#print axioms recomplete_uses_fresh_append_source
#print axioms frozen_tag73_prefix_has_no_late_snapshot
#print axioms staged_pool_prefix_is_not_the_frozen_tag73_prefix
#print axioms exact_stageB_lane_expansion
#print axioms exact_semantic_row_owner_cardinalities

end AspisPool.V7PoolRootRoleConcurrency
