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

/-- A completed proof is pinned to exactly one live append snapshot.  It
cannot be accepted against two distinct `(sequence, nextPairIndex, root,
frontier)` states. -/
theorem completed_proof_accepts_at_most_one_live_state
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
    {left right : LiveAppendState Root Frontier}
    {proof : StagedLateBoundSpendProof statement stableRelation transitionValid
      continuationValid}
    (acceptedLeft : Accepts retained statement stableRelation transitionValid
      continuationValid left proof)
    (acceptedRight : Accepts retained statement stableRelation transitionValid
      continuationValid right proof) :
    left = right := by
  exact acceptedLeft.2.symm.trans acceptedRight.2

/-- If another append changes any live snapshot component after a completed
proof was made, those same final proof bytes reject.  Reusing Stage A still
requires `recomplete` with a fresh tail and fresh suffix. -/
theorem competing_append_invalidates_completed_proof
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
    {before after : LiveAppendState Root Frontier}
    {proof : StagedLateBoundSpendProof statement stableRelation transitionValid
      continuationValid}
    (acceptedBefore : Accepts retained statement stableRelation transitionValid
      continuationValid before proof)
    (changed : before ≠ after) :
    ¬ Accepts retained statement stableRelation transitionValid
      continuationValid after proof := by
  intro acceptedAfter
  exact changed
    (completed_proof_accepts_at_most_one_live_state acceptedBefore acceptedAfter)

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

theorem exact_staged_pool_prefix_positions :
    stagedPoolPrefix.idxOf .stageARoot = 1 ∧
      stagedPoolPrefix.idxOf .lambda = 2 ∧
      stagedPoolPrefix.idxOf .chi = 3 ∧
      stagedPoolPrefix.idxOf .liveAppendSnapshot = 4 ∧
      stagedPoolPrefix.idxOf .stageBRoot = 5 ∧
      stagedPoolPrefix.idxOf .batchingChallenges = 6 := by
  decide

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

/-! ## Primary execution-time append profile

The one-transaction audit found that authenticating the live append columns in
Stage B is not the minimum wire.  The primary profile proves the stable pair
relation only and lets the locked Pool execute the deterministic pair append.
Consequently its transcript has the frozen Tag-73 shape and contains no live
snapshot.  These are arithmetic/wire design gates, not a claim that the
production prover and verifier already implement this profile. -/

def stablePairPoseidonBlocks : Nat := 34
def stablePairAuxiliaryBlocks : Nat := 7
def stablePairAllocatedRows : Nat :=
  (stablePairPoseidonBlocks + stablePairAuxiliaryBlocks) * 16
def stablePairUnusedRows : Nat := traceRows - stablePairAllocatedRows

theorem exact_stable_pair_row_screen :
    stablePairAllocatedRows = 656 ∧ stablePairUnusedRows = 368 := by
  decide

def stablePairPrefix : List TranscriptStep := frozenTag73Prefix

theorem stable_pair_prefix_has_no_live_append_snapshot :
    TranscriptStep.liveAppendSnapshot ∉ stablePairPrefix := by
  decide

theorem stable_pair_prefix_keeps_frozen_tag73_order :
    stablePairPrefix =
      [.stableStatement, .stageARoot, .lambda, .chi, .stageBRoot,
        .batchingChallenges] := by
  rfl

/-- A completed primary-profile proof contains only the stable relation.  Its
type has no live root, sequence, cursor or frontier field. -/
structure StablePairSpendProof
    {Root Nullifier K : Type}
    (statement : StableSpendStatement Root Nullifier K)
    (stableRelation : StableSpendStatement Root Nullifier K → Prop) : Type where
  valid : stableRelation statement

def StablePairProofAccepts
    {Root Nullifier K : Type}
    (retained : HistoricalMembershipAnchor Root → Prop)
    (statement : StableSpendStatement Root Nullifier K)
    (stableRelation : StableSpendStatement Root Nullifier K → Prop)
    (_proof : StablePairSpendProof statement stableRelation) : Prop :=
  retained statement.membershipAnchor ∧ stableRelation statement

/-- Settlement applies the verified public output pair to the state locked at
execution.  `append = none` represents an ordinary state-side rejection such as
a full tree; it is not proof staleness. -/
noncomputable def settleStablePair
    {Root Frontier Nullifier K : Type}
    (append : PairLeaf K → LiveAppendState Root Frontier →
      Option (LiveAppendState Root Frontier))
    (retained : HistoricalMembershipAnchor Root → Prop)
    (statement : StableSpendStatement Root Nullifier K)
    (stableRelation : StableSpendStatement Root Nullifier K → Prop)
    (live : LiveAppendState Root Frontier)
    (proof : StablePairSpendProof statement stableRelation) :
    Option (LiveAppendState Root Frontier) := by
  classical
  exact if StablePairProofAccepts retained statement stableRelation proof then
    append statement.outputPair live
  else none

theorem stable_pair_proof_acceptance_has_no_live_state_dependency
    {Root Frontier Nullifier K : Type}
    (retained : HistoricalMembershipAnchor Root → Prop)
    (statement : StableSpendStatement Root Nullifier K)
    (stableRelation : StableSpendStatement Root Nullifier K → Prop)
    (proof : StablePairSpendProof statement stableRelation)
    (_before _after : LiveAppendState Root Frontier) :
    StablePairProofAccepts retained statement stableRelation proof ↔
      StablePairProofAccepts retained statement stableRelation proof :=
  Iff.rfl

theorem accepted_stable_pair_settlement_uses_execution_state
    {Root Frontier Nullifier K : Type}
    (append : PairLeaf K → LiveAppendState Root Frontier →
      Option (LiveAppendState Root Frontier))
    (retained : HistoricalMembershipAnchor Root → Prop)
    (statement : StableSpendStatement Root Nullifier K)
    (stableRelation : StableSpendStatement Root Nullifier K → Prop)
    (live : LiveAppendState Root Frontier)
    (proof : StablePairSpendProof statement stableRelation)
    (accepted : StablePairProofAccepts retained statement stableRelation proof) :
    settleStablePair append retained statement stableRelation live proof =
      append statement.outputPair live := by
  simp [settleStablePair, accepted]

/-! ## Exact unchanged-backend wire consequence

The four late lanes are QM31 columns, and each authenticated layer-zero query
opens four circle-fibre slots.  They therefore add sixteen QM31 values, not
four, to every query record.  The point-claim table also grows by four columns
at each of its three evaluation points.  These definitions mirror the frozen
31-bit packing arithmetic and make the cost of the candidate explicit before
any production source is changed.
-/

def packedM31Bytes (limbs : Nat) : Nat :=
  (limbs * 31 + 7) / 8

def frozenC1Columns : Nat := 26
def frozenC2Columns : Nat := 3
def stagedC2Columns : Nat := stagedPoolStageBQM31Lanes
def queryFibreSlots : Nat := 4
def m31LimbsPerQM31 : Nat := 4
def pointClaimRows : Nat := 3
def queryCount : Nat := 16
def privateSaltBytes : Nat := 32
def compactDigestBytes : Nat := 26
def frontierNodesPerTree : Nat := 203
def workNonceBytes : Nat := 24
def uploadChunkBytes : Nat := 960

def c1BytesPerQuery : Nat :=
  packedM31Bytes (m31LimbsPerQM31 * frozenC1Columns)

def c2BytesPerQuery (columns : Nat) : Nat :=
  packedM31Bytes
    (m31LimbsPerQM31 * queryFibreSlots * columns)

def queryBytes (c2Columns : Nat) : Nat :=
  c1BytesPerQuery + c2BytesPerQuery c2Columns + privateSaltBytes

/-- Frozen Tag-73 has 641 fixed QM31 values.  Four new point-claim columns at
three points add exactly twelve values. -/
def frozenFixedQM31Values : Nat := 641
def stagedFixedQM31Values : Nat :=
  frozenFixedQM31Values + pointClaimRows * lateAppendQM31Lanes

def fixedFieldBytes (values : Nat) : Nat :=
  packedM31Bytes (m31LimbsPerQM31 * values)

def rootBytes : Nat := 2 * compactDigestBytes
def bodyWithoutFrontiers (fixedValues c2Columns : Nat) : Nat :=
  fixedFieldBytes fixedValues + rootBytes + workNonceBytes +
    queryCount * queryBytes c2Columns

def bothFrontierBytes : Nat :=
  2 * frontierNodesPerTree * compactDigestBytes

def maximumBodyBytes (fixedValues c2Columns : Nat) : Nat :=
  bodyWithoutFrontiers fixedValues c2Columns + bothFrontierBytes

def frozenMaximumBodyBytes : Nat :=
  maximumBodyBytes frozenFixedQM31Values frozenC2Columns

def stagedMaximumBodyBytes : Nat :=
  maximumBodyBytes stagedFixedQM31Values stagedC2Columns

def stablePairMaximumBodyBytes : Nat :=
  maximumBodyBytes frozenFixedQM31Values frozenC2Columns

def uploadChunks (bytes : Nat) : Nat :=
  (bytes + uploadChunkBytes - 1) / uploadChunkBytes

/-- SHA-256 message blocks for `0x10 || tree_tag || value || salt32`, including
the `0x80`, length field and padding. -/
def sha256LeafBlocks (valueBytes : Nat) : Nat :=
  (2 + valueBytes + privateSaltBytes + 9 + 63) / 64

theorem exact_staged_wire_cost_if_four_late_lanes_authenticated :
    c1BytesPerQuery = 403 ∧
      c2BytesPerQuery frozenC2Columns = 186 ∧
      c2BytesPerQuery stagedC2Columns = 434 ∧
      queryBytes frozenC2Columns = 621 ∧
      queryBytes stagedC2Columns = 869 ∧
      stagedFixedQM31Values = 653 ∧
      fixedFieldBytes frozenFixedQM31Values = 9936 ∧
      fixedFieldBytes stagedFixedQM31Values = 10122 ∧
      bodyWithoutFrontiers frozenFixedQM31Values frozenC2Columns = 19948 ∧
      bodyWithoutFrontiers stagedFixedQM31Values stagedC2Columns = 24102 ∧
      bothFrontierBytes = 10556 ∧
      frozenMaximumBodyBytes = 30504 ∧
      stagedMaximumBodyBytes = 34658 ∧
      stagedMaximumBodyBytes - frozenMaximumBodyBytes = 4154 ∧
      uploadChunks frozenMaximumBodyBytes = 32 ∧
      uploadChunks stagedMaximumBodyBytes = 37 := by
  decide

theorem exact_stable_pair_wire_screen_keeps_frozen_body_size :
    stablePairMaximumBodyBytes = 30504 ∧
      stablePairMaximumBodyBytes = frozenMaximumBodyBytes ∧
      uploadChunks stablePairMaximumBodyBytes = 32 := by
  decide

theorem exact_staged_c2_leaf_sha_block_increase :
    sha256LeafBlocks (c2BytesPerQuery frozenC2Columns) = 4 ∧
      sha256LeafBlocks (c2BytesPerQuery stagedC2Columns) = 8 ∧
      queryCount *
          (sha256LeafBlocks (c2BytesPerQuery stagedC2Columns) -
            sha256LeafBlocks (c2BytesPerQuery frozenC2Columns)) = 64 := by
  decide

/-! ## Exact live-dependent suffix

Reading the live append state after `lambda, chi` does not make the completed
proof rebasable.  Every item below is downstream of the snapshot and must be
recomputed after a competing append.  In particular all three positioned work
searches remain downstream; moving them before the live statement would change
their security meaning.
-/

inductive LiveDependentSuffixStep where
  | liveSnapshotAbsorption
  | stageBRoot
  | zerocheckChallenges
  | semanticSumcheck
  | pointClaims
  | batchWork
  | gammaAndKappa
  | circleSamples
  | relationRoundZero
  | foldWork
  | final256
  | finalWork
  | querySchedule
  | authenticatedOpenings
  | remainingRelationRounds
  deriving DecidableEq

def liveDependentSuffix : List LiveDependentSuffixStep :=
  [.liveSnapshotAbsorption, .stageBRoot, .zerocheckChallenges,
    .semanticSumcheck, .pointClaims, .batchWork, .gammaAndKappa,
    .circleSamples, .relationRoundZero, .foldWork, .final256, .finalWork,
    .querySchedule, .authenticatedOpenings, .remainingRelationRounds]

theorem exact_live_dependent_suffix_has_fifteen_steps :
    liveDependentSuffix.length = 15 := by
  decide

theorem every_positioned_work_stage_is_live_dependent :
    LiveDependentSuffixStep.batchWork ∈ liveDependentSuffix ∧
      LiveDependentSuffixStep.foldWork ∈ liveDependentSuffix ∧
      LiveDependentSuffixStep.finalWork ∈ liveDependentSuffix := by
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
#print axioms completed_proof_accepts_at_most_one_live_state
#print axioms competing_append_invalidates_completed_proof
#print axioms recomplete_preserves_stageA_exactly
#print axioms recomplete_uses_fresh_append_source
#print axioms exact_staged_pool_prefix_positions
#print axioms frozen_tag73_prefix_has_no_late_snapshot
#print axioms staged_pool_prefix_is_not_the_frozen_tag73_prefix
#print axioms exact_stageB_lane_expansion
#print axioms exact_staged_wire_cost_if_four_late_lanes_authenticated
#print axioms exact_stable_pair_row_screen
#print axioms stable_pair_prefix_has_no_live_append_snapshot
#print axioms stable_pair_prefix_keeps_frozen_tag73_order
#print axioms stable_pair_proof_acceptance_has_no_live_state_dependency
#print axioms accepted_stable_pair_settlement_uses_execution_state
#print axioms exact_stable_pair_wire_screen_keeps_frozen_body_size
#print axioms exact_staged_c2_leaf_sha_block_increase
#print axioms exact_live_dependent_suffix_has_fifteen_steps
#print axioms every_positioned_work_stage_is_live_dependent
#print axioms exact_semantic_row_owner_cardinalities

end AspisPool.V7PoolRootRoleConcurrency
