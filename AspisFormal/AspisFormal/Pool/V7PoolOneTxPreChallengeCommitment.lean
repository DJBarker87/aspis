import AspisFormal.Pool.V7PoolRootRoleConcurrency

/-!
# Sound pre-challenge commitment schedule for the one-transaction Pool path

The earlier staged screen placed the live append trace beside the auxiliary
columns committed after `lambda, chi`.  That ordering is not an acceptable
knowledge-soundness interface: the main-trace values participating in the
randomized copy argument must already be fixed when its compression
challenges are sampled.

The conservative production route instead overlays the stable and live
regions in the same sixteen semantic C1 columns.  Their row supports are
disjoint.  The exact old-snapshot/candidate-afterstate record is public and is
absorbed before the full C1 root; the full C1 root precedes `lambda, chi`.
This retains the frozen 26+3 PCS geometry and 30,504-byte maximum proof, at the
cost that a competing append invalidates the whole completed proof rather
than only a reusable suffix.
-/

set_option autoImplicit false

namespace AspisPool.V7PoolOneTxPreChallengeCommitment

open AspisPool.V7PairTreeTraceGeometry
open AspisPool.V7PoolRootRoleConcurrency

inductive OneTxTranscriptStep where
  | baseStatement
  | liveTransitionRecord
  | fullTraceRoot
  | lambda
  | chi
  | helperRoot
  | batchingChallenges
  deriving DecidableEq

def oneTxPrefix : List OneTxTranscriptStep :=
  [.baseStatement, .liveTransitionRecord, .fullTraceRoot, .lambda, .chi,
    .helperRoot, .batchingChallenges]

def postChallengeStagedPrefix : List OneTxTranscriptStep :=
  [.baseStatement, .fullTraceRoot, .lambda, .chi, .liveTransitionRecord,
    .helperRoot, .batchingChallenges]

def MainTraceFixedBeforeCopyChallenges
    (schedule : List OneTxTranscriptStep) : Prop :=
  schedule.take 5 =
    [.baseStatement, .liveTransitionRecord, .fullTraceRoot, .lambda, .chi]

theorem one_tx_prefix_fixes_complete_trace_before_copy_challenges :
    MainTraceFixedBeforeCopyChallenges oneTxPrefix := by
  rfl

theorem post_challenge_staged_prefix_fails_main_trace_order :
    ¬ MainTraceFixedBeforeCopyChallenges postChallengeStagedPrefix := by
  simp [MainTraceFixedBeforeCopyChallenges, postChallengeStagedPrefix]

/-! The stable and late regions occupy the same sixteen physical semantic
columns but disjoint rows.  Their union uses rows `0..976`; rows `976..1024`
remain unused. -/

def stableRowCount : Nat := 544 + (976 - 864)
def lateRowCount : Nat := 864 - 544
def unifiedAllocatedRows : Nat := stableRowCount + lateRowCount
def unifiedUnusedRows : Nat := traceRows - unifiedAllocatedRows

theorem exact_unified_row_partition :
    stableRowCount = 656 ∧ lateRowCount = 320 ∧
      unifiedAllocatedRows = 976 ∧ unifiedUnusedRows = 48 := by
  decide

theorem stable_and_late_intervals_are_disjoint
    (row : Nat)
    (stable : row < 544 ∨ (864 ≤ row ∧ row < 976))
    (late : 544 ≤ row ∧ row < 864) : False := by
  omega

def semanticColumns : Nat := 16
def selectedMaskOnlyColumns : Nat := 10
def helperColumns : Nat := 3
def c1Columns : Nat := semanticColumns + selectedMaskOnlyColumns
def c2Columns : Nat := helperColumns
def logicalGammaColumns : Nat := c1Columns + c2Columns

theorem exact_unified_frozen_column_geometry :
    c1Columns = 26 ∧ c2Columns = 3 ∧ logicalGammaColumns = 29 := by
  decide

/-! Exact canonical public record:

* 32-byte `ASPLATE1` header;
* 800-byte canonical locked live snapshot;
* 688-byte canonical candidate `ASJA` envelope and afterstate.
-/

def lateRecordHeaderBytes : Nat := 32
def oldLiveSnapshotBytes : Nat := 800
def candidateAfterstateEnvelopeBytes : Nat := 688
def lateTransitionRecordBytes : Nat :=
  lateRecordHeaderBytes + oldLiveSnapshotBytes + candidateAfterstateEnvelopeBytes

theorem exact_late_transition_record_wire :
    lateTransitionRecordBytes = 1520 := by
  decide

/-! The unified route changes the public transcript/profile, not the PCS wire
geometry.  These are the frozen Tag-73 body components. -/

def packedM31Bytes (limbs : Nat) : Nat := (limbs * 31 + 7) / 8
def fixedQM31Values : Nat := 641
def fixedFieldBytes : Nat := packedM31Bytes (4 * fixedQM31Values)
def c1BytesPerQuery : Nat := packedM31Bytes (4 * 26)
def c2BytesPerQuery : Nat := packedM31Bytes (4 * 4 * 3)
def queryBytes : Nat := c1BytesPerQuery + c2BytesPerQuery + 32
def bodyWithoutFrontiers : Nat :=
  fixedFieldBytes + 2 * 26 + 24 + 16 * queryBytes
def maximumBodyBytes : Nat := bodyWithoutFrontiers + 2 * 203 * 26
def candidateAfterstateMetadataBytes : Nat := 688
def maximumFinalizedProfileBodyBytes : Nat :=
  candidateAfterstateMetadataBytes + maximumBodyBytes

theorem exact_unified_route_keeps_frozen_wire :
    fixedFieldBytes = 9936 ∧ c1BytesPerQuery = 403 ∧
      c2BytesPerQuery = 186 ∧ queryBytes = 621 ∧
      bodyWithoutFrontiers = 19948 ∧ maximumBodyBytes = 30504 := by
  decide

theorem exact_profile_account_body_includes_public_candidate :
    maximumFinalizedProfileBodyBytes = 31192 := by
  decide

/-! Pair indices count pair leaves.  Each private transfer pair leaf contains
two occupied commitment slots, while one accepted append increments the pair
cursor and chronological root sequence exactly once. -/

def commitmentSlotsPerPrivateTransfer : Nat := 2
def pairLeavesPerPrivateTransfer : Nat := 1

theorem one_pair_append_adds_two_occupied_commitment_slots :
    pairLeavesPerPrivateTransfer = 1 ∧
      commitmentSlotsPerPrivateTransfer = 2 := by
  decide

#print axioms one_tx_prefix_fixes_complete_trace_before_copy_challenges
#print axioms post_challenge_staged_prefix_fails_main_trace_order
#print axioms exact_unified_row_partition
#print axioms stable_and_late_intervals_are_disjoint
#print axioms exact_unified_frozen_column_geometry
#print axioms exact_late_transition_record_wire
#print axioms exact_unified_route_keeps_frozen_wire
#print axioms exact_profile_account_body_includes_public_candidate
#print axioms one_pair_append_adds_two_occupied_commitment_slots

end AspisPool.V7PoolOneTxPreChallengeCommitment
