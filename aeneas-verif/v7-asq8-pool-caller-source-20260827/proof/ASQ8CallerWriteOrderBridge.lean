import Aeneas

/-!
Operational control-flow bridge for the part of
`process_pair_forest_terminal_with_verifier_v1` that Charon records but Aeneas
cannot currently translate (generic HRTB callbacks plus Solana interior
borrows).  This model deliberately contains no cryptographic assumptions: its
inputs are the concrete identities/images checked or produced by the source.
-/

set_option autoImplicit false

namespace AspisPool.ASQ8CallerWriteOrderBridge

inductive TransitionKind where
  | transfer
  | withdrawal
  deriving DecidableEq, Repr

/-- Concrete values retained by the Pool before verifier invocation. -/
structure LockedSource where
  master : Nat
  checkpoint : Nat
  selectedLane : Nat
  deterministicOutputLane : Nat
  retainedCheckpointSequence : Nat
  retainedHistoricalRoot : Nat
  currentLaneSequence : Nat
  currentLaneRoot : Nat
  currentLaneFrontier : Nat
  deriving DecidableEq, Repr

/-- ASR8 identity/snapshot values consumed immediately after the CPI. -/
structure ReturnedASR8 where
  master : Nat
  checkpoint : Nat
  selectedLane : Nat
  outputLane : Nat
  checkpointSequence : Nat
  historicalRoot : Nat
  sourceLaneSequence : Nat
  sourceLaneRoot : Nat
  sourceLaneFrontier : Nat
  nextLaneSequence : Nat
  nextLaneRoot : Nat
  nextLaneFrontier : Nat
  deriving DecidableEq, Repr

/-- The exact equality inventory enforced by statement reconstruction and
`validate_pool_v1_pair_forest_terminal_result_against_statement_v1`. -/
def exactBindings (source : LockedSource) (result : ReturnedASR8) : Bool :=
  result.master == source.master &&
  result.checkpoint == source.checkpoint &&
  result.selectedLane == source.selectedLane &&
  result.outputLane == source.deterministicOutputLane &&
  result.checkpointSequence == source.retainedCheckpointSequence &&
  result.historicalRoot == source.retainedHistoricalRoot &&
  result.sourceLaneSequence == source.currentLaneSequence &&
  result.sourceLaneRoot == source.currentLaneRoot &&
  result.sourceLaneFrontier == source.currentLaneFrontier

structure MarkerScope where
  master : Nat
  nullifier : Nat
  retainedCheckpointSequence : Nat
  retainedHistoricalRoot : Nat
  deriving DecidableEq, Repr

/-- Only these three Pool-owned byte images are mutable in the terminal caller. -/
structure PoolOwnedImages where
  lane : Nat
  historyPage : List Nat
  marker : Option MarkerScope
  unrelated : Nat
  deriving DecidableEq, Repr

structure PreparedWrites where
  nextLaneImage : Nat
  nextHistoryPage : List Nat
  marker : MarkerScope
  deriving DecidableEq, Repr

/-- Low-level success/failure outcomes in exact source order after registry and
dispatch authentication.  These are runtime/codec operations, not assumptions
that settlement is valid. -/
structure LateOutcomes where
  verifierReturned : Bool
  statementReconstructed : Bool
  resultValidated : Bool
  nextLaneConstructed : Bool
  laneEncoded : Bool
  resultEncoded : Bool
  laneBorrowed : Bool
  pageBorrowed : Bool
  markerBorrowed : Bool
  withdrawalInfosExact : Bool
  withdrawalCpiSucceeded : Bool
  withdrawalDeltaExact : Bool
  deriving DecidableEq, Repr

inductive LateError where
  | verifier
  | statement
  | validation
  | nextLane
  | laneEncoding
  | resultEncoding
  | laneBorrow
  | pageBorrow
  | markerBorrow
  | withdrawalInfos
  | withdrawalCpi
  | withdrawalDelta
  deriving DecidableEq, Repr

inductive CallerResult where
  | error (stage : LateError) (pool : PoolOwnedImages)
  | accepted (pool : PoolOwnedImages)
  deriving DecidableEq, Repr

def persist (before : PoolOwnedImages) (writes : PreparedWrites) : PoolOwnedImages :=
  { before with
    lane := writes.nextLaneImage
    historyPage := writes.nextHistoryPage
    marker := some writes.marker }

/-- Literal post-verifier sequencing from the Rust caller.  Token CPI and its
delta check precede `persist`; transfer bypasses those three withdrawal gates. -/
def runLate (kind : TransitionKind) (before : PoolOwnedImages)
    (writes : PreparedWrites) (outcome : LateOutcomes) : CallerResult :=
  if !outcome.verifierReturned then .error .verifier before else
  if !outcome.statementReconstructed then .error .statement before else
  if !outcome.resultValidated then .error .validation before else
  if !outcome.nextLaneConstructed then .error .nextLane before else
  if !outcome.laneEncoded then .error .laneEncoding before else
  if !outcome.resultEncoded then .error .resultEncoding before else
  if !outcome.laneBorrowed then .error .laneBorrow before else
  if !outcome.pageBorrowed then .error .pageBorrow before else
  if !outcome.markerBorrowed then .error .markerBorrow before else
  match kind with
  | .transfer => .accepted (persist before writes)
  | .withdrawal =>
      if !outcome.withdrawalInfosExact then .error .withdrawalInfos before else
      if !outcome.withdrawalCpiSucceeded then .error .withdrawalCpi before else
      if !outcome.withdrawalDeltaExact then .error .withdrawalDelta before else
      .accepted (persist before writes)

def allSuccessful : LateOutcomes where
  verifierReturned := true
  statementReconstructed := true
  resultValidated := true
  nextLaneConstructed := true
  laneEncoded := true
  resultEncoded := true
  laneBorrowed := true
  pageBorrowed := true
  markerBorrowed := true
  withdrawalInfosExact := true
  withdrawalCpiSucceeded := true
  withdrawalDeltaExact := true

def failAt (stage : LateError) : LateOutcomes :=
  match stage with
  | .verifier => { allSuccessful with verifierReturned := false }
  | .statement => { allSuccessful with statementReconstructed := false }
  | .validation => { allSuccessful with resultValidated := false }
  | .nextLane => { allSuccessful with nextLaneConstructed := false }
  | .laneEncoding => { allSuccessful with laneEncoded := false }
  | .resultEncoding => { allSuccessful with resultEncoded := false }
  | .laneBorrow => { allSuccessful with laneBorrowed := false }
  | .pageBorrow => { allSuccessful with pageBorrowed := false }
  | .markerBorrow => { allSuccessful with markerBorrowed := false }
  | .withdrawalInfos => { allSuccessful with withdrawalInfosExact := false }
  | .withdrawalCpi => { allSuccessful with withdrawalCpiSucceeded := false }
  | .withdrawalDelta => { allSuccessful with withdrawalDeltaExact := false }

def relevantError (kind : TransitionKind) (stage : LateError) : Prop :=
  kind = .withdrawal ∨
    stage ∉ [.withdrawalInfos, .withdrawalCpi, .withdrawalDelta]

/-- Every modeled late failure preserves all Pool-owned bytes.  For transfer,
withdrawal-only runtime outcomes are unreachable and therefore excluded. -/
theorem every_relevant_late_error_has_no_pool_owned_writes
    (kind : TransitionKind) (stage : LateError) (before : PoolOwnedImages)
    (writes : PreparedWrites) (relevant : relevantError kind stage) :
    runLate kind before writes (failAt stage) = .error stage before := by
  cases kind <;> cases stage <;>
    simp_all [runLate, failAt, allSuccessful, relevantError]

/-- Successful transfer writes exactly lane, history and the already
master-scoped marker image. -/
theorem accepted_transfer_writes_exact_three_pool_images
    (before : PoolOwnedImages) (writes : PreparedWrites) :
    runLate .transfer before writes allSuccessful =
      .accepted {
        lane := writes.nextLaneImage
        historyPage := writes.nextHistoryPage
        marker := some writes.marker
        unrelated := before.unrelated
      } := by
  rfl

/-- Successful withdrawal reaches the same three writes only after exact token
account selection, successful CPI, and exact post-CPI balance deltas. -/
theorem accepted_withdrawal_writes_only_after_exact_token_deltas
    (before : PoolOwnedImages) (writes : PreparedWrites) :
    runLate .withdrawal before writes allSuccessful =
      .accepted {
        lane := writes.nextLaneImage
        historyPage := writes.nextHistoryPage
        marker := some writes.marker
        unrelated := before.unrelated
      } := by
  rfl

/-- The marker written by the accepted flow is explicitly scoped to the same
master and retained anchor used by the locked statement. -/
def markerMatchesLockedSource (source : LockedSource)
    (nullifier : Nat) (marker : MarkerScope) : Prop :=
  marker = {
    master := source.master
    nullifier := nullifier
    retainedCheckpointSequence := source.retainedCheckpointSequence
    retainedHistoricalRoot := source.retainedHistoricalRoot
  }

theorem exact_bindings_pin_retained_and_current_snapshots
    (source : LockedSource) (result : ReturnedASR8)
    (accepted : exactBindings source result = true) :
    result.checkpointSequence = source.retainedCheckpointSequence ∧
    result.historicalRoot = source.retainedHistoricalRoot ∧
    result.sourceLaneSequence = source.currentLaneSequence ∧
    result.sourceLaneRoot = source.currentLaneRoot ∧
    result.sourceLaneFrontier = source.currentLaneFrontier ∧
    result.outputLane = source.deterministicOutputLane := by
  simp [exactBindings] at accepted
  aesop

#print axioms every_relevant_late_error_has_no_pool_owned_writes
#print axioms accepted_transfer_writes_exact_three_pool_images
#print axioms accepted_withdrawal_writes_only_after_exact_token_deltas
#print axioms exact_bindings_pin_retained_and_current_snapshots

end AspisPool.ASQ8CallerWriteOrderBridge
