import Mathlib

/-!
# v5 production cap-17 retry control flow

This module models only the bounded control flow of
`build_v5_production_host_artifact_cap17_indexed` in
`crates/aspis-prover/src/v5_real_host_proof.rs`, audited at source SHA-256
`1d29387da937f31c650f067042e0a906c1bb80ac0f2fb53149c27aa6d739449b`.

The deployed manager starts with failed-attempt index zero, invokes attempt
indices `0, ..., 16`, recurses only after `AllGoodCandidatesBad`, reports the
successful index as the public failed-attempt count, propagates every other
single-attempt error immediately, and returns `GoodRetryCapExhausted` before an
attempt at index 17.

The cryptographic body of one attempt is deliberately opaque here.  The final
lifting theorem takes equality of the Rust and Lean single-attempt outcomes on
indices below 17 as an explicit premise.  Thus this file proves the retry
manager's control flow; it does not manufacture Rust-to-Lean correspondence,
entropy, hash/random-oracle, PCS/Merkle, or Fiat--Shamir assumptions.
-/

namespace AspisV5ProductionCap17RetryControl

/-- Exact deployed public-Good retry cap. -/
def retryCap : Nat := 17

/-- The complete observable class of one production attempt for purposes of
the retry manager.  `fatal` abstracts every Rust error other than
`AllGoodCandidatesBad`. -/
inductive AttemptOutcome (Value FatalError : Type*) where
  | success (value : Value)
  | allGoodCandidatesBad
  | fatal (error : FatalError)
deriving DecidableEq

/-- The successful manager result.  `failedAttempts` is the exact public retry
count emitted by the Rust wrapper. -/
structure ManagerSuccess (Value : Type*) where
  failedAttempts : Nat
  value : Value
deriving DecidableEq

/-- Errors visible at the exact internal manager seam.  The public Rust wrapper
later maps either case to its opaque zero-sized abort type. -/
inductive ManagerError (FatalError : Type*) where
  | goodRetryCapExhausted
  | fatal (error : FatalError)
deriving DecidableEq

/-- Structurally recursive semantics of the indexed Rust helper.  `fuel` is the
number of remaining allowed attempts and `failedAttempts` is the next attempt
index as well as the count released on success. -/
def runAux {Value FatalError : Type*}
    (attempt : Nat → AttemptOutcome Value FatalError) :
    Nat → Nat → Except (ManagerError FatalError) (ManagerSuccess Value)
  | 0, _ => .error .goodRetryCapExhausted
  | fuel + 1, failedAttempts =>
      match attempt failedAttempts with
      | .success value => .ok { failedAttempts, value }
      | .allGoodCandidatesBad => runAux attempt fuel (failedAttempts + 1)
      | .fatal error => .error (.fatal error)

/-- Exact public entry point: 17 remaining attempts, starting at index zero. -/
def runCap17 {Value FatalError : Type*}
    (attempt : Nat → AttemptOutcome Value FatalError) :
    Except (ManagerError FatalError) (ManagerSuccess Value) :=
  runAux attempt retryCap 0

/-- The zero-fuel guard fires before consulting the single-attempt operation. -/
theorem runAux_zero {Value FatalError : Type*}
    (attempt : Nat → AttemptOutcome Value FatalError) (failedAttempts : Nat) :
    runAux attempt 0 failedAttempts = .error .goodRetryCapExhausted := by
  rfl

/-- A successful attempt returns immediately and reports its exact index. -/
theorem runAux_success {Value FatalError : Type*}
    (attempt : Nat → AttemptOutcome Value FatalError) (fuel failedAttempts : Nat)
    (value : Value) (h : attempt failedAttempts = .success value) :
    runAux attempt (fuel + 1) failedAttempts =
      .ok { failedAttempts, value } := by
  simp [runAux, h]

/-- `AllGoodCandidatesBad` is the unique outcome that advances the index and
consumes one unit of the cap. -/
theorem runAux_allGoodCandidatesBad {Value FatalError : Type*}
    (attempt : Nat → AttemptOutcome Value FatalError) (fuel failedAttempts : Nat)
    (h : attempt failedAttempts = .allGoodCandidatesBad) :
    runAux attempt (fuel + 1) failedAttempts =
      runAux attempt fuel (failedAttempts + 1) := by
  simp [runAux, h]

/-- Every non-gate error is propagated immediately, without a retry. -/
theorem runAux_fatal {Value FatalError : Type*}
    (attempt : Nat → AttemptOutcome Value FatalError) (fuel failedAttempts : Nat)
    (error : FatalError) (h : attempt failedAttempts = .fatal error) :
    runAux attempt (fuel + 1) failedAttempts = .error (.fatal error) := by
  simp [runAux, h]

/-- An arbitrary retry prefix followed by success reports the successful
attempt's exact index. -/
theorem runAux_success_after_retry_prefix {Value FatalError : Type*}
    (attempt : Nat → AttemptOutcome Value FatalError)
    (fuel start successOffset : Nat) (value : Value)
    (hwithin : successOffset < fuel)
    (hprefix : ∀ offset, offset < successOffset →
      attempt (start + offset) = .allGoodCandidatesBad)
    (hsuccess : attempt (start + successOffset) = .success value) :
    runAux attempt fuel start =
      .ok { failedAttempts := start + successOffset, value } := by
  induction fuel generalizing start successOffset with
  | zero => omega
  | succ fuel ih =>
      cases successOffset with
      | zero =>
          exact runAux_success attempt fuel start value (by simpa using hsuccess)
      | succ successOffset =>
          have hretry : attempt start = .allGoodCandidatesBad := by
            simpa using hprefix 0 (by omega)
          rw [runAux_allGoodCandidatesBad attempt fuel start hretry]
          have hprefix' : ∀ offset, offset < successOffset →
              attempt ((start + 1) + offset) = .allGoodCandidatesBad := by
            intro offset hoffset
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              hprefix (offset + 1) (by omega)
          have hsuccess' : attempt ((start + 1) + successOffset) = .success value := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsuccess
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            ih (start + 1) successOffset (by omega) hprefix' hsuccess'

/-- An arbitrary retry prefix followed by a fatal outcome propagates that exact
error and does not inspect any later attempt. -/
theorem runAux_fatal_after_retry_prefix {Value FatalError : Type*}
    (attempt : Nat → AttemptOutcome Value FatalError)
    (fuel start fatalOffset : Nat) (error : FatalError)
    (hwithin : fatalOffset < fuel)
    (hprefix : ∀ offset, offset < fatalOffset →
      attempt (start + offset) = .allGoodCandidatesBad)
    (hfatal : attempt (start + fatalOffset) = .fatal error) :
    runAux attempt fuel start = .error (.fatal error) := by
  induction fuel generalizing start fatalOffset with
  | zero => omega
  | succ fuel ih =>
      cases fatalOffset with
      | zero =>
          exact runAux_fatal attempt fuel start error (by simpa using hfatal)
      | succ fatalOffset =>
          have hretry : attempt start = .allGoodCandidatesBad := by
            simpa using hprefix 0 (by omega)
          rw [runAux_allGoodCandidatesBad attempt fuel start hretry]
          have hprefix' : ∀ offset, offset < fatalOffset →
              attempt ((start + 1) + offset) = .allGoodCandidatesBad := by
            intro offset hoffset
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              hprefix (offset + 1) (by omega)
          have hfatal' : attempt ((start + 1) + fatalOffset) = .fatal error := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfatal
          exact ih (start + 1) fatalOffset (by omega) hprefix' hfatal'

/-- If every allowed attempt is all-good-bad, the manager stops exactly at the
cap.  In particular, no success at the next index can affect the result. -/
theorem runAux_all_retry_exhausts {Value FatalError : Type*}
    (attempt : Nat → AttemptOutcome Value FatalError) (fuel start : Nat)
    (hall : ∀ offset, offset < fuel →
      attempt (start + offset) = .allGoodCandidatesBad) :
    runAux attempt fuel start = .error .goodRetryCapExhausted := by
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
      have hretry : attempt start = .allGoodCandidatesBad := by
        simpa using hall 0 (by omega)
      rw [runAux_allGoodCandidatesBad attempt fuel start hretry]
      apply ih
      intro offset hoffset
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hall (offset + 1) (by omega)

/-- The structurally recursive manager always reaches exactly one of success,
cap exhaustion, or immediate propagation of a fatal error. -/
theorem runCap17_terminates {Value FatalError : Type*}
    (attempt : Nat → AttemptOutcome Value FatalError) :
    (∃ output, runCap17 attempt = .ok output) ∨
      runCap17 attempt = .error .goodRetryCapExhausted ∨
      ∃ error, runCap17 attempt = .error (.fatal error) := by
  cases hrun : runCap17 attempt with
  | ok output => exact Or.inl ⟨output, rfl⟩
  | error error =>
      cases error with
      | goodRetryCapExhausted => exact Or.inr (Or.inl rfl)
      | fatal error => exact Or.inr (Or.inr ⟨error, rfl⟩)

/-- Agreement of two opaque single-attempt implementations throughout the
window that a manager invocation is permitted to inspect. -/
def AttemptsAgreeInWindow {Value FatalError : Type*}
    (left right : Nat → AttemptOutcome Value FatalError)
    (start fuel : Nat) : Prop :=
  ∀ index, start ≤ index → index < start + fuel → left index = right index

/-- The manager is extensional on its permitted attempt-index window. -/
theorem runAux_congr_of_attemptsAgreeInWindow {Value FatalError : Type*}
    (left right : Nat → AttemptOutcome Value FatalError)
    (fuel start : Nat) (hagrees : AttemptsAgreeInWindow left right start fuel) :
    runAux left fuel start = runAux right fuel start := by
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
      have hhead : left start = right start := hagrees start (by omega) (by omega)
      simp only [runAux]
      rw [hhead]
      cases hright : right start with
      | success value => rfl
      | fatal error => rfl
      | allGoodCandidatesBad =>
          apply ih
          intro index hlower hupper
          exact hagrees index (by omega) (by omega)

/-- The explicit Rust-to-Lean single-attempt seam.  Instantiating this predicate
requires source-authentic correspondence for the opaque production attempt;
this file does not assume or prove it. -/
def RustSingleAttemptCorrespondence {Value FatalError : Type*}
    (rustAttempt leanAttempt : Nat → AttemptOutcome Value FatalError) : Prop :=
  ∀ index, index < retryCap → rustAttempt index = leanAttempt index

/-- Exact cap-17 control-flow correspondence lifted from the explicit opaque
single-attempt premise.  The theorem also proves observationally that attempt
index 17 and every later index are irrelevant. -/
theorem runCap17_of_rustSingleAttemptCorrespondence {Value FatalError : Type*}
    (rustAttempt leanAttempt : Nat → AttemptOutcome Value FatalError)
    (hsingle : RustSingleAttemptCorrespondence rustAttempt leanAttempt) :
    runCap17 rustAttempt = runCap17 leanAttempt := by
  apply runAux_congr_of_attemptsAgreeInWindow
  intro index hlower hupper
  apply hsingle
  simpa [retryCap] using hupper

/-! ## Hostile regression teeth -/

/-- Sixteen failures followed by a success, so the last permitted (seventeenth)
attempt is load-bearing. -/
def successOnIndex16 : Nat → AttemptOutcome Nat Nat
  | 16 => .success 41
  | _ => .allGoodCandidatesBad

/-- A correct cap of 17 accepts success at index 16 and reports sixteen prior
failures. -/
theorem cap17_keeps_seventeenth_attempt :
    runCap17 successOnIndex16 = .ok { failedAttempts := 16, value := 41 } := by
  decide

/-- The off-by-one cap of 16 incorrectly rejects the same trace. -/
theorem cap16_is_a_concrete_off_by_one_failure :
    runAux successOnIndex16 16 0 = .error .goodRetryCapExhausted := by
  decide

/-- A success at index 17 is outside the deployed cap and is never observed. -/
def successOnIndex17 : Nat → AttemptOutcome Nat Nat
  | 17 => .success 41
  | _ => .allGoodCandidatesBad

/-- Exactly 17 retryable outcomes exhaust the cap before index 17. -/
theorem cap17_does_not_run_eighteenth_attempt :
    runCap17 successOnIndex17 = .error .goodRetryCapExhausted := by
  decide

/-- Fatal at index zero and success thereafter. -/
def fatalThenSuccess : Nat → AttemptOutcome Nat Nat
  | 0 => .fatal 73
  | _ => .success 41

/-- The correct manager propagates the fatal error at index zero. -/
theorem fatal_error_is_not_retried :
    runCap17 fatalThenSuccess = .error (.fatal 73) := by
  decide

/-- Deliberately wrong attempt adapter that turns fatal errors into retryable
all-good-bad outcomes. -/
def wronglyRetryFatal (attempt : Nat → AttemptOutcome Nat Nat) :
    Nat → AttemptOutcome Nat Nat := fun index =>
  match attempt index with
  | .fatal _ => .allGoodCandidatesBad
  | outcome => outcome

/-- Retrying a fatal error is observably wrong: it changes the fatal trace into
a success at index one. -/
theorem retrying_fatal_error_changes_result :
    runCap17 (wronglyRetryFatal fatalThenSuccess) =
      .ok { failedAttempts := 1, value := 41 } ∧
    runCap17 (wronglyRetryFatal fatalThenSuccess) ≠ runCap17 fatalThenSuccess := by
  decide

/-- One retryable failure followed by success. -/
def successOnIndex1 : Nat → AttemptOutcome Nat Nat
  | 0 => .allGoodCandidatesBad
  | _ => .success 41

/-- Success after one retry reports index/count one, never zero. -/
theorem successful_index_cannot_be_shifted :
    runCap17 successOnIndex1 = .ok { failedAttempts := 1, value := 41 } ∧
    runCap17 successOnIndex1 ≠ .ok { failedAttempts := 0, value := 41 } := by
  decide

#print axioms runAux_zero
#print axioms runAux_success
#print axioms runAux_allGoodCandidatesBad
#print axioms runAux_fatal
#print axioms runAux_success_after_retry_prefix
#print axioms runAux_fatal_after_retry_prefix
#print axioms runAux_all_retry_exhausts
#print axioms runCap17_terminates
#print axioms runAux_congr_of_attemptsAgreeInWindow
#print axioms runCap17_of_rustSingleAttemptCorrespondence
#print axioms cap17_keeps_seventeenth_attempt
#print axioms cap16_is_a_concrete_off_by_one_failure
#print axioms cap17_does_not_run_eighteenth_attempt
#print axioms fatal_error_is_not_retried
#print axioms retrying_fatal_error_changes_result
#print axioms successful_index_cannot_be_shifted

end AspisV5ProductionCap17RetryControl
