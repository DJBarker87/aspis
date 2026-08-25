import AspisFormal.K1.V7FsStateRestorationCoupling

/-!
# Honest plain-ROM compiler failure accounting for Tag 73

This file contains the six compiler-side failure categories isolated by the
current plain classical-ROM Fiat--Shamir audit.  Once a concrete coupling
instantiates the sets, its raw error is the sum of their actual probabilities
under one supplied master law.  There is no structure of symbolic allowances
and no theorem connecting the union to acceptance, extraction, or an
interactive trace; in particular this file does not prove that the six sets
cover every failed accepting execution.

K1.2--K1.5 failures remain in the separate `UpstreamFailureKind` accounting
from `V7FsAokCompiler`.  In particular, this vocabulary has no constructors
for challenge-dependent C2, any of the three work predicates, sampler
exhaustion, all-fail cap-203 search, simulation, or weak unique response.
The q16 constructor below concerns only failure of the adaptive query-DAG
forest coupling; it is not the event that all deployed q16 candidates fail.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73PlainRawError

open MeasureTheory
open AspisK1.V7FsStateRestorationCoupling

noncomputable section

/-! ## Typed six-event compiler vocabulary -/

/-- Current vocabulary for the *compiler-side* plain-ROM failure partition.
These are event labels, not numerical bounds or a proved exhaustive cover. -/
inductive PlainRomCompilerFailureKind where
  /-- The adversary predicts a transcript-driving random-oracle output without
  first making the corresponding query. -/
  | unqueriedTranscriptDrivingPrediction
  /-- A collision involving a full 256-bit oracle input, duplex state, or
  output.  This does not include the upstream 208-bit Merkle commitment. -/
  | full256InputStateOutputCollision
  /-- An answer is needed before it is legally available, or programming
  conflicts with an already-defined oracle point. -/
  | forwardReferenceOrProgrammingConflict
  /-- The adaptive q16 query-DAG forest cannot be coupled to the required
  legal replay forest.  This is not a q16 work/all-fail event. -/
  | adaptiveQ16QueryDagForestFailure
  /-- The public instance or fixed attempt/proof-account binding differs
  between the observed forgery and its replay. -/
  | fixedInstanceAttemptBindingFailure
  /-- A strict oracle-query, restart, runtime, fuel, or timeout limit is
  exceeded. -/
  | strictQueryRestartRuntimeTimeoutBudgetFailure
  deriving DecidableEq, Fintype, Repr

theorem plain_rom_compiler_failure_kind_count :
    Fintype.card PlainRomCompilerFailureKind = 6 := by
  decide

/-- The six actual bad-event sets in one finite master experiment.  The
structure contains no probability allowance and no upper-bound field. -/
structure PlainRomCompilerFailureEvents (Sample : Type*) where
  unqueriedTranscriptDrivingPrediction : Set Sample
  full256InputStateOutputCollision : Set Sample
  forwardReferenceOrProgrammingConflict : Set Sample
  adaptiveQ16QueryDagForestFailure : Set Sample
  fixedInstanceAttemptBindingFailure : Set Sample
  strictQueryRestartRuntimeTimeoutBudgetFailure : Set Sample

def PlainRomCompilerFailureEvents.event
    {Sample : Type*} (events : PlainRomCompilerFailureEvents Sample) :
    PlainRomCompilerFailureKind → Set Sample
  | .unqueriedTranscriptDrivingPrediction =>
      events.unqueriedTranscriptDrivingPrediction
  | .full256InputStateOutputCollision =>
      events.full256InputStateOutputCollision
  | .forwardReferenceOrProgrammingConflict =>
      events.forwardReferenceOrProgrammingConflict
  | .adaptiveQ16QueryDagForestFailure =>
      events.adaptiveQ16QueryDagForestFailure
  | .fixedInstanceAttemptBindingFailure =>
      events.fixedInstanceAttemptBindingFailure
  | .strictQueryRestartRuntimeTimeoutBudgetFailure =>
      events.strictQueryRestartRuntimeTimeoutBudgetFailure

/-- Literal union of the six compiler-side bad events.  The grouping into two
triples is only to make the union-bound proof transparent. -/
def plainRomCompilerFailureUnion
    {Sample : Type*} (events : PlainRomCompilerFailureEvents Sample) :
    Set Sample :=
  (events.unqueriedTranscriptDrivingPrediction ∪
    events.full256InputStateOutputCollision ∪
    events.forwardReferenceOrProgrammingConflict) ∪
  (events.adaptiveQ16QueryDagForestFailure ∪
    events.fixedInstanceAttemptBindingFailure ∪
    events.strictQueryRestartRuntimeTimeoutBudgetFailure)

theorem plain_rom_compiler_failure_union_six_event_expansion
    {Sample : Type*} (events : PlainRomCompilerFailureEvents Sample) :
    plainRomCompilerFailureUnion events =
      (events.unqueriedTranscriptDrivingPrediction ∪
        events.full256InputStateOutputCollision ∪
        events.forwardReferenceOrProgrammingConflict) ∪
      (events.adaptiveQ16QueryDagForestFailure ∪
        events.fixedInstanceAttemptBindingFailure ∪
        events.strictQueryRestartRuntimeTimeoutBudgetFailure) := by
  rfl

/-! ## Actual raw probabilities -/

/-- Probability of one named bad event under the supplied master law. -/
def plainRomCompilerEventProbability
    {Sample : Type*} (law : PMF Sample)
    (events : PlainRomCompilerFailureEvents Sample)
    (kind : PlainRomCompilerFailureKind) : ENNReal :=
  law.toOuterMeasure (events.event kind)

/-- Honest raw compiler error: the sum of the six *measured event
probabilities*.  No symbolic allowance or BCS constant occurs here. -/
def plainRomCompilerRawError
    {Sample : Type*} (law : PMF Sample)
    (events : PlainRomCompilerFailureEvents Sample) : ENNReal :=
  ∑ kind : PlainRomCompilerFailureKind,
    plainRomCompilerEventProbability law events kind

theorem plain_rom_compiler_raw_error_six_term_expansion
    {Sample : Type*} (law : PMF Sample)
    (events : PlainRomCompilerFailureEvents Sample) :
    plainRomCompilerRawError law events =
      law.toOuterMeasure events.unqueriedTranscriptDrivingPrediction +
      law.toOuterMeasure events.full256InputStateOutputCollision +
      law.toOuterMeasure events.forwardReferenceOrProgrammingConflict +
      law.toOuterMeasure events.adaptiveQ16QueryDagForestFailure +
      law.toOuterMeasure events.fixedInstanceAttemptBindingFailure +
      law.toOuterMeasure
        events.strictQueryRestartRuntimeTimeoutBudgetFailure := by
  unfold plainRomCompilerRawError
  rw [show (Finset.univ : Finset PlainRomCompilerFailureKind) =
    {.unqueriedTranscriptDrivingPrediction,
      .full256InputStateOutputCollision,
      .forwardReferenceOrProgrammingConflict,
      .adaptiveQ16QueryDagForestFailure,
      .fixedInstanceAttemptBindingFailure,
      .strictQueryRestartRuntimeTimeoutBudgetFailure} by decide]
  simp [plainRomCompilerEventProbability,
    PlainRomCompilerFailureEvents.event]
  ac_rfl

/-- The probability of the six-event union is bounded by the honest raw
sum.  No disjointness or independence hypothesis is used. -/
theorem plain_rom_compiler_failure_union_probability_le_raw_error
    {Sample : Type*} (law : PMF Sample)
    (events : PlainRomCompilerFailureEvents Sample) :
    law.toOuterMeasure (plainRomCompilerFailureUnion events) ≤
      plainRomCompilerRawError law events := by
  calc
    law.toOuterMeasure (plainRomCompilerFailureUnion events) ≤
        law.toOuterMeasure
          (events.unqueriedTranscriptDrivingPrediction ∪
            events.full256InputStateOutputCollision ∪
            events.forwardReferenceOrProgrammingConflict) +
        law.toOuterMeasure
          (events.adaptiveQ16QueryDagForestFailure ∪
            events.fixedInstanceAttemptBindingFailure ∪
            events.strictQueryRestartRuntimeTimeoutBudgetFailure) := by
      exact measure_union_le _ _
    _ ≤
        (law.toOuterMeasure events.unqueriedTranscriptDrivingPrediction +
          law.toOuterMeasure events.full256InputStateOutputCollision +
          law.toOuterMeasure events.forwardReferenceOrProgrammingConflict) +
        (law.toOuterMeasure events.adaptiveQ16QueryDagForestFailure +
          law.toOuterMeasure events.fixedInstanceAttemptBindingFailure +
          law.toOuterMeasure
            events.strictQueryRestartRuntimeTimeoutBudgetFailure) := by
      exact add_le_add
        (three_event_union_probability_le law
          events.unqueriedTranscriptDrivingPrediction
          events.full256InputStateOutputCollision
          events.forwardReferenceOrProgrammingConflict)
        (three_event_union_probability_le law
          events.adaptiveQ16QueryDagForestFailure
          events.fixedInstanceAttemptBindingFailure
          events.strictQueryRestartRuntimeTimeoutBudgetFailure)
    _ = plainRomCompilerRawError law events := by
      rw [plain_rom_compiler_raw_error_six_term_expansion]
      ac_rfl

#print axioms plain_rom_compiler_failure_kind_count
#print axioms plain_rom_compiler_failure_union_six_event_expansion
#print axioms plain_rom_compiler_raw_error_six_term_expansion
#print axioms plain_rom_compiler_failure_union_probability_le_raw_error

end

end AspisK1.V7Tag73PlainRawError
