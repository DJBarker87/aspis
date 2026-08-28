import AspisFormal.K1.V7Tag73SchedulerNativeQ16Replay

/-!
# Scheduler-native replay of an ordered Tag-73 q16 candidate forest

The first q16 leaf proves the cache/fresh semantics for one candidate branch.
This module composes those branches without assuming that every verifier use
was the first oracle exposure of its input.  A cached coordinate is checked
against the routed forest and consumes no master-tape answer; a missing
coordinate is changed only at a real scheduler-native fresh pause.

The ordered branch list is deliberately explicit.  Its source-alignment
theorem must later prove that it is exactly counters zero through the first
cap-203 counter and that each `blocksUsed` is the production decoder's first
accepted prefix.  Keeping that obligation outside the replay engine prevents
the engine from silently assuming the very first-success fact needed by
K1.3.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73SchedulerNativeQ16ForestReplay

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73SchedulerNativeTargetPause
open AspisK1.V7Tag73SchedulerNativeQ16Replay

noncomputable section

universe u

/-- Start a later candidate from an arbitrary retained scheduler cursor.
Unlike the first-target entry point, the first output coordinate may already
be cached.  The ordinary coordinate consumer handles both cases. -/
def runSchedulerNativeQ16BranchFromCursor
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (branch : SchedulerNativeQ16Branch)
    (forest : TotalQ16DuplexForest)
    (state : SchedulerNativeQ16Cursor globalOracleCalls Result) :
    Except SchedulerNativeQ16ReplayFailure
      (SchedulerNativeQ16Cursor globalOracleCalls Result) :=
  match q16BranchDuplexPairs branch forest with
  | [] => .error .emptyBranch
  | (output, advanced) :: rest =>
      match consumeSchedulerNativeQ16Coordinate transitionFuel .output
          (q16OutputInput branch.initialDigest) output state with
      | .error failure => .error failure
      | .ok afterOutput =>
          match consumeSchedulerNativeQ16Coordinate transitionFuel .advance
              (q16AdvanceInput branch.initialDigest) advanced afterOutput with
          | .error failure => .error failure
          | .ok afterAdvance =>
              runSchedulerNativeQ16BranchTail transitionFuel rest advanced
                afterAdvance

/-- Replay the remaining candidate branches in their literal source order. -/
def runSchedulerNativeQ16BranchList
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (forest : TotalQ16DuplexForest) :
    List SchedulerNativeQ16Branch ->
      SchedulerNativeQ16Cursor globalOracleCalls Result ->
      Except SchedulerNativeQ16ReplayFailure
        (SchedulerNativeQ16Cursor globalOracleCalls Result)
  | [], state => .ok state
  | branch :: rest, state =>
      match runSchedulerNativeQ16BranchFromCursor transitionFuel branch forest
          state with
      | .error failure => .error failure
      | .ok afterBranch =>
          runSchedulerNativeQ16BranchList transitionFuel forest rest afterBranch

/-- Enter the forest at one proved first exposure.  The first routed output
replaces the answer retained by the pause; all later coordinates use the
cache-aware branch engine. -/
def runSchedulerNativeQ16ForestFromFirstPause
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (firstBranch : SchedulerNativeQ16Branch)
    (firstPause : SchedulerNativeFreshPause globalOracleCalls Result
      (q16OutputInput firstBranch.initialDigest))
    (rest : List SchedulerNativeQ16Branch)
    (forest : TotalQ16DuplexForest) :
    Except SchedulerNativeQ16ReplayFailure
      (SchedulerNativeQ16Cursor globalOracleCalls Result) :=
  match runSchedulerNativeQ16BranchFromFirstPause transitionFuel firstBranch
      firstPause forest with
  | .error failure => .error failure
  | .ok afterFirst =>
      runSchedulerNativeQ16BranchList transitionFuel forest rest afterFirst

/-- Observable completed run after replaying the selected q16 prefix. -/
structure SchedulerNativeQ16ForestResponse (Result : Type u) where
  run : SchedulerNativeRun Result
  remainingAnswers : List Digest256

/-- Finish the ordinary scheduler on the untouched master-tape suffix.  Any
trailing cached q16 calls are normalized here by the production scheduler. -/
def finishSchedulerNativeQ16Forest
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat)
    (state : SchedulerNativeQ16Cursor globalOracleCalls Result) :
    SchedulerNativeQ16ForestResponse Result :=
  let tail := runSchedulerNativeListRun transitionFuel state.cursor
    state.remainingAnswers
  { run :=
      { terminal := tail.terminal
        trace := state.tracePrefix ++ tail.trace }
    remainingAnswers := state.remainingAnswers }

/-- Total occurrence driver: replay the ordered prefix and then finish the
literal scheduler. -/
def replaySchedulerNativeQ16ForestOccurrence
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (firstBranch : SchedulerNativeQ16Branch)
    (firstPause : SchedulerNativeFreshPause globalOracleCalls Result
      (q16OutputInput firstBranch.initialDigest))
    (rest : List SchedulerNativeQ16Branch)
    (forest : TotalQ16DuplexForest) :
    Except SchedulerNativeQ16ReplayFailure
      (SchedulerNativeQ16ForestResponse Result) :=
  match runSchedulerNativeQ16ForestFromFirstPause transitionFuel firstBranch
      firstPause rest forest with
  | .error failure => .error failure
  | .ok state => .ok (finishSchedulerNativeQ16Forest transitionFuel state)

@[simp] theorem run_scheduler_native_q16_branch_list_nil
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (forest : TotalQ16DuplexForest)
    (state : SchedulerNativeQ16Cursor globalOracleCalls Result) :
    runSchedulerNativeQ16BranchList transitionFuel forest [] state =
      .ok state := by
  rfl

@[simp] theorem run_scheduler_native_q16_branch_list_cons
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (forest : TotalQ16DuplexForest)
    (branch : SchedulerNativeQ16Branch)
    (rest : List SchedulerNativeQ16Branch)
    (state : SchedulerNativeQ16Cursor globalOracleCalls Result) :
    runSchedulerNativeQ16BranchList transitionFuel forest (branch :: rest)
        state =
      match runSchedulerNativeQ16BranchFromCursor transitionFuel branch forest
          state with
      | .error failure => .error failure
      | .ok afterBranch =>
          runSchedulerNativeQ16BranchList transitionFuel forest rest
            afterBranch := by
  rfl

/-- A positive later branch cannot reach the defensive empty-list arm. -/
theorem run_scheduler_native_q16_branch_from_cursor_ne_empty_failure
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (branch : SchedulerNativeQ16Branch)
    (forest : TotalQ16DuplexForest)
    (state : SchedulerNativeQ16Cursor globalOracleCalls Result) :
    runSchedulerNativeQ16BranchFromCursor transitionFuel branch forest state ≠
      .error .emptyBranch := by
  unfold runSchedulerNativeQ16BranchFromCursor
  generalize pairsExact : q16BranchDuplexPairs branch forest = pairs
  cases pairs with
  | nil =>
      exact False.elim
        (q16_branch_duplex_pairs_nonempty branch forest pairsExact)
  | cons pair rest =>
      simp only
      cases outputResult : consumeSchedulerNativeQ16Coordinate transitionFuel
          .output (q16OutputInput branch.initialDigest) pair.1 state with
      | error failure =>
          simp only
          cases failure with
          | expectedQueryAbsent => simp
          | cachedAnswerMismatch => simp
          | emptyBranch =>
              exact False.elim
                (consume_scheduler_native_q16_ne_empty_failure transitionFuel
                  .output (q16OutputInput branch.initialDigest) pair.1 state
                  outputResult)
      | ok afterOutput =>
          simp only
          cases advanceResult : consumeSchedulerNativeQ16Coordinate
              transitionFuel .advance
              (q16AdvanceInput branch.initialDigest) pair.2 afterOutput with
          | error failure =>
              simp only
              cases failure with
              | expectedQueryAbsent => simp
              | cachedAnswerMismatch => simp
              | emptyBranch =>
                  exact False.elim
                    (consume_scheduler_native_q16_ne_empty_failure
                      transitionFuel .advance
                      (q16AdvanceInput branch.initialDigest) pair.2 afterOutput
                      advanceResult)
          | ok afterAdvance =>
              simp only
              exact run_scheduler_native_q16_branch_tail_ne_empty_failure
                transitionFuel rest pair.2 afterAdvance

/-- The complete ordered replay does not inspect the retained source answer
at its first target.  The routed forest supplies that answer instead. -/
@[simp] theorem replay_scheduler_native_q16_forest_independent_of_target_answer
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (firstBranch : SchedulerNativeQ16Branch)
    (firstPause : SchedulerNativeFreshPause globalOracleCalls Result
      (q16OutputInput firstBranch.initialDigest))
    (replacement : Digest256) (rest : List SchedulerNativeQ16Branch)
    (forest : TotalQ16DuplexForest) :
    replaySchedulerNativeQ16ForestOccurrence transitionFuel firstBranch
        { firstPause with targetAnswer := replacement } rest forest =
      replaySchedulerNativeQ16ForestOccurrence transitionFuel firstBranch
        firstPause rest forest := by
  rfl

@[simp] theorem finish_scheduler_native_q16_forest_run
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat)
    (state : SchedulerNativeQ16Cursor globalOracleCalls Result) :
    (finishSchedulerNativeQ16Forest transitionFuel state).run =
      let tail := runSchedulerNativeListRun transitionFuel state.cursor
        state.remainingAnswers
      { terminal := tail.terminal
        trace := state.tracePrefix ++ tail.trace } := by
  rfl

#print axioms run_scheduler_native_q16_branch_from_cursor_ne_empty_failure
#print axioms
  replay_scheduler_native_q16_forest_independent_of_target_answer
#print axioms finish_scheduler_native_q16_forest_run

end

end AspisK1.V7Tag73SchedulerNativeQ16ForestReplay
