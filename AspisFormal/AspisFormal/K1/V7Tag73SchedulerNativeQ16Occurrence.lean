import AspisFormal.K1.V7Tag73SchedulerNativeCounterfactualPause
import AspisFormal.K1.V7Tag73SchedulerNativeQ16ForestReplay

/-!
# A cache-aware q16 forest is an actual scheduler occurrence

The q16 replay engine changes an answer only at a literal scheduler-native
fresh pause and leaves cache hits untouched.  This module proves composition:
every successful routed forest, including adversary-first cache hits, is the
ordinary production scheduler on one explicitly modified master tape.

There is no acceptance, extraction, probability, or source-decoder premise in
this leaf.  The final theorem starts from the actual source scanner equality.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73SchedulerNativeQ16Occurrence

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73SchedulerNativeTargetPause
open AspisK1.V7Tag73SchedulerNativeCounterfactualPause
open AspisK1.V7Tag73SchedulerNativeQ16Replay
open AspisK1.V7Tag73SchedulerNativeQ16ForestReplay

noncomputable section

universe u

/-- Finish a routed prefix from an arbitrary replacement suffix. -/
def q16ContinuationRun
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat)
    (state : SchedulerNativeQ16Cursor globalOracleCalls Result)
    (answers : List Digest256) : SchedulerNativeRun Result :=
  let tail := runSchedulerNativeListRun transitionFuel state.cursor answers
  { terminal := tail.terminal
    trace := state.tracePrefix ++ tail.trace }

/-- A completed run is obtainable from a routed cursor by an explicit answer
suffix. -/
def Q16RunOccursFrom
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat)
    (state : SchedulerNativeQ16Cursor globalOracleCalls Result)
    (run : SchedulerNativeRun Result) : Prop :=
  ∃ answers, run = q16ContinuationRun transitionFuel state answers

theorem finish_scheduler_native_q16_forest_occurs
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat)
    (state : SchedulerNativeQ16Cursor globalOracleCalls Result) :
    Q16RunOccursFrom transitionFuel state
      (finishSchedulerNativeQ16Forest transitionFuel state).run := by
  exact ⟨state.remainingAnswers, rfl⟩

/-- Pull one successful cache-aware coordinate backwards.  The cache case is
literally inert.  The fresh case is the generic counterfactual-pause theorem,
so the replacement is part of an ordinary scheduler tape rather than a
postulated continuation. -/
theorem consume_scheduler_native_q16_coordinate_pullback
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (kind : SchedulerNativeQ16QueryKind)
    (expectedInput : ShaInput) (expectedAnswer : Digest256)
    (state after : SchedulerNativeQ16Cursor globalOracleCalls Result)
    (run : SchedulerNativeRun Result)
    (consumed : consumeSchedulerNativeQ16Coordinate transitionFuel kind
      expectedInput expectedAnswer state = .ok after)
    (occurs : Q16RunOccursFrom transitionFuel after run) :
    Q16RunOccursFrom transitionFuel state run := by
  rcases occurs with ⟨suffix, runExact⟩
  unfold consumeSchedulerNativeQ16Coordinate at consumed
  cases found : lookupEntry state.oracle expectedInput with
  | some entry =>
      by_cases answerExact : entry.output = expectedAnswer
      · simp only [found, answerExact, ↓reduceIte] at consumed
        cases consumed
        exact ⟨suffix, runExact⟩
      · simp only [found, answerExact, ↓reduceIte] at consumed
        cases consumed
  | none =>
      simp only [found] at consumed
      cases scanned : scanSchedulerNativeToInput transitionFuel expectedInput
          state.cursor state.remainingAnswers with
      | absent tail => simp [scanned] at consumed
      | paused pause =>
          simp only [scanned] at consumed
          cases consumed
          refine ⟨pause.consumedAnswers ++ expectedAnswer :: suffix, ?_⟩
          rw [runExact]
          have counterfactual :=
            scan_scheduler_native_to_input_paused_resume_with_replacement_exact
              transitionFuel expectedInput state.cursor state.remainingAnswers
              pause scanned expectedAnswer suffix
          unfold q16ContinuationRun
          rw [← counterfactual]
          simp [SchedulerNativeFreshPause.resumeRunWith,
            runSchedulerNativeListRun, q16MachineFreshRecord,
            List.append_assoc]

theorem run_scheduler_native_q16_branch_tail_pullback
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) :
    ∀ (pairs : List (Digest256 × Digest256)) (digest : Digest256)
      (state final : SchedulerNativeQ16Cursor globalOracleCalls Result)
      (run : SchedulerNativeRun Result),
      runSchedulerNativeQ16BranchTail transitionFuel pairs digest state =
          .ok final →
      Q16RunOccursFrom transitionFuel final run →
      Q16RunOccursFrom transitionFuel state run := by
  intro pairs
  induction pairs with
  | nil =>
      intro digest state final run executed occurs
      simp only [runSchedulerNativeQ16BranchTail] at executed
      cases executed
      exact occurs
  | cons pair rest ih =>
      intro digest state final run executed occurs
      rw [runSchedulerNativeQ16BranchTail] at executed
      cases outputResult : consumeSchedulerNativeQ16Coordinate transitionFuel
          .output (q16OutputInput digest) pair.1 state with
      | error failure => simp [outputResult] at executed
      | ok afterOutput =>
          simp only [outputResult] at executed
          cases advanceResult : consumeSchedulerNativeQ16Coordinate
              transitionFuel .advance (q16AdvanceInput digest) pair.2
              afterOutput with
          | error failure => simp [advanceResult] at executed
          | ok afterAdvance =>
              simp only [advanceResult] at executed
              have fromAfterAdvance := ih pair.2 afterAdvance final run
                executed occurs
              have fromAfterOutput :=
                consume_scheduler_native_q16_coordinate_pullback
                  transitionFuel .advance (q16AdvanceInput digest) pair.2
                  afterOutput afterAdvance run advanceResult fromAfterAdvance
              exact consume_scheduler_native_q16_coordinate_pullback
                transitionFuel .output (q16OutputInput digest) pair.1 state
                afterOutput run outputResult fromAfterOutput

theorem run_scheduler_native_q16_branch_from_cursor_pullback
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (branch : SchedulerNativeQ16Branch)
    (forest : TotalQ16DuplexForest)
    (state final : SchedulerNativeQ16Cursor globalOracleCalls Result)
    (run : SchedulerNativeRun Result)
    (executed : runSchedulerNativeQ16BranchFromCursor transitionFuel branch
      forest state = .ok final)
    (occurs : Q16RunOccursFrom transitionFuel final run) :
    Q16RunOccursFrom transitionFuel state run := by
  unfold runSchedulerNativeQ16BranchFromCursor at executed
  generalize pairsExact : q16BranchDuplexPairs branch forest = pairs at executed
  cases pairs with
  | nil => simp at executed
  | cons pair rest =>
      cases outputResult : consumeSchedulerNativeQ16Coordinate transitionFuel
          .output (q16OutputInput branch.initialDigest) pair.1 state with
      | error failure => simp [outputResult] at executed
      | ok afterOutput =>
          simp only [outputResult] at executed
          cases advanceResult : consumeSchedulerNativeQ16Coordinate
              transitionFuel .advance
              (q16AdvanceInput branch.initialDigest) pair.2 afterOutput with
          | error failure => simp [advanceResult] at executed
          | ok afterAdvance =>
              simp only [advanceResult] at executed
              have fromAfterAdvance :=
                run_scheduler_native_q16_branch_tail_pullback transitionFuel
                  rest pair.2 afterAdvance final run executed occurs
              have fromAfterOutput :=
                consume_scheduler_native_q16_coordinate_pullback
                  transitionFuel .advance
                  (q16AdvanceInput branch.initialDigest) pair.2 afterOutput
                  afterAdvance run advanceResult fromAfterAdvance
              exact consume_scheduler_native_q16_coordinate_pullback
                transitionFuel .output
                (q16OutputInput branch.initialDigest) pair.1 state afterOutput
                run outputResult fromAfterOutput

theorem run_scheduler_native_q16_branch_list_pullback
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (forest : TotalQ16DuplexForest) :
    ∀ (branches : List SchedulerNativeQ16Branch)
      (state final : SchedulerNativeQ16Cursor globalOracleCalls Result)
      (run : SchedulerNativeRun Result),
      runSchedulerNativeQ16BranchList transitionFuel forest branches state =
          .ok final →
      Q16RunOccursFrom transitionFuel final run →
      Q16RunOccursFrom transitionFuel state run := by
  intro branches
  induction branches with
  | nil =>
      intro state final run executed occurs
      simp only [runSchedulerNativeQ16BranchList] at executed
      cases executed
      exact occurs
  | cons branch rest ih =>
      intro state final run executed occurs
      rw [runSchedulerNativeQ16BranchList] at executed
      cases branchResult : runSchedulerNativeQ16BranchFromCursor transitionFuel
          branch forest state with
      | error failure => simp [branchResult] at executed
      | ok afterBranch =>
          simp only [branchResult] at executed
          have afterOccurs := ih afterBranch final run executed occurs
          exact run_scheduler_native_q16_branch_from_cursor_pullback
            transitionFuel branch forest state afterBranch run branchResult
            afterOccurs

/-- A successful first-pause forest is an exact continuation of that pause
with the routed first output and one explicit replacement suffix. -/
theorem replay_scheduler_native_q16_forest_occurs_from_first_pause
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (firstBranch : SchedulerNativeQ16Branch)
    (firstPause : SchedulerNativeFreshPause globalOracleCalls Result
      (q16OutputInput firstBranch.initialDigest))
    (restBranches : List SchedulerNativeQ16Branch)
    (forest : TotalQ16DuplexForest)
    (response : SchedulerNativeQ16ForestResponse Result)
    (replayed : replaySchedulerNativeQ16ForestOccurrence transitionFuel
      firstBranch firstPause restBranches forest = .ok response) :
    ∃ replacement suffix,
      response.run = firstPause.resumeRunWith transitionFuel replacement
        suffix := by
  unfold replaySchedulerNativeQ16ForestOccurrence at replayed
  unfold runSchedulerNativeQ16ForestFromFirstPause at replayed
  unfold runSchedulerNativeQ16BranchFromFirstPause at replayed
  generalize pairsExact : q16BranchDuplexPairs firstBranch forest = pairs
    at replayed
  cases pairs with
  | nil => simp at replayed
  | cons pair branchTail =>
      let afterOutput : SchedulerNativeQ16Cursor globalOracleCalls Result :=
        { cursor := firstPause.resumeCursorWith pair.1
          remainingAnswers := firstPause.remainingAnswers
          oracle := freshQueryState firstPause.actor firstPause.requestState
            firstPause.input pair.1
          tracePrefix := firstPause.consumedTrace ++
            [q16MachineFreshRecord firstPause pair.1] }
      cases advanceResult : consumeSchedulerNativeQ16Coordinate transitionFuel
          .advance (q16AdvanceInput firstBranch.initialDigest) pair.2
          afterOutput with
      | error failure => simp [afterOutput, advanceResult] at replayed
      | ok afterAdvance =>
          simp only [afterOutput, advanceResult] at replayed
          cases tailResult : runSchedulerNativeQ16BranchTail transitionFuel
              branchTail pair.2 afterAdvance with
          | error failure => simp [tailResult] at replayed
          | ok afterFirst =>
              simp only [tailResult] at replayed
              cases listResult : runSchedulerNativeQ16BranchList transitionFuel
                  forest restBranches afterFirst with
              | error failure => simp [listResult] at replayed
              | ok final =>
                  simp only [listResult] at replayed
                  cases replayed
                  have finalOccurs :=
                    finish_scheduler_native_q16_forest_occurs transitionFuel
                      final
                  have afterFirstOccurs :=
                    run_scheduler_native_q16_branch_list_pullback
                      transitionFuel forest restBranches afterFirst final
                      (finishSchedulerNativeQ16Forest transitionFuel final).run
                      listResult finalOccurs
                  have afterAdvanceOccurs :=
                    run_scheduler_native_q16_branch_tail_pullback
                      transitionFuel branchTail pair.2 afterAdvance afterFirst
                      (finishSchedulerNativeQ16Forest transitionFuel final).run
                      tailResult afterFirstOccurs
                  have afterOutputOccurs :=
                    consume_scheduler_native_q16_coordinate_pullback
                      transitionFuel .advance
                      (q16AdvanceInput firstBranch.initialDigest) pair.2
                      afterOutput afterAdvance
                      (finishSchedulerNativeQ16Forest transitionFuel final).run
                      advanceResult afterAdvanceOccurs
                  rcases afterOutputOccurs with ⟨suffix, runExact⟩
                  refine ⟨pair.1, suffix, ?_⟩
                  rw [runExact]
                  simp [q16ContinuationRun, afterOutput,
                    SchedulerNativeFreshPause.resumeRunWith,
                    runSchedulerNativeListRun, q16MachineFreshRecord,
                    List.append_assoc]

/-- Source-facing occurrence theorem.  Starting only from the scanner result
on the actual source cursor/tape, every successful routed q16 forest is one
literal production scheduler run on a concrete modified tape. -/
theorem replay_scheduler_native_q16_forest_is_scheduler_run
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (firstBranch : SchedulerNativeQ16Branch)
    (cursor : SchedulerNativeCursor globalOracleCalls Result)
    (answers : List Digest256)
    (firstPause : SchedulerNativeFreshPause globalOracleCalls Result
      (q16OutputInput firstBranch.initialDigest))
    (found : scanSchedulerNativeToInput transitionFuel
      (q16OutputInput firstBranch.initialDigest) cursor answers =
        .paused firstPause)
    (restBranches : List SchedulerNativeQ16Branch)
    (forest : TotalQ16DuplexForest)
    (response : SchedulerNativeQ16ForestResponse Result)
    (replayed : replaySchedulerNativeQ16ForestOccurrence transitionFuel
      firstBranch firstPause restBranches forest = .ok response) :
    ∃ modifiedAnswers,
      response.run = runSchedulerNativeListRun transitionFuel cursor
        modifiedAnswers := by
  obtain ⟨replacement, suffix, responseExact⟩ :=
    replay_scheduler_native_q16_forest_occurs_from_first_pause transitionFuel
      firstBranch firstPause restBranches forest response replayed
  refine ⟨firstPause.consumedAnswers ++ replacement :: suffix, ?_⟩
  rw [responseExact]
  exact scan_scheduler_native_to_input_paused_resume_with_replacement_exact
    transitionFuel (q16OutputInput firstBranch.initialDigest) cursor answers
    firstPause found replacement suffix

#print axioms consume_scheduler_native_q16_coordinate_pullback
#print axioms run_scheduler_native_q16_branch_tail_pullback
#print axioms run_scheduler_native_q16_branch_from_cursor_pullback
#print axioms run_scheduler_native_q16_branch_list_pullback
#print axioms replay_scheduler_native_q16_forest_occurs_from_first_pause
#print axioms replay_scheduler_native_q16_forest_is_scheduler_run

end

end AspisK1.V7Tag73SchedulerNativeQ16Occurrence
