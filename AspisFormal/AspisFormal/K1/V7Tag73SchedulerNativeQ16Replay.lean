import AspisFormal.K1.V7Tag73SchedulerNativeTargetPause

/-!
# Scheduler-native counterfactual replay of one Tag-73 q16 branch

The q16 output coordinates have the same unlabelled duplex byte grammar as
the ordinary challenge samplers.  Consequently an earlier adversary query
may already have installed one of the answers used by a later verifier q16
branch.  This module does not retroactively relabel such an answer.  It runs
one complete candidate branch through the result-carrying scheduler and uses
the exact cache/fresh dichotomy at every output and advance coordinate:

* an already defined table entry is immutable and consumes no master-tape
  coordinate;
* a missing entry is replaced only at a genuine scheduler-native fresh pause;
* the actor attached to that pause is preserved; and
* the first routed output replaces, rather than reads, the answer retained by
  the source scan.

The branch geometry is fixed before execution: a counter, the post-counter-
absorb digest, and a positive block count at most eight.  The complete
`64 x 8` output and advance forests are supplied independently of the branch
result, while execution consumes only the selected branch prefix.  This leaf
does not yet assert that the supplied branch is the first cap-203 branch or
that a full forest replay equals the actual accepted source run; those are
the next source-alignment theorems.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73SchedulerNativeQ16Replay

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerNativeTargetPause

noncomputable section

universe u

/-- All possible q16 duplex answers.  Output halves are the public q16 digest
forest used by the compact-schedule theorem; advance halves remain explicit
nuisance coordinates because they determine later SHA inputs. -/
abbrev TotalQ16DuplexForest :=
  (Fin 64 -> Fin 8 -> Digest256) × (Fin 64 -> Fin 8 -> Digest256)

/-- One candidate branch whose counter, initial digest and stopping length are
fixed before any routed answer in that branch is read. -/
structure SchedulerNativeQ16Branch where
  counter : Fin 64
  initialDigest : Digest256
  blocksUsed : Nat
  blocksPositive : 0 < blocksUsed
  blocksCap : blocksUsed <= 8

inductive SchedulerNativeQ16QueryKind where
  | output
  | advance
  deriving DecidableEq

inductive SchedulerNativeQ16ReplayFailure where
  | expectedQueryAbsent (kind : SchedulerNativeQ16QueryKind)
  | cachedAnswerMismatch (kind : SchedulerNativeQ16QueryKind)
  | emptyBranch
  deriving DecidableEq

def q16OutputInput (digest : Digest256) : ShaInput :=
  bytes digest ++ [domSqueeze]

def q16AdvanceInput (digest : Digest256) : ShaInput :=
  bytes digest ++ [domAdvance]

/-- The exact chronological duplex pairs consumed by one branch.  The cap
proof embeds every local block into the release `Fin 8` rectangle. -/
def q16BranchDuplexPairs (branch : SchedulerNativeQ16Branch)
    (forest : TotalQ16DuplexForest) : List (Digest256 × Digest256) :=
  List.ofFn fun (blockIndex : Fin branch.blocksUsed) =>
    let block : Fin 8 :=
      ⟨blockIndex.val, lt_of_lt_of_le blockIndex.isLt branch.blocksCap⟩
    (forest.1 branch.counter block, forest.2 branch.counter block)

@[simp] theorem q16_branch_duplex_pairs_length
    (branch : SchedulerNativeQ16Branch)
    (forest : TotalQ16DuplexForest) :
    (q16BranchDuplexPairs branch forest).length = branch.blocksUsed := by
  simp [q16BranchDuplexPairs]

/-- The output halves consumed by the production candidate decoder. -/
def q16BranchOutputBlocks (branch : SchedulerNativeQ16Branch)
    (forest : TotalQ16DuplexForest) : List Digest256 :=
  (q16BranchDuplexPairs branch forest).map Prod.fst

@[simp] theorem q16_branch_output_blocks_length
    (branch : SchedulerNativeQ16Branch)
    (forest : TotalQ16DuplexForest) :
    (q16BranchOutputBlocks branch forest).length = branch.blocksUsed := by
  simp [q16BranchOutputBlocks]

/-- A replay branch consumes exactly the corresponding prefix of its full
eight-block candidate tape. -/
theorem q16_branch_output_blocks_eq_take
    (branch : SchedulerNativeQ16Branch)
    (forest : TotalQ16DuplexForest) :
    q16BranchOutputBlocks branch forest =
      (List.ofFn (forest.1 branch.counter)).take branch.blocksUsed := by
  apply List.ext_getElem
  · simp [q16BranchOutputBlocks, branch.blocksCap]
  · intro index leftBound rightBound
    unfold q16BranchOutputBlocks
    rw [List.getElem_map]
    unfold q16BranchDuplexPairs
    rw [List.getElem_ofFn]
    rw [List.getElem_take, List.getElem_ofFn]

theorem q16_branch_duplex_pairs_nonempty
    (branch : SchedulerNativeQ16Branch)
    (forest : TotalQ16DuplexForest) :
    q16BranchDuplexPairs branch forest ≠ [] := by
  intro empty
  have lengthZero := congrArg List.length empty
  rw [q16_branch_duplex_pairs_length] at lengthZero
  simp only [List.length_nil] at lengthZero
  exact branch.blocksPositive.ne' lengthZero

def q16MachineFreshRecord
    {globalOracleCalls : Nat} {Result : Type u} {target : ShaInput}
    (pause : SchedulerNativeFreshPause globalOracleCalls Result target)
    (answer : Digest256) : UnifiedExposureRecord :=
  .machineFresh pause.actor pause.input answer

/-- Scheduler state retained between q16 duplex coordinates. -/
structure SchedulerNativeQ16Cursor
    (globalOracleCalls : Nat) (Result : Type u) where
  cursor : SchedulerNativeCursor globalOracleCalls Result
  remainingAnswers : List Digest256
  oracle : OracleState
  tracePrefix : List UnifiedExposureRecord

/-- Consume one expected q16 coordinate without retroactive role assignment.
The table lookup is authoritative on a cache hit; otherwise the ordinary
scheduler is scanned to the exact requested input. -/
def consumeSchedulerNativeQ16Coordinate
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (kind : SchedulerNativeQ16QueryKind)
    (expectedInput : ShaInput) (expectedAnswer : Digest256)
    (state : SchedulerNativeQ16Cursor globalOracleCalls Result) :
    Except SchedulerNativeQ16ReplayFailure
      (SchedulerNativeQ16Cursor globalOracleCalls Result) :=
  match lookupEntry state.oracle expectedInput with
  | some entry =>
      if entry.output = expectedAnswer then .ok state
      else .error (.cachedAnswerMismatch kind)
  | none =>
      match scanSchedulerNativeToInput transitionFuel expectedInput
          state.cursor state.remainingAnswers with
      | .absent _ => .error (.expectedQueryAbsent kind)
      | .paused pause =>
          .ok
            { cursor := pause.resumeCursorWith expectedAnswer
              remainingAnswers := pause.remainingAnswers
              oracle := freshQueryState pause.actor pause.requestState
                pause.input expectedAnswer
              tracePrefix := state.tracePrefix ++ pause.consumedTrace ++
                [q16MachineFreshRecord pause expectedAnswer] }

theorem consume_scheduler_native_q16_cached_is_inert
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (kind : SchedulerNativeQ16QueryKind)
    (expectedInput : ShaInput) (expectedAnswer : Digest256)
    (state : SchedulerNativeQ16Cursor globalOracleCalls Result)
    (entry : TableEntry)
    (found : lookupEntry state.oracle expectedInput = some entry)
    (answerExact : entry.output = expectedAnswer) :
    consumeSchedulerNativeQ16Coordinate transitionFuel kind expectedInput
        expectedAnswer state = .ok state := by
  simp [consumeSchedulerNativeQ16Coordinate, found, answerExact]

theorem consume_scheduler_native_q16_fresh_uses_exact_pause_actor
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (kind : SchedulerNativeQ16QueryKind)
    (expectedInput : ShaInput) (expectedAnswer : Digest256)
    (state : SchedulerNativeQ16Cursor globalOracleCalls Result)
    (missing : lookupEntry state.oracle expectedInput = none)
    (pause : SchedulerNativeFreshPause globalOracleCalls Result expectedInput)
    (paused : scanSchedulerNativeToInput transitionFuel expectedInput
      state.cursor state.remainingAnswers = .paused pause) :
    consumeSchedulerNativeQ16Coordinate transitionFuel kind expectedInput
        expectedAnswer state =
      .ok
        { cursor := pause.resumeCursorWith expectedAnswer
          remainingAnswers := pause.remainingAnswers
          oracle := freshQueryState pause.actor pause.requestState pause.input
            expectedAnswer
          tracePrefix := state.tracePrefix ++ pause.consumedTrace ++
            [q16MachineFreshRecord pause expectedAnswer] } := by
  simp [consumeSchedulerNativeQ16Coordinate, missing, paused]

theorem consume_scheduler_native_q16_ne_empty_failure
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (kind : SchedulerNativeQ16QueryKind)
    (expectedInput : ShaInput) (expectedAnswer : Digest256)
    (state : SchedulerNativeQ16Cursor globalOracleCalls Result) :
    consumeSchedulerNativeQ16Coordinate transitionFuel kind expectedInput
        expectedAnswer state ≠ .error .emptyBranch := by
  unfold consumeSchedulerNativeQ16Coordinate
  cases found : lookupEntry state.oracle expectedInput with
  | none =>
      cases scanned : scanSchedulerNativeToInput transitionFuel expectedInput
          state.cursor state.remainingAnswers <;> simp
  | some entry =>
      by_cases answerExact : entry.output = expectedAnswer <;>
        simp [answerExact]

/-- Run the remainder of one branch after its first output has been installed.
Each advance answer becomes the expected state for the following output. -/
def runSchedulerNativeQ16BranchTail
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) :
    (pairs : List (Digest256 × Digest256)) ->
      (digest : Digest256) ->
      SchedulerNativeQ16Cursor globalOracleCalls Result ->
      Except SchedulerNativeQ16ReplayFailure
        (SchedulerNativeQ16Cursor globalOracleCalls Result)
  | [], _, state => .ok state
  | (output, advanced) :: rest, digest, state =>
      match consumeSchedulerNativeQ16Coordinate transitionFuel .output
          (q16OutputInput digest) output state with
      | .error failure => .error failure
      | .ok afterOutput =>
          match consumeSchedulerNativeQ16Coordinate transitionFuel .advance
              (q16AdvanceInput digest) advanced afterOutput with
          | .error failure => .error failure
          | .ok afterAdvance =>
              runSchedulerNativeQ16BranchTail transitionFuel rest advanced
                afterAdvance

theorem run_scheduler_native_q16_branch_tail_ne_empty_failure
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat)
    (pairs : List (Digest256 × Digest256)) (digest : Digest256)
    (state : SchedulerNativeQ16Cursor globalOracleCalls Result) :
    runSchedulerNativeQ16BranchTail transitionFuel pairs digest state ≠
      .error .emptyBranch := by
  induction pairs generalizing digest state with
  | nil => simp [runSchedulerNativeQ16BranchTail]
  | cons pair rest ih =>
      rw [runSchedulerNativeQ16BranchTail]
      cases outputResult : consumeSchedulerNativeQ16Coordinate transitionFuel
          .output (q16OutputInput digest) pair.1 state with
      | error failure =>
          simp only
          cases failure with
          | expectedQueryAbsent => simp
          | cachedAnswerMismatch => simp
          | emptyBranch =>
              exact False.elim
                (consume_scheduler_native_q16_ne_empty_failure transitionFuel
                  .output (q16OutputInput digest) pair.1 state outputResult)
      | ok afterOutput =>
          simp only
          cases advanceResult : consumeSchedulerNativeQ16Coordinate
              transitionFuel .advance (q16AdvanceInput digest) pair.2
              afterOutput with
          | error failure =>
              simp only
              cases failure with
              | expectedQueryAbsent => simp
              | cachedAnswerMismatch => simp
              | emptyBranch =>
                  exact False.elim
                    (consume_scheduler_native_q16_ne_empty_failure transitionFuel
                      .advance (q16AdvanceInput digest) pair.2 afterOutput
                      advanceResult)
          | ok afterAdvance =>
              simp only
              exact ih pair.2 afterAdvance

/-- Start one branch at an already proved fresh pause for its first output.
The retained actual target answer is not read. -/
def runSchedulerNativeQ16BranchFromFirstPause
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (branch : SchedulerNativeQ16Branch)
    (firstPause : SchedulerNativeFreshPause globalOracleCalls Result
      (q16OutputInput branch.initialDigest))
    (forest : TotalQ16DuplexForest) :
    Except SchedulerNativeQ16ReplayFailure
      (SchedulerNativeQ16Cursor globalOracleCalls Result) :=
  match q16BranchDuplexPairs branch forest with
  | [] => .error .emptyBranch
  | (output, advanced) :: rest =>
      let afterOutput : SchedulerNativeQ16Cursor globalOracleCalls Result :=
        { cursor := firstPause.resumeCursorWith output
          remainingAnswers := firstPause.remainingAnswers
          oracle := freshQueryState firstPause.actor firstPause.requestState
            firstPause.input output
          tracePrefix := firstPause.consumedTrace ++
            [q16MachineFreshRecord firstPause output] }
      match consumeSchedulerNativeQ16Coordinate transitionFuel .advance
          (q16AdvanceInput branch.initialDigest) advanced afterOutput with
      | .error failure => .error failure
      | .ok afterAdvance =>
          runSchedulerNativeQ16BranchTail transitionFuel rest advanced
            afterAdvance

/-- The q16 counterfactual branch is definitionally independent of the actual
answer retained by the source scan. -/
@[simp] theorem run_scheduler_native_q16_branch_independent_of_target_answer
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (branch : SchedulerNativeQ16Branch)
    (firstPause : SchedulerNativeFreshPause globalOracleCalls Result
      (q16OutputInput branch.initialDigest))
    (replacement : Digest256) (forest : TotalQ16DuplexForest) :
    runSchedulerNativeQ16BranchFromFirstPause transitionFuel branch
        { firstPause with targetAnswer := replacement } forest =
      runSchedulerNativeQ16BranchFromFirstPause transitionFuel branch
        firstPause forest := by
  rfl

/-- A positive branch cannot take the defensive empty-branch arm. -/
theorem run_scheduler_native_q16_branch_ne_empty_failure
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (branch : SchedulerNativeQ16Branch)
    (firstPause : SchedulerNativeFreshPause globalOracleCalls Result
      (q16OutputInput branch.initialDigest))
    (forest : TotalQ16DuplexForest) :
    runSchedulerNativeQ16BranchFromFirstPause transitionFuel branch firstPause
        forest ≠ .error .emptyBranch := by
  unfold runSchedulerNativeQ16BranchFromFirstPause
  generalize pairsExact : q16BranchDuplexPairs branch forest = pairs
  cases pairs with
  | nil =>
      exact False.elim
        (q16_branch_duplex_pairs_nonempty branch forest pairsExact)
  | cons pair rest =>
      simp only
      cases advancedResult : consumeSchedulerNativeQ16Coordinate transitionFuel
          .advance (q16AdvanceInput branch.initialDigest) pair.2
          { cursor := firstPause.resumeCursorWith pair.1
            remainingAnswers := firstPause.remainingAnswers
            oracle := freshQueryState firstPause.actor firstPause.requestState
              firstPause.input pair.1
            tracePrefix := firstPause.consumedTrace ++
              [q16MachineFreshRecord firstPause pair.1] } with
      | error failure =>
          simp only
          cases failure with
          | expectedQueryAbsent => simp
          | cachedAnswerMismatch => simp
          | emptyBranch =>
              exact False.elim
                (consume_scheduler_native_q16_ne_empty_failure transitionFuel
                  .advance (q16AdvanceInput branch.initialDigest) pair.2
                  { cursor := firstPause.resumeCursorWith pair.1
                    remainingAnswers := firstPause.remainingAnswers
                    oracle := freshQueryState firstPause.actor
                      firstPause.requestState firstPause.input pair.1
                    tracePrefix := firstPause.consumedTrace ++
                      [q16MachineFreshRecord firstPause pair.1] }
                  advancedResult)
      | ok afterAdvance =>
          simp only
          exact
            run_scheduler_native_q16_branch_tail_ne_empty_failure
              transitionFuel rest pair.2 afterAdvance

#print axioms q16_branch_duplex_pairs_length
#print axioms q16_branch_output_blocks_eq_take
#print axioms q16_branch_duplex_pairs_nonempty
#print axioms consume_scheduler_native_q16_cached_is_inert
#print axioms consume_scheduler_native_q16_fresh_uses_exact_pause_actor
#print axioms run_scheduler_native_q16_branch_independent_of_target_answer
#print axioms run_scheduler_native_q16_branch_ne_empty_failure

end

end AspisK1.V7Tag73SchedulerNativeQ16Replay
