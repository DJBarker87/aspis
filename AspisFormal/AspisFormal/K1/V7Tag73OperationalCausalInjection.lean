import AspisFormal.K1.V7Tag73GlobalForwardReferenceBound
import AspisFormal.K1.V7Tag73AtomicPairReplay
import AspisFormal.K1.V7Tag73StableFirstRunBridge
import AspisFormal.K1.V7Tag73NoPairOccurrenceTrichotomy
import AspisFormal.K1.V7Tag73OperationalOracleExposure
import AspisFormal.K1.V7Tag73ExecutionDigestProvenance
import AspisFormal.K1.V7Tag73AtomicPairProbabilityAudit

/-!
# Operational causal targets for Tag-73 replay

This module constructs the finite target set used at a fresh full-256
exposure from data available *before that answer is supplied*:

* the full outputs exposed at earlier compiler steps; and
* the literal 32-byte prefixes of SHA inputs in the current oracle history;
  and
* the current pending query input.

It also defines a fuel-bounded `seekNextFresh` interpreter.  Cached queries
are executed, while the first missing query is returned together with its
continuation before any controller answer is read.  This is the resumable
machine primitive needed to build a genuinely nonanticipating causal tree.
In particular this file does **not** build a tree from a completed Q1: that
history depends on the same oracle tape and would be anticipatory.

The exact atomic Tag-73 pair is also connected to literal-reference facts. If
`programAtomicPair` reports an input conflict in a table covered by its query
history, the generated pre-squeeze state literally prefixes a previously
issued query.  This fact alone is not a probability charge: the referenced
history must already be frozen before the relevant fresh coin is exposed.
The same conclusion follows from the executable first
literal-forward-reference branch, and the scheduled-fork theorem below proves
the required temporal order for that no-pair branch.

There are two deliberate boundaries.  `QueryRecord` contains a raw input but
no information-flow provenance, so this construction covers literal prefix
references only.  Generated checkpoints are now proved to be the dummy zero
or an actual execution reply, but replies are not yet classified as fresh,
programmed, or cached tape coordinates.  In particular `forkOutput` and
`forkAdvance` are caller fields, not answers exposed by `seekNextFresh`; the
last sections give an explicit two-coordinate scheduler shape and state the
remaining integration gap.  No probability bound, BCS coefficient, or
compiler conclusion is asserted here.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73OperationalCausalInjection

set_option maxRecDepth 8192

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ConcreteQueryDag
open AspisK1.V7Tag73InteractiveExecution
open AspisK1.V7Tag73AtomicPairFork
open AspisK1.V7Tag73AtomicPairReplay
open AspisK1.V7Tag73StableFirstRunBridge
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73GlobalForwardReferenceBound
open AspisK1.V7Tag73ResourceLazyOracle
open AspisK1.V7Tag73ExecutionDigestProvenance
open AspisK1.V7Tag73AtomicPairProbabilityAudit
open AspisK1.V7FsAokExperiment

noncomputable section

/-! ## Finite targets computed from concrete history -/

/-- All full digests that literally occupy the first 32 bytes of one actual
SHA input.  The set is empty for a short input and a singleton otherwise. -/
def oneInputLiteralTargets (input : ShaInput) : Finset Digest256 :=
  Finset.univ.filter fun state => HasLiteralStatePrefix state input

@[simp] theorem mem_one_input_literal_targets_iff
    (state : Digest256) (input : ShaInput) :
    state ∈ oneInputLiteralTargets input ↔
      HasLiteralStatePrefix state input := by
  simp [oneInputLiteralTargets]

theorem one_input_literal_targets_card_le_one (input : ShaInput) :
    (oneInputLiteralTargets input).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro first second firstMember secondMember
  exact literal_state_prefix_target_subsingleton input
    ((mem_one_input_literal_targets_iff first input).mp firstMember)
    ((mem_one_input_literal_targets_iff second input).mp secondMember)

/-- Literal-prefix targets named by a chronological concrete query history. -/
def historyLiteralTargets : List QueryRecord → Finset Digest256
  | [] => ∅
  | record :: records =>
      oneInputLiteralTargets record.input ∪ historyLiteralTargets records

set_option maxRecDepth 4096 in
theorem mem_history_literal_targets_iff
    (state : Digest256) (history : List QueryRecord) :
    state ∈ historyLiteralTargets history ↔
      ∃ record ∈ history, HasLiteralStatePrefix state record.input := by
  induction history with
  | nil => simp [historyLiteralTargets]
  | cons record records ih =>
      simp [historyLiteralTargets, ih]

theorem history_literal_targets_card_le_length
    (history : List QueryRecord) :
    (historyLiteralTargets history).card ≤ history.length := by
  induction history with
  | nil => simp [historyLiteralTargets]
  | cons record records ih =>
      have unionBound := Finset.card_union_le
        (oneInputLiteralTargets record.input)
        (historyLiteralTargets records)
      have headBound := one_input_literal_targets_card_le_one record.input
      simp only [historyLiteralTargets, List.length_cons]
      omega

/-- Exact target set at one compiler exposure.  `seen` contains the earlier
full-256 answers; `history` is frozen before the new compiler tape is exposed. -/
def operationalHistoryTargets
    (seen : Finset Digest256) (history : List QueryRecord) :
    Finset Digest256 :=
  seen ∪ historyLiteralTargets history

theorem operational_history_targets_card_le
    (seen : Finset Digest256) (history : List QueryRecord) :
    (operationalHistoryTargets seen history).card ≤
      seen.card + history.length := by
  exact (Finset.card_union_le seen (historyLiteralTargets history)).trans
    (Nat.add_le_add_left
      (history_literal_targets_card_le_length history) seen.card)

/-- Operational, constructor-based classification of why the current answer
hits the concrete target set. -/
inductive OperationalTargetHit
    (seen : Finset Digest256) (history : List QueryRecord)
    (answer : Digest256) : Prop where
  | priorFullOutput (member : answer ∈ seen)
  | literalPrefix (record : QueryRecord) (member : record ∈ history)
      (prefixProof : HasLiteralStatePrefix answer record.input)

theorem operational_target_hit_iff_mem
    (seen : Finset Digest256) (history : List QueryRecord)
    (answer : Digest256) :
    OperationalTargetHit seen history answer ↔
      answer ∈ operationalHistoryTargets seen history := by
  constructor
  · intro hit
    cases hit with
    | priorFullOutput member =>
        exact Finset.mem_union_left _ member
    | literalPrefix record member prefixProof =>
        apply Finset.mem_union_right
        exact (mem_history_literal_targets_iff answer history).mpr
          ⟨record, member, prefixProof⟩
  · intro member
    rcases Finset.mem_union.mp member with prior | literal
    · exact .priorFullOutput prior
    · obtain ⟨record, recordMember, prefixProof⟩ :=
        (mem_history_literal_targets_iff answer history).mp literal
      exact .literalPrefix record recordMember prefixProof

theorem operational_target_hit_is_collision_or_literal_prefix
    (seen : Finset Digest256) (history : List QueryRecord)
    (answer : Digest256)
    (hit : OperationalTargetHit seen history answer) :
    answer ∈ seen ∨
      ∃ record ∈ history, HasLiteralStatePrefix answer record.input := by
  cases hit with
  | priorFullOutput member => exact Or.inl member
  | literalPrefix record member prefixProof =>
      exact Or.inr ⟨record, member, prefixProof⟩

/-! ## Targets at the next operational fresh request -/

/-- At a missing query, the current input is available before its answer and
can therefore be added without violating causality. -/
def operationalRequestTargets
    (seen : Finset Digest256) (history : List QueryRecord)
    (currentInput : ShaInput) : Finset Digest256 :=
  operationalHistoryTargets seen history ∪
    oneInputLiteralTargets currentInput

theorem operational_request_targets_card_le
    (seen : Finset Digest256) (history : List QueryRecord)
    (currentInput : ShaInput) :
    (operationalRequestTargets seen history currentInput).card ≤
      seen.card + (history.length + 1) := by
  have unionBound := Finset.card_union_le
    (operationalHistoryTargets seen history)
    (oneInputLiteralTargets currentInput)
  have historyBound := operational_history_targets_card_le seen history
  have currentBound := one_input_literal_targets_card_le_one currentInput
  calc
    (operationalRequestTargets seen history currentInput).card ≤
        (operationalHistoryTargets seen history).card +
          (oneInputLiteralTargets currentInput).card := unionBound
    _ ≤ (seen.card + history.length) + 1 :=
      Nat.add_le_add historyBound currentBound
    _ = seen.card + (history.length + 1) := by omega

theorem operational_request_targets_within_step_plus_global_cap
    (seen : Finset Digest256) (history : List QueryRecord)
    (currentInput : ShaInput) (step globalOracleCalls : Nat)
    (seenBound : seen.card ≤ step)
    (requestBound : history.length + 1 ≤ globalOracleCalls) :
    (operationalRequestTargets seen history currentInput).card ≤
      step + globalOracleCalls := by
  exact (operational_request_targets_card_le seen history currentInput).trans
    (Nat.add_le_add seenBound requestBound)

inductive OperationalRequestTargetHit
    (seen : Finset Digest256) (history : List QueryRecord)
    (currentInput : ShaInput) (answer : Digest256) : Prop where
  | priorFullOutput (member : answer ∈ seen)
  | priorLiteralPrefix (record : QueryRecord) (member : record ∈ history)
      (prefixProof : HasLiteralStatePrefix answer record.input)
  | currentLiteralPrefix
      (prefixProof : HasLiteralStatePrefix answer currentInput)

theorem operational_request_target_hit_iff_mem
    (seen : Finset Digest256) (history : List QueryRecord)
    (currentInput : ShaInput) (answer : Digest256) :
    OperationalRequestTargetHit seen history currentInput answer ↔
      answer ∈ operationalRequestTargets seen history currentInput := by
  constructor
  · intro hit
    cases hit with
    | priorFullOutput member =>
        exact Finset.mem_union_left _
          ((operational_target_hit_iff_mem seen history answer).mp
            (.priorFullOutput member))
    | priorLiteralPrefix record member prefixProof =>
        exact Finset.mem_union_left _
          ((operational_target_hit_iff_mem seen history answer).mp
            (.literalPrefix record member prefixProof))
    | currentLiteralPrefix prefixProof =>
        exact Finset.mem_union_right _
          ((mem_one_input_literal_targets_iff answer currentInput).mpr
            prefixProof)
  · intro member
    rcases Finset.mem_union.mp member with prior | current
    · cases (operational_target_hit_iff_mem seen history answer).mpr prior with
      | priorFullOutput member => exact .priorFullOutput member
      | literalPrefix record recordMember prefixProof =>
          exact .priorLiteralPrefix record recordMember prefixProof
    · exact .currentLiteralPrefix
        ((mem_one_input_literal_targets_iff answer currentInput).mp current)

/-! ## Pause before the next missing oracle query -/

def HistoryTotalCoherent (state : OracleState) : Prop :=
  state.history.length = state.totalCalls

theorem empty_oracle_history_total_coherent :
    HistoryTotalCoherent emptyOracle := by
  rfl

def cachedQueryState (actor : QueryActor) (state : OracleState)
    (input : ShaInput)
    (entry : AspisK1.V7FsAokExperiment.TableEntry) : OracleState :=
  let record : QueryRecord :=
    { input := input
      output := entry.output
      actor := actor
      origin := cachedOrigin entry.source }
  { state with
    history := state.history ++ [record]
    totalCalls := state.totalCalls + 1 }

def freshQueryState (actor : QueryActor) (state : OracleState)
    (input : ShaInput) (output : ShaOutput) : OracleState :=
  let entry : AspisK1.V7FsAokExperiment.TableEntry :=
    { input := input, output := output, source := .fresh }
  let record : QueryRecord :=
    { input := input, output := output, actor := actor, origin := .fresh }
  { table := state.table ++ [entry]
    history := state.history ++ [record]
    programmingHistory := state.programmingHistory
    totalCalls := state.totalCalls + 1
    freshCalls := state.freshCalls + 1 }

theorem cached_query_state_preserves_history_total_coherent
    (actor : QueryActor) (state : OracleState) (input : ShaInput)
    (entry : AspisK1.V7FsAokExperiment.TableEntry)
    (coherent : HistoryTotalCoherent state) :
    HistoryTotalCoherent (cachedQueryState actor state input entry) := by
  unfold HistoryTotalCoherent at coherent ⊢
  unfold cachedQueryState
  simp only [List.length_append, List.length_singleton]
  rw [coherent]

theorem fresh_query_state_preserves_history_total_coherent
    (actor : QueryActor) (state : OracleState) (input : ShaInput)
    (output : ShaOutput)
    (coherent : HistoryTotalCoherent state) :
    HistoryTotalCoherent (freshQueryState actor state input output) := by
  unfold HistoryTotalCoherent at coherent ⊢
  unfold freshQueryState
  simp only [List.length_append, List.length_singleton]
  rw [coherent]

/-- Result of executing cached queries and stopping immediately before the
next missing query.  The request constructor retains the residual
continuation that `MachineRun` otherwise erases on controller refusal. -/
inductive SeekNextFreshResult (Result : Type*) (limits : OracleLimits) where
  | returned (result : Result) (state : OracleState) (steps : Nat)
  | explicitAbort (reason : OracleAbort) (state : OracleState) (steps : Nat)
  | resourceAbort (reason : OracleAbort) (state : OracleState) (steps : Nat)
  | outOfFuel (state : OracleState) (steps : Nat)
  | request (state : OracleState) (input : ShaInput)
      (next : ShaOutput → OracleMachine Result)
      (remainingFuel steps : Nat)
      (coherent : HistoryTotalCoherent state)
      (totalRoom : state.totalCalls < limits.totalCalls)
      (freshRoom : state.freshCalls < limits.freshCalls)
      (missing : lookupEntry state input = none)

def SeekNextFreshResult.addCompletedQuery
    {Result : Type*} {limits : OracleLimits} :
    SeekNextFreshResult Result limits → SeekNextFreshResult Result limits
  | .returned result state steps => .returned result state (steps + 1)
  | .explicitAbort reason state steps =>
      .explicitAbort reason state (steps + 1)
  | .resourceAbort reason state steps =>
      .resourceAbort reason state (steps + 1)
  | .outOfFuel state steps => .outOfFuel state (steps + 1)
  | .request state input next remainingFuel steps coherent totalRoom freshRoom
      missing =>
      .request state input next remainingFuel (steps + 1) coherent totalRoom
        freshRoom missing

/-- Execute cached queries but never ask a controller for a missing answer. -/
def seekNextFresh {Result : Type*}
    (limits : OracleLimits) (actor : QueryActor) :
    (fuel : Nat) → (state : OracleState) → OracleMachine Result →
      HistoryTotalCoherent state → SeekNextFreshResult Result limits
  | _, state, .pure result, _ => .returned result state 0
  | _, state, .abort reason, _ => .explicitAbort reason state 0
  | 0, state, .query _ _, _ => .outOfFuel state 0
  | fuel + 1, state, .query input next, coherent =>
      if totalBlocked : state.totalCalls ≥ limits.totalCalls then
        .resourceAbort .totalCallBudget state 1
      else
        match found : lookupEntry state input with
        | some entry =>
            (seekNextFresh limits actor fuel
              (cachedQueryState actor state input entry) (next entry.output)
              (cached_query_state_preserves_history_total_coherent actor state
                input entry coherent)).addCompletedQuery
        | none =>
            if freshBlocked : state.freshCalls ≥ limits.freshCalls then
              .resourceAbort .freshCallBudget state 1
            else
              .request state input next fuel 0 coherent
                (Nat.lt_of_not_ge totalBlocked)
                (Nat.lt_of_not_ge freshBlocked) found

/-- Installing a supplied answer at a paused request is the exact fresh branch
of `queryOracle`. -/
theorem query_oracle_answer_at_seek_request_exact
    (limits : OracleLimits) (actor : QueryActor)
    (state : OracleState) (input : ShaInput)
    (totalRoom : state.totalCalls < limits.totalCalls)
    (freshRoom : state.freshCalls < limits.freshCalls)
    (missing : lookupEntry state input = none)
    (output : ShaOutput) :
    queryOracle (fun _ _ => .answer output) limits actor state input =
      .ok (output, freshQueryState actor state input output) := by
  simp [queryOracle, Nat.not_le.mpr totalRoom, missing,
    Nat.not_le.mpr freshRoom, freshQueryState]

/-! ## Nonanticipating machine tree -/

def operationalCapsFrom : Nat → Nat → Nat → List Nat
  | _step, 0, _globalOracleCalls => []
  | step, remaining + 1, globalOracleCalls =>
      (step + globalOracleCalls) ::
        operationalCapsFrom (step + 1) remaining globalOracleCalls

@[simp] theorem operational_caps_from_zero
    (step globalOracleCalls : Nat) :
    operationalCapsFrom step 0 globalOracleCalls = [] := by
  rfl

theorem operational_caps_from_succ
    (step remaining globalOracleCalls : Nat) :
    operationalCapsFrom step (remaining + 1) globalOracleCalls =
      (step + globalOracleCalls) ::
        operationalCapsFrom (step + 1) remaining globalOracleCalls := by
  rfl

theorem operational_caps_from_eq_range_map
    (step remaining globalOracleCalls : Nat) :
    operationalCapsFrom step remaining globalOracleCalls =
      (List.range' step remaining).map fun prior =>
        prior + globalOracleCalls := by
  induction remaining generalizing step with
  | zero => simp [operationalCapsFrom]
  | succ remaining ih =>
      rw [operational_caps_from_succ, List.range'_succ, List.map_cons,
        ih (step + 1)]

inductive MachineCausalCursor (Result : Type*) where
  | live (state : OracleState) (program : OracleMachine Result) (fuel : Nat)
      (coherent : HistoryTotalCoherent state)
  | halted

/-- At most `remaining` fresh answers are exposed.  `seekNextFresh` first
executes every cached query, so the target set at a live node contains only
the history and pending input available before that node's answer.  If the
program halts early, empty nodes pad the tree to the declared exposure cap. -/
noncomputable def operationalMachineTargetTreeFrom
    {Result : Type*} (limits : OracleLimits) (actor : QueryActor)
    (globalOracleCalls : Nat)
    (limitBound : limits.totalCalls ≤ globalOracleCalls) :
    (step remaining : Nat) →
      (seen : Finset Digest256) → seen.card ≤ step →
      MachineCausalCursor Result →
      CausalTargetTree Digest256
        (operationalCapsFrom step remaining globalOracleCalls)
  | _step, 0, _seen, _seenBound, _cursor => .done
  | step, remaining + 1, seen, seenBound, .halted =>
      .step ∅ (by simp) fun _answer =>
        operationalMachineTargetTreeFrom limits actor globalOracleCalls
          limitBound (step + 1) remaining seen
          (seenBound.trans (Nat.le_add_right step 1))
          (.halted : MachineCausalCursor Result)
  | step, remaining + 1, seen, seenBound,
      .live state program fuel coherent =>
      match seekNextFresh limits actor fuel state program coherent with
      | .returned _result _finalState _steps =>
          .step ∅ (by simp) fun _answer =>
            operationalMachineTargetTreeFrom limits actor globalOracleCalls
              limitBound (step + 1) remaining seen
              (seenBound.trans (Nat.le_add_right step 1))
              (.halted : MachineCausalCursor Result)
      | .explicitAbort _reason _finalState _steps =>
          .step ∅ (by simp) fun _answer =>
            operationalMachineTargetTreeFrom limits actor globalOracleCalls
              limitBound (step + 1) remaining seen
              (seenBound.trans (Nat.le_add_right step 1))
              (.halted : MachineCausalCursor Result)
      | .resourceAbort _reason _finalState _steps =>
          .step ∅ (by simp) fun _answer =>
            operationalMachineTargetTreeFrom limits actor globalOracleCalls
              limitBound (step + 1) remaining seen
              (seenBound.trans (Nat.le_add_right step 1))
              (.halted : MachineCausalCursor Result)
      | .outOfFuel _finalState _steps =>
          .step ∅ (by simp) fun _answer =>
            operationalMachineTargetTreeFrom limits actor globalOracleCalls
              limitBound (step + 1) remaining seen
              (seenBound.trans (Nat.le_add_right step 1))
              (.halted : MachineCausalCursor Result)
      | .request requestState input next remainingFuel _steps requestCoherent
          totalRoom _freshRoom _missing => by
          have requestWithinGlobal :
              requestState.history.length + 1 ≤ globalOracleCalls := by
            unfold HistoryTotalCoherent at requestCoherent
            rw [requestCoherent]
            exact (Nat.succ_le_of_lt totalRoom).trans limitBound
          exact .step
            (operationalRequestTargets seen requestState.history input)
            (operational_request_targets_within_step_plus_global_cap
              seen requestState.history input step globalOracleCalls
                seenBound requestWithinGlobal)
            fun answer =>
              operationalMachineTargetTreeFrom limits actor
                globalOracleCalls limitBound (step + 1) remaining
                (insert answer seen)
                ((Finset.card_insert_le answer seen).trans
                  (Nat.add_le_add_right seenBound 1))
                (.live (freshQueryState actor requestState input answer)
                  (next answer) remainingFuel
                  (fresh_query_state_preserves_history_total_coherent
                    actor requestState input answer requestCoherent))

/-- Root form with exactly the cap list consumed by the global arithmetic
module. -/
noncomputable def operationalMachineTargetTree
    {Result : Type*} (limits : OracleLimits) (actor : QueryActor)
    (globalOracleCalls full256FreshExposures : Nat)
    (limitBound : limits.totalCalls ≤ globalOracleCalls)
    (state : OracleState) (program : OracleMachine Result) (fuel : Nat)
    (coherent : HistoryTotalCoherent state) :
    CausalTargetTree Digest256
      (tag73GlobalForwardReferenceCaps full256FreshExposures
        globalOracleCalls) := by
  unfold tag73GlobalForwardReferenceCaps
  rw [← operational_caps_from_eq_range_map 0 full256FreshExposures
    globalOracleCalls]
  exact operationalMachineTargetTreeFrom limits actor globalOracleCalls
    limitBound 0 full256FreshExposures ∅ (by simp)
      (.live state program fuel coherent)

/-- Actual fixed-hidden-tape start program, empty oracle, and adversary actor.
The tree is a function of the hidden tape but not of any unseen fresh answer. -/
noncomputable def emptySourceOperationalTargetTree
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    (source : EmptyOracleFirstRunSource HiddenTape TapeIdentity Observation
      Statement Proof Result)
    (globalOracleCalls full256FreshExposures : Nat)
    (limitBound : source.oracleLimits.totalCalls ≤ globalOracleCalls) :
    CausalTargetTree Digest256
      (tag73GlobalForwardReferenceCaps full256FreshExposures
        globalOracleCalls) :=
  operationalMachineTargetTree source.oracleLimits .adversary
    globalOracleCalls full256FreshExposures limitBound emptyOracle
    (source.blackBox.start source.hiddenTape source.observation)
    source.adversaryFuel empty_oracle_history_total_coherent

/-! ## Independent tape-driven target-hit semantics -/

/-- Direct operational target-hit evaluator.  It repeats the same
`seekNextFresh` transition relation as the tree builder, but its result is a
predicate phrased with `OperationalRequestTargetHit`, not `everHits` or target
finset membership.  This is not named or asserted to be an actual compiler
abort/failure event; the protocol-specific abort-to-hit implication remains a
separate integration theorem. -/
noncomputable def OperationalMachineTargetHitFrom
    {Result : Type*} (limits : OracleLimits) (actor : QueryActor)
    (globalOracleCalls : Nat)
    (limitBound : limits.totalCalls ≤ globalOracleCalls) :
    (step remaining : Nat) →
      (seen : Finset Digest256) → seen.card ≤ step →
      MachineCausalCursor Result →
      FreshAnswerTape Digest256
        (operationalCapsFrom step remaining globalOracleCalls).length → Prop
  | _step, 0, _seen, _seenBound, _cursor, _tape => False
  | step, remaining + 1, seen, seenBound, .halted, tape =>
      OperationalMachineTargetHitFrom limits actor globalOracleCalls
        limitBound (step + 1) remaining seen
          (seenBound.trans (Nat.le_add_right step 1))
          (.halted : MachineCausalCursor Result) tape.2
  | step, remaining + 1, seen, seenBound,
      .live state program fuel coherent, tape =>
      match seekNextFresh limits actor fuel state program coherent with
      | .returned _result _finalState _steps =>
          OperationalMachineTargetHitFrom limits actor globalOracleCalls
            limitBound (step + 1) remaining seen
              (seenBound.trans (Nat.le_add_right step 1))
              (.halted : MachineCausalCursor Result) tape.2
      | .explicitAbort _reason _finalState _steps =>
          OperationalMachineTargetHitFrom limits actor globalOracleCalls
            limitBound (step + 1) remaining seen
              (seenBound.trans (Nat.le_add_right step 1))
              (.halted : MachineCausalCursor Result) tape.2
      | .resourceAbort _reason _finalState _steps =>
          OperationalMachineTargetHitFrom limits actor globalOracleCalls
            limitBound (step + 1) remaining seen
              (seenBound.trans (Nat.le_add_right step 1))
              (.halted : MachineCausalCursor Result) tape.2
      | .outOfFuel _finalState _steps =>
          OperationalMachineTargetHitFrom limits actor globalOracleCalls
            limitBound (step + 1) remaining seen
              (seenBound.trans (Nat.le_add_right step 1))
              (.halted : MachineCausalCursor Result) tape.2
      | .request requestState input next remainingFuel _steps requestCoherent
          _totalRoom _freshRoom _missing =>
          OperationalRequestTargetHit seen requestState.history input tape.1 ∨
            OperationalMachineTargetHitFrom limits actor
              globalOracleCalls limitBound (step + 1) remaining
              (insert tape.1 seen)
              ((Finset.card_insert_le tape.1 seen).trans
                (Nat.add_le_add_right seenBound 1))
              (.live (freshQueryState actor requestState input tape.1)
                (next tape.1) remainingFuel
                (fresh_query_state_preserves_history_total_coherent actor
                  requestState input tape.1 requestCoherent)) tape.2

noncomputable def OperationalMachineTargetHit
    {Result : Type*} (limits : OracleLimits) (actor : QueryActor)
    (globalOracleCalls full256FreshExposures : Nat)
    (limitBound : limits.totalCalls ≤ globalOracleCalls)
    (state : OracleState) (program : OracleMachine Result) (fuel : Nat)
    (coherent : HistoryTotalCoherent state)
    (tape : FreshAnswerTape Digest256
      (tag73GlobalForwardReferenceCaps full256FreshExposures
        globalOracleCalls).length) : Prop := by
  unfold tag73GlobalForwardReferenceCaps at tape
  rw [← operational_caps_from_eq_range_map 0 full256FreshExposures
    globalOracleCalls] at tape
  exact OperationalMachineTargetHitFrom limits actor globalOracleCalls
    limitBound 0 full256FreshExposures ∅ (by simp)
      (.live state program fuel coherent) tape

/-- The independently phrased run event is exactly the hit event of the
constructed nonanticipating target tree. -/
theorem operational_machine_target_tree_from_exact
    {Result : Type*} (limits : OracleLimits) (actor : QueryActor)
    (globalOracleCalls : Nat)
    (limitBound : limits.totalCalls ≤ globalOracleCalls)
    (step remaining : Nat) (seen : Finset Digest256)
    (seenBound : seen.card ≤ step) (cursor : MachineCausalCursor Result)
    (tape : FreshAnswerTape Digest256
      (operationalCapsFrom step remaining globalOracleCalls).length) :
    (operationalMachineTargetTreeFrom limits actor globalOracleCalls
      limitBound step remaining seen seenBound cursor).everHits tape ↔
      OperationalMachineTargetHitFrom limits actor globalOracleCalls
        limitBound step remaining seen seenBound cursor tape := by
  induction remaining generalizing step seen cursor with
  | zero => rfl
  | succ remaining ih =>
      change Digest256 × FreshAnswerTape Digest256
        (operationalCapsFrom (step + 1) remaining globalOracleCalls).length
          at tape
      cases cursor with
      | halted =>
          change (tape.1 ∈ (∅ : Finset Digest256) ∨
              (operationalMachineTargetTreeFrom limits actor globalOracleCalls
                limitBound (step + 1) remaining seen
                (seenBound.trans (Nat.le_add_right step 1))
                (.halted : MachineCausalCursor Result)).everHits tape.2) ↔
            OperationalMachineTargetHitFrom limits actor
              globalOracleCalls limitBound (step + 1) remaining seen
              (seenBound.trans (Nat.le_add_right step 1))
              (.halted : MachineCausalCursor Result) tape.2
          simpa using ih (step + 1) seen
            (seenBound.trans (Nat.le_add_right step 1))
            (.halted : MachineCausalCursor Result) tape.2
      | live state program fuel coherent =>
          cases hseek : seekNextFresh limits actor fuel state program coherent with
          | returned result finalState steps =>
              simp only [operationalMachineTargetTreeFrom,
                OperationalMachineTargetHitFrom, hseek]
              change (tape.1 ∈ (∅ : Finset Digest256) ∨
                  (operationalMachineTargetTreeFrom limits actor
                    globalOracleCalls limitBound (step + 1) remaining seen
                    (seenBound.trans (Nat.le_add_right step 1))
                    (.halted : MachineCausalCursor Result)).everHits tape.2) ↔
                OperationalMachineTargetHitFrom limits actor
                  globalOracleCalls limitBound (step + 1) remaining seen
                  (seenBound.trans (Nat.le_add_right step 1))
                  (.halted : MachineCausalCursor Result) tape.2
              simpa using ih (step + 1) seen
                (seenBound.trans (Nat.le_add_right step 1))
                (.halted : MachineCausalCursor Result) tape.2
          | explicitAbort reason finalState steps =>
              simp only [operationalMachineTargetTreeFrom,
                OperationalMachineTargetHitFrom, hseek]
              change (tape.1 ∈ (∅ : Finset Digest256) ∨
                  (operationalMachineTargetTreeFrom limits actor
                    globalOracleCalls limitBound (step + 1) remaining seen
                    (seenBound.trans (Nat.le_add_right step 1))
                    (.halted : MachineCausalCursor Result)).everHits tape.2) ↔
                OperationalMachineTargetHitFrom limits actor
                  globalOracleCalls limitBound (step + 1) remaining seen
                  (seenBound.trans (Nat.le_add_right step 1))
                  (.halted : MachineCausalCursor Result) tape.2
              simpa using ih (step + 1) seen
                (seenBound.trans (Nat.le_add_right step 1))
                (.halted : MachineCausalCursor Result) tape.2
          | resourceAbort reason finalState steps =>
              simp only [operationalMachineTargetTreeFrom,
                OperationalMachineTargetHitFrom, hseek]
              change (tape.1 ∈ (∅ : Finset Digest256) ∨
                  (operationalMachineTargetTreeFrom limits actor
                    globalOracleCalls limitBound (step + 1) remaining seen
                    (seenBound.trans (Nat.le_add_right step 1))
                    (.halted : MachineCausalCursor Result)).everHits tape.2) ↔
                OperationalMachineTargetHitFrom limits actor
                  globalOracleCalls limitBound (step + 1) remaining seen
                  (seenBound.trans (Nat.le_add_right step 1))
                  (.halted : MachineCausalCursor Result) tape.2
              simpa using ih (step + 1) seen
                (seenBound.trans (Nat.le_add_right step 1))
                (.halted : MachineCausalCursor Result) tape.2
          | outOfFuel finalState steps =>
              simp only [operationalMachineTargetTreeFrom,
                OperationalMachineTargetHitFrom, hseek]
              change (tape.1 ∈ (∅ : Finset Digest256) ∨
                  (operationalMachineTargetTreeFrom limits actor
                    globalOracleCalls limitBound (step + 1) remaining seen
                    (seenBound.trans (Nat.le_add_right step 1))
                    (.halted : MachineCausalCursor Result)).everHits tape.2) ↔
                OperationalMachineTargetHitFrom limits actor
                  globalOracleCalls limitBound (step + 1) remaining seen
                  (seenBound.trans (Nat.le_add_right step 1))
                  (.halted : MachineCausalCursor Result) tape.2
              simpa using ih (step + 1) seen
                (seenBound.trans (Nat.le_add_right step 1))
                (.halted : MachineCausalCursor Result) tape.2
          | request requestState input next remainingFuel steps requestCoherent
              totalRoom freshRoom missing =>
              have tail := ih (step + 1) (insert tape.1 seen)
                ((Finset.card_insert_le tape.1 seen).trans
                  (Nat.add_le_add_right seenBound 1))
                (.live (freshQueryState actor requestState input tape.1)
                  (next tape.1) remainingFuel
                  (fresh_query_state_preserves_history_total_coherent actor
                    requestState input tape.1 requestCoherent)) tape.2
              simp only [operationalMachineTargetTreeFrom,
                OperationalMachineTargetHitFrom, hseek]
              change (tape.1 ∈
                    operationalRequestTargets seen requestState.history input ∨
                  (operationalMachineTargetTreeFrom limits actor
                    globalOracleCalls limitBound (step + 1) remaining
                    (insert tape.1 seen)
                    ((Finset.card_insert_le tape.1 seen).trans
                      (Nat.add_le_add_right seenBound 1))
                    (.live (freshQueryState actor requestState input tape.1)
                      (next tape.1) remainingFuel
                      (fresh_query_state_preserves_history_total_coherent actor
                        requestState input tape.1 requestCoherent))).everHits
                    tape.2) ↔
                (OperationalRequestTargetHit seen requestState.history input
                    tape.1 ∨
                  OperationalMachineTargetHitFrom limits actor
                    globalOracleCalls limitBound (step + 1) remaining
                    (insert tape.1 seen)
                    ((Finset.card_insert_le tape.1 seen).trans
                      (Nat.add_le_add_right seenBound 1))
                    (.live (freshQueryState actor requestState input tape.1)
                      (next tape.1) remainingFuel
                      (fresh_query_state_preserves_history_total_coherent actor
                        requestState input tape.1 requestCoherent)) tape.2)
              exact or_congr
                (operational_request_target_hit_iff_mem seen
                  requestState.history input tape.1).symm tail

/-! ## Explicit uniform coordinates for an atomic programmed pair -/

/-- Replace the two arbitrary fork-value fields by two explicit fresh-answer
tape coordinates.  This is the deterministic scheduler shape required before
the uniform-tape counting theorem can be applied to programmed pair values. -/
def atomicPairConfigurationFromFreshTape
    (template : AtomicPairReplayConfiguration)
    (forkTape : FreshAnswerTape Digest256 2) :
    AtomicPairReplayConfiguration :=
  { template with
    forkOutput := forkTape.1
    forkAdvance := forkTape.2.1 }

@[simp] theorem atomic_pair_configuration_from_fresh_tape_values
    (template : AtomicPairReplayConfiguration)
    (forkTape : FreshAnswerTape Digest256 2) :
    (atomicPairConfigurationFromFreshTape template forkTape).forkOutput =
        forkTape.1 ∧
      (atomicPairConfigurationFromFreshTape template forkTape).forkAdvance =
        forkTape.2.1 := by
  exact ⟨rfl, rfl⟩

/-- A two-coordinate causal tree for a pair that is programmed only after a
first-run history has been frozen.  At the first coordinate, targets use only
the earlier outputs and frozen history.  At the second coordinate, the first
fork output is additionally available.  No completed history depending on
either coordinate is consulted. -/
noncomputable def frozenHistoryAtomicForkTargetTree
    (history : List QueryRecord) (seen : Finset Digest256)
    (step globalOracleCalls : Nat)
    (seenBound : seen.card ≤ step)
    (historyBound : history.length ≤ globalOracleCalls) :
    CausalTargetTree Digest256
      (operationalCapsFrom step 2 globalOracleCalls) := by
  have firstBound :
      (operationalHistoryTargets seen history).card ≤
        step + globalOracleCalls :=
    (operational_history_targets_card_le seen history).trans
      (Nat.add_le_add seenBound historyBound)
  refine .step (operationalHistoryTargets seen history) firstBound ?_
  intro forkOutput
  have insertedBound : (insert forkOutput seen).card ≤ step + 1 :=
    (Finset.card_insert_le forkOutput seen).trans
      (Nat.add_le_add_right seenBound 1)
  have secondBound :
      (operationalHistoryTargets (insert forkOutput seen) history).card ≤
        (step + 1) + globalOracleCalls :=
    (operational_history_targets_card_le (insert forkOutput seen) history).trans
      (Nat.add_le_add insertedBound historyBound)
  exact .step (operationalHistoryTargets (insert forkOutput seen) history)
    secondBound fun _forkAdvance => .done

/-- Exact constructor-level meaning of a scheduled-pair tree hit. -/
theorem frozen_history_atomic_fork_target_tree_hit_iff
    (history : List QueryRecord) (seen : Finset Digest256)
    (step globalOracleCalls : Nat)
    (seenBound : seen.card ≤ step)
    (historyBound : history.length ≤ globalOracleCalls)
    (forkTape : FreshAnswerTape Digest256 2) :
    (frozenHistoryAtomicForkTargetTree history seen step globalOracleCalls
      seenBound historyBound).everHits forkTape ↔
      OperationalTargetHit seen history forkTape.1 ∨
        OperationalTargetHit (insert forkTape.1 seen) history
          forkTape.2.1 := by
  change (forkTape.1 ∈ operationalHistoryTargets seen history ∨
      (forkTape.2.1 ∈
        operationalHistoryTargets (insert forkTape.1 seen) history ∨ False)) ↔
    OperationalTargetHit seen history forkTape.1 ∨
      OperationalTargetHit (insert forkTape.1 seen) history forkTape.2.1
  simp only [or_false, operational_target_hit_iff_mem]

/-- The pair-occurrence branch is selected entirely from frozen Q1 before
either scheduled fork coordinate is read.  The two assigned answers are then
exactly the two tape coordinates. -/
theorem generated_pair_occurrence_is_frozen_before_scheduled_fork
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (stateAtAdversaryHalt : OracleState)
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (occurrence : PairOccurrenceSplit)
    (found : firstGeneratedPairOccurrenceInFrozenQ1 stateAtAdversaryHalt
      execution generated = some occurrence)
    (template : AtomicPairReplayConfiguration)
    (forkTape : FreshAnswerTape Digest256 2) :
    freezeAdversaryQ1 stateAtAdversaryHalt =
        occurrence.before ++ occurrence.chosen :: occurrence.after ∧
      (∀ prior ∈ occurrence.before,
        prior.input ≠ generatedPairInput execution generated .output ∧
        prior.input ≠ generatedPairInput execution generated .advance) ∧
      (occurrence.chosen.input =
          generatedPairInput execution generated .output ∨
        occurrence.chosen.input =
          generatedPairInput execution generated .advance) ∧
      (atomicPairConfigurationFromFreshTape template forkTape).forkOutput =
        forkTape.1 ∧
      (atomicPairConfigurationFromFreshTape template forkTape).forkAdvance =
        forkTape.2.1 := by
  have frozen := first_generated_pair_occurrence_in_frozen_q1_is_exact
    stateAtAdversaryHalt execution generated occurrence found
  exact ⟨frozen.1, frozen.2.1, frozen.2.2.1, rfl, rfl⟩

/-- In the no-pair/literal-forward-reference branch, frozen Q1 is a causal
target for the independently scheduled advance coordinate.  `noPair` selects
the actual Tag-73 branch; the tree contains Q1 before reading either fork
coordinate. -/
theorem generated_no_pair_literal_reference_hits_scheduled_fork_tree
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (stateAtAdversaryHalt : OracleState)
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (occurrence : StatePrefixOccurrence)
    (template : AtomicPairReplayConfiguration)
    (forkTape : FreshAnswerTape Digest256 2)
    (seen : Finset Digest256) (step globalOracleCalls : Nat)
    (seenBound : seen.card ≤ step)
    (historyBound :
      (freezeAdversaryQ1 stateAtAdversaryHalt).length ≤ globalOracleCalls)
    (noPair : firstGeneratedPairOccurrenceInFrozenQ1 stateAtAdversaryHalt
      execution generated = none)
    (found : firstStatePrefixOccurrence
      (atomicPairConfigurationFromFreshTape template forkTape).forkAdvance
      (freezeAdversaryQ1 stateAtAdversaryHalt) = some occurrence) :
    (frozenHistoryAtomicForkTargetTree
      (freezeAdversaryQ1 stateAtAdversaryHalt) seen step globalOracleCalls
      seenBound historyBound).everHits forkTape := by
  have found' : firstStatePrefixOccurrence forkTape.2.1
      (freezeAdversaryQ1 stateAtAdversaryHalt) = some occurrence := by
    simpa [atomicPairConfigurationFromFreshTape] using found
  have exactReference := generated_first_literal_forward_reference_is_exact
    stateAtAdversaryHalt execution generated forkTape.2.1 occurrence noPair
      found'
  have chosenMember : occurrence.chosen ∈
      freezeAdversaryQ1 stateAtAdversaryHalt := by
    rw [exactReference.1]
    simp
  apply (frozen_history_atomic_fork_target_tree_hit_iff
    (freezeAdversaryQ1 stateAtAdversaryHalt) seen step globalOracleCalls
      seenBound historyBound forkTape).mpr
  right
  exact .literalPrefix occurrence.chosen chosenMember exactReference.2.2.1

/-! ## Exact generated-pair injection -/

theorem generated_pair_state_prefixes_pair_input
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag) (half : SqueezeHalf) :
    HasLiteralStatePrefix (generatedPairState execution generated)
      (generatedPairInput execution generated half) := by
  cases half <;>
    simp [HasLiteralStatePrefix, generatedPairInput,
      generatedPairState, bytes]

private theorem lookup_entry_some_has_exact_input_and_membership
    (state : OracleState) (input : ShaInput)
    (entry : AspisK1.V7FsAokExperiment.TableEntry)
    (found : lookupEntry state input = some entry) :
    entry.input = input ∧ entry ∈ state.table := by
  unfold lookupEntry at found
  have predicate := List.find?_some found
  exact ⟨of_decide_eq_true predicate, List.mem_of_find?_eq_some found⟩

theorem covered_pair_lookup_is_literal_history_target
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (actor : QueryActor) (state : OracleState) (half : SqueezeHalf)
    (covered : TableCoveredByActorHistory actor state)
    (entry : AspisK1.V7FsAokExperiment.TableEntry)
    (found : lookupEntry state
      (generatedPairInput execution generated half) = some entry) :
    ∃ record ∈ state.history,
      record.actor = actor ∧
      HasLiteralStatePrefix (generatedPairState execution generated)
        record.input := by
  obtain ⟨entryInput, entryMember⟩ :=
    lookup_entry_some_has_exact_input_and_membership state
      (generatedPairInput execution generated half) entry found
  obtain ⟨record, recordMember, recordActor, recordInput, _recordOutput⟩ :=
    covered entry entryMember
  refine ⟨record, recordMember, recordActor, ?_⟩
  rw [recordInput, entryInput]
  exact generated_pair_state_prefixes_pair_input execution generated half

private theorem program_pair_in_order_ne_input_conflict
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : AtomicPairReplayConfiguration)
    (firstHalf secondHalf conflictHalf : SqueezeHalf)
    (state : OracleState) :
    programPairInOrder execution generated configuration firstHalf secondHalf
        state ≠ .error (.inputConflict conflictHalf) := by
  intro impossible
  unfold programPairInOrder at impossible
  cases firstProgram : programOracle configuration.oracleLimits
      .extractorReplay state
      (programmingForHalf execution generated configuration firstHalf) with
  | error reason =>
      simp [firstProgram] at impossible
  | ok afterFirst =>
      cases secondProgram : programOracle configuration.oracleLimits
          .extractorReplay afterFirst
          (programmingForHalf execution generated configuration secondHalf) with
      | error reason =>
          simp [firstProgram, secondProgram] at impossible
      | ok afterBoth =>
          simp [firstProgram, secondProgram] at impossible

theorem program_atomic_pair_input_conflict_has_lookup
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : AtomicPairReplayConfiguration)
    (state : OracleState) (half : SqueezeHalf)
    (conflict : programAtomicPair execution generated configuration state =
      .error (.inputConflict half)) :
    ∃ entry : AspisK1.V7FsAokExperiment.TableEntry,
      lookupEntry state (generatedPairInput execution generated half) =
        some entry := by
  have distinct := generated_pair_inputs_are_distinct execution generated
  simp only [programAtomicPair, distinct, if_false] at conflict
  cases outputFound : lookupEntry state
      (generatedPairInput execution generated .output) with
  | some entry =>
      rw [outputFound] at conflict
      simp only [Except.error.injEq,
        AtomicPairReplayFailure.inputConflict.injEq] at conflict
      subst half
      exact ⟨entry, outputFound⟩
  | none =>
      rw [outputFound] at conflict
      cases advanceFound : lookupEntry state
          (generatedPairInput execution generated .advance) with
      | some entry =>
          rw [advanceFound] at conflict
          simp only [Except.error.injEq,
            AtomicPairReplayFailure.inputConflict.injEq] at conflict
          subst half
          exact ⟨entry, advanceFound⟩
      | none =>
          rw [advanceFound] at conflict
          cases order : configuration.programmingOrder with
          | outputThenAdvance =>
              exact (program_pair_in_order_ne_input_conflict execution
                generated configuration .output .advance half state
                (by simpa [order] using conflict)).elim
          | advanceThenOutput =>
              exact (program_pair_in_order_ne_input_conflict execution
                generated configuration .advance .output half state
                (by simpa [order] using conflict)).elim

/-- Concrete deterministic classification of an actual pair-programming
conflict as a literal reference in an already covered history.  This theorem
does not call it a causal probability event; that additionally requires the
history to predate the random value being charged. -/
theorem covered_program_atomic_pair_conflict_is_literal_history_reference
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : AtomicPairReplayConfiguration)
    (actor : QueryActor) (state : OracleState) (half : SqueezeHalf)
    (covered : TableCoveredByActorHistory actor state)
    (conflict : programAtomicPair execution generated configuration state =
      .error (.inputConflict half))
    : ∃ record ∈ state.history,
      record.actor = actor ∧
      HasLiteralStatePrefix (generatedPairState execution generated)
        record.input := by
  obtain ⟨entry, found⟩ := program_atomic_pair_input_conflict_has_lookup
    execution generated configuration state half conflict
  exact covered_pair_lookup_is_literal_history_target execution generated
    actor state half covered entry found

/-- Hidden-tape specialization: because this source starts at the genuinely
empty oracle, its post-adversary table is proved to be covered by frozen Q1. -/
theorem empty_source_pair_programming_conflict_is_q1_literal_reference
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (source : EmptyOracleFirstRunSource HiddenTape TapeIdentity Observation
      Statement Proof Result)
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : AtomicPairReplayConfiguration)
    (half : SqueezeHalf)
    (conflict : programAtomicPair execution generated configuration
      source.postAdversaryState = .error (.inputConflict half))
    : ∃ record ∈ source.q1,
      HasLiteralStatePrefix (generatedPairState execution generated)
        record.input := by
  obtain ⟨entry, found⟩ := program_atomic_pair_input_conflict_has_lookup
    execution generated configuration source.postAdversaryState half conflict
  obtain ⟨record, member, actorEq, prefixProof⟩ :=
    covered_pair_lookup_is_literal_history_target execution generated
      .adversary source.postAdversaryState half
      (post_adversary_table_is_covered_by_q1_history source) entry found
  have q1Member : record ∈ source.q1 := by
    change record ∈ actorHistory .adversary source.postAdversaryState
    exact List.mem_filter.mpr ⟨member, by simpa [actorEq]⟩
  exact ⟨record, q1Member, prefixProof⟩

/-- Any executable literal-forward-reference occurrence maps directly to the
concrete frozen-history target set. -/
theorem literal_forward_reference_is_operational_target
    (stateAtAdversaryHalt : OracleState)
    (advanceAnswer : Digest256)
    (occurrence : StatePrefixOccurrence)
    (found : firstStatePrefixOccurrence advanceAnswer
      (freezeAdversaryQ1 stateAtAdversaryHalt) = some occurrence)
    (seen : Finset Digest256) :
    OperationalTargetHit seen (freezeAdversaryQ1 stateAtAdversaryHalt)
      advanceAnswer := by
  have specification := first_state_prefix_occurrence_spec advanceAnswer
    (freezeAdversaryQ1 stateAtAdversaryHalt) occurrence found
  have chosenMember : occurrence.chosen ∈
      freezeAdversaryQ1 stateAtAdversaryHalt := by
    rw [specification.1]
    simp
  exact .literalPrefix occurrence.chosen chosenMember specification.2.2

/-- Specialization to the first literal-forward-reference branch of one
generated squeeze.  Here `noPair` is used to select that concrete branch of
the Tag-73 trichotomy; the target remains the actual first Q1 record. -/
theorem generated_literal_forward_reference_is_operational_target
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (stateAtAdversaryHalt : OracleState)
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (advanceAnswer : Digest256)
    (occurrence : StatePrefixOccurrence)
    (noPair : firstGeneratedPairOccurrenceInFrozenQ1 stateAtAdversaryHalt
      execution generated = none)
    (found : firstStatePrefixOccurrence advanceAnswer
      (freezeAdversaryQ1 stateAtAdversaryHalt) = some occurrence)
    (seen : Finset Digest256) :
    OperationalTargetHit seen (freezeAdversaryQ1 stateAtAdversaryHalt)
      advanceAnswer := by
  have exactReference := generated_first_literal_forward_reference_is_exact
    stateAtAdversaryHalt execution generated advanceAnswer occurrence noPair
      found
  have chosenMember : occurrence.chosen ∈
      freezeAdversaryQ1 stateAtAdversaryHalt := by
    rw [exactReference.1]
    simp
  exact .literalPrefix occurrence.chosen chosenMember
    exactReference.2.2.1

/-! ## Strict `F,G` arithmetic and precise remaining projection gaps -/

theorem q1_bound_is_within_strict_global_call_cap
    (envelope : StrictTag73ResourceEnvelope) (history : List QueryRecord)
    (q1Bound : history.length ≤ envelope.q1Calls) :
    history.length ≤ strictGlobalOracleCallCap envelope := by
  unfold strictGlobalOracleCallCap
  omega

/-- The checkpoint side is now concrete: every generated pre-squeeze state is
the dummy zero or one of the exact replies in the accepted verifier execution.
What remains is to classify that reply as cached, programmed, or a particular
fresh tape coordinate. -/
theorem generated_pair_state_has_execution_digest_provenance
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag) :
    generatedPairState execution generated = zeroBytes 32 ∨
      generatedPairState execution generated ∈
        traceReplyDigests execution.trace :=
  generated_pair_state_is_zero_or_execution_reply execution generated

/-- If proof-visible data fix only a decoded output-half challenge, the exact
known target before raw verifier-output exposure is the decoder fiber.  Its
uniform mass is its cardinality divided by `2^256`, not automatically one
raw target. -/
theorem uniform_output_prediction_target_is_decoder_fiber
    {Challenge : Type*} [DecidableEq Challenge]
    (decode : Digest256 → Challenge) (challenge : Challenge) :
    uniformRawDigestLaw.toOuterMeasure (decodedFiber decode challenge) =
      (Fintype.card {output : Digest256 // decode output = challenge} : ENNReal) /
        ((2 : ENNReal) ^ 256) :=
  uniform_decoded_fiber_probability_exact decode challenge

/-- The independent advance query does not make a missing output-half query
an atomic singleton prediction.  A deployed bound therefore still needs an
exact accepted decoder-fiber cardinality or a stronger response property. -/
theorem advance_only_does_not_resolve_output_prediction
    {Challenge : Type*} (state : Digest256)
    (decode : Digest256 → Challenge) (challenge : Challenge) :
    ¬ AtomicSingletonPredictionReady (advanceOnlyProgram state) state decode
      challenge :=
  advance_only_is_not_atomic_singleton_ready state decode challenge

/-- Raw query history cannot supply the missing semantic dependency
provenance: two inputs with opposite provenance erase to the same bytes. -/
theorem operational_history_projection_does_not_determine_provenance
    (input : ShaInput) :
    ∃ independent derived : ProvenancedInput,
      independent.provenance = .independent ∧
      derived.provenance = .derivedFromAdvance ∧
      independent.erase = derived.erase :=
  raw_query_input_erases_dependency_provenance input

/-!
The remaining global theorem must schedule every invocation of
`programAtomicPair` with `atomicPairConfigurationFromFreshTape`, prove those
two coordinates are independent uniform coordinates in the global exposure
tape, and include them in `full256FreshExposures`.  Neither `programOracle`
nor `seekNextFresh` does this: the former records `.programmed` values and the
latter pauses only for missing `.fresh` queries.  It must additionally map
each concrete replay/coupling abort into a constructor above.  For an absent
output-half query, the target is the accepted decoder fiber unless a stronger
raw-output pinning theorem is proved; the independent advance half does not
make that fiber a singleton.
-/

#print axioms one_input_literal_targets_card_le_one
#print axioms history_literal_targets_card_le_length
#print axioms operational_target_hit_iff_mem
#print axioms operational_request_targets_card_le
#print axioms operational_request_targets_within_step_plus_global_cap
#print axioms operational_request_target_hit_iff_mem
#print axioms cached_query_state_preserves_history_total_coherent
#print axioms fresh_query_state_preserves_history_total_coherent
#print axioms query_oracle_answer_at_seek_request_exact
#print axioms operational_caps_from_eq_range_map
#print axioms operational_machine_target_tree_from_exact
#print axioms atomic_pair_configuration_from_fresh_tape_values
#print axioms frozen_history_atomic_fork_target_tree_hit_iff
#print axioms generated_pair_occurrence_is_frozen_before_scheduled_fork
#print axioms generated_no_pair_literal_reference_hits_scheduled_fork_tree
#print axioms generated_pair_state_prefixes_pair_input
#print axioms program_atomic_pair_input_conflict_has_lookup
#print axioms covered_program_atomic_pair_conflict_is_literal_history_reference
#print axioms empty_source_pair_programming_conflict_is_q1_literal_reference
#print axioms literal_forward_reference_is_operational_target
#print axioms generated_literal_forward_reference_is_operational_target
#print axioms q1_bound_is_within_strict_global_call_cap
#print axioms generated_pair_state_has_execution_digest_provenance
#print axioms uniform_output_prediction_target_is_decoder_fiber
#print axioms advance_only_does_not_resolve_output_prediction
#print axioms operational_history_projection_does_not_determine_provenance

end

end AspisK1.V7Tag73OperationalCausalInjection
