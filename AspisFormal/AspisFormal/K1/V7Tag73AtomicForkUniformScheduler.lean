import AspisFormal.K1.V7Tag73OperationalCausalInjection

/-!
# Adaptive uniform scheduler for Tag-73 full-256 exposures

The deployed replay code stores fork outputs in
`AtomicPairReplayConfiguration` and later inserts them as `.programmed`
oracle entries.  Those values are not exposed by the lazy-oracle controller.
This module puts ordinary missing-query answers and atomic programmed-pair
answers on one explicit finite uniform `Digest256` tape.

The scheduler is adaptive.  A returned machine run may choose the next
cursor, and completion of a fork pair passes the configuration built from
both newly exposed coordinates to its continuation.  Thus later histories,
programs, and forks may depend on earlier coordinates, while every target set
is fixed before its own coordinate is read.

Each machine node carries its own query actor and oracle limits, with a proof
that its total-call limit is below the shared global cap.  The same cursor can
therefore interleave adversary, verifier, and extractor-replay phases without
relabeling their query records.

The fixed strict cap is

`F = envelope.full256FreshExposures + 2 * envelope.restorationCount`.

The first term retains its documented meaning: fresh full-256 lazy-oracle
answers.  The second term is new and reserves two uniform coordinates for
every actual or padded restoration/fork slot.  Halting and transition-limit
branches are padded by empty target nodes, so they do not shorten the sampled
tape.

Both concrete programmed inputs are literal-prefix targets at each pair node.
Their two calls do not add an unexplained coefficient: the cursor carries
`frozenHistory.length + 2 ≤ G`, keeping those targets inside the same
per-exposure cap `i + G`.

This is still not the compiler-failure inclusion theorem.  The causal event
covers full-output collisions and literal-prefix targets.  Nonliteral
provenance and the accepted output-decoder fiber remain explicit boundaries.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73AtomicForkUniformScheduler

set_option maxRecDepth 8192

open MeasureTheory
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AtomicPairReplay
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73GlobalForwardReferenceBound
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73ResourceLazyOracle
open AspisK1.V7FsAokExperiment

noncomputable section

/-! ## Adaptive exposure cursor -/

/-- One adaptive cursor for both controller-supplied missing-query answers and
the two explicitly sampled values of an atomic programmed pair.

`forkPair` stores the history, both concrete pair inputs, and proof that those
two programmed calls still fit the global `G` bound before either pair
coordinate is exposed.  After the output coordinate, `forkAdvance` retains it
while waiting for the immediately following advance coordinate. -/
inductive UnifiedExposureCursor (globalOracleCalls : Nat) where
  | machine
      {MachineResult : Type}
      (limits : OracleLimits)
      (limitBound : limits.totalCalls ≤ globalOracleCalls)
      (actor : QueryActor)
      (state : OracleState)
      (program : OracleMachine MachineResult)
      (fuel : Nat)
      (coherent : HistoryTotalCoherent state)
      (onReturned : MachineResult → OracleState →
        UnifiedExposureCursor globalOracleCalls)
  | forkPair
      (frozenHistory : List QueryRecord)
      (pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls)
      (outputInput advanceInput : ShaInput)
      (template : AtomicPairReplayConfiguration)
      (next : AtomicPairReplayConfiguration →
        UnifiedExposureCursor globalOracleCalls)
  | forkAdvance
      (frozenHistory : List QueryRecord)
      (pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls)
      (outputInput advanceInput : ShaInput)
      (template : AtomicPairReplayConfiguration)
      (forkOutput : Digest256)
      (next : AtomicPairReplayConfiguration →
        UnifiedExposureCursor globalOracleCalls)
  | halted

/-- Exact configuration delivered after the two adjacent fork coordinates. -/
def scheduledForkConfiguration
    (template : AtomicPairReplayConfiguration)
    (forkOutput forkAdvance : Digest256) : AtomicPairReplayConfiguration :=
  atomicPairConfigurationFromFreshTape template
    (forkOutput, (forkAdvance, PUnit.unit))

@[simp] theorem scheduled_fork_configuration_coordinates
    (template : AtomicPairReplayConfiguration)
    (forkOutput forkAdvance : Digest256) :
    (scheduledForkConfiguration template forkOutput forkAdvance).forkOutput =
        forkOutput ∧
      (scheduledForkConfiguration template forkOutput forkAdvance).forkAdvance =
        forkAdvance := by
  exact ⟨rfl, rfl⟩

def completeForkAdvance
    {globalOracleCalls : Nat}
    (template : AtomicPairReplayConfiguration) (forkOutput : Digest256)
    (next : AtomicPairReplayConfiguration →
      UnifiedExposureCursor globalOracleCalls)
    (forkAdvance : Digest256) :
    UnifiedExposureCursor globalOracleCalls :=
  next (scheduledForkConfiguration template forkOutput forkAdvance)

/-! ## Pause at the next exposure -/

/-- Result of eliminating zero-exposure transitions.  A machine run executes
cached calls via `seekNextFresh`; a normal return invokes `onReturned` and may
continue to another cursor.  `transitionFuel` bounds such chains. -/
inductive UnifiedExposureRequest (globalOracleCalls : Nat) where
  | halted
  | transitionLimit
  | machineFresh
      {MachineResult : Type}
      (limits : OracleLimits)
      (limitBound : limits.totalCalls ≤ globalOracleCalls)
      (actor : QueryActor)
      (state : OracleState) (input : ShaInput)
      (nextProgram : ShaOutput → OracleMachine MachineResult)
      (remainingFuel : Nat)
      (coherent : HistoryTotalCoherent state)
      (totalRoom : state.totalCalls < limits.totalCalls)
      (freshRoom : state.freshCalls < limits.freshCalls)
      (missing : lookupEntry state input = none)
      (onReturned : MachineResult → OracleState →
        UnifiedExposureCursor globalOracleCalls)
  | forkOutput
      (frozenHistory : List QueryRecord)
      (pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls)
      (outputInput advanceInput : ShaInput)
      (template : AtomicPairReplayConfiguration)
      (next : AtomicPairReplayConfiguration →
        UnifiedExposureCursor globalOracleCalls)
  | forkAdvance
      (frozenHistory : List QueryRecord)
      (pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls)
      (outputInput advanceInput : ShaInput)
      (template : AtomicPairReplayConfiguration)
      (forkOutput : Digest256)
      (next : AtomicPairReplayConfiguration →
        UnifiedExposureCursor globalOracleCalls)

/-- Normalize a cursor until it either needs one new full-256 answer or
halts.  No target or answer is chosen in this function. -/
def seekUnifiedExposure
    {globalOracleCalls : Nat} :
    Nat → UnifiedExposureCursor globalOracleCalls →
      UnifiedExposureRequest globalOracleCalls
  | 0, _cursor => .transitionLimit
  | _transitionFuel + 1, .halted => .halted
  | _transitionFuel + 1,
      .forkPair frozenHistory pairRoom outputInput advanceInput template next =>
      .forkOutput frozenHistory pairRoom outputInput advanceInput template next
  | _transitionFuel + 1,
      .forkAdvance frozenHistory pairRoom outputInput advanceInput template
        forkOutput next =>
      .forkAdvance frozenHistory pairRoom outputInput advanceInput template
        forkOutput next
  | transitionFuel + 1,
      .machine limits limitBound actor state program fuel coherent onReturned =>
      match seekNextFresh limits actor fuel state program coherent with
      | .returned result finalState _steps =>
          seekUnifiedExposure transitionFuel
            (onReturned result finalState)
      | .request requestState input nextProgram remainingFuel _steps
          requestCoherent totalRoom freshRoom missing =>
          .machineFresh limits limitBound actor requestState input nextProgram
            remainingFuel
            requestCoherent totalRoom freshRoom missing onReturned
      | .explicitAbort _reason _finalState _steps => .halted
      | .resourceAbort _reason _finalState _steps => .halted
      | .outOfFuel _finalState _steps => .halted

@[simp] theorem seek_unified_exposure_fork_pair
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (frozenHistory : List QueryRecord)
    (pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls)
    (outputInput advanceInput : ShaInput)
    (template : AtomicPairReplayConfiguration)
    (next : AtomicPairReplayConfiguration →
      UnifiedExposureCursor globalOracleCalls) :
    seekUnifiedExposure (transitionFuel + 1)
      (.forkPair frozenHistory pairRoom outputInput advanceInput template next) =
        .forkOutput frozenHistory pairRoom outputInput advanceInput template
          next := by
  rfl

@[simp] theorem seek_unified_exposure_fork_advance
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (frozenHistory : List QueryRecord)
    (pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls)
    (outputInput advanceInput : ShaInput)
    (template : AtomicPairReplayConfiguration)
    (forkOutput : Digest256)
    (next : AtomicPairReplayConfiguration →
      UnifiedExposureCursor globalOracleCalls) :
    seekUnifiedExposure (transitionFuel + 1)
      (.forkAdvance frozenHistory pairRoom outputInput advanceInput template
        forkOutput next) =
        .forkAdvance frozenHistory pairRoom outputInput advanceInput template
          forkOutput next := by
  rfl

/-! ## Executable finite scheduler -/

structure ScheduledForkCoins where
  frozenHistory : List QueryRecord
  outputInput : ShaInput
  advanceInput : ShaInput
  template : AtomicPairReplayConfiguration
  forkOutput : Digest256
  forkAdvance : Digest256

def ScheduledForkCoins.configuration
    (scheduled : ScheduledForkCoins) : AtomicPairReplayConfiguration :=
  scheduledForkConfiguration scheduled.template scheduled.forkOutput
    scheduled.forkAdvance

@[simp] theorem scheduled_fork_coins_configuration_exact
    (scheduled : ScheduledForkCoins) :
    scheduled.configuration.forkOutput = scheduled.forkOutput ∧
      scheduled.configuration.forkAdvance = scheduled.forkAdvance := by
  exact ⟨rfl, rfl⟩

/-- Consume a fixed master tape.  Every recursive step consumes exactly one
coordinate.  A pair emits a configuration only at its advance step, after the
immediately preceding output coordinate has been retained by `forkAdvance`.
Halt/transition-limit branches consume the remaining tape as inert padding. -/
def runUnifiedExposureSchedule
    {globalOracleCalls : Nat}
    (transitionFuel : Nat) :
    (remaining : Nat) → UnifiedExposureCursor globalOracleCalls →
      FreshAnswerTape Digest256 remaining → List ScheduledForkCoins
  | 0, _cursor, _tape => []
  | remaining + 1, cursor, tape =>
      match seekUnifiedExposure transitionFuel cursor with
      | .halted | .transitionLimit =>
          runUnifiedExposureSchedule transitionFuel remaining
            (.halted : UnifiedExposureCursor globalOracleCalls) tape.2
      | .machineFresh limits limitBound actor state input nextProgram
          remainingFuel coherent
          _totalRoom _freshRoom _missing onReturned =>
          runUnifiedExposureSchedule transitionFuel remaining
            (.machine limits limitBound actor
              (freshQueryState actor state input tape.1)
              (nextProgram tape.1) remainingFuel
              (fresh_query_state_preserves_history_total_coherent actor state
                input tape.1 coherent) onReturned) tape.2
      | .forkOutput frozenHistory pairRoom outputInput advanceInput template
          next =>
          runUnifiedExposureSchedule transitionFuel remaining
            (.forkAdvance frozenHistory pairRoom outputInput advanceInput
              template tape.1 next)
            tape.2
      | .forkAdvance _frozenHistory _pairRoom outputInput advanceInput template
          forkOutput next =>
          let scheduled : ScheduledForkCoins :=
            { frozenHistory := _frozenHistory
              outputInput := outputInput
              advanceInput := advanceInput
              template := template
              forkOutput := forkOutput
              forkAdvance := tape.1 }
          scheduled ::
            runUnifiedExposureSchedule transitionFuel remaining
              (next scheduled.configuration) tape.2

/-- One direct fork consumes two successive coordinates and emits exactly the
configuration made from those two values. -/
theorem run_unified_exposure_schedule_direct_fork_exactly_two
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (frozenHistory : List QueryRecord)
    (pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls)
    (outputInput advanceInput : ShaInput)
    (template : AtomicPairReplayConfiguration)
    (next : AtomicPairReplayConfiguration →
      UnifiedExposureCursor globalOracleCalls)
    (forkOutput forkAdvance : Digest256) :
    runUnifiedExposureSchedule (transitionFuel + 1) 2
      (.forkPair frozenHistory pairRoom outputInput advanceInput template next)
      (forkOutput, (forkAdvance, PUnit.unit)) =
        [{ frozenHistory := frozenHistory
           outputInput := outputInput
           advanceInput := advanceInput
           template := template
           forkOutput := forkOutput
           forkAdvance := forkAdvance }] := by
  rfl

/-- Every emitted configuration contains exactly its retained pair of master
tape coordinates. -/
theorem every_unified_scheduled_fork_has_exact_coordinates
    {globalOracleCalls : Nat}
    (transitionFuel remaining : Nat)
    (cursor : UnifiedExposureCursor globalOracleCalls)
    (tape : FreshAnswerTape Digest256 remaining) :
    ∀ scheduled ∈ runUnifiedExposureSchedule transitionFuel remaining cursor
        tape,
      scheduled.configuration.forkOutput = scheduled.forkOutput ∧
        scheduled.configuration.forkAdvance = scheduled.forkAdvance := by
  intro scheduled _member
  exact scheduled_fork_coins_configuration_exact scheduled

/-! ## Fixed-length trace and padding -/

/-- One record per master-tape coordinate.  Pair output and advance are
distinct consecutive record kinds; halt padding is explicit. -/
inductive UnifiedExposureRecord where
  | padding (answer : Digest256)
  | machineFresh (actor : QueryActor) (input : ShaInput) (answer : Digest256)
  | forkOutput (frozenHistory : List QueryRecord)
      (outputInput advanceInput : ShaInput)
      (template : AtomicPairReplayConfiguration)
      (answer : Digest256)
  | forkAdvance (scheduled : ScheduledForkCoins)

def UnifiedExposureRecord.answer : UnifiedExposureRecord → Digest256
  | .padding answer => answer
  | .machineFresh _actor _input answer => answer
  | .forkOutput _frozenHistory _outputInput _advanceInput _template answer =>
      answer
  | .forkAdvance scheduled => scheduled.forkAdvance

/-- Trace interpreter for the same branch-step function.  Unlike the compact
configuration list, this emits exactly one record for every sampled
coordinate, including inert padding after halt. -/
def runUnifiedExposureTrace
    {globalOracleCalls : Nat}
    (transitionFuel : Nat) :
    (remaining : Nat) → UnifiedExposureCursor globalOracleCalls →
      FreshAnswerTape Digest256 remaining → List UnifiedExposureRecord
  | 0, _cursor, _tape => []
  | remaining + 1, cursor, tape =>
      match seekUnifiedExposure transitionFuel cursor with
      | .halted | .transitionLimit =>
          .padding tape.1 ::
            runUnifiedExposureTrace transitionFuel remaining
              (.halted : UnifiedExposureCursor globalOracleCalls)
              tape.2
      | .machineFresh limits limitBound actor state input nextProgram
          remainingFuel coherent
          _totalRoom _freshRoom _missing onReturned =>
          .machineFresh actor input tape.1 ::
            runUnifiedExposureTrace transitionFuel remaining
              (.machine limits limitBound actor
                (freshQueryState actor state input tape.1)
                (nextProgram tape.1) remainingFuel
                (fresh_query_state_preserves_history_total_coherent actor state
                  input tape.1 coherent) onReturned) tape.2
      | .forkOutput frozenHistory pairRoom outputInput advanceInput template
          next =>
          .forkOutput frozenHistory outputInput advanceInput template tape.1 ::
            runUnifiedExposureTrace transitionFuel remaining
              (.forkAdvance frozenHistory pairRoom outputInput advanceInput
                template tape.1 next)
              tape.2
      | .forkAdvance _frozenHistory _pairRoom outputInput advanceInput template
          forkOutput next =>
          let scheduled : ScheduledForkCoins :=
            { frozenHistory := _frozenHistory
              outputInput := outputInput
              advanceInput := advanceInput
              template := template
              forkOutput := forkOutput
              forkAdvance := tape.1 }
          .forkAdvance scheduled ::
            runUnifiedExposureTrace transitionFuel remaining
              (next scheduled.configuration) tape.2

theorem run_unified_exposure_trace_length_exact
    {globalOracleCalls : Nat}
    (transitionFuel remaining : Nat)
    (cursor : UnifiedExposureCursor globalOracleCalls)
    (tape : FreshAnswerTape Digest256 remaining) :
    (runUnifiedExposureTrace transitionFuel remaining cursor tape).length =
      remaining := by
  induction remaining generalizing cursor with
  | zero => rfl
  | succ remaining ih =>
      simp only [runUnifiedExposureTrace]
      cases request : seekUnifiedExposure transitionFuel cursor <;>
        simp [ih]

theorem run_unified_exposure_trace_answers_are_exact_tape
    {globalOracleCalls : Nat}
    (transitionFuel remaining : Nat)
    (cursor : UnifiedExposureCursor globalOracleCalls)
    (tape : FreshAnswerTape Digest256 remaining) :
    (runUnifiedExposureTrace transitionFuel remaining cursor tape).map
        UnifiedExposureRecord.answer = freshAnswerTapeToList tape := by
  induction remaining generalizing cursor with
  | zero => rfl
  | succ remaining ih =>
      simp only [runUnifiedExposureTrace]
      cases request : seekUnifiedExposure transitionFuel cursor <;>
        simp [UnifiedExposureRecord.answer, freshAnswerTapeToList, ih]

theorem run_unified_exposure_trace_halted_is_exact_padding
    {globalOracleCalls : Nat}
    (transitionFuel remaining : Nat)
    (tape : FreshAnswerTape Digest256 remaining) :
    runUnifiedExposureTrace transitionFuel remaining
        (.halted : UnifiedExposureCursor globalOracleCalls) tape =
      (freshAnswerTapeToList tape).map UnifiedExposureRecord.padding := by
  induction remaining with
  | zero => rfl
  | succ remaining ih =>
      cases transitionFuel with
      | zero =>
          simp [runUnifiedExposureTrace, seekUnifiedExposure,
            freshAnswerTapeToList, ih]
      | succ transitionFuel =>
          simp [runUnifiedExposureTrace, seekUnifiedExposure,
            freshAnswerTapeToList, ih]

theorem run_unified_exposure_trace_direct_fork_is_adjacent_pair
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (frozenHistory : List QueryRecord)
    (pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls)
    (outputInput advanceInput : ShaInput)
    (template : AtomicPairReplayConfiguration)
    (next : AtomicPairReplayConfiguration →
      UnifiedExposureCursor globalOracleCalls)
    (forkOutput forkAdvance : Digest256) :
    runUnifiedExposureTrace (transitionFuel + 1) 2
      (.forkPair frozenHistory pairRoom outputInput advanceInput template next)
      (forkOutput, (forkAdvance, PUnit.unit)) =
        [.forkOutput frozenHistory outputInput advanceInput template forkOutput,
          .forkAdvance
            { frozenHistory := frozenHistory
              outputInput := outputInput
              advanceInput := advanceInput
              template := template
              forkOutput := forkOutput
              forkAdvance := forkAdvance }] := by
  rfl

/-- Explicit law for the complete adaptive schedule: draw the fixed master
tape uniformly, then run the deterministic scheduler. -/
noncomputable def uniformUnifiedExposureScheduleLaw
    {globalOracleCalls : Nat}
    (transitionFuel exposures : Nat)
    (cursor : UnifiedExposureCursor globalOracleCalls) :
    PMF (List ScheduledForkCoins) :=
  (uniformDigestFreshTape exposures).map
    (runUnifiedExposureSchedule transitionFuel exposures cursor)

/-! ## Adaptive causal target tree over the same cursor -/

/-- Targets available before either programmed-pair coin is exposed: earlier
full outputs, literal prefixes in the frozen history, and the literal state
prefixes of both concrete inputs about to be programmed. -/
def operationalForkTargets
    (seen : Finset Digest256) (frozenHistory : List QueryRecord)
    (outputInput advanceInput : ShaInput) : Finset Digest256 :=
  (operationalHistoryTargets seen frozenHistory ∪
      oneInputLiteralTargets outputInput) ∪
    oneInputLiteralTargets advanceInput

theorem operational_fork_targets_card_le
    (seen : Finset Digest256) (frozenHistory : List QueryRecord)
    (outputInput advanceInput : ShaInput) :
    (operationalForkTargets seen frozenHistory outputInput advanceInput).card ≤
      seen.card + (frozenHistory.length + 2) := by
  have firstUnion := Finset.card_union_le
    (operationalHistoryTargets seen frozenHistory)
    (oneInputLiteralTargets outputInput)
  have secondUnion := Finset.card_union_le
    (operationalHistoryTargets seen frozenHistory ∪
      oneInputLiteralTargets outputInput)
    (oneInputLiteralTargets advanceInput)
  have historyBound := operational_history_targets_card_le seen frozenHistory
  have outputBound := one_input_literal_targets_card_le_one outputInput
  have advanceBound := one_input_literal_targets_card_le_one advanceInput
  unfold operationalForkTargets
  omega

theorem operational_fork_targets_within_step_plus_global_cap
    (seen : Finset Digest256) (frozenHistory : List QueryRecord)
    (outputInput advanceInput : ShaInput) (step globalOracleCalls : Nat)
    (seenBound : seen.card ≤ step)
    (pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls) :
    (operationalForkTargets seen frozenHistory outputInput advanceInput).card ≤
      step + globalOracleCalls := by
  exact (operational_fork_targets_card_le seen frozenHistory outputInput
    advanceInput).trans (Nat.add_le_add seenBound pairRoom)

theorem output_input_literal_prefix_is_fork_target
    (seen : Finset Digest256) (frozenHistory : List QueryRecord)
    (outputInput advanceInput : ShaInput) (state : Digest256)
    (prefixProof : HasLiteralStatePrefix state outputInput) :
    state ∈ operationalForkTargets seen frozenHistory outputInput
      advanceInput := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact (mem_one_input_literal_targets_iff state outputInput).mpr prefixProof

theorem advance_input_literal_prefix_is_fork_target
    (seen : Finset Digest256) (frozenHistory : List QueryRecord)
    (outputInput advanceInput : ShaInput) (state : Digest256)
    (prefixProof : HasLiteralStatePrefix state advanceInput) :
    state ∈ operationalForkTargets seen frozenHistory outputInput
      advanceInput := by
  apply Finset.mem_union_right
  exact (mem_one_input_literal_targets_iff state advanceInput).mpr prefixProof

/-- At each node, normalize the same cursor used by the executable scheduler,
then choose targets before supplying the current tape coordinate. -/
noncomputable def unifiedExposureTargetTreeFrom
    (globalOracleCalls : Nat) (transitionFuel : Nat) :
    (step remaining : Nat) → (seen : Finset Digest256) → seen.card ≤ step →
      UnifiedExposureCursor globalOracleCalls →
      CausalTargetTree Digest256
        (operationalCapsFrom step remaining globalOracleCalls)
  | _step, 0, _seen, _seenBound, _cursor => .done
  | step, remaining + 1, seen, seenBound, cursor =>
      match seekUnifiedExposure transitionFuel cursor with
      | .halted | .transitionLimit =>
          .step ∅ (by simp) fun _padding =>
            unifiedExposureTargetTreeFrom globalOracleCalls transitionFuel
              (step + 1) remaining seen
              (seenBound.trans (Nat.le_add_right step 1))
              (.halted : UnifiedExposureCursor globalOracleCalls)
      | .machineFresh limits limitBound actor state input nextProgram
          remainingFuel coherent totalRoom _freshRoom _missing onReturned => by
          have requestWithinGlobal :
              state.history.length + 1 ≤ globalOracleCalls := by
            unfold HistoryTotalCoherent at coherent
            rw [coherent]
            exact (Nat.succ_le_of_lt totalRoom).trans limitBound
          exact .step (operationalRequestTargets seen state.history input)
            (operational_request_targets_within_step_plus_global_cap seen
              state.history input step globalOracleCalls seenBound
              requestWithinGlobal)
            fun answer =>
              unifiedExposureTargetTreeFrom globalOracleCalls transitionFuel
                (step + 1) remaining
                (insert answer seen)
                ((Finset.card_insert_le answer seen).trans
                  (Nat.add_le_add_right seenBound 1))
                (.machine limits limitBound actor
                  (freshQueryState actor state input answer)
                  (nextProgram answer) remainingFuel
                  (fresh_query_state_preserves_history_total_coherent actor
                    state input answer coherent) onReturned)
      | .forkOutput frozenHistory pairRoom outputInput advanceInput template
          next =>
          .step
            (operationalForkTargets seen frozenHistory outputInput advanceInput)
            (operational_fork_targets_within_step_plus_global_cap seen
              frozenHistory outputInput advanceInput step globalOracleCalls
              seenBound pairRoom)
            fun forkOutput =>
              unifiedExposureTargetTreeFrom globalOracleCalls transitionFuel
                (step + 1) remaining
                (insert forkOutput seen)
                ((Finset.card_insert_le forkOutput seen).trans
                  (Nat.add_le_add_right seenBound 1))
                (.forkAdvance frozenHistory pairRoom outputInput advanceInput
                  template forkOutput next)
      | .forkAdvance frozenHistory pairRoom outputInput advanceInput template
          forkOutput next =>
          .step
            (operationalForkTargets seen frozenHistory outputInput advanceInput)
            (operational_fork_targets_within_step_plus_global_cap seen
              frozenHistory outputInput advanceInput step globalOracleCalls
              seenBound pairRoom)
            fun forkAdvance =>
              let configuration :=
                scheduledForkConfiguration template forkOutput forkAdvance
              unifiedExposureTargetTreeFrom globalOracleCalls transitionFuel
                (step + 1) remaining
                (insert forkAdvance seen)
                ((Finset.card_insert_le forkAdvance seen).trans
                  (Nat.add_le_add_right seenBound 1))
                (next configuration)

/-- Root form for an arbitrary fixed exposure cap. -/
noncomputable def unifiedExposureTargetTree
    (globalOracleCalls exposures : Nat) (transitionFuel : Nat)
    (cursor : UnifiedExposureCursor globalOracleCalls) :
    CausalTargetTree Digest256
      (tag73GlobalForwardReferenceCaps exposures globalOracleCalls) := by
  unfold tag73GlobalForwardReferenceCaps
  rw [← operational_caps_from_eq_range_map 0 exposures globalOracleCalls]
  exact unifiedExposureTargetTreeFrom globalOracleCalls transitionFuel 0
    exposures ∅ (by simp) cursor

/-! ## Executable generic target abort -/

/-- Evidence returned by the generic checker at the first target hit.  It
contains the concrete pre-answer target set and membership proof. -/
structure CausalTargetAbort where
  answer : Digest256
  targets : Finset Digest256
  member : answer ∈ targets

/-- Execute a causal target tree against one tape and abort at the first hit. -/
def checkCausalTargets :
    {caps : List Nat} → CausalTargetTree Digest256 caps →
      FreshAnswerTape Digest256 caps.length → Except CausalTargetAbort PUnit
  | [], .done, _tape => .ok PUnit.unit
  | _cap :: _caps, .step targets _targetCardLe next, tape =>
      if member : tape.1 ∈ targets then
        .error { answer := tape.1, targets := targets, member := member }
      else
        checkCausalTargets (next tape.1) tape.2

/-- A generic checker abort is always an actual hit in the structurally causal
tree.  This is not a claim about a concrete compiler abort. -/
theorem causal_target_check_abort_implies_hit :
    ∀ {caps : List Nat} (tree : CausalTargetTree Digest256 caps)
      (tape : FreshAnswerTape Digest256 caps.length)
      (abort : CausalTargetAbort),
      checkCausalTargets tree tape = .error abort → tree.everHits tape
  | [], .done, _tape, _abort => by
      simp [checkCausalTargets]
  | _cap :: _caps, .step targets _targetCardLe next, tape, abort => by
      by_cases member : tape.1 ∈ targets
      · intro _checked
        exact Or.inl member
      · intro checked
        have tailChecked :
            checkCausalTargets (next tape.1) tape.2 = .error abort := by
          simpa [checkCausalTargets, member] using checked
        exact Or.inr
          (causal_target_check_abort_implies_hit (next tape.1) tape.2 abort
            tailChecked)

def checkUnifiedExposureTargets
    (globalOracleCalls exposures : Nat) (transitionFuel : Nat)
    (cursor : UnifiedExposureCursor globalOracleCalls)
    (tape : FreshAnswerTape Digest256
      (tag73GlobalForwardReferenceCaps exposures globalOracleCalls).length) :
    Except CausalTargetAbort PUnit :=
  checkCausalTargets
    (unifiedExposureTargetTree globalOracleCalls exposures transitionFuel
      cursor) tape

theorem unified_target_check_abort_implies_causal_hit
    (globalOracleCalls exposures : Nat) (transitionFuel : Nat)
    (cursor : UnifiedExposureCursor globalOracleCalls)
    (tape : FreshAnswerTape Digest256
      (tag73GlobalForwardReferenceCaps exposures globalOracleCalls).length)
    (abort : CausalTargetAbort)
    (aborted : checkUnifiedExposureTargets globalOracleCalls exposures
      transitionFuel cursor tape = .error abort) :
    (unifiedExposureTargetTree globalOracleCalls exposures transitionFuel
      cursor).everHits tape :=
  causal_target_check_abort_implies_hit _ _ abort aborted

/-! ## Exact strict `F` and arithmetic -/

/-- Actual non-padded use: old fresh lazy-oracle coordinates plus two
coordinates for every completed atomic fork. -/
def unifiedFull256ExposureUse
    (freshLazyOracleExposures completedAtomicForks : Nat) : Nat :=
  freshLazyOracleExposures + 2 * completedAtomicForks

/-- Fixed sampled cap.  Unused restoration slots remain two-coordinate
padding and therefore do not change the probability space after early halt. -/
def strictUnifiedFull256ExposureCap
    (envelope : StrictTag73ResourceEnvelope) : Nat :=
  envelope.full256FreshExposures + 2 * envelope.restorationCount

theorem strict_unified_full256_exposure_cap_exact
    (envelope : StrictTag73ResourceEnvelope) :
    strictUnifiedFull256ExposureCap envelope =
      envelope.full256FreshExposures + 2 * envelope.restorationCount := by
  rfl

theorem unified_full256_actual_use_le_strict_cap
    (envelope : StrictTag73ResourceEnvelope)
    (freshLazyOracleExposures completedAtomicForks : Nat)
    (freshBound : freshLazyOracleExposures ≤
      envelope.full256FreshExposures)
    (forkBound : completedAtomicForks ≤ envelope.restorationCount) :
    unifiedFull256ExposureUse freshLazyOracleExposures completedAtomicForks ≤
      strictUnifiedFull256ExposureCap envelope := by
  unfold unifiedFull256ExposureUse strictUnifiedFull256ExposureCap
  omega

theorem strict_unified_target_caps_length_exact
    (envelope : StrictTag73ResourceEnvelope) :
    (tag73GlobalForwardReferenceCaps
      (strictUnifiedFull256ExposureCap envelope)
      (strictGlobalOracleCallCap envelope)).length =
        strictUnifiedFull256ExposureCap envelope :=
  tag73_global_forward_reference_caps_length _ _

theorem strict_unified_target_coefficient_expansion
    (envelope : StrictTag73ResourceEnvelope) :
    tag73GlobalForwardReferenceCoefficient
        (strictUnifiedFull256ExposureCap envelope)
        (strictGlobalOracleCallCap envelope) =
      (envelope.full256FreshExposures +
          2 * envelope.restorationCount).choose 2 +
        (envelope.full256FreshExposures +
          2 * envelope.restorationCount) *
        (envelope.q1Calls + envelope.verifierOracleCalls +
          envelope.restorationCount * envelope.oracleCallsPerRestoration) := by
  rfl

/-! ## Strict uniform probability forms -/

noncomputable def strictUnifiedExposureTargetTree
    (envelope : StrictTag73ResourceEnvelope)
    (transitionFuel : Nat)
    (cursor : UnifiedExposureCursor
      (strictGlobalOracleCallCap envelope)) :
    CausalTargetTree Digest256
      (tag73GlobalForwardReferenceCaps
        (strictUnifiedFull256ExposureCap envelope)
        (strictGlobalOracleCallCap envelope)) :=
  unifiedExposureTargetTree (strictGlobalOracleCallCap envelope)
    (strictUnifiedFull256ExposureCap envelope) transitionFuel cursor

/-- Bound for the adaptive collision/literal-prefix union.  No compiler abort
or acceptance event appears in this theorem. -/
theorem strict_unified_target_probability_le_exact_count
    (envelope : StrictTag73ResourceEnvelope)
    (transitionFuel : Nat)
    (cursor : UnifiedExposureCursor
      (strictGlobalOracleCallCap envelope)) :
    (uniformDigestFreshTape
      (tag73GlobalForwardReferenceCaps
        (strictUnifiedFull256ExposureCap envelope)
        (strictGlobalOracleCallCap envelope)).length).toOuterMeasure
      (causalHitEvent
        (strictUnifiedExposureTargetTree envelope transitionFuel cursor)) ≤
      ((tag73GlobalForwardReferenceCoefficient
          (strictUnifiedFull256ExposureCap envelope)
          (strictGlobalOracleCallCap envelope) *
        (2 ^ 256) ^
          (strictUnifiedFull256ExposureCap envelope - 1) : Nat) : ENNReal) /
        (((2 : ENNReal) ^ 256) ^
          strictUnifiedFull256ExposureCap envelope) :=
  global_forward_reference_tree_probability_le_exact_count
    (strictUnifiedFull256ExposureCap envelope)
    (strictGlobalOracleCallCap envelope)
    (strictUnifiedExposureTargetTree envelope transitionFuel cursor)

theorem strict_unified_target_probability_le_div_two_pow_256
    (envelope : StrictTag73ResourceEnvelope)
    (positive : 0 < strictUnifiedFull256ExposureCap envelope)
    (transitionFuel : Nat)
    (cursor : UnifiedExposureCursor
      (strictGlobalOracleCallCap envelope)) :
    (uniformDigestFreshTape
      (tag73GlobalForwardReferenceCaps
        (strictUnifiedFull256ExposureCap envelope)
        (strictGlobalOracleCallCap envelope)).length).toOuterMeasure
      (causalHitEvent
        (strictUnifiedExposureTargetTree envelope transitionFuel cursor)) ≤
      (tag73GlobalForwardReferenceCoefficient
        (strictUnifiedFull256ExposureCap envelope)
        (strictGlobalOracleCallCap envelope) : ENNReal) /
          ((2 : ENNReal) ^ 256) :=
  global_forward_reference_tree_probability_le_div_two_pow_256
    (strictUnifiedFull256ExposureCap envelope)
    (strictGlobalOracleCallCap envelope) positive
    (strictUnifiedExposureTargetTree envelope transitionFuel cursor)

/-! The initial cursor may itself be selected by an arbitrary finite hidden
adversary-tape law.  The master full-256 tape remains the independent uniform
component of the explicit joint law. -/

theorem strict_unified_hidden_target_probability_le_exact_count
    {HiddenTape : Type} [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    (envelope : StrictTag73ResourceEnvelope)
    (transitionFuel : Nat)
    (cursor : HiddenTape → UnifiedExposureCursor
      (strictGlobalOracleCallCap envelope)) :
    (hiddenTapeUniformFreshJointLaw hiddenLaw
      (tag73GlobalForwardReferenceCaps
        (strictUnifiedFull256ExposureCap envelope)
        (strictGlobalOracleCallCap envelope)).length).toOuterMeasure
      (hiddenDependentCausalHitEvent fun hidden =>
        strictUnifiedExposureTargetTree envelope transitionFuel
          (cursor hidden)) ≤
      ((tag73GlobalForwardReferenceCoefficient
          (strictUnifiedFull256ExposureCap envelope)
          (strictGlobalOracleCallCap envelope) *
        (2 ^ 256) ^
          (strictUnifiedFull256ExposureCap envelope - 1) : Nat) : ENNReal) /
        (((2 : ENNReal) ^ 256) ^
          strictUnifiedFull256ExposureCap envelope) :=
  global_forward_reference_hidden_tree_probability_le_exact_count hiddenLaw
    (strictUnifiedFull256ExposureCap envelope)
    (strictGlobalOracleCallCap envelope)
    (fun hidden => strictUnifiedExposureTargetTree envelope transitionFuel
      (cursor hidden))

theorem strict_unified_hidden_target_probability_le_div_two_pow_256
    {HiddenTape : Type} [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    (envelope : StrictTag73ResourceEnvelope)
    (positive : 0 < strictUnifiedFull256ExposureCap envelope)
    (transitionFuel : Nat)
    (cursor : HiddenTape → UnifiedExposureCursor
      (strictGlobalOracleCallCap envelope)) :
    (hiddenTapeUniformFreshJointLaw hiddenLaw
      (tag73GlobalForwardReferenceCaps
        (strictUnifiedFull256ExposureCap envelope)
        (strictGlobalOracleCallCap envelope)).length).toOuterMeasure
      (hiddenDependentCausalHitEvent fun hidden =>
        strictUnifiedExposureTargetTree envelope transitionFuel
          (cursor hidden)) ≤
      (tag73GlobalForwardReferenceCoefficient
        (strictUnifiedFull256ExposureCap envelope)
        (strictGlobalOracleCallCap envelope) : ENNReal) /
          ((2 : ENNReal) ^ 256) :=
  global_forward_reference_hidden_tree_probability_le_div_two_pow_256
    hiddenLaw (strictUnifiedFull256ExposureCap envelope)
    (strictGlobalOracleCallCap envelope) positive
    (fun hidden => strictUnifiedExposureTargetTree envelope transitionFuel
      (cursor hidden))

/-!
Remaining protocol-specific work is deliberately visible:

* construct this cursor from the concrete adaptive replay dispatcher;
* prove actual fresh-answer and completed-fork counts fit the two separate
  envelope terms, supply `frozenHistory.length + 2 ≤ G` at every pair node,
  and prove that a pair is never cut by the fixed cap;
* inject each concrete compiler abort into this collision/literal target
  event or a deterministic resource/binding event;
* retain provenance for transformed inputs; and
* construct and bound the accepted deployed output-decoder fiber.

Until those statements are proved, this module is an adaptive uniform
scheduler and target-union bound, not K1.6 closure.
-/

#print axioms scheduled_fork_configuration_coordinates
#print axioms seek_unified_exposure_fork_pair
#print axioms seek_unified_exposure_fork_advance
#print axioms run_unified_exposure_schedule_direct_fork_exactly_two
#print axioms every_unified_scheduled_fork_has_exact_coordinates
#print axioms run_unified_exposure_trace_length_exact
#print axioms run_unified_exposure_trace_answers_are_exact_tape
#print axioms run_unified_exposure_trace_halted_is_exact_padding
#print axioms run_unified_exposure_trace_direct_fork_is_adjacent_pair
#print axioms operational_fork_targets_within_step_plus_global_cap
#print axioms output_input_literal_prefix_is_fork_target
#print axioms advance_input_literal_prefix_is_fork_target
#print axioms causal_target_check_abort_implies_hit
#print axioms unified_target_check_abort_implies_causal_hit
#print axioms strict_unified_full256_exposure_cap_exact
#print axioms unified_full256_actual_use_le_strict_cap
#print axioms strict_unified_target_caps_length_exact
#print axioms strict_unified_target_coefficient_expansion
#print axioms strict_unified_target_probability_le_exact_count
#print axioms strict_unified_target_probability_le_div_two_pow_256
#print axioms strict_unified_hidden_target_probability_le_exact_count
#print axioms strict_unified_hidden_target_probability_le_div_two_pow_256

end

end AspisK1.V7Tag73AtomicForkUniformScheduler
