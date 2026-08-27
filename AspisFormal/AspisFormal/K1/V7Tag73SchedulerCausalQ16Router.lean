import AspisFormal.K1.V7Tag73CausalQ16ProbabilityBridge
import AspisFormal.K1.V7Tag73CausalSlotMachineRouter
import AspisFormal.K1.V7Tag73AtomicForkUniformScheduler

/-!
# A causal q16 router driven by the literal unified-exposure cursor

The exact Fiat--Shamir compiler samples one fixed-length master tape and
interprets it with `UnifiedExposureCursor`.  This file turns any q16 labelling
of that cursor into the exact `CausalSlotRouter` consumed by the q16
probability theorem.

The label is read from the cursor before `seekUnifiedExposure` receives the
current answer.  The next cursor is then computed by precisely the same five
branches as `runUnifiedExposureTrace`: halt padding, a fresh machine query,
fork output, or fork advance.  Consequently the current answer cannot affect
its own label, while every later label may depend on it through the cursor.

This file does not assert which cursor states are Tag--73 q16 output halves.
That is the remaining source-alignment theorem: it must label the literal
future-free q16 controls and prove that the selected operational schedule is
the first admitted schedule in the routed forest.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73SchedulerCausalQ16Router

open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73CausalQ16ProbabilityBridge
open AspisK1.V7Tag73CausalSlotMachineRouter
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Advance the unified-exposure cursor by exactly one full-256 answer.  This
is the state transition embedded in `runUnifiedExposureTrace`, separated from
trace emission so it can drive a pre-answer slot machine. -/
def unifiedCursorAfterAnswer
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (cursor : UnifiedExposureCursor globalOracleCalls)
    (answer : Digest256) : UnifiedExposureCursor globalOracleCalls :=
  match seekUnifiedExposure transitionFuel cursor with
  | .halted | .transitionLimit => .halted
  | .machineFresh limits limitBound actor state input nextProgram
      remainingFuel coherent _totalRoom _freshRoom _missing onReturned =>
      .machine limits limitBound actor
        (freshQueryState actor state input answer)
        (nextProgram answer) remainingFuel
        (fresh_query_state_preserves_history_total_coherent actor state input
          answer coherent) onReturned
  | .forkOutput frozenHistory pairRoom outputInput advanceInput template next =>
      .forkAdvance frozenHistory pairRoom outputInput advanceInput template
        answer next
  | .forkAdvance _frozenHistory _pairRoom _outputInput _advanceInput template
      forkOutput next =>
      next (scheduledForkConfiguration template forkOutput answer)

/-- The trace record emitted at the same pre-answer cursor. -/
def unifiedRecordAtAnswer
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (cursor : UnifiedExposureCursor globalOracleCalls)
    (answer : Digest256) : UnifiedExposureRecord :=
  match seekUnifiedExposure transitionFuel cursor with
  | .halted | .transitionLimit => .padding answer
  | .machineFresh _limits _limitBound actor _state input _nextProgram
      _remainingFuel _coherent _totalRoom _freshRoom _missing _onReturned =>
      .machineFresh actor input answer
  | .forkOutput frozenHistory _pairRoom outputInput advanceInput template _next =>
      .forkOutput frozenHistory outputInput advanceInput template answer
  | .forkAdvance frozenHistory _pairRoom outputInput advanceInput template
      forkOutput _next =>
      .forkAdvance
        { frozenHistory := frozenHistory
          outputInput := outputInput
          advanceInput := advanceInput
          template := template
          forkOutput := forkOutput
          forkAdvance := answer }

/-- The separated transition and record are definitionally the head step of
the production scheduler trace interpreter. -/
theorem run_unified_exposure_trace_succ_eq_record_and_cursor
    {globalOracleCalls : Nat}
    (transitionFuel remaining : Nat)
    (cursor : UnifiedExposureCursor globalOracleCalls)
    (answer : Digest256)
    (tail : FreshAnswerTape Digest256 remaining) :
    runUnifiedExposureTrace transitionFuel (remaining + 1) cursor
        (answer, tail) =
      unifiedRecordAtAnswer transitionFuel cursor answer ::
        runUnifiedExposureTrace transitionFuel remaining
          (unifiedCursorAfterAnswer transitionFuel cursor answer) tail := by
  simp only [runUnifiedExposureTrace, unifiedRecordAtAnswer,
    unifiedCursorAfterAnswer]
  cases request : seekUnifiedExposure transitionFuel cursor <;> rfl

/-- A cursor labelling is explicitly a pre-answer function.  It may inspect
the complete current cursor (and therefore all earlier answers), but it is not
given the answer about to be sampled. -/
abbrev UnifiedQ16PreAnswerLabel (globalOracleCalls : Nat) :=
  UnifiedExposureCursor globalOracleCalls → Option Q16DigestSlot

/-- The literal scheduler cursor equipped with one pre-answer q16 label. -/
def unifiedExposureSlotMachine
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (label : UnifiedQ16PreAnswerLabel globalOracleCalls) :
    PreAnswerSlotMachine Digest256 Q16DigestSlot
      (UnifiedExposureCursor globalOracleCalls) where
  preferredSlot := label
  afterAnswer := unifiedCursorAfterAnswer transitionFuel

/-- Total causal q16 router for the exact compiler master tape.  Unused q16
slots are filled from the fixed padding/residual tail, so this is an
equivalence on every tape, including rejecting and early-halting runs. -/
def exactCompilerSchedulerQ16Router
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel : Nat)
    (label : UnifiedQ16PreAnswerLabel
      (globalFull256OracleCallCap parameters))
    (cursor : UnifiedExposureCursor
      (globalFull256OracleCallCap parameters)) :
    ExactCompilerCausalQ16Router parameters :=
  (unifiedExposureSlotMachine transitionFuel label).fullRouter
    ((exactCompilerTargetCaps parameters).length - 512) cursor

/-- Hence every literal pre-answer labelling immediately supplies the exact
measure-preserving coordinates expected by the q16 probability bridge. -/
def exactCompilerSchedulerQ16Coordinates
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel : Nat)
    (label : UnifiedQ16PreAnswerLabel
      (globalFull256OracleCallCap parameters))
    (cursor : UnifiedExposureCursor
      (globalFull256OracleCallCap parameters)) :
    FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
      ExactCompilerQ16Residual parameters × Q16CandidateDigestForest :=
  exactCompilerCausalQ16Coordinates parameters
    (exactCompilerSchedulerQ16Router parameters transitionFuel label cursor)

end

#print axioms unifiedCursorAfterAnswer
#print axioms run_unified_exposure_trace_succ_eq_record_and_cursor
#print axioms unifiedExposureSlotMachine
#print axioms exactCompilerSchedulerQ16Router
#print axioms exactCompilerSchedulerQ16Coordinates

end AspisK1.V7Tag73SchedulerCausalQ16Router
