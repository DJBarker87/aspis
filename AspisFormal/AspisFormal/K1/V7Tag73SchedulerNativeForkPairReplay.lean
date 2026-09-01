import AspisFormal.K1.V7Tag73SchedulerNativePrefixTraversal

/-!
# Scheduler-native replay from an atomic restoration fork pair

Gamma coordinates installed by a restoration fork are not ordinary
`machineFresh` pauses.  They are the two adjacent `.forkOutput` and
`.forkAdvance` scheduler exposures.  This leaf records the exact executable
two-answer transition to the production continuation, without assuming which
actor first queried either programmed input.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73SchedulerNativeForkPairReplay

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AtomicPairReplay
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73SchedulerNativePrefixTraversal
open AspisK1.V7Tag73SchedulerNativeResult

universe u

/-- Supplying two answers to a literal native fork-pair cursor reaches the
exact production continuation instantiated with those same answers. -/
@[simp] theorem scheduler_native_prefix_cursor_fork_pair_exact
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat)
    (frozenHistory : List QueryRecord)
    (pairRoom : frozenHistory.length + 2 <= globalOracleCalls)
    (outputInput advanceInput : ShaInput)
    (template : AtomicPairReplayConfiguration)
    (next : AtomicPairReplayConfiguration ->
      SchedulerNativeCursor globalOracleCalls Result)
    (forkOutput forkAdvance : Digest256) :
    schedulerNativePrefixCursor (transitionFuel + 1)
      (.forkPair frozenHistory pairRoom outputInput advanceInput template next)
      [forkOutput, forkAdvance] =
        next (scheduledForkConfiguration template forkOutput forkAdvance) := by
  rfl

/-- The same two-step replay reaches the continuation at the exact scheduled
configuration stored in a `ScheduledForkCoins` value. -/
theorem scheduler_native_prefix_cursor_scheduled_fork_exact
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat)
    (scheduled : ScheduledForkCoins)
    (pairRoom : scheduled.frozenHistory.length + 2 <= globalOracleCalls)
    (next : AtomicPairReplayConfiguration ->
      SchedulerNativeCursor globalOracleCalls Result) :
    schedulerNativePrefixCursor (transitionFuel + 1)
      (.forkPair scheduled.frozenHistory pairRoom scheduled.outputInput
        scheduled.advanceInput scheduled.template next)
      [scheduled.forkOutput, scheduled.forkAdvance] =
        next scheduled.configuration := by
  rfl

#print axioms scheduler_native_prefix_cursor_fork_pair_exact
#print axioms scheduler_native_prefix_cursor_scheduled_fork_exact

end AspisK1.V7Tag73SchedulerNativeForkPairReplay
