import AspisFormal.K1.V7Tag73SchedulerNativePlainRomExperiment

/-!
# Static terminal safety for scheduler-native cursors

This predicate talks about every result constructor reachable through the
continuation tree of a native cursor.  It is independent of probability and
does not assert that a machine returns.  It is useful for plain-data
invariants, such as the ancestry of restoration nodes, which hold for every
possible machine result and therefore do not need a controller premise.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73SchedulerNativeSafety

open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment

noncomputable section

universe u

/-- Every ordinary result stored anywhere below this cursor satisfies `P`.
Scheduler failures carry no protocol result and are therefore harmless. -/
def SchedulerNativeCursorAllReturned
    {globalOracleCalls : Nat} {Result : Type u}
    (P : Result → Prop) : SchedulerNativeCursor globalOracleCalls Result → Prop
  | .machine _limits _limitBound _actor _state _program _fuel _coherent
      onReturned =>
      ∀ result finalState finalCoherent,
        SchedulerNativeCursorAllReturned P
          (onReturned result finalState finalCoherent)
  | .forkPair _history _room _outputInput _advanceInput _template next =>
      ∀ configuration, SchedulerNativeCursorAllReturned P (next configuration)
  | .forkAdvance _history _room _outputInput _advanceInput _template
      _forkOutput next =>
      ∀ configuration, SchedulerNativeCursorAllReturned P (next configuration)
  | .returned result => P result
  | .failed _reason => True

@[simp] theorem all_returned_returned
    {globalOracleCalls : Nat} {Result : Type u}
    (P : Result → Prop) (result : Result) :
    SchedulerNativeCursorAllReturned P
      (SchedulerNativeCursor.returned result :
        SchedulerNativeCursor globalOracleCalls Result) ↔
        P result := by
  rfl

@[simp] theorem all_returned_failed
    {globalOracleCalls : Nat} {Result : Type u}
    (P : Result → Prop) (reason : SchedulerNativeFailure) :
    SchedulerNativeCursorAllReturned P
      (SchedulerNativeCursor.failed reason :
        SchedulerNativeCursor globalOracleCalls Result) := by
  trivial

/-- Result mapping preserves static safety under the corresponding pointwise
implication. -/
theorem all_returned_map
    {globalOracleCalls : Nat} {Input Output : Type u}
    (P : Input → Prop) (Q : Output → Prop) (map : Input → Output)
    (pointwise : ∀ input, P input → Q (map input)) :
    ∀ cursor : SchedulerNativeCursor globalOracleCalls Input,
      SchedulerNativeCursorAllReturned P cursor →
        SchedulerNativeCursorAllReturned Q
          (mapSchedulerNativeCursorResult map cursor) := by
  intro cursor
  induction cursor with
  | @machine MachineResult limits limitBound actor state program fuel coherent
      onReturned ih =>
      intro safe result finalState finalCoherent
      exact ih result finalState finalCoherent
        (safe result finalState finalCoherent)
  | forkPair history room outputInput advanceInput template next ih =>
      intro safe configuration
      exact ih configuration (safe configuration)
  | forkAdvance history room outputInput advanceInput template forkOutput next
      ih =>
      intro safe configuration
      exact ih configuration (safe configuration)
  | returned result =>
      intro safe
      exact pointwise result safe
  | failed reason =>
      intro _safe
      trivial

#print axioms all_returned_returned
#print axioms all_returned_map

end

end AspisK1.V7Tag73SchedulerNativeSafety
