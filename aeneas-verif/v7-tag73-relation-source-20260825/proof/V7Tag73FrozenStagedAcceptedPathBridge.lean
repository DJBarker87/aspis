import V7Tag73ExtractionTransformEquivalence

/-!
# Frozen-original to staged Tag-73 accepted-control bridge

The original finish root has no generated Lean body because Aeneas fails in
`InterpJoin` on its fixed `1..4` loop.  This file therefore does not pretend
to be an Aeneas theorem about a declaration which was never emitted.  It
kernel-checks the exact control refinement used by the byte-pinned source
transform: the three fixed point rows, two fixed OOD samples, three fixed
relation rounds, tail extraction, and the reachable Tag-73 terminal branch.

All transition functions remain arbitrary `Aeneas.Std.Result` computations,
so the equality preserves successful output, the first failure, and
divergence.  The separate source-transform certificate binds this semantic
skeleton to the frozen and staged Rust bytes.
-/

namespace V7Tag73FrozenStagedAcceptedPathBridge

open Aeneas Aeneas.Std Result Error
open AspisV7Tag73ExtractionTransformEquivalence

/-- Control spelling in the frozen source: fixed ranges followed by the
terminal block inline in `finish_onefold_relation`. -/
def frozenFinishControl {State Output : Type}
    (pointStep oodStep roundStep : Nat → State → Result State)
    (prelude : State → Result State)
    (terminal : State → Result Output)
    (initial : State) : Result Output := do
  let afterPoints ← runSteps pointStep [0, 1, 2] initial
  let afterOods ← runSteps oodStep [0, 1] afterPoints
  let beforeRounds ← prelude afterOods
  let afterRounds ← runSteps roundStep [1, 2, 3] beforeRounds
  terminal afterRounds

/-- Control spelling in the staged source: the same fixed calls explicitly
unrolled and the terminal block called as an extracted helper. -/
def stagedFinishControl {State Output : Type}
    (pointStep oodStep roundStep : Nat → State → Result State)
    (prelude : State → Result State)
    (extractedTail : State → Result Output)
    (initial : State) : Result Output := do
  let afterPoints ← unrolled012 pointStep initial
  let afterOods ← unrolled01 oodStep afterPoints
  let beforeRounds ← prelude afterOods
  let afterRounds ← unrolled123 roundStep beforeRounds
  extractedTail afterRounds

/-- Exact result equality for the loop unrolling and tail extraction.  No
success or totality hypothesis is needed. -/
theorem frozen_staged_finish_control_result_exact {State Output : Type}
    (pointStep oodStep roundStep : Nat → State → Result State)
    (prelude : State → Result State)
    (tail : State → Result Output)
    (initial : State) :
    frozenFinishControl pointStep oodStep roundStep prelude tail initial =
      stagedFinishControl pointStep oodStep roundStep prelude tail initial := by
  simp only [frozenFinishControl, stagedFinishControl,
    point_rows_0_1_2_result_exact, ood_samples_0_1_result_exact,
    relation_rounds_1_2_3_result_exact]

theorem frozen_staged_finish_control_success_iff {State Output : Type}
    (pointStep oodStep roundStep : Nat → State → Result State)
    (prelude : State → Result State)
    (tail : State → Result Output)
    (initial : State) (output : Output) :
    frozenFinishControl pointStep oodStep roundStep prelude tail initial =
        .ok output ↔
      stagedFinishControl pointStep oodStep roundStep prelude tail initial =
        .ok output := by
  rw [frozen_staged_finish_control_result_exact]

theorem frozen_staged_finish_control_failure_iff {State Output : Type}
    (pointStep oodStep roundStep : Nat → State → Result State)
    (prelude : State → Result State)
    (tail : State → Result Output)
    (initial : State) (error : Error) :
    frozenFinishControl pointStep oodStep roundStep prelude tail initial =
        .fail error ↔
      stagedFinishControl pointStep oodStep roundStep prelude tail initial =
        .fail error := by
  rw [frozen_staged_finish_control_result_exact]

theorem frozen_staged_finish_control_divergence_iff {State Output : Type}
    (pointStep oodStep roundStep : Nat → State → Result State)
    (prelude : State → Result State)
    (tail : State → Result Output)
    (initial : State) :
    frozenFinishControl pointStep oodStep roundStep prelude tail initial =
        .div ↔
      stagedFinishControl pointStep oodStep roundStep prelude tail initial =
        .div := by
  rw [frozen_staged_finish_control_result_exact]

/-- The frozen generic terminal has a fallback; the staged extraction marks
that fallback unreachable.  They are equal on the branch actually reachable
from the Tag-73 finish state, independently of either fallback's value. -/
def frozenTerminalDispatch {Output : Type}
    (terminalShape : Bool) (optimized fallback : Result Output) :
    Result Output :=
  if terminalShape then optimized else fallback

def stagedTerminalDispatch {Output : Type}
    (terminalShape : Bool) (optimized unreachableBranch : Result Output) :
    Result Output :=
  if terminalShape then optimized else unreachableBranch

theorem terminal_dispatch_reachable_result_exact {Output : Type}
    (terminalShape : Bool) (optimized frozenFallback stagedUnreachable :
      Result Output)
    (hshape : terminalShape = true) :
    frozenTerminalDispatch terminalShape optimized frozenFallback =
      stagedTerminalDispatch terminalShape optimized stagedUnreachable := by
  simp [frozenTerminalDispatch, stagedTerminalDispatch, hshape]

/-- Four radix-4 folds take the deployed weight log length `10` to `2`; the
round-zero plus rounds-1--3 value folds take `256` terminal coefficients to
four. -/
def tag73TerminalShape : Bool :=
  decide (((((10 : Nat) - 2) - 2) - 2) - 2 = 2 ∧
    256 / 4 / 4 / 4 = 4)

theorem tag73_terminal_shape_true : tag73TerminalShape = true := by
  rfl

theorem tag73_terminal_dispatch_result_exact {Output : Type}
    (optimized frozenFallback stagedUnreachable : Result Output) :
    frozenTerminalDispatch tag73TerminalShape optimized frozenFallback =
      stagedTerminalDispatch tag73TerminalShape optimized stagedUnreachable := by
  rfl

/-- Whole accepted-control model including the only transformation which is
conditional outside the reachable Tag-73 state: terminal-dot specialization.
The two arbitrary fallback computations disappear because the exact deployed
shape selects the shared optimized branch. -/
def frozenTag73FinishControl {State Output : Type}
    (pointStep oodStep roundStep : Nat → State → Result State)
    (prelude : State → Result State)
    (optimizedTerminal genericTerminal : State → Result Output)
    (initial : State) : Result Output :=
  frozenFinishControl pointStep oodStep roundStep prelude
    (fun state => frozenTerminalDispatch tag73TerminalShape
      (optimizedTerminal state) (genericTerminal state)) initial

def stagedTag73FinishControl {State Output : Type}
    (pointStep oodStep roundStep : Nat → State → Result State)
    (prelude : State → Result State)
    (optimizedTerminal unreachableTerminal : State → Result Output)
    (initial : State) : Result Output :=
  stagedFinishControl pointStep oodStep roundStep prelude
    (fun state => stagedTerminalDispatch tag73TerminalShape
      (optimizedTerminal state) (unreachableTerminal state)) initial

theorem frozen_staged_tag73_accepted_control_result_exact
    {State Output : Type}
    (pointStep oodStep roundStep : Nat → State → Result State)
    (prelude : State → Result State)
    (optimizedTerminal frozenFallback stagedUnreachable :
      State → Result Output)
    (initial : State) :
    frozenTag73FinishControl pointStep oodStep roundStep prelude
        optimizedTerminal frozenFallback initial =
      stagedTag73FinishControl pointStep oodStep roundStep prelude
        optimizedTerminal stagedUnreachable initial := by
  have htail :
      (fun state => frozenTerminalDispatch tag73TerminalShape
        (optimizedTerminal state) (frozenFallback state)) =
      (fun state => stagedTerminalDispatch tag73TerminalShape
        (optimizedTerminal state) (stagedUnreachable state)) := by
    funext state
    exact tag73_terminal_dispatch_result_exact _ _ _
  unfold frozenTag73FinishControl stagedTag73FinishControl
  rw [htail]
  exact frozen_staged_finish_control_result_exact _ _ _ _ _ _

theorem frozen_staged_tag73_accepted_control_success_iff
    {State Output : Type}
    (pointStep oodStep roundStep : Nat → State → Result State)
    (prelude : State → Result State)
    (optimizedTerminal frozenFallback stagedUnreachable :
      State → Result Output)
    (initial : State) (output : Output) :
    frozenTag73FinishControl pointStep oodStep roundStep prelude
        optimizedTerminal frozenFallback initial = .ok output ↔
      stagedTag73FinishControl pointStep oodStep roundStep prelude
        optimizedTerminal stagedUnreachable initial = .ok output := by
  rw [frozen_staged_tag73_accepted_control_result_exact]

#print axioms frozen_staged_finish_control_result_exact
#print axioms frozen_staged_finish_control_success_iff
#print axioms frozen_staged_finish_control_failure_iff
#print axioms frozen_staged_finish_control_divergence_iff
#print axioms terminal_dispatch_reachable_result_exact
#print axioms tag73_terminal_dispatch_result_exact
#print axioms frozen_staged_tag73_accepted_control_result_exact
#print axioms frozen_staged_tag73_accepted_control_success_iff

end V7Tag73FrozenStagedAcceptedPathBridge
