import Aeneas

/-!
# Kernel-checked equivalence of the extraction-only control rewrites

The deployed Rust stays frozen.  These lemmas validate the generic control
identities used to present its fixed Tag-73 loops to Charon/Aeneas.  Because
the transition returns `Aeneas.Std.Result`, each equality preserves success,
the first failure, and divergence; no totality premise is hidden here.
-/

namespace AspisV7Tag73ExtractionTransformEquivalence

open Aeneas Aeneas.Std Result ControlFlow Error

@[simp] theorem bind_ok_identity {Value : Type} (result : Result Value) :
    (do
      let value ← result
      .ok value) = result := by
  cases result <;> rfl

def runSteps {State : Type}
    (step : Nat → State → Result State) : List Nat → State → Result State
  | [], state => .ok state
  | index :: rest, state => do
      let next ← step index state
      runSteps step rest next

def unrolled012 {State : Type}
    (step : Nat → State → Result State) (state : State) : Result State := do
  let state0 ← step 0 state
  let state1 ← step 1 state0
  let state2 ← step 2 state1
  .ok state2

def unrolled01 {State : Type}
    (step : Nat → State → Result State) (state : State) : Result State := do
  let state0 ← step 0 state
  let state1 ← step 1 state0
  .ok state1

def unrolled123 {State : Type}
    (step : Nat → State → Result State) (state : State) : Result State := do
  let state1 ← step 1 state
  let state2 ← step 2 state1
  let state3 ← step 3 state2
  .ok state3

/-- Exact control equivalence for the three statement-point rows. -/
theorem point_rows_0_1_2_result_exact {State : Type}
    (step : Nat → State → Result State) (state : State) :
    runSteps step [0, 1, 2] state = unrolled012 step state := by
  simp [runSteps, unrolled012, Bind.bind, Aeneas.Std.bind]

/-- Exact control equivalence for the two OOD samples. -/
theorem ood_samples_0_1_result_exact {State : Type}
    (step : Nat → State → Result State) (state : State) :
    runSteps step [0, 1] state = unrolled01 step state := by
  simp [runSteps, unrolled01, Bind.bind, Aeneas.Std.bind]

/-- Exact control equivalence for the deployed relation range `1..4`. -/
theorem relation_rounds_1_2_3_result_exact {State : Type}
    (step : Nat → State → Result State) (state : State) :
    runSteps step [1, 2, 3] state = unrolled123 step state := by
  simp [runSteps, unrolled123, Bind.bind, Aeneas.Std.bind]

theorem relation_rounds_1_2_3_success_iff {State : Type}
    (step : Nat → State → Result State) (initial output : State) :
    runSteps step [1, 2, 3] initial = .ok output ↔
      unrolled123 step initial = .ok output := by
  rw [relation_rounds_1_2_3_result_exact]

theorem relation_rounds_1_2_3_failure_iff {State : Type}
    (step : Nat → State → Result State) (initial : State)
    (error : Error) :
    runSteps step [1, 2, 3] initial = .fail error ↔
      unrolled123 step initial = .fail error := by
  rw [relation_rounds_1_2_3_result_exact]

theorem relation_rounds_1_2_3_divergence_iff {State : Type}
    (step : Nat → State → Result State) (initial : State) :
    runSteps step [1, 2, 3] initial = .div ↔
      unrolled123 step initial = .div := by
  rw [relation_rounds_1_2_3_result_exact]

def pairFoldM {Left Right State : Type}
    (step : Left → Right → State → Result State) :
    List (Left × Right) → State → Result State
  | [], state => .ok state
  | (left, right) :: rest, state => do
      let next ← step left right state
      pairFoldM step rest next

def indexedCommonPrefixM {Left Right State : Type}
    (step : Left → Right → State → Result State) :
    List Left → List Right → State → Result State
  | left :: leftRest, right :: rightRest, state => do
      let next ← step left right state
      indexedCommonPrefixM step leftRest rightRest next
  | _, _, state => .ok state

/-- Rust `zip` and an indexed loop bounded by `min(len(left), len(right))`
visit the same common prefix in the same order and stop on the same error. -/
theorem zip_indexed_common_prefix_result_exact {Left Right State : Type}
    (step : Left → Right → State → Result State)
    (left : List Left) (right : List Right) (state : State) :
    pairFoldM step (List.zip left right) state =
      indexedCommonPrefixM step left right state := by
  induction left generalizing right state with
  | nil => simp [pairFoldM, indexedCommonPrefixM]
  | cons leftHead leftTail ih =>
    cases right with
    | nil => simp [pairFoldM, indexedCommonPrefixM]
    | cons rightHead rightTail =>
      change
        (do
          let next ← step leftHead rightHead state
          pairFoldM step (List.zip leftTail rightTail) next) =
        (do
          let next ← step leftHead rightHead state
          indexedCommonPrefixM step leftTail rightTail next)
      cases run : step leftHead rightHead state with
      | ok next => simpa [run, Bind.bind, Aeneas.Std.bind] using ih rightTail next
      | fail error => simp [run, Bind.bind, Aeneas.Std.bind]
      | div => simp [run, Bind.bind, Aeneas.Std.bind]

def optionMaximum : List (Option Nat) → Nat
  | [] => 0
  | value :: rest => Nat.max (value.getD 0) (optionMaximum rest)

def filterMaximum (values : List (Option Nat)) : Nat :=
  (values.filterMap (fun value => value)).foldr Nat.max 0

/-- Replacing `filter_map(...).max().unwrap_or(0)` by a zero-seeded indexed
maximum is exact, including the empty/no-line-component case. -/
theorem indexed_maximum_result_exact (values : List (Option Nat)) :
    filterMaximum values = optionMaximum values := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    cases value with
    | none =>
      change filterMaximum rest = optionMaximum rest
      exact ih
    | some value =>
      change Nat.max value (filterMaximum rest) =
        Nat.max value (optionMaximum rest)
      rw [ih]

def mapCoreError {Value SourceError TargetError : Type}
    (wrap : SourceError → TargetError) :
    core.result.Result Value SourceError →
      core.result.Result Value TargetError
  | .Ok value => .Ok value
  | .Err error => .Err (wrap error)

def namedErrorAdapter {SourceError TargetError : Type}
    (wrap : SourceError → TargetError) (error : SourceError) : TargetError :=
  wrap error

/-- Naming `V6TranscriptError::Wire` before passing it to `map_err` changes
neither the successful value nor the exact error constructor. -/
theorem named_error_adapter_result_exact
    {Value SourceError TargetError : Type}
    (wrap : SourceError → TargetError)
    (result : core.result.Result Value SourceError) :
    mapCoreError (namedErrorAdapter wrap) result = mapCoreError wrap result := by
  cases result <;> rfl

/-- The exact deployed shape after round zero and the three unrolled rounds:
log length `10 → 8 → 6 → 4 → 2`, final vector
`256 → 64 → 16 → 4`. -/
theorem terminal_shape_log2_len4 :
    (((((10 : Nat) - 2) - 2) - 2) - 2 = 2) ∧
      (256 / 4 / 4 / 4 = 4) := by
  decide

#print axioms point_rows_0_1_2_result_exact
#print axioms ood_samples_0_1_result_exact
#print axioms relation_rounds_1_2_3_result_exact
#print axioms relation_rounds_1_2_3_success_iff
#print axioms relation_rounds_1_2_3_failure_iff
#print axioms relation_rounds_1_2_3_divergence_iff
#print axioms zip_indexed_common_prefix_result_exact
#print axioms indexed_maximum_result_exact
#print axioms named_error_adapter_result_exact
#print axioms terminal_shape_log2_len4

end AspisV7Tag73ExtractionTransformEquivalence
