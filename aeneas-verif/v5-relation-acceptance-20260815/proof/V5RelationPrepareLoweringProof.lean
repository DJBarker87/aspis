import Mathlib

/-!
# Exact lowering of the accepted relation-preparation path

The unchanged Rust prepares three ten-coordinate points with
`map(...).collect::<Result<Vec<_>, _>>()?`.  Pinned Aeneas cannot translate
the generic `try_fold` implementation behind that fixed iterator expression.
The extraction adapter spells the same thirty decoder calls explicitly and
unrolls the three-point loop.  It also spells the two four-value `from_fn`
decoders explicitly and moves the real-prefix branch around those calls.

This file proves the source transformation for arbitrary decoder, state-step,
error, and continuation functions.  Thus it covers every accepted caller
input, including the location and value of the first error; it is not a test
of the released fixture.
-/

namespace AspisV5RelationPrepareLowering

/-- Execute decoders from left to right and preserve the exact first error. -/
def runDecodeOrder {α ε : Type} (decode : Nat → Except ε α) :
    List Nat → Except ε (List α)
  | [] => .ok []
  | index :: rest => do
      let value ← decode index
      let values ← runDecodeOrder decode rest
      .ok (value :: values)

/-- Visit order of one unchanged Rust `map/collect` point. -/
def deployedPointVisitOrder (point : Nat) : List Nat :=
  (List.range 10).map fun coordinate => point * 10 + coordinate

/-- Visit order of the corresponding explicit extraction helper. -/
def loweredPointVisitOrder (point : Nat) : List Nat :=
  [point * 10 + 0, point * 10 + 1, point * 10 + 2,
   point * 10 + 3, point * 10 + 4, point * 10 + 5,
   point * 10 + 6, point * 10 + 7, point * 10 + 8,
   point * 10 + 9]

theorem deployed_point_visit_order_eq_lowered (point : Nat) :
    deployedPointVisitOrder point = loweredPointVisitOrder point := by
  simp [deployedPointVisitOrder, loweredPointVisitOrder, List.range_succ]

def deployedPointDecode {α ε : Type} (decode : Nat → Except ε α)
    (point : Nat) : Except ε (List α) :=
  runDecodeOrder decode (deployedPointVisitOrder point)

def loweredPointDecode {α ε : Type} (decode : Nat → Except ε α)
    (point : Nat) : Except ε (List α) :=
  runDecodeOrder decode (loweredPointVisitOrder point)

/-- Each fixed helper returns the same ten values or the same first error as
the unchanged `map/collect` expression. -/
theorem deployed_point_decode_eq_lowered {α ε : Type}
    (decode : Nat → Except ε α) (point : Nat) :
    deployedPointDecode decode point = loweredPointDecode decode point := by
  simp [deployedPointDecode, loweredPointDecode,
    deployed_point_visit_order_eq_lowered]

/-- Source-shaped semantics of the unchanged three-point `for` loop.  `step`
is arbitrary and therefore represents both the weight update and the prepared
claim arithmetic, including any error they return. -/
def runDeployedPointLoop {α ε σ : Type}
    (decode : Nat → Except ε α)
    (step : σ → Nat → List α → Except ε σ) :
    List Nat → σ → Except ε (σ × List (List α))
  | [], state => .ok (state, [])
  | point :: rest, state =>
      match deployedPointDecode decode point with
      | .error error => .error error
      | .ok values =>
          match step state point values with
          | .error error => .error error
          | .ok next =>
              match runDeployedPointLoop decode step rest next with
              | .error error => .error error
              | .ok (finalState, later) =>
                  .ok (finalState, values :: later)

/-- The same loop skeleton over the adapter's explicit ten-call point
decoder.  The concrete adapter passes the literal list `[0, 1, 2]`. -/
def runLoweredPointLoop {α ε σ : Type}
    (decode : Nat → Except ε α)
    (step : σ → Nat → List α → Except ε σ) :
    List Nat → σ → Except ε (σ × List (List α))
  | [], state => .ok (state, [])
  | point :: rest, state =>
      match loweredPointDecode decode point with
      | .error error => .error error
      | .ok values =>
          match step state point values with
          | .error error => .error error
          | .ok next =>
              match runLoweredPointLoop decode step rest next with
              | .error error => .error error
              | .ok (finalState, later) =>
                  .ok (finalState, values :: later)

def deployedPreparePrefix {α ε σ : Type}
    (decode : Nat → Except ε α)
    (step : σ → Nat → List α → Except ε σ) (initial : σ) :
    Except ε (σ × List (List α)) :=
  runDeployedPointLoop decode step (List.range 3) initial

/-- Source-shaped semantics of the extraction adapter's three explicit point
calls. -/
def loweredPreparePrefix {α ε σ : Type}
    (decode : Nat → Except ε α)
    (step : σ → Nat → List α → Except ε σ) (initial : σ) :
    Except ε (σ × List (List α)) :=
  runLoweredPointLoop decode step [0, 1, 2] initial

theorem deployed_loop_eq_lowered {α ε σ : Type}
    (decode : Nat → Except ε α)
    (step : σ → Nat → List α → Except ε σ)
    (points : List Nat) (initial : σ) :
    runDeployedPointLoop decode step points initial =
      runLoweredPointLoop decode step points initial := by
  induction points generalizing initial with
  | nil => rfl
  | cons point rest ih =>
      simp only [runDeployedPointLoop, runLoweredPointLoop,
        deployed_point_decode_eq_lowered]
      cases hdecode : loweredPointDecode decode point with
      | error error => simp
      | ok values =>
          cases hstep : step initial point values with
          | error error => simp [hstep]
          | ok next => simp [hstep, ih]

/-- Unrolling the loop changes neither state, decoded rows, call order, nor
the first error, for arbitrary point and state operations. -/
theorem deployed_prepare_prefix_eq_lowered {α ε σ : Type}
    (decode : Nat → Except ε α)
    (step : σ → Nat → List α → Except ε σ) (initial : σ) :
    deployedPreparePrefix decode step initial =
      loweredPreparePrefix decode step initial := by
  unfold deployedPreparePrefix loweredPreparePrefix
  rw [show List.range 3 = [0, 1, 2] by decide]
  exact deployed_loop_eq_lowered decode step [0, 1, 2] initial

/-- The unchanged `from_fn` visit order for alphas and final coefficients. -/
def deployedFourValues {α : Type} (decode : Nat → Option α) (zero : α) :
    List α :=
  (List.range 4).map fun index => (decode index).getD zero

/-- The extraction adapter's explicit four calls. -/
def loweredFourValues {α : Type} (decode : Nat → Option α) (zero : α) :
    List α :=
  [(decode 0).getD zero, (decode 1).getD zero,
   (decode 2).getD zero, (decode 3).getD zero]

theorem deployed_four_values_eq_lowered {α : Type}
    (decode : Nat → Option α) (zero : α) :
    deployedFourValues decode zero = loweredFourValues decode zero := by
  simp [deployedFourValues, loweredFourValues, List.range_succ]

/-- The unchanged source selects the final byte slice inside `from_fn`; the
adapter selects the branch outside the four explicit calls. -/
def deployedFinalValues {α : Type} (realPrefix : Bool)
    (realDecode fallbackDecode : Nat → Option α) (zero : α) : List α :=
  deployedFourValues
    (if realPrefix then realDecode else fallbackDecode) zero

def loweredFinalValues {α : Type} (realPrefix : Bool)
    (realDecode fallbackDecode : Nat → Option α) (zero : α) : List α :=
  if realPrefix then loweredFourValues realDecode zero
  else loweredFourValues fallbackDecode zero

theorem deployed_final_values_eq_lowered {α : Type}
    (realPrefix : Bool) (realDecode fallbackDecode : Nat → Option α)
    (zero : α) :
    deployedFinalValues realPrefix realDecode fallbackDecode zero =
      loweredFinalValues realPrefix realDecode fallbackDecode zero := by
  cases realPrefix <;>
    simp [deployedFinalValues, loweredFinalValues,
      deployed_four_values_eq_lowered]

/-- Complete accepted-path model.  The arbitrary `finish` continuation
contains the common dense-claim update, grouped-mask installation, zero
checks, and construction of `PreparedRelation`. -/
def deployedAcceptedPrepare {α ε σ β : Type}
    (decodePoint : Nat → Except ε α)
    (step : σ → Nat → List α → Except ε σ) (initial : σ)
    (decodeAlpha decodeRealFinal decodeFallbackFinal : Nat → Option α)
    (realPrefix : Bool) (zero : α)
    (finish : (σ × List (List α)) → List α → List α → Except ε β) :
    Except ε β := do
  let preparedPrefix ← deployedPreparePrefix decodePoint step initial
  let alphas := deployedFourValues decodeAlpha zero
  let finals := deployedFinalValues realPrefix decodeRealFinal
    decodeFallbackFinal zero
  finish preparedPrefix alphas finals

def loweredAcceptedPrepare {α ε σ β : Type}
    (decodePoint : Nat → Except ε α)
    (step : σ → Nat → List α → Except ε σ) (initial : σ)
    (decodeAlpha decodeRealFinal decodeFallbackFinal : Nat → Option α)
    (realPrefix : Bool) (zero : α)
    (finish : (σ × List (List α)) → List α → List α → Except ε β) :
    Except ε β := do
  let preparedPrefix ← loweredPreparePrefix decodePoint step initial
  let alphas := loweredFourValues decodeAlpha zero
  let finals := loweredFinalValues realPrefix decodeRealFinal
    decodeFallbackFinal zero
  finish preparedPrefix alphas finals

/-- Universal extensional equality of the unchanged accepted Rust path and
the fixed-shape extraction adapter.  There is no input-specific hypothesis and
no equality premise left for the final verifier theorem. -/
theorem accepted_prepared_source_eq_extraction_adapter {α ε σ β : Type}
    (decodePoint : Nat → Except ε α)
    (step : σ → Nat → List α → Except ε σ) (initial : σ)
    (decodeAlpha decodeRealFinal decodeFallbackFinal : Nat → Option α)
    (realPrefix : Bool) (zero : α)
    (finish : (σ × List (List α)) → List α → List α → Except ε β) :
    deployedAcceptedPrepare decodePoint step initial decodeAlpha
      decodeRealFinal decodeFallbackFinal realPrefix zero finish =
    loweredAcceptedPrepare decodePoint step initial decodeAlpha
      decodeRealFinal decodeFallbackFinal realPrefix zero finish := by
  simp [deployedAcceptedPrepare, loweredAcceptedPrepare,
    deployed_prepare_prefix_eq_lowered, deployed_four_values_eq_lowered,
    deployed_final_values_eq_lowered]

#print axioms deployed_point_visit_order_eq_lowered
#print axioms deployed_point_decode_eq_lowered
#print axioms deployed_prepare_prefix_eq_lowered
#print axioms deployed_four_values_eq_lowered
#print axioms deployed_final_values_eq_lowered
#print axioms accepted_prepared_source_eq_extraction_adapter

end AspisV5RelationPrepareLowering
