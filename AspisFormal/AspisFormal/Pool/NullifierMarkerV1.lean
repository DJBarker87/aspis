import Mathlib

/-!
# Pool V1 nullifier-marker planning

This is the pure P3b state model.  A canonical writable PDA may be either a
data-empty System-owned account or an exact-size program-owned zero image.
Both plan as fresh.  Any valid occupied marker rejects, including an occupied
marker carrying a different context, and malformed account state fails closed.

The model deliberately excludes System CPI, allocation, assignment, rent,
Solana locking/rollback and Rust byte parsing.  A future atomic composition
must connect the successful verifier path, final account recheck and fixed
marker copy to this model.  Those are named source/runtime boundaries, not
hidden premises of the theorems below.
-/

set_option autoImplicit false

namespace AspisPool.NullifierMarkerV1

inductive TransitionKind where
  | privateTransfer
  | withdrawal
  deriving DecidableEq, Repr

/-- Semantic model of all fields frozen in the exact 208-byte `ASNM` marker. -/
structure Marker (Digest Binding : Type) where
  transitionKind : TransitionKind
  pool : Binding
  deploymentDomain : Binding
  nullifier : Digest
  retainedAnchorSequence : Nat
  retainedAnchorRoot : Digest
  verifierProfile : Binding
  verifierRelease : Binding
  deriving DecidableEq, Repr

/-- Account states distinguished by the Rust planner after owner/type/length
parsing. -/
inductive MarkerCell (MarkerType : Type) where
  | systemOwnedEmpty
  | programOwnedZeroed
  | consumed (marker : MarkerType)
  | malformed
  deriving DecidableEq, Repr

inductive Preparation where
  | createOrAllocateSystemOwned
  | populateProgramOwnedZeroed
  deriving DecidableEq, Repr

inductive PlanningError where
  | invalidAddress
  | invalidAccount
  | alreadyConsumed
  | malformed
  deriving DecidableEq, Repr

/-- Pure fail-closed planning. `addressValid` includes the exact seed-derived
PDA; `accountValid` includes writable, nonsigner and nonexecutable privilege
checks. -/
def plan {MarkerType : Type} (addressValid accountValid : Bool)
    (cell : MarkerCell MarkerType) : Except PlanningError Preparation :=
  if addressValid then
    if accountValid then
      match cell with
      | .systemOwnedEmpty => .ok .createOrAllocateSystemOwned
      | .programOwnedZeroed => .ok .populateProgramOwnedZeroed
      | .consumed _ => .error .alreadyConsumed
      | .malformed => .error .malformed
    else
      .error .invalidAccount
  else
    .error .invalidAddress

/-- Abstract final copy after a successful plan. No fallible runtime action is
modeled after this point. -/
def consume {MarkerType : Type} (addressValid accountValid : Bool)
    (cell : MarkerCell MarkerType) (marker : MarkerType) :
    Except PlanningError (MarkerCell MarkerType) :=
  match plan addressValid accountValid cell with
  | .ok _ => .ok (.consumed marker)
  | .error error => .error error

theorem wrong_address_fails_closed {MarkerType : Type}
    (accountValid : Bool) (cell : MarkerCell MarkerType) :
    plan false accountValid cell = .error .invalidAddress := by
  simp [plan]

theorem invalid_privileges_fail_closed {MarkerType : Type}
    (cell : MarkerCell MarkerType) :
    plan true false cell = .error .invalidAccount := by
  simp [plan]

theorem malformed_fails_closed {MarkerType : Type} :
    plan true true (.malformed : MarkerCell MarkerType) = .error .malformed := by
  rfl

/-- Any valid occupied marker blocks overwrite; equality of marker payloads
or injectivity of the PDA derivation is not required. -/
theorem occupied_marker_rejects {MarkerType : Type}
    (stored : MarkerType) :
    plan true true (.consumed stored) = .error .alreadyConsumed := by
  rfl

/-- The requested theorem: either admitted fresh account form consumes the
exact marker once, and the resulting occupied cell rejects a second use. -/
theorem fresh_nullifier_consumed_once {MarkerType : Type} (marker : MarkerType) :
    (consume true true .systemOwnedEmpty marker = .ok (.consumed marker) ∧
      consume true true (.consumed marker) marker = .error .alreadyConsumed) ∧
    (consume true true .programOwnedZeroed marker = .ok (.consumed marker) ∧
      consume true true (.consumed marker) marker = .error .alreadyConsumed) := by
  constructor
  · constructor <;> rfl
  · constructor <;> rfl

/-- Every successful pure consumption writes the exact requested marker. -/
theorem successful_consume_writes_exact_marker {MarkerType : Type}
    (addressValid accountValid : Bool) (cell next : MarkerCell MarkerType)
    (marker : MarkerType)
    (success : consume addressValid accountValid cell marker = .ok next) :
    next = .consumed marker := by
  unfold consume at success
  cases planned : plan addressValid accountValid cell with
  | ok preparation =>
      simp only [planned] at success
      cases success
      rfl
  | error planningError => simp [planned] at success

/-- Exact boundary obligations for connecting byte/account Rust to this pure
model and then relying on Solana atomicity. -/
structure SourceRuntimeBoundary (MarkerType : Type) where
  decodeCell : MarkerCell MarkerType
  modeledCell : MarkerCell MarkerType
  rustDecodeEqualsModel : decodeCell = modeledCell
  finalCopyPersistsOrRollsBack : Prop

#print axioms wrong_address_fails_closed
#print axioms invalid_privileges_fail_closed
#print axioms malformed_fails_closed
#print axioms occupied_marker_rejects
#print axioms fresh_nullifier_consumed_once
#print axioms successful_consume_writes_exact_marker

end AspisPool.NullifierMarkerV1
