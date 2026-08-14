import Mathlib

/-!
# V5 nullifier-marker replay prevention

This file models the nullifier-account branch in
`programs/aspis-verifier/src/atomic_payment.rs`.

The relevant validation and marker-write branches are identical in the
recorded deployed source commit
`06788d44d30ea8cbd391899dddaf6f0acc6e4a3f` and the current file.  Current
code adds a bump-255 check before this branch; that extra rejection does not
change any theorem below.  This source comparison is an audit observation,
not a machine-checked Rust-to-Lean correspondence theorem.

The program accepts two empty marker-account forms: a System-owned empty
account and a program-owned, correctly sized zeroed account.  A successful
transition replaces either form with a marker containing the pool and public
nullifier.  A later transition at that address rejects both the same
nullifier and a different nullifier.

The important consequence is independent of PDA injectivity.  Even if two
different nullifiers were to resolve to the same address, they could not both
consume that address in sequence: after the first commit, the second observes
an occupied marker and rejects.  A PDA collision could still deny service by
occupying an address that another nullifier would need.

This file is not yet connected to the fixed-victim theft game, whose deployed
case split still lists PDA aliasing separately.  Removing that term requires a
proof that the Rust/runtime execution and the deployed attack experiment obey
this marker model; the result below does not silently assume that connection.

This is a theorem about the explicit state model below.  It does not prove
that the compiled Rust implements this model or that Solana provides account
locking, transaction rollback, and persistent finalized state.  Those remain
the exact external runtime and implementation boundaries.  It also does not
stop the first fraudulent spend that reaches an empty marker.  Preventing that
requires the separate proof-soundness and fixed-victim arguments.  The model
combines initial marker validation and the final marker write into one
sequential step; it does not model an account changing while the verifier is
running, the System Program CPI, marker bytes, or the pool-state update.
-/

namespace AspisV5NullifierMarkerReplay

/-- The four marker-account states distinguished by the Rust validator. -/
inductive MarkerCell (Pool Nullifier : Type*) where
  /-- A System-owned account with no data. -/
  | systemOwnedEmpty
  /-- A program-owned, correctly sized all-zero account. -/
  | programOwnedZeroed
  /-- A valid marker written by a successful spend. -/
  | spent (pool : Pool) (nullifier : Nullifier)
  /-- Any other owner, length, discriminator, version, or contents. -/
  | malformed
  deriving DecidableEq

/-- The marker errors relevant to replay and address validation. -/
inductive MarkerError where
  | invalidAddress
  | alreadySpent
  | occupiedByDifferentNullifier
  | malformed
  deriving DecidableEq

/-- One marker cell per derived address. -/
abbrev MarkerLedger (Address Pool Nullifier : Type*) :=
  Address → MarkerCell Pool Nullifier

/-- With one program id and seed schedule fixed inside `derive`, equal
nullifiers necessarily select equal marker addresses. -/
theorem same_nullifier_has_same_address
    {Address Nullifier : Type*}
    (derive : Nullifier → Address)
    {firstNullifier secondNullifier : Nullifier}
    (sameNullifier : firstNullifier = secondNullifier) :
    derive firstNullifier = derive secondNullifier := by
  exact congrArg derive sameNullifier

/-- Pure model of the Rust marker validation and final marker write.

`derive` includes the fixed seed and program id.  Keeping it arbitrary makes
the replay theorem stronger: no injectivity assumption is used. -/
def consumeMarker
    {Address Pool Nullifier : Type*}
    [DecidableEq Address] [DecidableEq Nullifier]
    (derive : Nullifier → Address)
    (ledger : MarkerLedger Address Pool Nullifier)
    (pool : Pool) (nullifier : Nullifier) (suppliedAddress : Address) :
    Except MarkerError (MarkerLedger Address Pool Nullifier) :=
  if suppliedAddress = derive nullifier then
    match ledger suppliedAddress with
    | .systemOwnedEmpty | .programOwnedZeroed =>
        .ok (Function.update ledger suppliedAddress (.spent pool nullifier))
    | .spent _ storedNullifier =>
        if storedNullifier = nullifier then
          .error .alreadySpent
        else
          .error .occupiedByDifferentNullifier
    | .malformed => .error .malformed
  else
    .error .invalidAddress

/-- Every successful marker consumption used the derived address and wrote
the exact pool/nullifier pair there. -/
theorem successful_consume_writes_exact_marker
    {Address Pool Nullifier : Type*}
    [DecidableEq Address] [DecidableEq Nullifier]
    (derive : Nullifier → Address)
    (ledger nextLedger : MarkerLedger Address Pool Nullifier)
    (pool : Pool) (nullifier : Nullifier) (suppliedAddress : Address)
    (success : consumeMarker derive ledger pool nullifier suppliedAddress =
      .ok nextLedger) :
    suppliedAddress = derive nullifier ∧
      nextLedger (derive nullifier) = .spent pool nullifier := by
  unfold consumeMarker at success
  split at success
  next correctAddress =>
    constructor
    · exact correctAddress
    · subst suppliedAddress
      cases current : ledger (derive nullifier) <;> simp [current] at success
      · subst nextLedger
        simp
      · subst nextLedger
        simp
      · split at success <;> simp at success
  next wrongAddress =>
    simp at success

/-- Exact result of retrying an occupied marker address.  Equality of the two
nullifiers selects the ordinary replay error; inequality selects the
inconsistent-marker error. -/
theorem consume_after_success_at_same_address
    {Address Pool Nullifier : Type*}
    [DecidableEq Address] [DecidableEq Nullifier]
    (derive : Nullifier → Address)
    (ledger nextLedger : MarkerLedger Address Pool Nullifier)
    (firstPool secondPool : Pool)
    (firstNullifier secondNullifier : Nullifier)
    (firstAddress : Address)
    (firstSuccess : consumeMarker derive ledger firstPool firstNullifier
      firstAddress = .ok nextLedger)
    (sameAddress : derive secondNullifier = derive firstNullifier) :
    consumeMarker derive nextLedger secondPool secondNullifier
        (derive secondNullifier) =
      .error (if firstNullifier = secondNullifier then .alreadySpent
        else .occupiedByDifferentNullifier) := by
  have written :=
    (successful_consume_writes_exact_marker derive ledger nextLedger firstPool
      firstNullifier firstAddress firstSuccess).2
  simp only [consumeMarker, if_pos]
  rw [sameAddress, written]
  by_cases equalNullifiers : firstNullifier = secondNullifier
  · subst secondNullifier
    simp
  · simp [equalNullifiers]

/-- A committed nullifier cannot be consumed a second time.  This theorem
uses no hash-security or PDA-injectivity premise. -/
theorem same_nullifier_replay_rejected
    {Address Pool Nullifier : Type*}
    [DecidableEq Address] [DecidableEq Nullifier]
    (derive : Nullifier → Address)
    (ledger nextLedger : MarkerLedger Address Pool Nullifier)
    (firstPool secondPool : Pool) (nullifier : Nullifier)
    (firstAddress : Address)
    (firstSuccess : consumeMarker derive ledger firstPool nullifier
      firstAddress = .ok nextLedger) :
    consumeMarker derive nextLedger secondPool nullifier (derive nullifier) =
      .error .alreadySpent := by
  simpa using consume_after_success_at_same_address derive ledger nextLedger
    firstPool secondPool nullifier nullifier firstAddress firstSuccess rfl

/-- Even a collision of the address-derivation function cannot make a second,
different nullifier overwrite the first marker.  It rejects instead. -/
theorem different_nullifier_same_address_rejected
    {Address Pool Nullifier : Type*}
    [DecidableEq Address] [DecidableEq Nullifier]
    (derive : Nullifier → Address)
    (ledger nextLedger : MarkerLedger Address Pool Nullifier)
    (firstPool secondPool : Pool)
    (firstNullifier secondNullifier : Nullifier)
    (firstAddress : Address)
    (firstSuccess : consumeMarker derive ledger firstPool firstNullifier
      firstAddress = .ok nextLedger)
    (differentNullifiers : firstNullifier ≠ secondNullifier)
    (sameAddress : derive secondNullifier = derive firstNullifier) :
    consumeMarker derive nextLedger secondPool secondNullifier
        (derive secondNullifier) =
      .error .occupiedByDifferentNullifier := by
  rw [consume_after_success_at_same_address derive ledger nextLedger firstPool
    secondPool firstNullifier secondNullifier firstAddress firstSuccess sameAddress]
  simp [differentNullifiers]

/-- Therefore two successful sequential consumptions must use different marker
addresses.  This remains true when the nullifiers themselves are different. -/
theorem successive_successes_have_different_addresses
    {Address Pool Nullifier : Type*}
    [DecidableEq Address] [DecidableEq Nullifier]
    (derive : Nullifier → Address)
    (ledger firstLedger secondLedger : MarkerLedger Address Pool Nullifier)
    (firstPool secondPool : Pool)
    (firstNullifier secondNullifier : Nullifier)
    (firstAddress secondAddress : Address)
    (firstSuccess : consumeMarker derive ledger firstPool firstNullifier
      firstAddress = .ok firstLedger)
    (secondSuccess : consumeMarker derive firstLedger secondPool secondNullifier
      secondAddress = .ok secondLedger) :
    derive firstNullifier ≠ derive secondNullifier := by
  intro sameAddress
  have secondDerived :=
    (successful_consume_writes_exact_marker derive firstLedger secondLedger
      secondPool secondNullifier secondAddress secondSuccess).1
  have rejected := consume_after_success_at_same_address derive ledger firstLedger
    firstPool secondPool firstNullifier secondNullifier firstAddress firstSuccess
    sameAddress.symm
  rw [secondDerived] at secondSuccess
  rw [secondSuccess] at rejected
  simp at rejected

end AspisV5NullifierMarkerReplay

#print axioms AspisV5NullifierMarkerReplay.successful_consume_writes_exact_marker
#print axioms AspisV5NullifierMarkerReplay.same_nullifier_has_same_address
#print axioms AspisV5NullifierMarkerReplay.same_nullifier_replay_rejected
#print axioms AspisV5NullifierMarkerReplay.different_nullifier_same_address_rejected
#print axioms AspisV5NullifierMarkerReplay.successive_successes_have_different_addresses
