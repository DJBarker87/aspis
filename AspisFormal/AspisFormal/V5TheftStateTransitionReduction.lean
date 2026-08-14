import AspisFormal.V5FixedVictimTheftGame
import AspisFormal.V5NullifierMarkerReplay

/-!
# Theft and state-transition reduction for the V5 spend

This file joins two existing results:

* the fixed-victim mathematical theft reduction; and
* the deterministic nullifier-marker replay model.

The combined theorem distinguishes a first fraudulent spend from a later
attempt to spend the same victim again.  A first spend is reduced to extractor
failure, recovery of the victim credential, a nullifier second preimage, a
note-commitment second preimage, or an explicit collision along the victim's
fixed Merkle position.  An exact-nullifier replay cannot succeed twice in the
sequential marker model.  A same-position attack with a different nullifier is
already covered by the mathematical theft reduction.  A collision in the
nullifier-to-marker address map can deny service, but the occupied-marker check
prevents it from making a second spend commit.  Any escape from that conclusion
lands in one of the named implementation/runtime failures below.

The latter half records the successful state shape of the current Rust path.
The current V5 source requires bump 255, checks the expected marker address
and account roles, rejects an occupied marker, verifies before writing, writes
the marker before the pool image, and retains the proof account.  The recorded
source that produced the mainnet program checked the expected marker address
but did not itself require the numeric bump; bump 255 was selected by the
runner and observed in the transaction.  Both source shapes are represented
below so that those facts are not conflated.  The proof rent is returned only
by the separate close instruction, to the writable System-owned signer
supplied as its refund account.  The close invalidates the proof data, credits
that account, and then zeros the proof balance.

These are executable Lean models of the source control flow, not Charon/Aeneas
translations of the Rust.  Correspondence to the compiled program, System
Program CPI behavior, writable-account locking, rollback of rejected
transactions, persistence, and finality remain explicit runtime boundaries.
-/

namespace AspisV5TheftStateTransitionReduction

open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open Aspis.TheftResistance
open AspisV5AcceptedSpendRelation
open AspisApplicationMerkleBinding
open AspisV5FixedVictimTheftGame
open AspisV5NullifierMarkerReplay
open AspisV5TheftResistance

/-! ## One sequential marker history -/

/-- Evidence that two marker consumptions both succeeded in one sequential
ledger history. -/
structure SequentialMarkerSuccess
    {Address Pool Nullifier : Type*}
    [DecidableEq Address] [DecidableEq Nullifier]
    (derive : Nullifier → Address)
    (firstNullifier secondNullifier : Nullifier) where
  initialLedger : MarkerLedger Address Pool Nullifier
  firstLedger : MarkerLedger Address Pool Nullifier
  secondLedger : MarkerLedger Address Pool Nullifier
  firstPool : Pool
  secondPool : Pool
  firstAddress : Address
  secondAddress : Address
  firstSuccess :
    consumeMarker derive initialLedger firstPool firstNullifier firstAddress =
      .ok firstLedger
  secondSuccess :
    consumeMarker derive firstLedger secondPool secondNullifier secondAddress =
      .ok secondLedger

/-- Two successful sequential marker writes necessarily used different
derived addresses. -/
theorem SequentialMarkerSuccess.derived_addresses_differ
    {Address Pool Nullifier : Type*}
    [DecidableEq Address] [DecidableEq Nullifier]
    {derive : Nullifier → Address}
    {firstNullifier secondNullifier : Nullifier}
    (run : SequentialMarkerSuccess (Pool := Pool) derive firstNullifier
      secondNullifier) :
    derive firstNullifier ≠ derive secondNullifier := by
  exact successive_successes_have_different_addresses derive
    run.initialLedger run.firstLedger run.secondLedger run.firstPool
    run.secondPool firstNullifier secondNullifier run.firstAddress
    run.secondAddress run.firstSuccess run.secondSuccess

/-- The same nullifier cannot be committed twice in a sequential marker
history. -/
theorem no_sequential_success_for_the_same_nullifier
    {Address Pool Nullifier : Type*}
    [DecidableEq Address] [DecidableEq Nullifier]
    (derive : Nullifier → Address) (nullifier : Nullifier) :
    ¬ Nonempty (SequentialMarkerSuccess (Pool := Pool) derive nullifier
      nullifier) := by
  rintro ⟨run⟩
  exact run.derived_addresses_differ rfl

/-! ## Failures outside the deterministic marker and theft models -/

/-- Runtime and implementation failures that are deliberately not proved by
the deterministic Lean model.  Each field is a separately auditable event. -/
structure RuntimeFailurePredicates (Coins : Type*) where
  rustStateModelMismatch : Coins → Prop
  systemProgramOrPdaMismatch : Coins → Prop
  writableAccountLockFailure : Coins → Prop
  rejectedTransactionRollbackFailure : Coins → Prop
  committedMarkerPersistenceFailure : Coins → Prop
  finalizedStateObservationFailure : Coins → Prop
  closeOrRefundModelMismatch : Coins → Prop

/-- One of the named implementation or Solana-runtime boundaries failed. -/
def NamedRuntimeFailureEvent
    {Coins : Type*} (failures : RuntimeFailurePredicates Coins)
    (coins : Coins) : Prop :=
  failures.rustStateModelMismatch coins ∨
  failures.systemProgramOrPdaMismatch coins ∨
  failures.writableAccountLockFailure coins ∨
  failures.rejectedTransactionRollbackFailure coins ∨
  failures.committedMarkerPersistenceFailure coins ∨
  failures.finalizedStateObservationFailure coins ∨
  failures.closeOrRefundModelMismatch coins

/-- A collision in the nullifier-to-marker-address map.  This is kept
separate from a nullifier-hash collision. -/
def MarkerAddressCollisionEvent
    {Address Nullifier : Type*}
    (derive : Nullifier → Address)
    (firstNullifier secondNullifier : Nullifier) : Prop :=
  firstNullifier ≠ secondNullifier ∧
    derive firstNullifier = derive secondNullifier

/-! ## Combined first-spend/repeat-spend game -/

/-- A later successful spend targets either the already-used victim nullifier
or the victim's exact tree position. -/
def RepeatVictimSpendEvent
    {Execution Coins : Type*}
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (deployedNullifier : Digest → Digest → Digest)
    (deployedNode : Digest → Digest → Digest)
    (Accepts : V5PublicStatement → Execution → Prop)
    (extract : V5PublicStatement → Execution → V5Witness)
    (statement : V5PublicStatement) (victim : FixedVictim)
    (adversary : Coins → Execution)
    (committedAgain : Coins → Prop) (coins : Coins) : Prop :=
  let witness := extract statement (adversary coins)
  Accepts statement (adversary coins) ∧
    committedAgain coins ∧
    (statement.nullifier = victimNullifier deployedNullifier victim ∨
      (witness.opened.bits = victim.bits ∧
        statement.currentAnchor =
          victimAnchor deployedOwner deployedNote deployedNode victim))

/-- The event covered by the final reduction: either the first accepted
fixed-victim attack or a later committed attack on the same victim. -/
def FirstOrRepeatVictimSpendEvent
    {Execution Coins : Type*}
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (deployedNullifier : Digest → Digest → Digest)
    (deployedNode : Digest → Digest → Digest)
    (Accepts : V5PublicStatement → Execution → Prop)
    (extract : V5PublicStatement → Execution → V5Witness)
    (statement : V5PublicStatement) (victim : FixedVictim)
    (adversary : Coins → Execution)
    (committedAgain : Coins → Prop) (coins : Coins) : Prop :=
  FixedVictimAttackEvent deployedOwner deployedNote deployedNullifier
      deployedNode Accepts extract statement victim adversary coins ∨
    RepeatVictimSpendEvent deployedOwner deployedNote deployedNullifier
      deployedNode Accepts extract statement victim adversary committedAgain
      coins

/-- Exact same-position Merkle collision witness produced by the fixed-victim
path theorem. -/
def SamePositionMerkleCollisionEvent
    {Execution Coins : Type*}
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (deployedNode : Digest → Digest → Digest)
    (extract : V5PublicStatement → Execution → V5Witness)
    (statement : V5PublicStatement) (victim : FixedVictim)
    (adversary : Coins → Execution) (coins : Coins) : Prop :=
  PathsExposeNodeCollision deployedNode
    (extract statement (adversary coins)).opened.L_in
    (victimLeaf deployedOwner deployedNote victim)
    victim.bits
    (extract statement (adversary coins)).opened.sib
    victim.siblings

/-- The six failure classes in the deterministic first-or-repeat reduction. -/
def ListedTheftFailureEvent
    {Execution Coins : Type*}
    (runtimeFailures : RuntimeFailurePredicates Coins)
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (deployedNullifier : Digest → Digest → Digest)
    (deployedNode : Digest → Digest → Digest)
    (Accepts : V5PublicStatement → Execution → Prop)
    (extract : V5PublicStatement → Execution → V5Witness)
    (statement : V5PublicStatement) (victim : FixedVictim)
    (adversary : Coins → Execution) (coins : Coins) : Prop :=
  ExtractionFailureEvent
      (V5WitnessRelation deployedOwner deployedNote deployedNullifier deployedNode)
      Accepts extract statement adversary coins ∨
  VictimCredentialRecoveryEvent Accepts extract statement victim adversary
      coins ∨
  TargetSecondPreimageEvent deployedNullifier witnessSecret witnessRandomness
      extract statement victim.opening.secret victim.opening.randomness
      adversary coins ∨
  InputNoteTargetSecondPreimageEvent deployedOwner deployedNote extract
      statement victim.opening adversary coins ∨
  SamePositionMerkleCollisionEvent deployedOwner deployedNote deployedNode
      extract statement victim adversary coins ∨
  NamedRuntimeFailureEvent runtimeFailures coins

/-- Turn the existing five-way mathematical classification into the first
five branches of `ListedTheftFailureEvent`, replacing the abstract alternative
Merkle-leaf event by its explicit node-collision witness. -/
theorem mathematical_failure_implies_listed_failure
    {Execution Coins : Type*}
    (runtimeFailures : RuntimeFailurePredicates Coins)
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (deployedNullifier : Digest → Digest → Digest)
    (deployedNode : Digest → Digest → Digest)
    (Accepts : V5PublicStatement → Execution → Prop)
    (extract : V5PublicStatement → Execution → V5Witness)
    (statement : V5PublicStatement) (victim : FixedVictim)
    (adversary : Coins → Execution) (coins : Coins) :
    FixedVictimMathematicalFailureEvent deployedOwner deployedNote
        deployedNullifier deployedNode Accepts extract statement victim
        adversary coins →
      ListedTheftFailureEvent runtimeFailures deployedOwner
        deployedNote deployedNullifier deployedNode Accepts extract statement
        victim adversary coins := by
  intro failure
  rcases failure with extraction | recovery | nullifier | note | merkle
  · exact Or.inl extraction
  · exact Or.inr (Or.inl recovery)
  · exact Or.inr (Or.inr (Or.inl nullifier))
  · exact Or.inr (Or.inr (Or.inr (Or.inl note)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (alternative_leaf_at_victim_position_exposes_node_collision
        deployedOwner deployedNote deployedNode Accepts extract statement victim
        adversary coins merkle)))))

/-- A real repeat is either represented by one sequential marker history or
one of the named implementation/runtime failures occurred. -/
def RepeatMarkerConnection
    {Address Pool Coins : Type*}
    [DecidableEq Address]
    (deriveMarkerAddress : Digest → Address)
    (runtimeFailures : RuntimeFailurePredicates Coins)
    (committedAgain : Coins → Prop)
    (firstNullifier secondNullifier : Digest) : Prop :=
  ∀ coins, committedAgain coins →
    Nonempty (SequentialMarkerSuccess (Pool := Pool) deriveMarkerAddress
      firstNullifier secondNullifier) ∨
    NamedRuntimeFailureEvent runtimeFailures coins

/-- Main deterministic reduction.  No probability or cryptographic hardness
claim is used here. -/
theorem first_or_repeat_victim_spend_implies_listed_failure
    {Address Pool Execution Coins : Type*}
    [DecidableEq Address]
    (deriveMarkerAddress : Digest → Address)
    (runtimeFailures : RuntimeFailurePredicates Coins)
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (deployedNullifier : Digest → Digest → Digest)
    (deployedNode : Digest → Digest → Digest)
    (Accepts : V5PublicStatement → Execution → Prop)
    (extract : V5PublicStatement → Execution → V5Witness)
    (statement : V5PublicStatement) (victim : FixedVictim)
    (adversary : Coins → Execution)
    (committedAgain : Coins → Prop)
    (repeatConnection : RepeatMarkerConnection (Pool := Pool)
      deriveMarkerAddress runtimeFailures committedAgain
      (victimNullifier deployedNullifier victim) statement.nullifier)
    (coins : Coins) :
    FirstOrRepeatVictimSpendEvent deployedOwner deployedNote deployedNullifier
        deployedNode Accepts extract statement victim adversary committedAgain
        coins →
      ListedTheftFailureEvent runtimeFailures deployedOwner
        deployedNote deployedNullifier deployedNode Accepts extract statement
        victim adversary coins := by
  intro attack
  rcases attack with firstAttack | repeatAttack
  · exact mathematical_failure_implies_listed_failure runtimeFailures
      deployedOwner deployedNote deployedNullifier deployedNode
      Accepts extract statement victim adversary coins
      (fixed_victim_attack_implies_mathematical_failure deployedOwner deployedNote
        deployedNullifier deployedNode Accepts extract statement victim
        adversary coins firstAttack)
  · rcases repeatAttack with ⟨accepted, committed, target⟩
    rcases target with sameNullifier | samePosition
    · rcases repeatConnection coins committed with modeled | runtime
      · rcases modeled with ⟨sequential⟩
        have differentAddresses := sequential.derived_addresses_differ
        exact False.elim (differentAddresses (congrArg deriveMarkerAddress
          sameNullifier.symm))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr runtime))))
    · exact mathematical_failure_implies_listed_failure runtimeFailures
        deployedOwner deployedNote deployedNullifier deployedNode Accepts extract
        statement victim adversary coins
        (fixed_victim_attack_implies_mathematical_failure deployedOwner
          deployedNote deployedNullifier deployedNode Accepts extract statement
          victim adversary coins ⟨accepted, Or.inr samePosition⟩)

/-! ## Small source-shaped account and state model -/

inductive AccountOwner where
  | program
  | system
  | other
  deriving DecidableEq

/-- The account roles used by the V5 spend instruction.  The marker's owner
and data shape are represented together by `SourceState.markers`. -/
structure V5AccountView (Address : Type*) where
  proofAddress : Address
  poolAddress : Address
  markerAddress : Address
  payerAddress : Address
  systemProgramAddress : Address
  proofOwner : AccountOwner
  poolOwner : AccountOwner
  payerOwner : AccountOwner
  proofWritable : Bool
  poolWritable : Bool
  markerWritable : Bool
  payerWritable : Bool
  payerSigner : Bool
  systemProgramExecutable : Bool

/-- Transaction-visible mutable state relevant to theft, replay, and the later
proof-rent refund. -/
structure SourceState (Address Nullifier Anchor : Type*) where
  poolAnchor : Anchor
  poolDeploymentDomain : Anchor
  poolSequence : Nat
  markers : MarkerLedger Address Address Nullifier
  proofClosed : Bool
  proofLamports : Nat
  lastRefund : Option (Address × Nat)

structure V5SourceRequest (Nullifier Anchor : Type*) where
  currentAnchor : Anchor
  outputAnchor : Anchor
  deploymentDomain : Anchor
  nullifier : Nullifier

/-- Exact successful-account checks in `validate_accounts_and_state` for the
retained-proof V5 path. -/
structure V5AccountChecks
    {Address : Type*} [DecidableEq Address]
    (accounts : V5AccountView Address)
    (canonicalSystemProgram : Address) : Prop where
  proofOwnedByProgram : accounts.proofOwner = .program
  poolOwnedByProgram : accounts.poolOwner = .program
  proofReadOnly : accounts.proofWritable = false
  poolWritable : accounts.poolWritable = true
  markerWritable : accounts.markerWritable = true
  payerWritable : accounts.payerWritable = true
  payerSigner : accounts.payerSigner = true
  payerSystemOwned : accounts.payerOwner = .system
  canonicalSystemProgram : accounts.systemProgramAddress = canonicalSystemProgram
  systemProgramExecutable : accounts.systemProgramExecutable = true
  proofNePool : accounts.proofAddress ≠ accounts.poolAddress
  proofNeMarker : accounts.proofAddress ≠ accounts.markerAddress
  proofNePayer : accounts.proofAddress ≠ accounts.payerAddress
  poolNeMarker : accounts.poolAddress ≠ accounts.markerAddress
  payerNePool : accounts.payerAddress ≠ accounts.poolAddress
  payerNeMarker : accounts.payerAddress ≠ accounts.markerAddress

def markerAvailable
    {Address Nullifier : Type*}
    (cell : MarkerCell Address Nullifier) : Prop :=
  cell = .systemOwnedEmpty ∨ cell = .programOwnedZeroed

/-- Conditions common to the recorded deployed source and the current V5
source.  The numeric bump policy is intentionally absent here. -/
structure V5SourceCoreSuccessRequirements
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (derive : Nullifier → Address × Fin 256)
    (canonicalSystemProgram : Address)
    (accounts : V5AccountView Address)
    (state : SourceState Address Nullifier Anchor)
    (request : V5SourceRequest Nullifier Anchor)
    (proofAccepted mutableStateRechecked : Prop) : Prop where
  accountsValid : V5AccountChecks accounts canonicalSystemProgram
  expectedMarkerAddress : accounts.markerAddress = (derive request.nullifier).1
  deploymentDomainMatches :
    state.poolDeploymentDomain = request.deploymentDomain
  currentAnchorMatches : state.poolAnchor = request.currentAnchor
  sequenceCanAdvance : state.poolSequence < 2 ^ 64 - 1
  markerIsAvailable : markerAvailable (state.markers accounts.markerAddress)
  proofIsOpen : state.proofClosed = false
  proofAccepted : proofAccepted
  mutableStateRechecked : mutableStateRechecked

/-- The current source adds an explicit bump-255 rejection to the common
successful path. -/
structure V5SourceSuccessRequirements
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (derive : Nullifier → Address × Fin 256)
    (canonicalSystemProgram : Address)
    (accounts : V5AccountView Address)
    (state : SourceState Address Nullifier Anchor)
    (request : V5SourceRequest Nullifier Anchor)
    (proofAccepted mutableStateRechecked : Prop) : Prop
    extends V5SourceCoreSuccessRequirements derive canonicalSystemProgram
      accounts state request proofAccepted mutableStateRechecked where
  bumpIs255 : (derive request.nullifier).2 = 255

inductive SourceTraceEvent (Address : Type*) where
  | accountsValidated
  | proofVerified
  | systemOwnedMarkerPrepared
  | programOwnedMarkerReady
  | mutableStateRechecked
  | markerWritten
  | poolWritten
  | proofInvalidated
  | refundCredited (recipient : Address)
  | proofBalanceZeroed
  deriving DecidableEq

inductive SourceError where
  | spendRejected
  | closeRejected
  deriving DecidableEq

inductive SourceOutcome (State Address : Type*) where
  | rejected (error : SourceError) (trace : List (SourceTraceEvent Address))
  | committed (state : State) (trace : List (SourceTraceEvent Address))

def v5SuccessTrace
    {Address Nullifier Anchor : Type*}
    (accounts : V5AccountView Address)
    (state : SourceState Address Nullifier Anchor) :
    List (SourceTraceEvent Address) :=
  [.accountsValidated, .proofVerified] ++
    (match state.markers accounts.markerAddress with
    | .systemOwnedEmpty => [.systemOwnedMarkerPrepared]
    | _ => [.programOwnedMarkerReady]) ++
    [.mutableStateRechecked, .markerWritten, .poolWritten]

def applyV5Success
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (accounts : V5AccountView Address)
    (state : SourceState Address Nullifier Anchor)
    (request : V5SourceRequest Nullifier Anchor) :
    SourceState Address Nullifier Anchor :=
  { state with
    poolAnchor := request.outputAnchor
    poolSequence := state.poolSequence + 1
    markers := Function.update state.markers accounts.markerAddress
      (.spent accounts.poolAddress request.nullifier) }

/-- Transaction-visible model of the successful/rejected retained-proof V5
path.  A rejected outcome exposes no committed state; the rollback projection
below maps it to the input state. -/
noncomputable def runV5SourceTransition
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (derive : Nullifier → Address × Fin 256)
    (canonicalSystemProgram : Address)
    (accounts : V5AccountView Address)
    (state : SourceState Address Nullifier Anchor)
    (request : V5SourceRequest Nullifier Anchor)
    (proofAccepted mutableStateRechecked : Prop) :
    SourceOutcome (SourceState Address Nullifier Anchor) Address :=
  letI : Decidable (V5SourceSuccessRequirements derive canonicalSystemProgram
      accounts state request proofAccepted mutableStateRechecked) :=
    Classical.propDecidable _
  if _requirements : V5SourceSuccessRequirements derive canonicalSystemProgram
      accounts state request proofAccepted mutableStateRechecked then
    .committed (applyV5Success accounts state request)
      (v5SuccessTrace accounts state)
  else
    .rejected .spendRejected []

/-- Transaction-visible model of the recorded deployed source.  It uses the
same canonical PDA returned by `derive`, but does not reject merely because
the returned numeric bump is below 255. -/
noncomputable def runRecordedDeployedV5SourceTransition
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (derive : Nullifier → Address × Fin 256)
    (canonicalSystemProgram : Address)
    (accounts : V5AccountView Address)
    (state : SourceState Address Nullifier Anchor)
    (request : V5SourceRequest Nullifier Anchor)
    (proofAccepted mutableStateRechecked : Prop) :
    SourceOutcome (SourceState Address Nullifier Anchor) Address :=
  letI : Decidable (V5SourceCoreSuccessRequirements derive
      canonicalSystemProgram accounts state request proofAccepted
      mutableStateRechecked) := Classical.propDecidable _
  if _requirements : V5SourceCoreSuccessRequirements derive
      canonicalSystemProgram accounts state request proofAccepted
      mutableStateRechecked then
    .committed (applyV5Success accounts state request)
      (v5SuccessTrace accounts state)
  else
    .rejected .spendRejected []

/-- Success of the recorded deployed source exposes the common account,
address, domain, anchor, sequence, marker, proof, and recheck conditions, but
not a numeric bump condition. -/
theorem recorded_deployed_v5_success_implies_core_requirements
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (derive : Nullifier → Address × Fin 256)
    (canonicalSystemProgram : Address)
    (accounts : V5AccountView Address)
    (state nextState : SourceState Address Nullifier Anchor)
    (request : V5SourceRequest Nullifier Anchor)
    (proofAccepted mutableStateRechecked : Prop)
    (trace : List (SourceTraceEvent Address))
    (success : runRecordedDeployedV5SourceTransition derive
      canonicalSystemProgram accounts state request proofAccepted
      mutableStateRechecked = .committed nextState trace) :
    V5SourceCoreSuccessRequirements derive canonicalSystemProgram accounts
      state request proofAccepted mutableStateRechecked := by
  unfold runRecordedDeployedV5SourceTransition at success
  split at success
  · assumption
  · simp at success

/-- For the mainnet run, bump 255 is a separate observed/runner premise rather
than a consequence of the recorded program's acceptance branch. -/
theorem recorded_deployed_success_and_observed_bump_255
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (derive : Nullifier → Address × Fin 256)
    (canonicalSystemProgram : Address)
    (accounts : V5AccountView Address)
    (state nextState : SourceState Address Nullifier Anchor)
    (request : V5SourceRequest Nullifier Anchor)
    (proofAccepted mutableStateRechecked : Prop)
    (trace : List (SourceTraceEvent Address))
    (success : runRecordedDeployedV5SourceTransition derive
      canonicalSystemProgram accounts state request proofAccepted
      mutableStateRechecked = .committed nextState trace)
    (observedBump : (derive request.nullifier).2 = 255) :
    V5SourceCoreSuccessRequirements derive canonicalSystemProgram accounts
        state request proofAccepted mutableStateRechecked ∧
      (derive request.nullifier).2 = 255 := by
  exact ⟨recorded_deployed_v5_success_implies_core_requirements derive
    canonicalSystemProgram accounts state nextState request proofAccepted
    mutableStateRechecked trace success, observedBump⟩

/-- Success exposes every exact account, address, bump, marker, proof, and
recheck condition. -/
theorem v5_source_success_implies_requirements
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (derive : Nullifier → Address × Fin 256)
    (canonicalSystemProgram : Address)
    (accounts : V5AccountView Address)
    (state nextState : SourceState Address Nullifier Anchor)
    (request : V5SourceRequest Nullifier Anchor)
    (proofAccepted mutableStateRechecked : Prop)
    (trace : List (SourceTraceEvent Address))
    (success : runV5SourceTransition derive canonicalSystemProgram accounts
      state request proofAccepted mutableStateRechecked =
      .committed nextState trace) :
    V5SourceSuccessRequirements derive canonicalSystemProgram accounts state
      request proofAccepted mutableStateRechecked := by
  unfold runV5SourceTransition at success
  split at success
  · assumption
  · simp at success

/-- A successful V5 transition writes the exact marker and next pool image,
while retaining the proof account and its rent. -/
theorem v5_source_success_exact_state
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (derive : Nullifier → Address × Fin 256)
    (canonicalSystemProgram : Address)
    (accounts : V5AccountView Address)
    (state nextState : SourceState Address Nullifier Anchor)
    (request : V5SourceRequest Nullifier Anchor)
    (proofAccepted mutableStateRechecked : Prop)
    (trace : List (SourceTraceEvent Address))
    (success : runV5SourceTransition derive canonicalSystemProgram accounts
      state request proofAccepted mutableStateRechecked =
      .committed nextState trace) :
    nextState.poolAnchor = request.outputAnchor ∧
    nextState.poolSequence = state.poolSequence + 1 ∧
    nextState.markers ((derive request.nullifier).1) =
      .spent accounts.poolAddress request.nullifier ∧
    nextState.proofClosed = state.proofClosed ∧
    nextState.proofLamports = state.proofLamports ∧
    nextState.lastRefund = state.lastRefund := by
  have requirements := v5_source_success_implies_requirements derive
    canonicalSystemProgram accounts state nextState request proofAccepted
    mutableStateRechecked trace success
  have modeled : runV5SourceTransition derive canonicalSystemProgram accounts
      state request proofAccepted mutableStateRechecked =
      .committed (applyV5Success accounts state request)
        (v5SuccessTrace accounts state) := by
    simp [runV5SourceTransition, requirements]
  rw [modeled] at success
  injection success with stateEq _traceEq
  subst nextState
  simp [applyV5Success, requirements.expectedMarkerAddress]

/-- An already-written marker cannot reach the committed branch. -/
theorem v5_source_rejects_preexisting_marker
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (derive : Nullifier → Address × Fin 256)
    (canonicalSystemProgram : Address)
    (accounts : V5AccountView Address)
    (state : SourceState Address Nullifier Anchor)
    (request : V5SourceRequest Nullifier Anchor)
    (proofAccepted mutableStateRechecked : Prop)
    (storedPool : Address) (storedNullifier : Nullifier)
    (occupied : state.markers accounts.markerAddress =
      .spent storedPool storedNullifier) :
    ¬ ∃ nextState trace, runV5SourceTransition derive canonicalSystemProgram
      accounts state request proofAccepted mutableStateRechecked =
        .committed nextState trace := by
  rintro ⟨nextState, trace, success⟩
  have requirements := v5_source_success_implies_requirements derive
    canonicalSystemProgram accounts state nextState request proofAccepted
    mutableStateRechecked trace success
  have available := requirements.markerIsAvailable
  rw [occupied] at available
  rcases available with available | available <;>
    cases available

/-- A successful V5 transition really enforced bump 255. -/
theorem v5_source_success_has_bump_255
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (derive : Nullifier → Address × Fin 256)
    (canonicalSystemProgram : Address)
    (accounts : V5AccountView Address)
    (state nextState : SourceState Address Nullifier Anchor)
    (request : V5SourceRequest Nullifier Anchor)
    (proofAccepted mutableStateRechecked : Prop)
    (trace : List (SourceTraceEvent Address))
    (success : runV5SourceTransition derive canonicalSystemProgram accounts
      state request proofAccepted mutableStateRechecked =
      .committed nextState trace) :
    (derive request.nullifier).2 = 255 :=
  (v5_source_success_implies_requirements derive canonicalSystemProgram
    accounts state nextState request proofAccepted mutableStateRechecked trace
    success).bumpIs255

/-- The successful source path used the exact derived marker account as well
as bump 255. -/
theorem v5_source_success_has_expected_marker_and_bump
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (derive : Nullifier → Address × Fin 256)
    (canonicalSystemProgram : Address)
    (accounts : V5AccountView Address)
    (state nextState : SourceState Address Nullifier Anchor)
    (request : V5SourceRequest Nullifier Anchor)
    (proofAccepted mutableStateRechecked : Prop)
    (trace : List (SourceTraceEvent Address))
    (success : runV5SourceTransition derive canonicalSystemProgram accounts
      state request proofAccepted mutableStateRechecked =
      .committed nextState trace) :
    accounts.markerAddress = (derive request.nullifier).1 ∧
      (derive request.nullifier).2 = 255 := by
  have requirements := v5_source_success_implies_requirements derive
    canonicalSystemProgram accounts state nextState request proofAccepted
    mutableStateRechecked trace success
  exact ⟨requirements.expectedMarkerAddress, requirements.bumpIs255⟩

/-- The successful V5 trace ends with the mutable-state recheck, marker write,
and pool write.  It contains no proof close or refund. -/
theorem v5_source_success_exact_trace
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (derive : Nullifier → Address × Fin 256)
    (canonicalSystemProgram : Address)
    (accounts : V5AccountView Address)
    (state nextState : SourceState Address Nullifier Anchor)
    (request : V5SourceRequest Nullifier Anchor)
    (proofAccepted mutableStateRechecked : Prop)
    (trace : List (SourceTraceEvent Address))
    (success : runV5SourceTransition derive canonicalSystemProgram accounts
      state request proofAccepted mutableStateRechecked =
      .committed nextState trace) :
    trace = v5SuccessTrace accounts state := by
  have requirements := v5_source_success_implies_requirements derive
    canonicalSystemProgram accounts state nextState request proofAccepted
    mutableStateRechecked trace success
  have modeled : runV5SourceTransition derive canonicalSystemProgram accounts
      state request proofAccepted mutableStateRechecked =
      .committed (applyV5Success accounts state request)
        (v5SuccessTrace accounts state) := by
    simp [runV5SourceTransition, requirements]
  rw [modeled] at success
  injection success with _stateEq traceEq
  exact traceEq.symm

/-! ## The later proof-account close and rent refund -/

structure CloseAccountView (Address : Type*) where
  proofAddress : Address
  refundAddress : Address
  proofOwner : AccountOwner
  refundOwner : AccountOwner
  proofSigner : Bool
  refundSigner : Bool
  proofWritable : Bool
  refundWritable : Bool

structure CloseSuccessRequirements
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (accounts : CloseAccountView Address)
    (state : SourceState Address Nullifier Anchor) : Prop where
  proofOwnedByProgram : accounts.proofOwner = .program
  refundSystemOwned : accounts.refundOwner = .system
  proofSigner : accounts.proofSigner = true
  refundSigner : accounts.refundSigner = true
  proofWritable : accounts.proofWritable = true
  refundWritable : accounts.refundWritable = true
  distinctAccounts : accounts.proofAddress ≠ accounts.refundAddress
  proofIsOpen : state.proofClosed = false
  positiveRefund : state.proofLamports ≠ 0

def applyCloseSuccess
    {Address Nullifier Anchor : Type*}
    (accounts : CloseAccountView Address)
    (state : SourceState Address Nullifier Anchor) :
    SourceState Address Nullifier Anchor :=
  { state with
    proofClosed := true
    proofLamports := 0
    lastRefund := some (accounts.refundAddress, state.proofLamports) }

def closeSuccessTrace
    {Address : Type*} (accounts : CloseAccountView Address) :
    List (SourceTraceEvent Address) :=
  [.proofInvalidated, .refundCredited accounts.refundAddress,
    .proofBalanceZeroed]

/-- Source-shaped model of the separate proof close used after the retained V5
spend. -/
noncomputable def runSourceProofClose
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (accounts : CloseAccountView Address)
    (state : SourceState Address Nullifier Anchor) :
    SourceOutcome (SourceState Address Nullifier Anchor) Address :=
  letI : Decidable (CloseSuccessRequirements accounts state) :=
    Classical.propDecidable _
  if _requirements : CloseSuccessRequirements accounts state then
    .committed (applyCloseSuccess accounts state) (closeSuccessTrace accounts)
  else
    .rejected .closeRejected []

/-- A committed close exposes the signer, owner, access, distinct-address, and
positive-balance checks made before any mutation. -/
theorem close_success_implies_requirements
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (accounts : CloseAccountView Address)
    (state nextState : SourceState Address Nullifier Anchor)
    (trace : List (SourceTraceEvent Address))
    (success : runSourceProofClose accounts state =
      .committed nextState trace) :
    CloseSuccessRequirements accounts state := by
  unfold runSourceProofClose at success
  split at success
  · assumption
  · simp at success

/-- A successful close sends the entire modeled proof balance to the supplied
refund signer and leaves the already-committed pool and marker state alone. -/
theorem close_success_refunds_exact_recipient_and_preserves_spend
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (accounts : CloseAccountView Address)
    (state nextState : SourceState Address Nullifier Anchor)
    (trace : List (SourceTraceEvent Address))
    (success : runSourceProofClose accounts state =
      .committed nextState trace) :
    nextState.proofClosed = true ∧
    nextState.proofLamports = 0 ∧
    nextState.lastRefund = some (accounts.refundAddress, state.proofLamports) ∧
    nextState.poolAnchor = state.poolAnchor ∧
    nextState.poolSequence = state.poolSequence ∧
    nextState.markers = state.markers ∧
    trace = [.proofInvalidated, .refundCredited accounts.refundAddress,
      .proofBalanceZeroed] := by
  unfold runSourceProofClose at success
  split at success
  · cases success
    simp [applyCloseSuccess, closeSuccessTrace]
  · simp at success

/-- In the actual retained-proof lifecycle, the committed marker and pool
writes occur before the later close transaction invalidates and refunds the
proof account. -/
theorem v5_then_close_trace_has_state_writes_before_refund
    {Address Nullifier Anchor : Type*}
    [DecidableEq Address]
    (derive : Nullifier → Address × Fin 256)
    (canonicalSystemProgram : Address)
    (v5Accounts : V5AccountView Address)
    (closeAccounts : CloseAccountView Address)
    (initial afterSpend afterClose : SourceState Address Nullifier Anchor)
    (request : V5SourceRequest Nullifier Anchor)
    (proofAccepted mutableStateRechecked : Prop)
    (v5Trace closeTrace : List (SourceTraceEvent Address))
    (spendSuccess : runV5SourceTransition derive canonicalSystemProgram
      v5Accounts initial request proofAccepted mutableStateRechecked =
      .committed afterSpend v5Trace)
    (closeSuccess : runSourceProofClose closeAccounts afterSpend =
      .committed afterClose closeTrace) :
    ∃ eventsBeforeWrites,
      v5Trace ++ closeTrace =
        eventsBeforeWrites ++ [.markerWritten, .poolWritten, .proofInvalidated,
          .refundCredited closeAccounts.refundAddress, .proofBalanceZeroed] := by
  have spendTrace := v5_source_success_exact_trace derive
    canonicalSystemProgram v5Accounts initial afterSpend request proofAccepted
    mutableStateRechecked v5Trace spendSuccess
  have closeFacts := close_success_refunds_exact_recipient_and_preserves_spend
    closeAccounts afterSpend afterClose closeTrace closeSuccess
  rw [spendTrace, closeFacts.2.2.2.2.2.2]
  refine ⟨[.accountsValidated, .proofVerified] ++
      (match initial.markers v5Accounts.markerAddress with
      | .systemOwnedEmpty => [.systemOwnedMarkerPrepared]
      | _ => [.programOwnedMarkerReady]) ++
      [.mutableStateRechecked], ?_⟩
  simp [v5SuccessTrace, List.append_assoc]

/-- Transaction-visible rollback projection.  The theorem is definitional in
this model; real Solana rollback is one of the named runtime premises above. -/
def visibleStateAfter
    {State Address : Type*}
    (initial : State) (outcome : SourceOutcome State Address) : State :=
  match outcome with
  | .rejected _ _ => initial
  | .committed state _ => state

theorem rejected_outcome_rolls_back_in_model
    {State Address : Type*}
    (initial : State) (error : SourceError)
    (trace : List (SourceTraceEvent Address)) :
    visibleStateAfter initial (.rejected error trace) = initial := by
  rfl

#print axioms SequentialMarkerSuccess.derived_addresses_differ
#print axioms no_sequential_success_for_the_same_nullifier
#print axioms mathematical_failure_implies_listed_failure
#print axioms first_or_repeat_victim_spend_implies_listed_failure
#print axioms recorded_deployed_v5_success_implies_core_requirements
#print axioms recorded_deployed_success_and_observed_bump_255
#print axioms v5_source_success_exact_state
#print axioms v5_source_rejects_preexisting_marker
#print axioms v5_source_success_has_bump_255
#print axioms v5_source_success_has_expected_marker_and_bump
#print axioms v5_source_success_exact_trace
#print axioms close_success_implies_requirements
#print axioms close_success_refunds_exact_recipient_and_preserves_spend
#print axioms v5_then_close_trace_has_state_writes_before_refund
#print axioms rejected_outcome_rolls_back_in_model

end AspisV5TheftStateTransitionReduction
