import AspisFormal.Pool.AtomicSettlementV1

/-!
# Pool V1 prepared-settlement refinement

This module models the semantic effect of the production `ASPS`/`ASRS`
prepared-plan lifecycle.  Preparation freezes an exact source state and the
already-computed candidate state.  Final apply may copy that candidate only
when the live state, authority, activation interval, proof authorization,
runtime effects, and nullifier freshness all still agree.  Cancellation
retires only the plan and never changes custody state.

The model is deliberately hash- and byte-encoding-parametric.  The Rust/Aeneas
bridge must show that the authenticated plan images decode to this record and
that Solana rollback implements the failure branch.
-/

set_option autoImplicit false

namespace AspisPool.PreparedSettlementV1

open AspisPool.AtomicSettlementV1

inductive PlanKind where
  | privateTransfer
  | withdrawal
  deriving DecidableEq, Repr

inductive PlanStatus where
  | open
  | retired
  deriving DecidableEq, Repr

/-- Semantic fields authenticated by the prepared core and optional rollover
shard.  `candidate` is the complete post-settlement Pool state whose byte image
is committed by the production plan. -/
structure Plan (Note Root Marker Authority : Type) where
  kind : PlanKind
  authority : Authority
  activationSlot : Nat
  expirySlot : Nat
  source : State Note Root Marker
  candidate : State Note Root Marker
  marker : Marker
  status : PlanStatus
  deriving DecidableEq, Repr

structure ApplyResult (Note Root Marker Authority : Type) where
  state : State Note Root Marker
  plan : Plan Note Root Marker Authority
  deriving DecidableEq, Repr

def activeAt {Note Root Marker Authority : Type}
    (plan : Plan Note Root Marker Authority) (slot : Nat) : Prop :=
  plan.activationSlot ≤ slot ∧ slot ≤ plan.expirySlot

/-- Every final gate required before an authenticated candidate may replace
the live state. -/
def ApplyAuthorized {Note Root Marker Authority : Type}
    [DecidableEq Note] [DecidableEq Root] [DecidableEq Marker]
    [DecidableEq Authority]
    (live : State Note Root Marker) (slot : Nat) (signer : Authority)
    (proofAuthorized effectsComplete : Bool)
    (plan : Plan Note Root Marker Authority) : Prop :=
  plan.status = .open ∧
    signer = plan.authority ∧
    activeAt plan slot ∧
    live = plan.source ∧
    proofAuthorized = true ∧
    effectsComplete = true ∧
    plan.marker ∉ live.consumedNullifiers

instance instDecidableApplyAuthorized
    {Note Root Marker Authority : Type}
    [DecidableEq Note] [DecidableEq Root] [DecidableEq Marker]
    [DecidableEq Authority]
    (live : State Note Root Marker) (slot : Nat) (signer : Authority)
    (proofAuthorized effectsComplete : Bool)
    (plan : Plan Note Root Marker Authority) :
    Decidable (ApplyAuthorized live slot signer proofAuthorized
      effectsComplete plan) := by
  unfold ApplyAuthorized activeAt
  infer_instance

/-- Pure final apply.  The successful branch copies the exact authenticated
candidate and retires the plan; every failed gate returns both inputs exactly. -/
def applyPrepared {Note Root Marker Authority : Type}
    [DecidableEq Note] [DecidableEq Root] [DecidableEq Marker]
    [DecidableEq Authority]
    (live : State Note Root Marker) (slot : Nat) (signer : Authority)
    (proofAuthorized effectsComplete : Bool)
    (plan : Plan Note Root Marker Authority) :
    ApplyResult Note Root Marker Authority :=
  if ApplyAuthorized live slot signer proofAuthorized effectsComplete plan then
    { state := plan.candidate, plan := { plan with status := .retired } }
  else
    { state := live, plan := plan }

def prepareTransfer {Note Root Marker Authority : Type}
    (before : State Note Root Marker)
    (relation : AspisPool.TransferOneToTwoV1.Relation)
    (outputs : AspisPool.TransferOneToTwoV1.OrderedOutputs Note)
    (rootAfterFirst rootAfterSecond : Root) (marker : Marker)
    (authority : Authority) (activationSlot expirySlot : Nat) :
    Plan Note Root Marker Authority where
  kind := .privateTransfer
  authority := authority
  activationSlot := activationSlot
  expirySlot := expirySlot
  source := before
  candidate := transferCandidate before relation outputs rootAfterFirst
    rootAfterSecond marker
  marker := marker
  status := .open

def prepareWithdrawal {Note Root Marker Authority : Type}
    (before : State Note Root Marker)
    (relation : AspisPool.WithdrawalV1.Relation)
    (changeNote : Note) (rootAfterChange : Root) (marker : Marker)
    (authority : Authority) (activationSlot expirySlot : Nat) :
    Plan Note Root Marker Authority where
  kind := .withdrawal
  authority := authority
  activationSlot := activationSlot
  expirySlot := expirySlot
  source := before
  candidate := withdrawalCandidate before relation changeNote rootAfterChange
    marker
  marker := marker
  status := .open

/-- A rejected final apply is the exact pre-state and leaves the plan open. -/
theorem rejected_apply_is_exact_prestate
    {Note Root Marker Authority : Type}
    [DecidableEq Note] [DecidableEq Root] [DecidableEq Marker]
    [DecidableEq Authority]
    (live : State Note Root Marker) (slot : Nat) (signer : Authority)
    (proofAuthorized effectsComplete : Bool)
    (plan : Plan Note Root Marker Authority)
    (rejected : ¬ ApplyAuthorized live slot signer proofAuthorized
      effectsComplete plan) :
    applyPrepared live slot signer proofAuthorized effectsComplete plan =
      { state := live, plan := plan } := by
  simp [applyPrepared, rejected]

/-- A successful prepared transfer has exactly the same custody/nullifier
state as the direct atomic transition and retires its authenticated plan. -/
theorem prepared_transfer_apply_matches_direct
    {Note Root Marker Authority : Type}
    [DecidableEq Note] [DecidableEq Root] [DecidableEq Marker]
    [DecidableEq Authority]
    (before : State Note Root Marker)
    (relation : AspisPool.TransferOneToTwoV1.Relation)
    (outputs : AspisPool.TransferOneToTwoV1.OrderedOutputs Note)
    (rootAfterFirst rootAfterSecond : Root) (marker : Marker)
    (authority : Authority) (activationSlot expirySlot slot : Nat)
    (active : activationSlot ≤ slot ∧ slot ≤ expirySlot)
    (fresh : marker ∉ before.consumedNullifiers) :
    let plan := prepareTransfer before relation outputs rootAfterFirst
      rootAfterSecond marker authority activationSlot expirySlot
    let applied := applyPrepared before slot authority true true plan
    applied.state = settleTransfer before true true relation outputs
      rootAfterFirst rootAfterSecond marker ∧
      applied.plan = { plan with status := .retired } := by
  let plan := prepareTransfer before relation outputs rootAfterFirst
    rootAfterSecond marker authority activationSlot expirySlot
  have authorized : ApplyAuthorized before slot authority true true plan := by
    exact ⟨rfl, rfl, active, rfl, rfl, rfl, fresh⟩
  simp only [plan, applyPrepared, authorized, if_pos]
  constructor
  · simp [prepareTransfer, settleTransfer, fresh]
  · trivial

/-- A successful prepared withdrawal has exactly the same custody/nullifier
state as the direct atomic transition and retires its authenticated plan. -/
theorem prepared_withdrawal_apply_matches_direct
    {Note Root Marker Authority : Type}
    [DecidableEq Note] [DecidableEq Root] [DecidableEq Marker]
    [DecidableEq Authority]
    (before : State Note Root Marker)
    (relation : AspisPool.WithdrawalV1.Relation)
    (changeNote : Note) (rootAfterChange : Root) (marker : Marker)
    (authority : Authority) (activationSlot expirySlot slot : Nat)
    (active : activationSlot ≤ slot ∧ slot ≤ expirySlot)
    (fresh : marker ∉ before.consumedNullifiers) :
    let plan := prepareWithdrawal before relation changeNote rootAfterChange
      marker authority activationSlot expirySlot
    let applied := applyPrepared before slot authority true true plan
    applied.state = settleWithdrawal before true true relation changeNote
      rootAfterChange marker ∧
      applied.plan = { plan with status := .retired } := by
  let plan := prepareWithdrawal before relation changeNote rootAfterChange
    marker authority activationSlot expirySlot
  have authorized : ApplyAuthorized before slot authority true true plan := by
    exact ⟨rfl, rfl, active, rfl, rfl, rfl, fresh⟩
  simp only [plan, applyPrepared, authorized, if_pos]
  constructor
  · simp [prepareWithdrawal, settleWithdrawal, fresh]
  · trivial

theorem stale_source_apply_preserves_state
    {Note Root Marker Authority : Type}
    [DecidableEq Note] [DecidableEq Root] [DecidableEq Marker]
    [DecidableEq Authority]
    (live : State Note Root Marker) (slot : Nat) (signer : Authority)
    (proofAuthorized effectsComplete : Bool)
    (plan : Plan Note Root Marker Authority)
    (stale : live ≠ plan.source) :
    (applyPrepared live slot signer proofAuthorized effectsComplete plan).state =
      live := by
  have rejected : ¬ ApplyAuthorized live slot signer proofAuthorized
      effectsComplete plan := by
    intro accepted
    exact stale accepted.2.2.2.1
  rw [rejected_apply_is_exact_prestate live slot signer proofAuthorized
    effectsComplete plan rejected]

theorem retired_plan_apply_preserves_state
    {Note Root Marker Authority : Type}
    [DecidableEq Note] [DecidableEq Root] [DecidableEq Marker]
    [DecidableEq Authority]
    (live : State Note Root Marker) (slot : Nat) (signer : Authority)
    (proofAuthorized effectsComplete : Bool)
    (plan : Plan Note Root Marker Authority)
    (retired : plan.status = .retired) :
    (applyPrepared live slot signer proofAuthorized effectsComplete plan).state =
      live := by
  have rejected : ¬ ApplyAuthorized live slot signer proofAuthorized
      effectsComplete plan := by
    intro accepted
    have openStatus := accepted.1
    rw [retired] at openStatus
    cases openStatus
  rw [rejected_apply_is_exact_prestate live slot signer proofAuthorized
    effectsComplete plan rejected]

theorem expired_plan_apply_preserves_state
    {Note Root Marker Authority : Type}
    [DecidableEq Note] [DecidableEq Root] [DecidableEq Marker]
    [DecidableEq Authority]
    (live : State Note Root Marker) (slot : Nat) (signer : Authority)
    (proofAuthorized effectsComplete : Bool)
    (plan : Plan Note Root Marker Authority)
    (expired : plan.expirySlot < slot) :
    (applyPrepared live slot signer proofAuthorized effectsComplete plan).state =
      live := by
  have rejected : ¬ ApplyAuthorized live slot signer proofAuthorized
      effectsComplete plan := by
    intro accepted
    exact (Nat.not_le_of_lt expired) accepted.2.2.1.2
  rw [rejected_apply_is_exact_prestate live slot signer proofAuthorized
    effectsComplete plan rejected]

/-- Cancellation has no custody input and can only retire an open plan signed
by its exact authority. -/
def cancelPrepared {Note Root Marker Authority : Type}
    [DecidableEq Authority] (signer : Authority)
    (plan : Plan Note Root Marker Authority) : Plan Note Root Marker Authority :=
  if signer = plan.authority ∧ plan.status = .open then
    { plan with status := .retired }
  else
    plan

theorem authorized_cancel_retires_exact_plan
    {Note Root Marker Authority : Type} [DecidableEq Authority]
    (plan : Plan Note Root Marker Authority) (openPlan : plan.status = .open) :
    cancelPrepared plan.authority plan = { plan with status := .retired } := by
  simp [cancelPrepared, openPlan]

theorem unauthorized_cancel_preserves_exact_plan
    {Note Root Marker Authority : Type} [DecidableEq Authority]
    (signer : Authority) (plan : Plan Note Root Marker Authority)
    (unauthorized : signer ≠ plan.authority) :
    cancelPrepared signer plan = plan := by
  simp [cancelPrepared, unauthorized]

/-- Once cancellation retires an open plan, a later apply cannot mutate
custody even if every other input is favorable. -/
theorem cancelled_plan_cannot_later_apply
    {Note Root Marker Authority : Type}
    [DecidableEq Note] [DecidableEq Root] [DecidableEq Marker]
    [DecidableEq Authority]
    (live : State Note Root Marker) (slot : Nat)
    (plan : Plan Note Root Marker Authority) (openPlan : plan.status = .open) :
    (applyPrepared live slot plan.authority true true
      (cancelPrepared plan.authority plan)).state = live := by
  rw [authorized_cancel_retires_exact_plan plan openPlan]
  apply retired_plan_apply_preserves_state
  rfl

/-- The retired plan returned by a successful apply is intrinsically
single-use: replaying it preserves the already-updated live state. -/
theorem successful_apply_result_cannot_replay
    {Note Root Marker Authority : Type}
    [DecidableEq Note] [DecidableEq Root] [DecidableEq Marker]
    [DecidableEq Authority]
    (live : State Note Root Marker) (slot : Nat) (signer : Authority)
    (plan : Plan Note Root Marker Authority)
    (authorized : ApplyAuthorized live slot signer true true plan) :
    let first := applyPrepared live slot signer true true plan
    (applyPrepared first.state slot signer true true first.plan).state =
      first.state := by
  have firstExact : applyPrepared live slot signer true true plan =
      { state := plan.candidate, plan := { plan with status := .retired } } := by
    simp [applyPrepared, authorized]
  rw [firstExact]
  apply retired_plan_apply_preserves_state
  rfl

theorem cancel_cannot_change_custody
    {Note Root Marker Authority : Type} [DecidableEq Authority]
    (state : State Note Root Marker) (signer : Authority)
    (plan : Plan Note Root Marker Authority) :
    (state, cancelPrepared signer plan).1 = state := rfl

#print axioms rejected_apply_is_exact_prestate
#print axioms prepared_transfer_apply_matches_direct
#print axioms prepared_withdrawal_apply_matches_direct
#print axioms stale_source_apply_preserves_state
#print axioms retired_plan_apply_preserves_state
#print axioms expired_plan_apply_preserves_state
#print axioms authorized_cancel_retires_exact_plan
#print axioms unauthorized_cancel_preserves_exact_plan
#print axioms cancelled_plan_cannot_later_apply
#print axioms successful_apply_result_cannot_replay
#print axioms cancel_cannot_change_custody

end AspisPool.PreparedSettlementV1
