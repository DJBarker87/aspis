import AspisFormal.Pool.PreparedSettlementV1
import AspisFormal.Pool.VerifierDispatchV1

/-!
# Pool V1 verified prepared-settlement composition

This module connects the read-only verifier-dispatch decision to the pure
prepared-settlement state machine.  The verifier result is recomputed as a
Boolean from the selected program, exact expected binding, return-data code,
and echoed binding.  A rejected or missing dispatch therefore supplies
`proofAuthorized = false` to `applyPrepared`, whose failure branch preserves
both the live custody state and the plan exactly.

The model remains independent of SHA-256, CPI authenticity and Solana
rollback.  Those are the named source/runtime refinement boundaries of
`VerifierDispatchV1`; no additional cryptographic assumption is introduced
here.
-/

set_option autoImplicit false

namespace AspisPool.PreparedVerifiedSettlementV1

open AspisPool.AtomicSettlementV1
open AspisPool.PreparedSettlementV1
open AspisPool.VerifierDispatchV1

/-- Exact Boolean authorization consumed by the prepared settlement. -/
def dispatchAuthorized
    {Program BindingType : Type}
    [DecidableEq Program] [DecidableEq BindingType]
    (returningProgram selectedProgram : Program)
    (expectedBinding : BindingType) (returned : Result BindingType) : Bool :=
  decide (returningProgram = selectedProgram ∧
    returned.code = successCode ∧ returned.binding = expectedBinding)

theorem dispatchAuthorized_eq_true_iff
    {Program BindingType : Type}
    [DecidableEq Program] [DecidableEq BindingType]
    (returningProgram selectedProgram : Program)
    (expectedBinding : BindingType) (returned : Result BindingType) :
    dispatchAuthorized returningProgram selectedProgram expectedBinding returned = true ↔
      accepts returningProgram selectedProgram expectedBinding returned := by
  simp [dispatchAuthorized, accepts]

/-- Pure composition of immediate return-data capture with final settlement.
No state is exposed between these two decisions. -/
def applyAfterVerifiedDispatch
    {Note Root Marker Authority Program BindingType : Type}
    [DecidableEq Note] [DecidableEq Root] [DecidableEq Marker]
    [DecidableEq Authority] [DecidableEq Program] [DecidableEq BindingType]
    (live : State Note Root Marker) (slot : Nat) (signer : Authority)
    (effectsComplete : Bool) (plan : Plan Note Root Marker Authority)
    (returningProgram selectedProgram : Program)
    (expectedBinding : BindingType) (returned : Result BindingType) :
    ApplyResult Note Root Marker Authority :=
  applyPrepared live slot signer
    (dispatchAuthorized returningProgram selectedProgram expectedBinding returned)
    effectsComplete plan

/-- Any verifier-dispatch rejection selects the exact custody/plan pre-state,
even if all other settlement inputs are favorable. -/
theorem rejected_dispatch_preserves_exact_prestate
    {Note Root Marker Authority Program BindingType : Type}
    [DecidableEq Note] [DecidableEq Root] [DecidableEq Marker]
    [DecidableEq Authority] [DecidableEq Program] [DecidableEq BindingType]
    (live : State Note Root Marker) (slot : Nat) (signer : Authority)
    (effectsComplete : Bool) (plan : Plan Note Root Marker Authority)
    (returningProgram selectedProgram : Program)
    (expectedBinding : BindingType) (returned : Result BindingType)
    (rejected : ¬ accepts returningProgram selectedProgram expectedBinding returned) :
    applyAfterVerifiedDispatch live slot signer effectsComplete plan
        returningProgram selectedProgram expectedBinding returned =
      { state := live, plan := plan } := by
  apply rejected_apply_is_exact_prestate
  intro authorized
  have proofAccepted := authorized.2.2.2.2.1
  have dispatchAccepted :
      accepts returningProgram selectedProgram expectedBinding returned :=
    (dispatchAuthorized_eq_true_iff returningProgram selectedProgram
      expectedBinding returned).mp proofAccepted
  exact rejected dispatchAccepted

/-- Once the exact verifier result and every final state/runtime gate agree,
the only successful state is the authenticated candidate and the plan is
retired in the same pure transition. -/
theorem accepted_dispatch_applies_candidate_and_retires
    {Note Root Marker Authority Program BindingType : Type}
    [DecidableEq Note] [DecidableEq Root] [DecidableEq Marker]
    [DecidableEq Authority] [DecidableEq Program] [DecidableEq BindingType]
    (live : State Note Root Marker) (slot : Nat) (signer : Authority)
    (plan : Plan Note Root Marker Authority)
    (returningProgram selectedProgram : Program)
    (expectedBinding : BindingType) (returned : Result BindingType)
    (accepted : accepts returningProgram selectedProgram expectedBinding returned)
    (openPlan : plan.status = .open)
    (authorityExact : signer = plan.authority)
    (active : activeAt plan slot)
    (sourceExact : live = plan.source)
    (fresh : plan.marker ∉ live.consumedNullifiers) :
    applyAfterVerifiedDispatch live slot signer true plan returningProgram
        selectedProgram expectedBinding returned =
      { state := plan.candidate,
        plan := { plan with status := .retired } } := by
  have proofAccepted :
      dispatchAuthorized returningProgram selectedProgram expectedBinding returned = true :=
    (dispatchAuthorized_eq_true_iff returningProgram selectedProgram
      expectedBinding returned).mpr accepted
  have authorized : ApplyAuthorized live slot signer
      (dispatchAuthorized returningProgram selectedProgram expectedBinding returned)
      true plan :=
    ⟨openPlan, authorityExact, active, sourceExact, proofAccepted, rfl, fresh⟩
  simp [applyAfterVerifiedDispatch, applyPrepared, authorized]

/-- A successful verifier dispatch on a freshly prepared private transfer is
extensionally the direct atomic transfer transition. -/
theorem verified_prepared_transfer_matches_direct
    {Note Root Marker Authority Program BindingType : Type}
    [DecidableEq Note] [DecidableEq Root] [DecidableEq Marker]
    [DecidableEq Authority] [DecidableEq Program] [DecidableEq BindingType]
    (before : State Note Root Marker)
    (relation : AspisPool.TransferOneToTwoV1.Relation)
    (outputs : AspisPool.TransferOneToTwoV1.OrderedOutputs Note)
    (rootAfterFirst rootAfterSecond : Root) (marker : Marker)
    (authority : Authority) (activationSlot expirySlot slot : Nat)
    (active : activationSlot ≤ slot ∧ slot ≤ expirySlot)
    (fresh : marker ∉ before.consumedNullifiers)
    (returningProgram selectedProgram : Program)
    (expectedBinding : BindingType) (returned : Result BindingType)
    (accepted : accepts returningProgram selectedProgram expectedBinding returned) :
    let plan := prepareTransfer before relation outputs rootAfterFirst
      rootAfterSecond marker authority activationSlot expirySlot
    let applied := applyAfterVerifiedDispatch before slot authority true plan
      returningProgram selectedProgram expectedBinding returned
    applied.state = settleTransfer before true true relation outputs
      rootAfterFirst rootAfterSecond marker ∧
      applied.plan = { plan with status := .retired } := by
  let plan := prepareTransfer before relation outputs rootAfterFirst
    rootAfterSecond marker authority activationSlot expirySlot
  have applied := accepted_dispatch_applies_candidate_and_retires before slot
    authority plan returningProgram selectedProgram expectedBinding returned
    accepted rfl rfl active rfl fresh
  dsimp only
  rw [applied]
  constructor
  · simp [plan, prepareTransfer, settleTransfer, fresh]
  · rfl

/-- The analogous composition for withdrawal, including the exact change-note
candidate and nullifier update. -/
theorem verified_prepared_withdrawal_matches_direct
    {Note Root Marker Authority Program BindingType : Type}
    [DecidableEq Note] [DecidableEq Root] [DecidableEq Marker]
    [DecidableEq Authority] [DecidableEq Program] [DecidableEq BindingType]
    (before : State Note Root Marker)
    (relation : AspisPool.WithdrawalV1.Relation)
    (changeNote : Note) (rootAfterChange : Root) (marker : Marker)
    (authority : Authority) (activationSlot expirySlot slot : Nat)
    (active : activationSlot ≤ slot ∧ slot ≤ expirySlot)
    (fresh : marker ∉ before.consumedNullifiers)
    (returningProgram selectedProgram : Program)
    (expectedBinding : BindingType) (returned : Result BindingType)
    (accepted : accepts returningProgram selectedProgram expectedBinding returned) :
    let plan := prepareWithdrawal before relation changeNote rootAfterChange
      marker authority activationSlot expirySlot
    let applied := applyAfterVerifiedDispatch before slot authority true plan
      returningProgram selectedProgram expectedBinding returned
    applied.state = settleWithdrawal before true true relation changeNote
      rootAfterChange marker ∧
      applied.plan = { plan with status := .retired } := by
  let plan := prepareWithdrawal before relation changeNote rootAfterChange
    marker authority activationSlot expirySlot
  have applied := accepted_dispatch_applies_candidate_and_retires before slot
    authority plan returningProgram selectedProgram expectedBinding returned
    accepted rfl rfl active rfl fresh
  dsimp only
  rw [applied]
  constructor
  · simp [plan, prepareWithdrawal, settleWithdrawal, fresh]
  · rfl

#print axioms dispatchAuthorized_eq_true_iff
#print axioms rejected_dispatch_preserves_exact_prestate
#print axioms accepted_dispatch_applies_candidate_and_retires
#print axioms verified_prepared_transfer_matches_direct
#print axioms verified_prepared_withdrawal_matches_direct

end AspisPool.PreparedVerifiedSettlementV1
