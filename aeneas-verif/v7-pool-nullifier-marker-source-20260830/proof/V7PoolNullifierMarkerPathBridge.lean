import V7PoolNullifierMarkerSourceBridge

/-!
# Exact Pool nullifier-marker reservation paths

The production caller admits exactly four successful reservation shapes.  The
two dusted-account cases stay separate: one transfers a rent deficit before
allocate/assign, while the other is already funded and only allocate/assigns.
No theorem below hides those paths behind an unchecked reservation oracle.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace V7PoolNullifierMarkerGenerated

open Aeneas Aeneas.Std Result ControlFlow Error

def ExactCreateAccountReservation
    (input : MarkerTerminalInput) (before after : MarkerTerminalState) : Prop :=
  ExactCreateZeroLamportEntry input before.marker ∧
  input.runtime.create_account_succeeds = true ∧
  ∃ payerAfter,
    U64.checked_sub before.payer.lamports input.rent.required_lamports =
      some payerAfter ∧
    after = {
      before with
      payer := { before.payer with lamports := payerAfter }
      marker := {
        account := { before.marker.account with owner := input.program_id }
        lamports := input.rent.required_lamports
        data_len := NULLIFIER_MARKER_BYTES
        data_zeroed := true
        stored_marker := none
      }
    }

def ExactTransferAllocateAssignReservation
    (input : MarkerTerminalInput) (before after : MarkerTerminalState) : Prop :=
  ExactDustedSystemEntry input before.marker ∧
  before.marker.lamports < input.rent.required_lamports ∧
  input.runtime.transfer_succeeds = true ∧
  input.runtime.allocate_succeeds = true ∧
  input.runtime.assign_succeeds = true ∧
  ∃ deficit payerAfter,
    U64.checked_sub input.rent.required_lamports before.marker.lamports =
      some deficit ∧
    U64.checked_sub before.payer.lamports deficit = some payerAfter ∧
    after = {
      before with
      payer := { before.payer with lamports := payerAfter }
      marker := {
        account := { before.marker.account with owner := input.program_id }
        lamports := input.rent.required_lamports
        data_len := NULLIFIER_MARKER_BYTES
        data_zeroed := true
        stored_marker := none
      }
    }

def ExactAllocateAssignReservation
    (input : MarkerTerminalInput) (before after : MarkerTerminalState) : Prop :=
  ExactDustedSystemEntry input before.marker ∧
  ¬ before.marker.lamports < input.rent.required_lamports ∧
  input.runtime.allocate_succeeds = true ∧
  input.runtime.assign_succeeds = true ∧
  after = {
    before with
    marker := {
      before.marker with
      account := { before.marker.account with owner := input.program_id }
      data_len := NULLIFIER_MARKER_BYTES
      data_zeroed := true
      stored_marker := none
    }
  }

def ExactAlreadyProgramOwnedReservation
    (input : MarkerTerminalInput) (before after : MarkerTerminalState) : Prop :=
  ExactProgramOwnedZeroEntry input before.marker ∧ after = before

theorem translated_create_account_reservation_is_exact
    (input : MarkerTerminalInput) (before after : MarkerTerminalState)
    (planned : PlannedMarker)
    (entry : ExactCreateZeroLamportEntry input before.marker)
    (kind : planned.preparation = .CreateZeroLamport)
    (run : reserve_marker input before planned =
      .ok (.Ok (after, .CreateAccount))) :
    ExactCreateAccountReservation input before after := by
  unfold reserve_marker at run
  simp only [kind] at run
  split at run
  · cases run
  · split at run
    · rename_i createSucceeded
      generalize subRun : (before.payer.lamports -
        input.rent.required_lamports) = subResult at run
      cases subResult with
      | fail error => simp at run
      | div => simp at run
      | ok payerAfter =>
          simp at run
          subst after
          refine ⟨entry, createSucceeded, payerAfter, ?_, rfl⟩
          unfold U64.checked_sub core.num.checked_sub_UScalar
          rw [subRun]
          rfl
    · cases run

theorem translated_transfer_allocate_assign_reservation_is_exact
    (input : MarkerTerminalInput) (before after : MarkerTerminalState)
    (planned : PlannedMarker)
    (entry : ExactDustedSystemEntry input before.marker)
    (kind : planned.preparation = .AllocateDusted)
    (run : reserve_marker input before planned =
      .ok (.Ok (after, .TransferAllocateAssign))) :
    ExactTransferAllocateAssignReservation input before after := by
  unfold reserve_marker at run
  simp only [kind] at run
  split at run
  · rename_i needsTopup
    generalize deficitRun : (input.rent.required_lamports -
      before.marker.lamports) = deficitResult at run
    cases deficitResult with
    | fail error => simp at run
    | div => simp at run
    | ok deficit =>
      simp at run
      split at run
      · cases run
      · split at run
        · rename_i transferSucceeded
          generalize payerRun : (before.payer.lamports - deficit) =
            payerResult at run
          cases payerResult with
          | fail error => simp at run
          | div => simp at run
          | ok payerAfter =>
            simp at run
            split at run
            · rename_i allocateSucceeded
              split at run
              · rename_i assignSucceeded
                simp at run
                subst after
                refine ⟨entry, needsTopup, transferSucceeded,
                  allocateSucceeded, assignSucceeded, deficit, payerAfter,
                  ?_, ?_, rfl⟩
                · unfold U64.checked_sub core.num.checked_sub_UScalar
                  rw [deficitRun]
                  rfl
                · unfold U64.checked_sub core.num.checked_sub_UScalar
                  rw [payerRun]
                  rfl
              · cases run
            · cases run
        · cases run
  · split at run
    · split at run
      · simp at run
      · cases run
    · cases run

theorem translated_allocate_assign_reservation_is_exact
    (input : MarkerTerminalInput) (before after : MarkerTerminalState)
    (planned : PlannedMarker)
    (entry : ExactDustedSystemEntry input before.marker)
    (kind : planned.preparation = .AllocateDusted)
    (run : reserve_marker input before planned =
      .ok (.Ok (after, .AllocateAssign))) :
    ExactAllocateAssignReservation input before after := by
  unfold reserve_marker at run
  simp only [kind] at run
  split at run
  · generalize deficitRun : (input.rent.required_lamports -
      before.marker.lamports) = deficitResult at run
    cases deficitResult with
    | fail error => simp at run
    | div => simp at run
    | ok deficit =>
      simp at run
      split at run
      · cases run
      · split at run
        · generalize payerRun : (before.payer.lamports - deficit) =
            payerResult at run
          cases payerResult with
          | fail error => simp at run
          | div => simp at run
          | ok payerAfter =>
            simp at run
            split at run
            · split at run
              · simp at run
              · cases run
            · cases run
        · cases run
  · rename_i noTopup
    split at run
    · rename_i allocateSucceeded
      split at run
      · rename_i assignSucceeded
        simp at run
        subst after
        exact ⟨entry, noTopup, allocateSucceeded, assignSucceeded, rfl⟩
      · cases run
    · cases run

theorem translated_already_program_owned_reservation_is_exact
    (input : MarkerTerminalInput) (before after : MarkerTerminalState)
    (planned : PlannedMarker)
    (entry : ExactProgramOwnedZeroEntry input before.marker)
    (kind : planned.preparation = .ProgramOwnedZeroed)
    (run : reserve_marker input before planned =
      .ok (.Ok (after, .AlreadyProgramOwned))) :
    ExactAlreadyProgramOwnedReservation input before after := by
  unfold reserve_marker at run
  simp only [kind] at run
  simp at run
  subst after
  exact ⟨entry, rfl⟩

#print axioms translated_create_account_reservation_is_exact
#print axioms translated_transfer_allocate_assign_reservation_is_exact
#print axioms translated_allocate_assign_reservation_is_exact
#print axioms translated_already_program_owned_reservation_is_exact

end V7PoolNullifierMarkerGenerated
