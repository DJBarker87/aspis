import V7PoolNullifierMarkerPathBridge

/-!
# Accepted caller, ordering, replay, and rollback bridge

This file composes the four distinct reservation proofs with the translated
terminal caller.  It proves the exact per-path final state and call trace,
then proves that the consumed marker is rejected as `SpentNullifier` before
the verifier call and that the atomic wrapper returns the exact prestate.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace V7PoolNullifierMarkerGenerated

open Aeneas Aeneas.Std Result ControlFlow Error

theorem accepted_factorization_has_exact_trace
    (input : MarkerTerminalInput) (before : MarkerTerminalState)
    (out : MarkerTerminalOutcome)
    (factor : AcceptedMarkerTerminalFactorization input before out) :
    ExactTraceForPath factor.path out.trace := by
  have reservationRun := factor.reservationTraceRun
  have verifierRun := factor.verifierTraceRun
  have coreRun := factor.coreTraceRun
  have consumeRun := factor.consumedTraceRun
  have outTrace : out.trace = factor.consumedTrace := by
    exact congrArg MarkerTerminalOutcome.trace factor.outExact
  rw [outTrace]
  cases hpath : factor.path
  all_goals simp [hpath, reservation_trace, empty_trace] at reservationRun
  all_goals rw [← reservationRun] at verifierRun
  all_goals simp [hpath, record_verifier] at verifierRun
  all_goals rw [← verifierRun] at coreRun
  all_goals simp [hpath, record_core_apply] at coreRun
  all_goals rw [← coreRun] at consumeRun
  all_goals simp [hpath, record_consumption] at consumeRun
  all_goals rw [← consumeRun]
  all_goals rfl

theorem translated_accepted_create_account_path_is_exact
    (input : MarkerTerminalInput) (before : MarkerTerminalState)
    (out : MarkerTerminalOutcome)
    (factor : AcceptedMarkerTerminalFactorization input before out)
    (kind : factor.planned.preparation = .CreateZeroLamport)
    (path : factor.path = .CreateAccount) :
    ExactCreateAccountEffect input before out.state ∧
      ExactCreateAccountTrace out.trace := by
  have initial := translated_create_zero_plan_is_exact input before.marker
    factor.planned factor.initialPlanRun kind
  have reserveRun : reserve_marker input before factor.planned =
      .ok (.Ok (factor.reserved, .CreateAccount)) := by
    simpa only [path] using factor.reservationRun
  have reservation := translated_create_account_reservation_is_exact
    input before factor.reserved factor.planned initial.1 kind reserveRun
  have ready := translated_program_owned_plan_is_exact input
    factor.reserved.marker factor.ready factor.readyPlanRun factor.readyKind
  rcases reservation with ⟨entry, createSucceeded, payerAfter,
    payerSub, reservedEq⟩
  constructor
  · refine ⟨entry, createSucceeded, payerAfter, payerSub, ?_⟩
    rw [factor.outExact, ready.2.2, reservedEq]
  · have trace := accepted_factorization_has_exact_trace input before out factor
    simpa only [ExactTraceForPath, path] using trace

theorem translated_accepted_transfer_allocate_assign_path_is_exact
    (input : MarkerTerminalInput) (before : MarkerTerminalState)
    (out : MarkerTerminalOutcome)
    (factor : AcceptedMarkerTerminalFactorization input before out)
    (kind : factor.planned.preparation = .AllocateDusted)
    (path : factor.path = .TransferAllocateAssign) :
    ExactTransferAllocateAssignEffect input before out.state ∧
      ExactTransferAllocateAssignTrace out.trace := by
  have initial := translated_dusted_plan_is_exact input before.marker
    factor.planned factor.initialPlanRun kind
  have reserveRun : reserve_marker input before factor.planned =
      .ok (.Ok (factor.reserved, .TransferAllocateAssign)) := by
    simpa only [path] using factor.reservationRun
  have reservation := translated_transfer_allocate_assign_reservation_is_exact
    input before factor.reserved factor.planned initial.1 kind reserveRun
  have ready := translated_program_owned_plan_is_exact input
    factor.reserved.marker factor.ready factor.readyPlanRun factor.readyKind
  rcases reservation with ⟨entry, needsTopup, transferSucceeded,
    allocateSucceeded, assignSucceeded, deficit, payerAfter, deficitSub,
    payerSub, reservedEq⟩
  constructor
  · refine ⟨entry, needsTopup, transferSucceeded, allocateSucceeded,
      assignSucceeded, deficit, payerAfter, deficitSub, payerSub, ?_⟩
    rw [factor.outExact, ready.2.2, reservedEq]
  · have trace := accepted_factorization_has_exact_trace input before out factor
    simpa only [ExactTraceForPath, path] using trace

theorem translated_accepted_allocate_assign_path_is_exact
    (input : MarkerTerminalInput) (before : MarkerTerminalState)
    (out : MarkerTerminalOutcome)
    (factor : AcceptedMarkerTerminalFactorization input before out)
    (kind : factor.planned.preparation = .AllocateDusted)
    (path : factor.path = .AllocateAssign) :
    ExactAllocateAssignEffect input before out.state ∧
      ExactAllocateAssignTrace out.trace := by
  have initial := translated_dusted_plan_is_exact input before.marker
    factor.planned factor.initialPlanRun kind
  have reserveRun : reserve_marker input before factor.planned =
      .ok (.Ok (factor.reserved, .AllocateAssign)) := by
    simpa only [path] using factor.reservationRun
  have reservation := translated_allocate_assign_reservation_is_exact
    input before factor.reserved factor.planned initial.1 kind reserveRun
  have ready := translated_program_owned_plan_is_exact input
    factor.reserved.marker factor.ready factor.readyPlanRun factor.readyKind
  rcases reservation with ⟨entry, noTopup, allocateSucceeded,
    assignSucceeded, reservedEq⟩
  constructor
  · refine ⟨entry, noTopup, allocateSucceeded, assignSucceeded, ?_⟩
    rw [factor.outExact, ready.2.2, reservedEq]
  · have trace := accepted_factorization_has_exact_trace input before out factor
    simpa only [ExactTraceForPath, path] using trace

theorem translated_accepted_already_program_owned_path_is_exact
    (input : MarkerTerminalInput) (before : MarkerTerminalState)
    (out : MarkerTerminalOutcome)
    (factor : AcceptedMarkerTerminalFactorization input before out)
    (kind : factor.planned.preparation = .ProgramOwnedZeroed)
    (path : factor.path = .AlreadyProgramOwned) :
    ExactAlreadyProgramOwnedEffect input before out.state ∧
      ExactAlreadyProgramOwnedTrace out.trace := by
  have initial := translated_program_owned_plan_is_exact input before.marker
    factor.planned factor.initialPlanRun kind
  have reserveRun : reserve_marker input before factor.planned =
      .ok (.Ok (factor.reserved, .AlreadyProgramOwned)) := by
    simpa only [path] using factor.reservationRun
  have reservation := translated_already_program_owned_reservation_is_exact
    input before factor.reserved factor.planned initial.1 kind reserveRun
  have ready := translated_program_owned_plan_is_exact input
    factor.reserved.marker factor.ready factor.readyPlanRun factor.readyKind
  rcases reservation with ⟨entry, reservedEq⟩
  constructor
  · refine ⟨entry, ?_⟩
    rw [factor.outExact, ready.2.2, reservedEq]
  · have trace := accepted_factorization_has_exact_trace input before out factor
    simpa only [ExactTraceForPath, path] using trace

def ExactConsumedMarkerEntry
    (input : MarkerTerminalInput) (marker : MarkerAccount) : Prop :=
  ExactMarkerIdentity input marker ∧
  marker.account.owner.val = input.program_id.val ∧
  marker.data_len.val = NULLIFIER_MARKER_BYTES.val ∧
  marker.data_zeroed = false ∧
  marker.stored_marker = some input.expected_marker

theorem translated_consumed_marker_plan_rejects_replay
    (input : MarkerTerminalInput) (marker : MarkerAccount)
    (entry : ExactConsumedMarkerEntry input marker) :
    plan_marker input marker = .ok (.Err .SpentNullifier) := by
  rcases entry with ⟨identity, ownerVal, lenVal, zeroed, stored⟩
  rcases identity with ⟨pda, seedVal, poolVal, nullifierVal,
    imagePoolVal, keyVal, keyPoolVal, executable, signer, writable⟩
  have seed := UScalar.val_eq_imp _ _ seedVal
  have pool := UScalar.val_eq_imp _ _ poolVal
  have nullifier := UScalar.val_eq_imp _ _ nullifierVal
  have imagePool := UScalar.val_eq_imp _ _ imagePoolVal
  have key := UScalar.val_eq_imp _ _ keyVal
  have keyPool : marker.account.key ≠ input.pool := by
    intro eq
    exact keyPoolVal (congrArg UScalar.val eq)
  have expectedPool : input.derivation.expected_address ≠ input.pool := by
    intro eq
    exact keyPool (key.trans eq)
  have owner := UScalar.val_eq_imp _ _ ownerVal
  have len := UScalar.val_eq_imp _ _ lenVal
  simp [plan_marker, pda, seed, pool, nullifier, imagePool, key,
    expectedPool, executable, signer, writable, owner, len, stored]

theorem translated_exact_authentication_succeeds
    (input : MarkerTerminalInput) (state : MarkerTerminalState)
    (exact : ExactPayerAndSystemAuthentication input state) :
    authenticate_payer_and_system input state = .ok (.Ok ()) := by
  rcases exact with ⟨unique, payerSigner, payerWritable, payerExecutable,
    payerOwnerVal, systemKeyVal, systemOwnerVal, systemExecutable,
    systemSigner, systemWritable⟩
  have payerOwner := UScalar.val_eq_imp _ _ payerOwnerVal
  have systemKey := UScalar.val_eq_imp _ _ systemKeyVal
  have systemOwner := UScalar.val_eq_imp _ _ systemOwnerVal
  simp [authenticate_payer_and_system, unique, payerSigner, payerWritable,
    payerExecutable, payerOwner, systemKey, systemOwner, systemExecutable,
    systemSigner, systemWritable]

def ExactSpentReplayOutcome (before : MarkerTerminalState)
    (out : MarkerTerminalOutcome) : Prop :=
  out = {
    committed := false
    state := before
    trace := {
      create_account_step := 0#u8
      transfer_step := 0#u8
      allocate_step := 0#u8
      assign_step := 0#u8
      replan_step := 0#u8
      verifier_step := 0#u8
      core_apply_step := 0#u8
      consume_step := 0#u8
    }
    certificate := none
    error := some .SpentNullifier
  }

theorem translated_spent_replay_is_exact_and_atomic
    (input : MarkerTerminalInput) (before : MarkerTerminalState)
    (out : MarkerTerminalOutcome)
    (rentLoaded : input.rent.loaded_from_sysvar = true)
    (rentNonzero : input.rent.required_lamports.val ≠ 0)
    (authentication : ExactPayerAndSystemAuthentication input before)
    (consumed : ExactConsumedMarkerEntry input before.marker)
    (run : execute_atomic_marker_terminal input before = .ok out) :
    ExactSpentReplayOutcome before out := by
  have rentNe : ¬ input.rent.required_lamports = 0#u64 := by
    intro eq
    exact rentNonzero (congrArg UScalar.val eq)
  have authenticationRun :=
    translated_exact_authentication_succeeds input before authentication
  have planRun :=
    translated_consumed_marker_plan_rejects_replay input before.marker consumed
  unfold execute_atomic_marker_terminal execute_marker_terminal_inner at run
  rw [if_pos rentLoaded, if_neg rentNe, authenticationRun, planRun] at run
  simp [empty_trace, rejected_inner] at run
  subst out
  rfl

theorem translated_accepted_marker_is_consumed_exactly
    (input : MarkerTerminalInput) (before : MarkerTerminalState)
    (out : MarkerTerminalOutcome)
    (factor : AcceptedMarkerTerminalFactorization input before out) :
    ExactConsumedMarkerEntry input out.state.marker := by
  have ready := translated_program_owned_plan_is_exact input
    factor.reserved.marker factor.ready factor.readyPlanRun factor.readyKind
  rcases ready with ⟨readyEntry, readyBump, readyMarker⟩
  rcases readyEntry with ⟨identity, owner, len, zeroed, stored⟩
  have outMarker := congrArg (fun x : MarkerTerminalOutcome => x.state.marker)
    factor.outExact
  rw [outMarker, readyMarker]
  exact ⟨identity, owner, len, rfl, rfl⟩

def ExactReservationPathClassification (planned : PlannedMarker)
    (path : ReservationPath) : Prop :=
  (planned.preparation = .CreateZeroLamport ∧ path = .CreateAccount) ∨
  (planned.preparation = .AllocateDusted ∧
    (path = .TransferAllocateAssign ∨ path = .AllocateAssign)) ∨
  (planned.preparation = .ProgramOwnedZeroed ∧ path = .AlreadyProgramOwned)

theorem translated_successful_reservation_path_is_exactly_classified
    (input : MarkerTerminalInput) (before after : MarkerTerminalState)
    (planned : PlannedMarker) (path : ReservationPath)
    (run : reserve_marker input before planned = .ok (.Ok (after, path))) :
    ExactReservationPathClassification planned path := by
  cases hkind : planned.preparation
  · unfold reserve_marker at run
    simp only [hkind] at run
    split at run
    · cases run
    · split at run
      · generalize subRun : (before.payer.lamports -
          input.rent.required_lamports) = subResult at run
        cases subResult with
        | fail error => simp at run
        | div => simp at run
        | ok payerAfter =>
            simp at run
            rcases run with ⟨stateEq, pathEq⟩
            cases pathEq
            exact Or.inl ⟨hkind, rfl⟩
      · cases run
  · unfold reserve_marker at run
    simp only [hkind] at run
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
                  rcases run with ⟨stateEq, pathEq⟩
                  cases pathEq
                  exact Or.inr (Or.inl ⟨hkind, Or.inl rfl⟩)
                · cases run
              · cases run
          · cases run
    · split at run
      · split at run
        · simp at run
          rcases run with ⟨stateEq, pathEq⟩
          cases pathEq
          exact Or.inr (Or.inl ⟨hkind, Or.inr rfl⟩)
        · cases run
      · cases run
  · unfold reserve_marker at run
    simp only [hkind] at run
    simp at run
    rcases run with ⟨stateEq, pathEq⟩
    cases pathEq
    exact Or.inr (Or.inr ⟨hkind, rfl⟩)

def ExactAcceptedPathClassification (input : MarkerTerminalInput)
    (before : MarkerTerminalState) (out : MarkerTerminalOutcome) : Prop :=
  (ExactCreateAccountEffect input before out.state ∧
    ExactCreateAccountTrace out.trace) ∨
  (ExactTransferAllocateAssignEffect input before out.state ∧
    ExactTransferAllocateAssignTrace out.trace) ∨
  (ExactAllocateAssignEffect input before out.state ∧
    ExactAllocateAssignTrace out.trace) ∨
  (ExactAlreadyProgramOwnedEffect input before out.state ∧
    ExactAlreadyProgramOwnedTrace out.trace)

theorem translated_accepted_factorization_has_one_exact_marker_lifecycle
    (input : MarkerTerminalInput) (before : MarkerTerminalState)
    (out : MarkerTerminalOutcome)
    (factor : AcceptedMarkerTerminalFactorization input before out) :
    ExactAcceptedPathClassification input before out := by
  have classified :=
    translated_successful_reservation_path_is_exactly_classified input before
      factor.reserved factor.planned factor.path factor.reservationRun
  rcases classified with create | dusted | precreated
  · exact Or.inl (translated_accepted_create_account_path_is_exact
      input before out factor create.1 create.2)
  · rcases dusted.2 with transfer | allocate
    · exact Or.inr (Or.inl
        (translated_accepted_transfer_allocate_assign_path_is_exact
          input before out factor dusted.1 transfer))
    · exact Or.inr (Or.inr (Or.inl
        (translated_accepted_allocate_assign_path_is_exact
          input before out factor dusted.1 allocate)))
  · exact Or.inr (Or.inr (Or.inr
      (translated_accepted_already_program_owned_path_is_exact
        input before out factor precreated.1 precreated.2)))

theorem translated_accepted_atomic_has_one_exact_marker_lifecycle
    (input : MarkerTerminalInput) (before : MarkerTerminalState)
    (out : MarkerTerminalOutcome)
    (accepted : ExactAcceptedMarkerTerminal input before out) :
    ExactAcceptedPathClassification input before out := by
  rcases accepted with ⟨factor⟩
  exact translated_accepted_factorization_has_one_exact_marker_lifecycle
    input before out factor

#print axioms translated_accepted_create_account_path_is_exact
#print axioms translated_accepted_transfer_allocate_assign_path_is_exact
#print axioms translated_accepted_allocate_assign_path_is_exact
#print axioms translated_accepted_already_program_owned_path_is_exact
#print axioms translated_spent_replay_is_exact_and_atomic
#print axioms translated_accepted_marker_is_consumed_exactly
#print axioms translated_successful_reservation_path_is_exactly_classified
#print axioms translated_accepted_atomic_has_one_exact_marker_lifecycle

end V7PoolNullifierMarkerGenerated
