import V7PoolNullifierMarker.Funs

/-!
# V7 Pool nullifier-marker reservation source bridge

This bridge isolates the production delta introduced at `da77d5f5`: the Pool
authenticates the payer and System Program, plans the exact nullifier PDA,
creates or allocates/assigns it when necessary, replans the live account under
the canonical Rent schedule, and only then calls the verifier. The frozen
one-terminal caller bridge consumes the resulting program-owned zero marker at
`core_writeback_applied`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace V7PoolNullifierMarkerGenerated

open Aeneas Aeneas.Std Result ControlFlow Error

def ExactPayerAndSystemAuthentication
    (input : MarkerTerminalInput) (before : MarkerTerminalState) : Prop :=
  input.all_terminal_accounts_unique = true ∧
  before.payer.account.signer = true ∧
  before.payer.account.writable = true ∧
  before.payer.account.executable = false ∧
  before.payer.account.owner.val = SYSTEM_PROGRAM_ID.val ∧
  input.system_program.key.val = SYSTEM_PROGRAM_ID.val ∧
  input.system_program.owner.val = NATIVE_LOADER_ID.val ∧
  input.system_program.executable = true ∧
  input.system_program.signer = false ∧
  input.system_program.writable = false

def ExactMarkerIdentity
    (input : MarkerTerminalInput) (marker : MarkerAccount) : Prop :=
  input.derivation.pda_exact = true ∧
  input.derivation.seed_tag.val = NULLIFIER_MARKER_SEED_TAG.val ∧
  input.derivation.pool.val = input.pool.val ∧
  input.derivation.canonical_nullifier.val = input.expected_marker.nullifier.val ∧
  input.expected_marker.pool.val = input.pool.val ∧
  marker.account.key.val = input.derivation.expected_address.val ∧
  marker.account.key.val ≠ input.pool.val ∧
  marker.account.executable = false ∧
  marker.account.signer = false ∧
  marker.account.writable = true

def ExactCreateZeroLamportEntry
    (input : MarkerTerminalInput) (marker : MarkerAccount) : Prop :=
  ExactMarkerIdentity input marker ∧
  marker.account.owner.val = SYSTEM_PROGRAM_ID.val ∧
  marker.data_len.val = 0 ∧
  marker.data_zeroed = true ∧
  marker.stored_marker = none ∧
  marker.lamports.val = 0

def ExactDustedSystemEntry
    (input : MarkerTerminalInput) (marker : MarkerAccount) : Prop :=
  ExactMarkerIdentity input marker ∧
  marker.account.owner.val = SYSTEM_PROGRAM_ID.val ∧
  marker.data_len.val = 0 ∧
  marker.data_zeroed = true ∧
  marker.stored_marker = none ∧
  marker.lamports.val ≠ 0

def ExactProgramOwnedZeroEntry
    (input : MarkerTerminalInput) (marker : MarkerAccount) : Prop :=
  ExactMarkerIdentity input marker ∧
  marker.account.owner.val = input.program_id.val ∧
  marker.data_len.val = NULLIFIER_MARKER_BYTES.val ∧
  marker.data_zeroed = true ∧
  marker.stored_marker = none

theorem scalar_val_eq_of_not_bne_true {ty : UScalarTy}
    (x y : UScalar ty) (h : ¬ (x != y) = true) : x.val = y.val := by
  have hxy : x = y := not_ne_iff.mp (fun hne => h (bne_iff_ne.mpr hne))
  exact congrArg UScalar.val hxy

def ExactSuccessfulPlanClassification (input : MarkerTerminalInput)
    (marker : MarkerAccount) (planned : PlannedMarker) : Prop :=
  (planned.preparation = .CreateZeroLamport ∧
      ExactCreateZeroLamportEntry input marker ∧
      planned.address_bump = input.derivation.bump ∧
      planned.marker = input.expected_marker) ∨
  (planned.preparation = .AllocateDusted ∧
      ExactDustedSystemEntry input marker ∧
      planned.address_bump = input.derivation.bump ∧
      planned.marker = input.expected_marker) ∨
  (planned.preparation = .ProgramOwnedZeroed ∧
      ExactProgramOwnedZeroEntry input marker ∧
      planned.address_bump = input.derivation.bump ∧
      planned.marker = input.expected_marker)

def ExactCreateAccountTrace (trace : CallTrace) : Prop :=
  trace = {
    create_account_step := 1#u8
    transfer_step := 0#u8
    allocate_step := 0#u8
    assign_step := 0#u8
    replan_step := 2#u8
    verifier_step := 3#u8
    core_apply_step := 4#u8
    consume_step := 5#u8
  }

def ExactTransferAllocateAssignTrace (trace : CallTrace) : Prop :=
  trace = {
    create_account_step := 0#u8
    transfer_step := 1#u8
    allocate_step := 2#u8
    assign_step := 3#u8
    replan_step := 4#u8
    verifier_step := 5#u8
    core_apply_step := 6#u8
    consume_step := 7#u8
  }

def ExactAllocateAssignTrace (trace : CallTrace) : Prop :=
  trace = {
    create_account_step := 0#u8
    transfer_step := 0#u8
    allocate_step := 1#u8
    assign_step := 2#u8
    replan_step := 3#u8
    verifier_step := 4#u8
    core_apply_step := 5#u8
    consume_step := 6#u8
  }

def ExactAlreadyProgramOwnedTrace (trace : CallTrace) : Prop :=
  trace = {
    create_account_step := 0#u8
    transfer_step := 0#u8
    allocate_step := 0#u8
    assign_step := 0#u8
    replan_step := 1#u8
    verifier_step := 2#u8
    core_apply_step := 3#u8
    consume_step := 4#u8
  }

def ExactTraceForPath (path : ReservationPath) (trace : CallTrace) : Prop :=
  match path with
  | .CreateAccount => ExactCreateAccountTrace trace
  | .TransferAllocateAssign => ExactTransferAllocateAssignTrace trace
  | .AllocateAssign => ExactAllocateAssignTrace trace
  | .AlreadyProgramOwned => ExactAlreadyProgramOwnedTrace trace

def ExactCreateAccountEffect
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
        data_zeroed := false
        stored_marker := some input.expected_marker
      }
      core_writeback_applied := true
    }

def ExactTransferAllocateAssignEffect
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
        data_zeroed := false
        stored_marker := some input.expected_marker
      }
      core_writeback_applied := true
    }

def ExactAllocateAssignEffect
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
      data_zeroed := false
      stored_marker := some input.expected_marker
    }
    core_writeback_applied := true
  }

def ExactAlreadyProgramOwnedEffect
    (input : MarkerTerminalInput) (before after : MarkerTerminalState) : Prop :=
  ExactProgramOwnedZeroEntry input before.marker ∧
  after = {
    before with
    marker := {
      before.marker with
      data_zeroed := false
      stored_marker := some input.expected_marker
    }
    core_writeback_applied := true
  }

def ExactEffectForPath (input : MarkerTerminalInput)
    (before after : MarkerTerminalState) (path : ReservationPath) : Prop :=
  match path with
  | .CreateAccount => ExactCreateAccountEffect input before after
  | .TransferAllocateAssign =>
      ExactTransferAllocateAssignEffect input before after
  | .AllocateAssign => ExactAllocateAssignEffect input before after
  | .AlreadyProgramOwned => ExactAlreadyProgramOwnedEffect input before after

structure AcceptedMarkerTerminalFactorization (input : MarkerTerminalInput)
    (before : MarkerTerminalState) (out : MarkerTerminalOutcome) : Type where
  planned : PlannedMarker
  reserved : MarkerTerminalState
  path : ReservationPath
  ready : PlannedMarker
  reservationTrace : CallTrace
  verifierTrace : CallTrace
  coreTrace : CallTrace
  consumedTrace : CallTrace
  rentLoaded : input.rent.loaded_from_sysvar = true
  rentNonzero : input.rent.required_lamports.val ≠ 0
  authenticationRun :
    authenticate_payer_and_system input before = .ok (.Ok ())
  initialPlanRun : plan_marker input before.marker = .ok (.Ok planned)
  reservationRun :
    reserve_marker input before planned = .ok (.Ok (reserved, path))
  readyPlanRun : plan_marker input reserved.marker = .ok (.Ok ready)
  readyKind : ready.preparation = .ProgramOwnedZeroed
  readyBump : ready.address_bump = planned.address_bump
  readyImage : marker_images_equal ready.marker planned.marker = .ok true
  readyRent : ¬ reserved.marker.lamports < input.rent.required_lamports
  verifierSucceeded : input.runtime.verifier_cpi_succeeds = true
  coreSucceeded : input.runtime.core_apply_succeeds = true
  markerWriteSucceeded : input.runtime.marker_write_succeeds = true
  reservationTraceRun : reservation_trace path = .ok reservationTrace
  verifierTraceRun : record_verifier reservationTrace path = .ok verifierTrace
  coreTraceRun : record_core_apply verifierTrace path = .ok coreTrace
  consumedTraceRun : record_consumption coreTrace path = .ok consumedTrace
  outExact : out = {
    committed := true
    state := {
      reserved with
      marker := {
        reserved.marker with
        data_zeroed := false
        stored_marker := some ready.marker
      }
      core_writeback_applied := true
    }
    trace := consumedTrace
    certificate := some {
      path := path
      marker := ready.marker
      payer_before := before.payer.lamports
      payer_after := reserved.payer.lamports
      ready_marker_lamports := reserved.marker.lamports
      trace := consumedTrace
    }
    error := none
  }

def ExactAcceptedMarkerTerminal (input : MarkerTerminalInput)
    (before : MarkerTerminalState) (out : MarkerTerminalOutcome) : Prop :=
  Nonempty (AcceptedMarkerTerminalFactorization input before out)

theorem translated_payer_and_system_success_is_exact
    (input : MarkerTerminalInput) (before : MarkerTerminalState)
    (run : authenticate_payer_and_system input before = .ok (.Ok ())) :
    ExactPayerAndSystemAuthentication input before := by
  unfold authenticate_payer_and_system at run
  repeat'
    (split at run <;>
      try dsimp at run <;>
      try simp_all only [Bind.bind, Aeneas.Std.bind,
        Aeneas.Std.Result.ok.injEq])
  all_goals simp_all [ExactPayerAndSystemAuthentication]

theorem translated_successful_plan_is_exactly_classified
    (input : MarkerTerminalInput) (marker : MarkerAccount)
    (planned : PlannedMarker)
    (run : plan_marker input marker = .ok (.Ok planned)) :
    ExactSuccessfulPlanClassification input marker planned := by
  unfold plan_marker at run
  have hpda : input.derivation.pda_exact = true := by
    by_contra h
    rw [if_neg h] at run
    cases run
  rw [if_pos hpda] at run
  have hseed :
      ¬ (input.derivation.seed_tag != NULLIFIER_MARKER_SEED_TAG) = true := by
    intro h
    rw [if_pos h] at run
    cases run
  rw [if_neg hseed] at run
  have hpool : ¬ (input.derivation.pool != input.pool) = true := by
    intro h
    rw [if_pos h] at run
    cases run
  rw [if_neg hpool] at run
  have hnullifier :
      ¬ (input.derivation.canonical_nullifier !=
        input.expected_marker.nullifier) = true := by
    intro h
    rw [if_pos h] at run
    cases run
  rw [if_neg hnullifier] at run
  have himagepool :
      ¬ (input.expected_marker.pool != input.pool) = true := by
    intro h
    rw [if_pos h] at run
    cases run
  rw [if_neg himagepool] at run
  have hkey :
      ¬ (marker.account.key != input.derivation.expected_address) = true := by
    intro h
    rw [if_pos h] at run
    cases run
  rw [if_neg hkey] at run
  have hself : ¬ marker.account.key = input.pool := by
    intro h
    rw [if_pos h] at run
    cases run
  rw [if_neg hself] at run
  have hexec : ¬ marker.account.executable = true := by
    intro h
    rw [if_pos h] at run
    cases run
  rw [if_neg hexec] at run
  have hsigner : ¬ marker.account.signer = true := by
    intro h
    rw [if_pos h] at run
    cases run
  rw [if_neg hsigner] at run
  have hwritable : marker.account.writable = true := by
    by_contra h
    rw [if_neg h] at run
    cases run
  rw [if_pos hwritable] at run
  have identity : ExactMarkerIdentity input marker := by
    refine ⟨hpda,
      scalar_val_eq_of_not_bne_true input.derivation.seed_tag
        NULLIFIER_MARKER_SEED_TAG hseed,
      scalar_val_eq_of_not_bne_true input.derivation.pool input.pool hpool,
      scalar_val_eq_of_not_bne_true input.derivation.canonical_nullifier
        input.expected_marker.nullifier hnullifier,
      scalar_val_eq_of_not_bne_true input.expected_marker.pool input.pool
        himagepool,
      scalar_val_eq_of_not_bne_true marker.account.key
        input.derivation.expected_address hkey,
      ?_, Bool.eq_false_iff.mpr hexec, Bool.eq_false_iff.mpr hsigner,
      hwritable⟩
    intro keyEq
    exact hself (UScalar.val_eq_imp _ _ keyEq)
  by_cases hprogram : marker.account.owner = input.program_id
  · rw [if_pos hprogram] at run
    have hlen :
        ¬ (marker.data_len != NULLIFIER_MARKER_BYTES) = true := by
      intro h
      rw [if_pos h] at run
      cases run
    rw [if_neg hlen] at run
    have hstored : marker.stored_marker = none := by
      cases h : marker.stored_marker
      · rfl
      · rw [h] at run
        cases run
    rw [hstored] at run
    have hzero : marker.data_zeroed = true := by
      by_contra h
      rw [if_neg h] at run
      cases run
    rw [if_pos hzero] at run
    injection run with eqplanned
    injection eqplanned with hplanned
    cases hplanned
    exact Or.inr (Or.inr ⟨rfl,
      ⟨identity, congrArg UScalar.val hprogram,
        scalar_val_eq_of_not_bne_true marker.data_len
          NULLIFIER_MARKER_BYTES hlen, hzero, hstored⟩,
      rfl, rfl⟩)
  · rw [if_neg hprogram] at run
    have hsystem : marker.account.owner = SYSTEM_PROGRAM_ID := by
      by_contra h
      rw [if_neg h] at run
      cases run
    rw [if_pos hsystem] at run
    have hlen : ¬ (marker.data_len != 0#u16) = true := by
      intro h
      rw [if_pos h] at run
      cases run
    rw [if_neg hlen] at run
    have hzero : marker.data_zeroed = true := by
      by_contra h
      rw [if_neg h] at run
      cases run
    rw [if_pos hzero] at run
    have hstored : marker.stored_marker = none := by
      cases h : marker.stored_marker
      · rfl
      · rw [h] at run
        cases run
    rw [hstored] at run
    by_cases hlamports : marker.lamports = 0#u64
    · rw [if_pos hlamports] at run
      injection run with eqplanned
      injection eqplanned with hplanned
      cases hplanned
      exact Or.inl ⟨rfl,
        ⟨identity, congrArg UScalar.val hsystem,
          scalar_val_eq_of_not_bne_true marker.data_len 0#u16 hlen,
          hzero, hstored, congrArg UScalar.val hlamports⟩,
        rfl, rfl⟩
    · rw [if_neg hlamports] at run
      injection run with eqplanned
      injection eqplanned with hplanned
      cases hplanned
      apply Or.inr
      apply Or.inl
      refine ⟨rfl,
        ⟨identity, congrArg UScalar.val hsystem,
          scalar_val_eq_of_not_bne_true marker.data_len 0#u16 hlen,
          hzero, hstored, ?_⟩,
        rfl, rfl⟩
      intro zeroVal
      exact hlamports (UScalar.val_eq_imp _ _ zeroVal)

theorem translated_create_zero_plan_is_exact
    (input : MarkerTerminalInput) (marker : MarkerAccount)
    (planned : PlannedMarker)
    (run : plan_marker input marker = .ok (.Ok planned))
    (kind : planned.preparation = .CreateZeroLamport) :
    ExactCreateZeroLamportEntry input marker ∧
      planned.address_bump = input.derivation.bump ∧
      planned.marker = input.expected_marker := by
  rcases translated_successful_plan_is_exactly_classified input marker planned
      run with create | dusted | programOwned
  · exact ⟨create.2.1, create.2.2.1, create.2.2.2⟩
  · rw [kind] at dusted
    cases dusted.1
  · rw [kind] at programOwned
    cases programOwned.1

theorem translated_dusted_plan_is_exact
    (input : MarkerTerminalInput) (marker : MarkerAccount)
    (planned : PlannedMarker)
    (run : plan_marker input marker = .ok (.Ok planned))
    (kind : planned.preparation = .AllocateDusted) :
    ExactDustedSystemEntry input marker ∧
      planned.address_bump = input.derivation.bump ∧
      planned.marker = input.expected_marker := by
  rcases translated_successful_plan_is_exactly_classified input marker planned
      run with create | dusted | programOwned
  · rw [kind] at create
    cases create.1
  · exact ⟨dusted.2.1, dusted.2.2.1, dusted.2.2.2⟩
  · rw [kind] at programOwned
    cases programOwned.1

theorem translated_program_owned_plan_is_exact
    (input : MarkerTerminalInput) (marker : MarkerAccount)
    (planned : PlannedMarker)
    (run : plan_marker input marker = .ok (.Ok planned))
    (kind : planned.preparation = .ProgramOwnedZeroed) :
    ExactProgramOwnedZeroEntry input marker ∧
      planned.address_bump = input.derivation.bump ∧
      planned.marker = input.expected_marker := by
  rcases translated_successful_plan_is_exactly_classified input marker planned
      run with create | dusted | programOwned
  · rw [kind] at create
    cases create.1
  · rw [kind] at dusted
    cases dusted.1
  · exact ⟨programOwned.2.1, programOwned.2.2.1,
      programOwned.2.2.2⟩

theorem translated_rejected_atomic_marker_terminal_is_exact_prestate
    (input : MarkerTerminalInput) (before : MarkerTerminalState)
    (out : MarkerTerminalOutcome)
    (run : execute_atomic_marker_terminal input before = .ok out)
    (rejected : out.committed = false) :
    out.state = before ∧ out.certificate = none := by
  unfold execute_atomic_marker_terminal at run
  generalize innerRun : execute_marker_terminal_inner input before = innerResult at run
  cases innerResult with
  | fail error => simp [innerRun] at run
  | div => simp [innerRun] at run
  | ok inner =>
      cases h : inner.committed <;> simp [innerRun, h] at run
      · subst out
        exact ⟨rfl, rfl⟩
      · subst out
        exact Bool.noConfusion (h.symm.trans rejected)

theorem translated_accepted_atomic_marker_terminal_is_exact
    (input : MarkerTerminalInput) (before : MarkerTerminalState)
    (out : MarkerTerminalOutcome)
    (run : execute_atomic_marker_terminal input before = .ok out)
    (accepted : out.committed = true) :
    ExactAcceptedMarkerTerminal input before out := by
  unfold execute_atomic_marker_terminal at run
  generalize innerRun : execute_marker_terminal_inner input before = innerResult at run
  cases innerResult with
  | fail error => simp [innerRun] at run
  | div => simp [innerRun] at run
  | ok inner =>
      cases h : inner.committed <;> simp [innerRun, h] at run
      · subst out
        simp at accepted
      · subst out
        unfold execute_marker_terminal_inner at innerRun
        split at innerRun
        · rename_i rentLoaded
          split at innerRun
          · simp [empty_trace, rejected_inner] at innerRun
            subst inner
            simp at accepted
          · rename_i rentNonzero
            generalize authenticationRun :
              authenticate_payer_and_system input before = authenticationResult
                at innerRun
            cases authenticationResult with
            | fail error => simp [authenticationRun] at innerRun
            | div => simp [authenticationRun] at innerRun
            | ok authenticationResult =>
              cases authenticationResult with
              | Err error =>
                simp [authenticationRun, empty_trace, rejected_inner] at innerRun
                subst inner
                simp at accepted
              | Ok unit =>
                simp [authenticationRun] at innerRun
                generalize initialPlanRun :
                  plan_marker input before.marker = initialPlanResult at innerRun
                cases initialPlanResult with
                | fail error => simp [initialPlanRun] at innerRun
                | div => simp [initialPlanRun] at innerRun
                | ok initialPlanResult =>
                  cases initialPlanResult with
                  | Err error =>
                    simp [initialPlanRun, empty_trace, rejected_inner] at innerRun
                    subst inner
                    simp at accepted
                  | Ok planned =>
                    simp [initialPlanRun] at innerRun
                    generalize reservationRun :
                      reserve_marker input before planned = reservationResult
                        at innerRun
                    cases reservationResult with
                    | fail error => simp [reservationRun] at innerRun
                    | div => simp [reservationRun] at innerRun
                    | ok reservationResult =>
                      cases reservationResult with
                      | Err error =>
                        simp [reservationRun, empty_trace, rejected_inner]
                          at innerRun
                        subst inner
                        simp at accepted
                      | Ok reservedPair =>
                        simp [reservationRun] at innerRun
                        rcases reservedPair with ⟨reserved, path⟩
                        generalize readyPlanRun :
                          plan_marker input reserved.marker = readyPlanResult
                            at innerRun
                        cases readyPlanResult with
                        | fail error => simp [readyPlanRun] at innerRun
                        | div => simp [readyPlanRun] at innerRun
                        | ok readyPlanResult =>
                          cases readyPlanResult with
                          | Err error =>
                            simp [readyPlanRun, empty_trace, rejected_inner]
                              at innerRun
                            subst inner
                            simp at accepted
                          | Ok ready =>
                            simp [readyPlanRun] at innerRun
                            cases readyKind : ready.preparation with
                            | CreateZeroLamport =>
                              simp [readyKind,
                                MarkerPreparation.Insts.CoreCmpPartialEqMarkerPreparation.eq,
                                core.cmp.PartialEq.ne.trait_default,
                                core.cmp.PartialEq.ne.default,
                                MarkerPreparation.read_discriminant,
                                empty_trace, rejected_inner] at innerRun
                              subst inner
                              simp at accepted
                            | AllocateDusted =>
                              simp [readyKind,
                                MarkerPreparation.Insts.CoreCmpPartialEqMarkerPreparation.eq,
                                core.cmp.PartialEq.ne.trait_default,
                                core.cmp.PartialEq.ne.default,
                                MarkerPreparation.read_discriminant,
                                empty_trace, rejected_inner] at innerRun
                              subst inner
                              simp at accepted
                            | ProgramOwnedZeroed =>
                              simp [readyKind,
                                MarkerPreparation.Insts.CoreCmpPartialEqMarkerPreparation.eq,
                                core.cmp.PartialEq.ne.trait_default,
                                core.cmp.PartialEq.ne.default,
                                MarkerPreparation.read_discriminant] at innerRun
                              split at innerRun
                              · rename_i readyBump
                                generalize readyImageRun :
                                  marker_images_equal ready.marker planned.marker =
                                    readyImageResult at innerRun
                                cases readyImageResult with
                                | fail error => simp [readyImageRun] at innerRun
                                | div => simp [readyImageRun] at innerRun
                                | ok readyImage =>
                                  cases readyImage
                                  · simp [readyImageRun, empty_trace, rejected_inner]
                                      at innerRun
                                    subst inner
                                    simp at accepted
                                  · simp [readyImageRun] at innerRun
                                    split at innerRun
                                    · simp [empty_trace, rejected_inner] at innerRun
                                      subst inner
                                      simp at accepted
                                    · rename_i readyRent
                                      generalize reservationTraceRun :
                                        reservation_trace path = reservationTraceResult
                                          at innerRun
                                      cases reservationTraceResult with
                                      | fail error =>
                                        simp [reservationTraceRun] at innerRun
                                      | div => simp [reservationTraceRun] at innerRun
                                      | ok reservationTrace =>
                                        simp [reservationTraceRun] at innerRun
                                        generalize verifierTraceRun :
                                          record_verifier reservationTrace path =
                                            verifierTraceResult at innerRun
                                        cases verifierTraceResult with
                                        | fail error =>
                                          simp [verifierTraceRun] at innerRun
                                        | div => simp [verifierTraceRun] at innerRun
                                        | ok verifierTrace =>
                                          simp [verifierTraceRun] at innerRun
                                          split at innerRun
                                          · rename_i verifierSucceeded
                                            generalize coreTraceRun :
                                              record_core_apply verifierTrace path =
                                                coreTraceResult at innerRun
                                            cases coreTraceResult with
                                            | fail error =>
                                              simp [coreTraceRun] at innerRun
                                            | div => simp [coreTraceRun] at innerRun
                                            | ok coreTrace =>
                                              simp [coreTraceRun] at innerRun
                                              split at innerRun
                                              · rename_i coreSucceeded
                                                split at innerRun
                                                · rename_i markerWriteSucceeded
                                                  generalize consumedTraceRun :
                                                    record_consumption coreTrace path =
                                                      consumedTraceResult at innerRun
                                                  cases consumedTraceResult with
                                                  | fail error =>
                                                    simp [consumedTraceRun] at innerRun
                                                  | div =>
                                                    simp [consumedTraceRun] at innerRun
                                                  | ok consumedTrace =>
                                                    simp [consumedTraceRun] at innerRun
                                                    subst inner
                                                    refine ⟨{
                                                      planned := planned
                                                      reserved := reserved
                                                      path := path
                                                      ready := ready
                                                      reservationTrace := reservationTrace
                                                      verifierTrace := verifierTrace
                                                      coreTrace := coreTrace
                                                      consumedTrace := consumedTrace
                                                      rentLoaded := rentLoaded
                                                      rentNonzero := ?_
                                                      authenticationRun := authenticationRun
                                                      initialPlanRun := initialPlanRun
                                                      reservationRun := reservationRun
                                                      readyPlanRun := readyPlanRun
                                                      readyKind := readyKind
                                                      readyBump := ?_
                                                      readyImage := readyImageRun
                                                      readyRent := readyRent
                                                      verifierSucceeded := verifierSucceeded
                                                      coreSucceeded := coreSucceeded
                                                      markerWriteSucceeded := markerWriteSucceeded
                                                      reservationTraceRun := reservationTraceRun
                                                      verifierTraceRun := verifierTraceRun
                                                      coreTraceRun := coreTraceRun
                                                      consumedTraceRun := consumedTraceRun
                                                      outExact := rfl
                                                    }⟩
                                                    · intro zeroVal
                                                      exact rentNonzero
                                                        (UScalar.val_eq_imp _ _ zeroVal)
                                                    · exact UScalar.val_eq_imp _ _ readyBump
                                                · simp [empty_trace, rejected_inner] at innerRun
                                                  subst inner
                                                  simp at accepted
                                              · simp [rejected_inner] at innerRun
                                                subst inner
                                                simp at accepted
                                          · simp [rejected_inner] at innerRun
                                            subst inner
                                            simp at accepted
                              · simp [empty_trace, rejected_inner] at innerRun
                                subst inner
                                simp at accepted
        · simp [empty_trace, rejected_inner] at innerRun
          subst inner
          simp at accepted

#print axioms translated_payer_and_system_success_is_exact
#print axioms translated_create_zero_plan_is_exact
#print axioms translated_dusted_plan_is_exact
#print axioms translated_program_owned_plan_is_exact
#print axioms translated_rejected_atomic_marker_terminal_is_exact_prestate
#print axioms translated_accepted_atomic_marker_terminal_is_exact

end V7PoolNullifierMarkerGenerated
