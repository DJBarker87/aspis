import V7RegistryOperator.Funs

/-!
# V7 registry/operator and selected-verifier source bridge

These theorems consume the literal Charon/Aeneas translation of the focused
fixed-width operational projection. They keep mutation and read-only verifier
selection distinct. In particular, no theorem below invents ProgramData,
upgrade-authority, or executable-code-hash authentication: those values are
absent from the current on-chain V1 account contract.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace V7RegistryOperatorGenerated

open Aeneas Aeneas.Std Result ControlFlow Error

attribute [local simp] UScalar.eq_equiv

theorem scalar_val_eq_of_not_bne_true {ty : UScalarTy}
    (x y : UScalar ty) (h : ¬ (x != y) = true) : x.val = y.val := by
  have hxy : x = y := not_ne_iff.mp (fun hne => h (bne_iff_ne.mpr hne))
  exact congrArg UScalar.val hxy

theorem translated_operator_rejection_is_exact_rollback
    (before : RegistrySystem) (operation : RegistryOperation)
    (outcome : RegistryOutcome)
    (run : execute_atomic_registry_operation before operation = ok outcome)
    (rejected : outcome.committed = false) :
    outcome.state = before ∧ outcome.error.isSome = true := by
  cases applyRun : apply_operator before operation with
  | ok result =>
    cases result with
    | Ok state =>
      simp [execute_atomic_registry_operation, applyRun] at run
      subst outcome
      simp at rejected
    | Err error =>
      simp [execute_atomic_registry_operation, applyRun] at run
      subst outcome
      simp
  | fail error => simp [execute_atomic_registry_operation, applyRun] at run
  | div => simp [execute_atomic_registry_operation, applyRun] at run

theorem translated_operator_success_is_exact_apply
    (before : RegistrySystem) (operation : RegistryOperation)
    (outcome : RegistryOutcome)
    (run : execute_atomic_registry_operation before operation = ok outcome)
    (committed : outcome.committed = true) :
    ∃ state,
      apply_operator before operation = ok (.Ok state) ∧
      outcome = {
        committed := true
        state := { state with unrelated_pool_state := before.unrelated_pool_state }
        error := none
      } := by
  cases applyRun : apply_operator before operation with
  | ok result =>
    cases result with
    | Ok state =>
      simp [execute_atomic_registry_operation, applyRun] at run
      subst outcome
      exact ⟨state, rfl, rfl⟩
    | Err error =>
      simp [execute_atomic_registry_operation, applyRun] at run
      subst outcome
      simp at committed
  | fail error => simp [execute_atomic_registry_operation, applyRun] at run
  | div => simp [execute_atomic_registry_operation, applyRun] at run

theorem translated_operator_preserves_unrelated_pool_state
    (before : RegistrySystem) (operation : RegistryOperation)
    (outcome : RegistryOutcome)
    (run : execute_atomic_registry_operation before operation = ok outcome) :
    outcome.state.unrelated_pool_state = before.unrelated_pool_state := by
  cases applyRun : apply_operator before operation with
  | ok result =>
    cases result with
    | Ok state =>
      simp [execute_atomic_registry_operation, applyRun] at run
      subst outcome
      rfl
    | Err error =>
      simp [execute_atomic_registry_operation, applyRun] at run
      subst outcome
      rfl
  | fail error => simp [execute_atomic_registry_operation, applyRun] at run
  | div => simp [execute_atomic_registry_operation, applyRun] at run

theorem translated_frozen_registry_rejects_authority_gate
    (registry : Registry) (gate : AuthorityGate) (generation : Std.U64)
    (frozen : registry.immutable = true)
    (unique : gate.all_accounts_unique = true)
    (registryExact : gate.registry_account_exact = true)
    (programOwned : gate.registry_program_owned = true)
    (writable : gate.registry_writable = true)
    (nonsigner : gate.registry_nonsigner = true) :
    require_authority registry gate generation =
      ok (.Err RegistryError.RegistryFrozen) := by
  simp [require_authority, frozen, unique, registryExact, programOwned,
    writable, nonsigner]

theorem translated_generation_mismatch_rejects_authority_gate
    (registry : Registry) (gate : AuthorityGate) (generation : Std.U64)
    (mutable : registry.immutable = false)
    (authorityNonzero : registry.authority ≠ 0#u64)
    (unique : gate.all_accounts_unique = true)
    (registryExact : gate.registry_account_exact = true)
    (programOwned : gate.registry_program_owned = true)
    (writable : gate.registry_writable = true)
    (nonsigner : gate.registry_nonsigner = true)
    (authorityExact : gate.authority_key = registry.authority)
    (authoritySigner : gate.authority_signer = true)
    (authorityReadonly : gate.authority_readonly = true)
    (authorityNonexec : gate.authority_nonexecutable = true)
    (mismatch : registry.generation ≠ generation) :
    require_authority registry gate generation =
      ok (.Err RegistryError.GenerationMismatch) := by
  simp [require_authority, mutable, authorityNonzero, unique, registryExact,
    programOwned, writable, nonsigner, authorityExact, authoritySigner,
    authorityReadonly, authorityNonexec, mismatch]

def ExactRegistryAuthentication (input : SelectionInput) : Prop :=
  input.policy_registry_program ≠ 0#u64 ∧
  input.policy_binding ≠ 0#u64 ∧
  input.registry_account_program_owned = true ∧
  input.registry_account_readonly = true ∧
  input.registry_pda_exact = true ∧
  input.registry.pool = input.pool ∧
  input.registry.authority = input.policy_authority ∧
  input.registry.policy = input.policy_binding ∧
  input.registry.immutable = input.policy_requires_immutable ∧
  input.registry.paused = false

def ExactEntryAuthentication (input : SelectionInput) : Prop :=
  input.entry_account_program_owned = true ∧
  input.entry_account_readonly = true ∧
  input.entry_pda_exact = true ∧
  input.entry.pool.val = input.pool.val ∧
  input.entry.policy.val = input.policy_binding.val ∧
  input.entry.verifier_program.val = input.selected_verifier_program.val ∧
  input.entry.profile.val = input.selected_profile.val ∧
  input.entry.release.val = input.selected_release.val ∧
  input.entry.statement_version.val = input.statement_version.val ∧
  input.entry.status = EntryStatus.Active ∧
  input.entry.activation_slot.val ≤ input.current_slot.val ∧
  (input.entry.retirement_slot.val = NO_RETIREMENT_SLOT.val ∨
    input.current_slot.val < input.entry.retirement_slot.val)

def ExactVerifierAccountAuthentication (input : SelectionInput) : Prop :=
  input.verifier_key = input.selected_verifier_program ∧
  input.verifier_loader.read_discriminant ≠
    SupportedLoader.Unsupported.read_discriminant ∧
  input.verifier_executable = true ∧
  input.verifier_readonly = true ∧
  input.verifier_nonsigner = true ∧
  input.proof_owner = input.selected_verifier_program ∧
  input.proof_readonly = true ∧
  input.proof_nonsigner = true

def ExactVerifierReturnAuthentication (input : SelectionInput) : Prop :=
  input.verifier_cpi_succeeds = true ∧
  input.return_present = true ∧
  input.returned_program = input.selected_verifier_program ∧
  input.returned_length = ASR8_BYTES ∧
  input.returned_canonical = true ∧
  input.returned_semantics_exact = true

def ExactCompatibleReplacementBindings (retiring replacement : Entry) : Prop :=
  replacement.pool = retiring.pool ∧
  replacement.policy = retiring.policy ∧
  replacement.profile = retiring.profile ∧
  replacement.statement_version = retiring.statement_version ∧
  replacement.release ≠ retiring.release

theorem translated_compatible_replacement_success_binds_exact_relation
    (retiring replacement : Entry) (slot : Std.U64)
    (run : exact_replacement retiring replacement slot = ok true) :
    ExactCompatibleReplacementBindings retiring replacement := by
  unfold exact_replacement at run
  have hpool : replacement.pool = retiring.pool := by
    by_contra h
    rw [if_neg h] at run
    cases run
  rw [if_pos hpool] at run
  have hpolicy : replacement.policy = retiring.policy := by
    by_contra h
    rw [if_neg h] at run
    cases run
  rw [if_pos hpolicy] at run
  have hprofile : replacement.profile = retiring.profile := by
    by_contra h
    rw [if_neg h] at run
    cases run
  rw [if_pos hprofile] at run
  have hversion : replacement.statement_version = retiring.statement_version := by
    by_contra h
    rw [if_neg h] at run
    cases run
  rw [if_pos hversion] at run
  have hrelease : replacement.release ≠ retiring.release := by
    intro h
    simp [h] at run
  exact ⟨hpool, hpolicy, hprofile, hversion, hrelease⟩

def ExactSelectedVerifierGuarantee
    (input : SelectionInput) (accepted : AuthenticatedSelection) : Prop :=
  ExactRegistryAuthentication input ∧
  ExactEntryAuthentication input ∧
  ExactVerifierAccountAuthentication input ∧
  ExactVerifierReturnAuthentication input ∧
  accepted = {
    pool := input.pool
    registry_program := input.policy_registry_program
    registry_generation := input.registry.generation
    verifier_program := input.selected_verifier_program
    profile := input.selected_profile
    release := input.selected_release
    statement_version := input.statement_version
    authenticated_at_slot := input.current_slot
  }

theorem translated_registry_authentication_success_is_exact
    (input : SelectionInput)
    (run : authenticate_registry input = ok (.Ok ())) :
    ExactRegistryAuthentication input := by
  unfold authenticate_registry at run
  repeat'
    (split at run <;>
      try simp_all only [Bind.bind, Aeneas.Std.bind,
        Aeneas.Std.Result.ok.injEq])
  all_goals simp_all [ExactRegistryAuthentication]

theorem translated_entry_authentication_success_is_exact
    (input : SelectionInput)
    (run : authenticate_entry input = ok (.Ok ())) :
    ExactEntryAuthentication input := by
  unfold authenticate_entry at run
  have howned : input.entry_account_program_owned = true := by
    by_contra h
    simp [h] at run
  rw [if_pos howned] at run
  have hreadonly : input.entry_account_readonly = true := by
    by_contra h
    simp [h] at run
  rw [if_pos hreadonly] at run
  have hpda : input.entry_pda_exact = true := by
    by_contra h
    simp [h] at run
  rw [if_pos hpda] at run
  have hpool : ¬ (input.entry.pool != input.pool) = true := by
    intro h
    rw [if_pos h] at run
    cases run
  rw [if_neg hpool] at run
  have hpolicy : ¬ (input.entry.policy != input.policy_binding) = true := by
    intro h
    rw [if_pos h] at run
    cases run
  rw [if_neg hpolicy] at run
  have hprogram : ¬ (input.entry.verifier_program !=
      input.selected_verifier_program) = true := by
    intro h
    rw [if_pos h] at run
    cases run
  rw [if_neg hprogram] at run
  have hprofile : ¬ (input.entry.profile != input.selected_profile) = true := by
    intro h
    rw [if_pos h] at run
    cases run
  rw [if_neg hprofile] at run
  have hrelease : ¬ (input.entry.release != input.selected_release) = true := by
    intro h
    rw [if_pos h] at run
    cases run
  rw [if_neg hrelease] at run
  have hversion : ¬ (input.entry.statement_version !=
      input.statement_version) = true := by
    intro h
    rw [if_pos h] at run
    cases run
  rw [if_neg hversion] at run
  have hstatus : input.entry.status = EntryStatus.Active := by
    cases statusExact : input.entry.status
    all_goals simp [statusExact,
      EntryStatus.read_discriminant,
      EntryStatus.Insts.CoreCmpPartialEqEntryStatus.eq,
      core.cmp.PartialEq.ne.trait_default,
      core.cmp.PartialEq.ne.default] at run
    rfl
  simp [hstatus, EntryStatus.Insts.CoreCmpPartialEqEntryStatus.eq,
    core.cmp.PartialEq.ne.trait_default,
    core.cmp.PartialEq.ne.default] at run
  have hactive : ¬ input.current_slot.val < input.entry.activation_slot.val := by
    intro h
    rw [if_pos h] at run
    cases run
  rw [if_neg hactive] at run
  by_cases hretired : input.entry.retirement_slot.val = NO_RETIREMENT_SLOT.val
  · rw [if_pos hretired] at run
    exact ⟨howned, hreadonly, hpda,
      scalar_val_eq_of_not_bne_true input.entry.pool input.pool hpool,
      scalar_val_eq_of_not_bne_true input.entry.policy input.policy_binding hpolicy,
      scalar_val_eq_of_not_bne_true input.entry.verifier_program
        input.selected_verifier_program hprogram,
      scalar_val_eq_of_not_bne_true input.entry.profile input.selected_profile hprofile,
      scalar_val_eq_of_not_bne_true input.entry.release input.selected_release hrelease,
      scalar_val_eq_of_not_bne_true input.entry.statement_version
        input.statement_version hversion,
      hstatus,
      Nat.le_of_not_gt hactive, Or.inl hretired⟩
  · rw [if_neg hretired] at run
    have hfuture : ¬ input.entry.retirement_slot.val ≤ input.current_slot.val := by
      intro h
      rw [if_pos h] at run
      cases run
    rw [if_neg hfuture] at run
    exact ⟨howned, hreadonly, hpda,
      scalar_val_eq_of_not_bne_true input.entry.pool input.pool hpool,
      scalar_val_eq_of_not_bne_true input.entry.policy input.policy_binding hpolicy,
      scalar_val_eq_of_not_bne_true input.entry.verifier_program
        input.selected_verifier_program hprogram,
      scalar_val_eq_of_not_bne_true input.entry.profile input.selected_profile hprofile,
      scalar_val_eq_of_not_bne_true input.entry.release input.selected_release hrelease,
      scalar_val_eq_of_not_bne_true input.entry.statement_version
        input.statement_version hversion,
      hstatus,
      Nat.le_of_not_gt hactive, Or.inr (Nat.lt_of_not_ge hfuture)⟩

theorem translated_verifier_account_authentication_success_is_exact
    (input : SelectionInput)
    (run : authenticate_verifier_accounts input = ok (.Ok ())) :
    ExactVerifierAccountAuthentication input := by
  unfold authenticate_verifier_accounts at run
  repeat'
    (split at run <;>
      try simp_all only [Bind.bind, Aeneas.Std.bind,
        Aeneas.Std.Result.ok.injEq])
  all_goals simp_all [ExactVerifierAccountAuthentication,
    SupportedLoader.Insts.CoreCmpPartialEqSupportedLoader.eq]

theorem translated_verifier_return_authentication_success_is_exact
    (input : SelectionInput)
    (run : authenticate_verifier_return input = ok (.Ok ())) :
    ExactVerifierReturnAuthentication input := by
  unfold authenticate_verifier_return at run
  repeat'
    (split at run <;>
      try simp_all only [Bind.bind, Aeneas.Std.bind,
        Aeneas.Std.Result.ok.injEq])
  all_goals simp_all [ExactVerifierReturnAuthentication]

theorem translated_selected_verifier_success_has_exact_guarantee
    (input : SelectionInput) (accepted : AuthenticatedSelection)
    (run : authenticate_and_invoke_selected_verifier input = ok (.Ok accepted)) :
    ExactSelectedVerifierGuarantee input accepted := by
  cases registryRun : authenticate_registry input with
  | ok registryResult =>
    cases registryResult with
    | Ok unit =>
      cases entryRun : authenticate_entry input with
      | ok entryResult =>
        cases entryResult with
        | Ok unit =>
          cases accountRun : authenticate_verifier_accounts input with
          | ok accountResult =>
            cases accountResult with
            | Ok unit =>
              cases returnRun : authenticate_verifier_return input with
              | ok returnResult =>
                cases returnResult with
                | Ok unit =>
                  simp [authenticate_and_invoke_selected_verifier, registryRun,
                    entryRun, accountRun, returnRun,
                    core.result.Result.Insts.CoreOpsTry.branch] at run
                  subst accepted
                  have hr := translated_registry_authentication_success_is_exact input registryRun
                  have he := translated_entry_authentication_success_is_exact input entryRun
                  have ha := translated_verifier_account_authentication_success_is_exact input accountRun
                  have hv := translated_verifier_return_authentication_success_is_exact input returnRun
                  exact ⟨hr, he, ha, hv, rfl⟩
                | Err error => simp [authenticate_and_invoke_selected_verifier,
                    registryRun, entryRun, accountRun, returnRun,
                    core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at run
              | fail error => simp [authenticate_and_invoke_selected_verifier,
                  registryRun, entryRun, accountRun, returnRun,
                  core.result.Result.Insts.CoreOpsTry.branch] at run
              | div => simp [authenticate_and_invoke_selected_verifier,
                  registryRun, entryRun, accountRun, returnRun,
                  core.result.Result.Insts.CoreOpsTry.branch] at run
            | Err error => simp [authenticate_and_invoke_selected_verifier,
                registryRun, entryRun, accountRun,
                core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at run
          | fail error => simp [authenticate_and_invoke_selected_verifier,
              registryRun, entryRun, accountRun,
              core.result.Result.Insts.CoreOpsTry.branch] at run
          | div => simp [authenticate_and_invoke_selected_verifier,
              registryRun, entryRun, accountRun,
              core.result.Result.Insts.CoreOpsTry.branch] at run
        | Err error => simp [authenticate_and_invoke_selected_verifier,
            registryRun, entryRun,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at run
      | fail error => simp [authenticate_and_invoke_selected_verifier,
          registryRun, entryRun, core.result.Result.Insts.CoreOpsTry.branch] at run
      | div => simp [authenticate_and_invoke_selected_verifier,
          registryRun, entryRun, core.result.Result.Insts.CoreOpsTry.branch] at run
    | Err error => simp [authenticate_and_invoke_selected_verifier, registryRun,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at run
  | fail error => simp [authenticate_and_invoke_selected_verifier, registryRun,
      core.result.Result.Insts.CoreOpsTry.branch] at run
  | div => simp [authenticate_and_invoke_selected_verifier, registryRun,
      core.result.Result.Insts.CoreOpsTry.branch] at run

/-- Deployment facts intentionally absent from the current V1 on-chain input. -/
structure DeploymentEvidence where
  programDataAddress : Std.U64
  executableCodeHash : Std.U64
  upgradeAuthority : Std.U64
  immutableProgramData : Bool

def selectedWithDeploymentEvidence
    (input : SelectionInput) (_evidence : DeploymentEvidence) :
    Result (core.result.Result AuthenticatedSelection SelectionError) :=
  authenticate_and_invoke_selected_verifier input

theorem current_v1_selection_is_independent_of_programdata_code_hash_and_authority
    (input : SelectionInput) (left right : DeploymentEvidence) :
    selectedWithDeploymentEvidence input left =
      selectedWithDeploymentEvidence input right := by
  rfl

theorem translated_combined_root_keeps_operator_and_selection_separate
    (before : RegistrySystem) (operation : RegistryOperation)
    (selection : SelectionInput) (roots : SourceRoots)
    (run : registry_operator_and_selected_verifier_source_roots
      before operation selection = ok roots) :
    ∃ operator selected,
      execute_atomic_registry_operation before operation = ok operator ∧
      authenticate_and_invoke_selected_verifier selection = ok selected ∧
      roots = { operator := operator, selected := selected } := by
  cases operatorRun : execute_atomic_registry_operation before operation with
  | ok operator =>
    cases selectedRun : authenticate_and_invoke_selected_verifier selection with
    | ok selected =>
      simp [registry_operator_and_selected_verifier_source_roots,
        operatorRun, selectedRun] at run
      subst roots
      exact ⟨operator, selected, rfl, rfl, rfl⟩
    | fail error => simp [registry_operator_and_selected_verifier_source_roots,
        operatorRun, selectedRun] at run
    | div => simp [registry_operator_and_selected_verifier_source_roots,
        operatorRun, selectedRun] at run
  | fail error => simp [registry_operator_and_selected_verifier_source_roots,
      operatorRun] at run
  | div => simp [registry_operator_and_selected_verifier_source_roots,
      operatorRun] at run

end V7RegistryOperatorGenerated
