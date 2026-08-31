import V7RegistryV2OneTerminalCaller.Funs

/-!
# V7 Registry V2 one-terminal caller source bridge

The predicates below expose the exact facts established by a successful
translation of the hash-pinned caller's fixed-width operational projection.
They do not assume Registry V2 authorization, ASR8 validity, writeback or
rollback as premises. Solana `AccountInfo`, loader-v3, SHA-256 and CPI/runtime
semantics remain explicit composition boundaries documented by the bundle.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16000

namespace V7RegistryV2OneTerminalCallerGenerated

open Aeneas Aeneas.Std Result ControlFlow Error

def ExactRequestAuthentication (input : CallerInput) : Prop :=
  input.request.encoded_len = ASQ8_BYTES ∧
  input.request.canonical = true ∧
  input.request.pool_program = input.release.pool_program ∧
  input.request.master_account = input.master.account.key ∧
  input.request.checkpoint_account = input.checkpoint.account.key ∧
  input.request.selected_lane_account = input.lane.account.key ∧
  input.request.profile = input.release.profile ∧
  input.request.release = input.release.release ∧
  input.request.output_lane = input.lane.lane_id

def ExactPoolAuthentication (input : CallerInput) : Prop :=
  input.master.account.owner = input.release.pool_program ∧
  input.checkpoint.account.owner = input.release.pool_program ∧
  input.lane.account.owner = input.release.pool_program ∧
  input.master.account.writable = false ∧
  input.master.account.signer = false ∧
  input.checkpoint.account.writable = false ∧
  input.checkpoint.account.signer = false ∧
  input.lane.account.writable = true ∧
  input.lane.account.signer = false ∧
  input.checkpoint.master = input.master.account.key ∧
  input.lane.master = input.master.account.key ∧
  input.lane.invariant_capability = true

def ExactRegistryPolicyAndAccounts (input : CallerInput) : Prop :=
  input.master.policy.registry_program = input.release.registry_program ∧
  input.master.policy.registry_authority = 0#u64 ∧
  input.master.policy.policy_binding = input.release.policy_binding ∧
  input.master.policy.immutable_registry = true ∧
  input.master.policy.immutable_deployment = true ∧
  input.registry.account.owner = input.release.registry_program ∧
  input.entry.account.owner = input.release.registry_program ∧
  input.registry.account.writable = false ∧
  input.registry.account.signer = false ∧
  input.entry.account.writable = false ∧
  input.entry.account.signer = false

def ExactRegistryV2Certificate (input : CallerInput) : Prop :=
  input.registry.canonical_v2 = true ∧
  input.registry.pda_exact = true ∧
  input.registry.pool = input.master.account.key ∧
  input.registry.authority = 0#u64 ∧
  input.registry.policy_binding = input.release.policy_binding ∧
  input.registry.immutable = true ∧
  input.registry.paused = false ∧
  input.registry.registry_program = input.release.registry_program ∧
  input.registry.loader_program = input.release.loader_program ∧
  input.registry.programdata_address = input.release.registry_programdata ∧
  input.registry.programdata_pda_exact = true ∧
  input.registry.executable_hash ≠ 0#u64

def ExactEntryV2Certificate (input : CallerInput) : Prop :=
  input.entry.canonical_v2 = true ∧
  input.entry.pda_exact = true ∧
  input.entry.pool = input.master.account.key ∧
  input.entry.verifier_program = input.release.verifier_program ∧
  input.entry.profile = input.release.profile ∧
  input.entry.release = input.release.release ∧
  input.entry.loader_program = input.release.loader_program ∧
  input.entry.programdata_address = input.release.verifier_programdata ∧
  input.entry.programdata_pda_exact = true ∧
  input.entry.executable_hash ≠ 0#u64 ∧
  input.entry.expected_upgrade_authority = 0#u64 ∧
  input.entry.statement_version = STATEMENT_VERSION

def ExactEntryActive (input : CallerInput) : Prop :=
  input.entry.enabled = true ∧
  input.entry.activation_slot ≤ input.current_slot ∧
  (input.entry.retirement_slot = 0#u64 ∨
    input.current_slot < input.entry.retirement_slot)

def ExactRegistryAuthentication (input : CallerInput) : Prop :=
  ExactRegistryPolicyAndAccounts input ∧
  ExactRegistryV2Certificate input ∧
  ExactEntryV2Certificate input ∧
  ExactEntryActive input

def ExactSelectedVerifierAuthentication (input : CallerInput) : Prop :=
  input.verifier.key = input.release.verifier_program ∧
  input.verifier.owner = input.release.loader_program ∧
  input.verifier.executable = true ∧
  input.verifier.writable = false ∧
  input.verifier.signer = false ∧
  input.proof.account.owner = input.release.verifier_program ∧
  input.proof.account.writable = false ∧
  input.proof.account.signer = false ∧
  input.proof.bound_master = input.master.account.key ∧
  input.proof.bound_checkpoint = input.checkpoint.account.key ∧
  input.proof.bound_lane = input.lane.account.key

def ExactDistinctCpiAccounts (input : CallerInput) : Prop :=
  input.proof.account.key ≠ input.master.account.key ∧
  input.proof.account.key ≠ input.checkpoint.account.key ∧
  input.proof.account.key ≠ input.lane.account.key ∧
  input.proof.account.key ≠ input.registry.account.key ∧
  input.proof.account.key ≠ input.entry.account.key ∧
  input.master.account.key ≠ input.checkpoint.account.key ∧
  input.master.account.key ≠ input.lane.account.key ∧
  input.master.account.key ≠ input.registry.account.key ∧
  input.master.account.key ≠ input.entry.account.key ∧
  input.checkpoint.account.key ≠ input.lane.account.key ∧
  input.checkpoint.account.key ≠ input.registry.account.key ∧
  input.checkpoint.account.key ≠ input.entry.account.key ∧
  input.lane.account.key ≠ input.registry.account.key ∧
  input.lane.account.key ≠ input.entry.account.key ∧
  input.registry.account.key ≠ input.entry.account.key

def ExactReleaseAuthentication (input : CallerInput) : Prop :=
  ExactRequestAuthentication input ∧
  ExactPoolAuthentication input ∧
  ExactRegistryAuthentication input ∧
  ExactSelectedVerifierAuthentication input ∧
  ExactDistinctCpiAccounts input

def ExactResultBinding (input : CallerInput) (result : ReturnedResult) : Prop :=
  input.runtime.verifier_cpi_succeeded = true ∧
  input.verifier_return.program = input.release.verifier_program ∧
  input.verifier_return.encoded_len = ASR8_BYTES ∧
  input.verifier_return.canonical = true ∧
  input.verifier_return.decoded = some result ∧
  result.transition_kind = input.request.payment_kind ∧
  result.master_account = input.master.account.key ∧
  result.selected_lane_account = input.lane.account.key ∧
  result.output_lane = input.request.output_lane ∧
  result.nullifier = input.request.nullifier ∧
  U64.checked_add input.lane.next_pair_index 1#u64 =
    some result.next_pair_index ∧
  result.next_frontier_canonical = true

def ExactMarkerBinding (input : CallerInput) (marker : MarkerImage) : Prop :=
  input.marker.pda_exact = true ∧
  input.marker.program_owned_zeroed = true ∧
  input.marker.account.writable = true ∧
  input.marker.account.signer = false ∧
  input.marker.account.owner = input.release.pool_program ∧
  marker = {
    master := input.master.account.key
    deployment_domain := input.master.deployment_domain
    nullifier := input.request.nullifier
    checkpoint_sequence := input.checkpoint.sequence
    checkpoint_root := input.checkpoint.global_root
    profile := input.request.profile
    release := input.request.release
  }

def ExactCpiAccounts (input : CallerInput)
    (accounts : Array CpiMeta 6#usize) : Prop :=
  exact_cpi_accounts input = ok accounts

def ExactHistoryState (input : CallerInput) (base : PoolImages)
    (accepted : AcceptedExecution) : Prop :=
  (accepted.certificate.page_route = PageRoute.SamePage →
    accepted.state.current_page_last_root =
      accepted.certificate.result.next_root ∧
    accepted.state.current_page_filled =
      input.current_page.filled.wrapping_add 1#u16 ∧
    accepted.state.rollover_page_last_root = base.rollover_page_last_root ∧
    accepted.state.rollover_page_filled = base.rollover_page_filled) ∧
  (accepted.certificate.page_route = PageRoute.Rollover →
    accepted.state.current_page_last_root = base.current_page_last_root ∧
    accepted.state.current_page_filled = base.current_page_filled ∧
    accepted.state.rollover_page_last_root =
      accepted.certificate.result.next_root ∧
    accepted.state.rollover_page_filled = 1#u16)

def ExactPreparedTerminal (input : CallerInput)
    (prepared : PreparedTerminal) : Prop :=
  ExactReleaseAuthentication input ∧
  ExactResultBinding input prepared.result ∧
  ExactMarkerBinding input prepared.marker ∧
  prepared.history.first_sequence = prepared.result.next_pair_index ∧
  prepared.history.root = prepared.result.next_root

def ExactFinalizedCore (input : CallerInput) (base : PoolImages)
    (accepted : AcceptedExecution) : Prop :=
  ExactCpiAccounts input accepted.certificate.cpi_accounts ∧
  accepted.certificate.path_kind = input.request.payment_kind ∧
  accepted.certificate.history_write.route =
    accepted.certificate.page_route ∧
  accepted.certificate.history_write.first_sequence =
    accepted.certificate.result.next_pair_index ∧
  accepted.certificate.history_write.root =
    accepted.certificate.result.next_root ∧
  ExactHistoryState input base accepted ∧
  accepted.state.lane.account = input.lane.account ∧
  accepted.state.lane.master = input.lane.master ∧
  accepted.state.lane.lane_id = input.lane.lane_id ∧
  accepted.state.lane.next_pair_index =
    accepted.certificate.result.next_pair_index ∧
  accepted.state.lane.root = accepted.certificate.result.next_root ∧
  accepted.state.lane.frontier =
    accepted.certificate.result.next_frontier ∧
  accepted.state.lane.invariant_capability = input.lane.invariant_capability ∧
  accepted.state.marker = some accepted.certificate.marker ∧
  accepted.state.returned_result = some accepted.certificate.result ∧
  accepted.certificate.result_bytes_id = input.verifier_return.exact_bytes_id ∧
  accepted.state.returned_result_bytes_id =
    some input.verifier_return.exact_bytes_id ∧
  accepted.state.unrelated = base.unrelated

def ExactFinalizeBinding (input : CallerInput) (base : PoolImages)
    (prepared : PreparedTerminal) (accepted : AcceptedExecution) : Prop :=
  ExactFinalizedCore input base accepted ∧
  accepted.certificate.result = prepared.result ∧
  accepted.certificate.marker = prepared.marker ∧
  accepted.state.vault_balance = base.vault_balance ∧
  accepted.state.destination_balance = base.destination_balance

def ExactWithdrawalState (input : CallerInput) (before after : PoolImages) : Prop :=
  input.tokens.exact_five_accounts = true ∧
  input.tokens.token_program_exact = true ∧
  input.tokens.mint_exact = true ∧
  input.tokens.vault_authority_exact = true ∧
  input.tokens.destination_exact = true ∧
  input.request.withdrawal_destination ≠ 0#u64 ∧
  input.runtime.withdrawal_cpi_succeeded = true ∧
  U64.checked_sub input.tokens.vault_before
      input.request.withdrawal_amount = some input.tokens.vault_after ∧
  U64.checked_add input.tokens.destination_before
      input.request.withdrawal_amount = some input.tokens.destination_after ∧
  after = {
    before with
    vault_balance := input.tokens.vault_after
    destination_balance := input.tokens.destination_after
  }

def ExactAcceptedWriteback (input : CallerInput) (before : PoolImages)
    (accepted : AcceptedExecution) : Prop :=
  ExactReleaseAuthentication input ∧
  ExactResultBinding input accepted.certificate.result ∧
  ExactMarkerBinding input accepted.certificate.marker ∧
  ExactFinalizedCore input before accepted ∧
  input.runtime.lane_borrow_succeeded = true ∧
  input.runtime.page_borrow_succeeded = true ∧
  input.runtime.marker_borrow_succeeded = true ∧
  (input.request.payment_kind = PaymentKind.PrivateTransfer →
    accepted.state.vault_balance = before.vault_balance ∧
    accepted.state.destination_balance = before.destination_balance) ∧
  (input.request.payment_kind = PaymentKind.Withdrawal →
    input.runtime.withdrawal_cpi_succeeded = true ∧
    U64.checked_sub input.tokens.vault_before
      input.request.withdrawal_amount = some input.tokens.vault_after ∧
    U64.checked_add input.tokens.destination_before
      input.request.withdrawal_amount = some input.tokens.destination_after ∧
    accepted.state.vault_balance = input.tokens.vault_after ∧
    accepted.state.destination_balance = input.tokens.destination_after)

attribute [local simp] UScalar.eq_equiv

private theorem break_residual_cannot_return_ok
    {A E F B : Type}
    (input : core.result.Result A E)
    (residual : core.result.Result core.convert.Infallible E)
    (convert : core.convert.From F E)
    (output : B)
    (branchRun :
      core.result.Result.Insts.CoreOpsTry.branch input = .ok (.Break residual))
    (residualRun :
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          B convert residual = .ok (.Ok output)) : False := by
  cases input with
  | Ok value => simp [core.result.Result.Insts.CoreOpsTry.branch] at branchRun
  | Err error =>
      simp [core.result.Result.Insts.CoreOpsTry.branch] at branchRun
      subst residual
      simp only [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
        at residualRun
      cases convertRun : convert.from error <;> simp [convertRun] at residualRun

@[simp] private theorem branch_eq_continue_iff
    {A E : Type} (input : core.result.Result A E) (value : A) :
    core.result.Result.Insts.CoreOpsTry.branch input = .ok (.Continue value) ↔
      input = .Ok value := by
  cases input <;> simp [core.result.Result.Insts.CoreOpsTry.branch]

private theorem lifted_ok_success
    {A E : Type} (source : Result A) (value : A)
    (run : (do
      let current ← source
      ok (core.result.Result.Ok current : core.result.Result A E)) =
        ok (.Ok value)) : source = ok value := by
  cases source <;> simp_all

private theorem translated_request_success_is_exact
    (input : CallerInput)
    (run : authenticate_request input = ok (.Ok ())) :
    ExactRequestAuthentication input := by
  unfold authenticate_request at run
  all_goals repeat (split at run <;> simp_all [ExactRequestAuthentication])

private theorem translated_pool_accounts_success_is_exact
    (input : CallerInput)
    (run : authenticate_pool_accounts input = ok (.Ok ())) :
    ExactPoolAuthentication input := by
  unfold ExactPoolAuthentication
  repeat' apply And.intro
  all_goals by_contra h
  all_goals simp [Bool.ne_false_iff] at h
  all_goals simp [authenticate_pool_accounts, h] at run

private theorem translated_registry_policy_success_is_exact
    (input : CallerInput)
    (run : authenticate_registry_policy_and_accounts input = ok (.Ok ())) :
    ExactRegistryPolicyAndAccounts input := by
  unfold ExactRegistryPolicyAndAccounts
  repeat' apply And.intro
  all_goals by_contra h
  all_goals simp [Bool.ne_false_iff] at h
  all_goals simp [authenticate_registry_policy_and_accounts, h] at run

private theorem translated_registry_certificate_success_is_exact
    (input : CallerInput)
    (run : authenticate_registry_v2_certificate input = ok (.Ok ())) :
    ExactRegistryV2Certificate input := by
  unfold ExactRegistryV2Certificate
  repeat' apply And.intro
  all_goals by_contra h
  all_goals simp [Bool.ne_false_iff] at h
  all_goals simp [authenticate_registry_v2_certificate, h] at run

private theorem translated_entry_certificate_success_is_exact
    (input : CallerInput)
    (run : authenticate_entry_v2_certificate input = ok (.Ok ())) :
    ExactEntryV2Certificate input := by
  unfold ExactEntryV2Certificate
  repeat' apply And.intro
  all_goals by_contra h
  all_goals simp [Bool.ne_false_iff] at h
  all_goals simp [authenticate_entry_v2_certificate, h] at run

private theorem translated_entry_active_success_is_exact
    (input : CallerInput)
    (run : authenticate_entry_active input = ok (.Ok ())) :
    ExactEntryActive input := by
  unfold ExactEntryActive
  repeat' apply And.intro
  all_goals by_contra h
  all_goals simp [Bool.ne_false_iff, not_or] at h
  all_goals simp [authenticate_entry_active, h] at run

private theorem translated_registry_success_is_exact
    (input : CallerInput)
    (run : authenticate_registry input = ok (.Ok ())) :
    ExactRegistryAuthentication input := by
  unfold authenticate_registry at run
  simp_all only [Bind.bind, Aeneas.Std.bind, bind_tc_ok, bind_tc_fail,
    bind_tc_div, Aeneas.Std.Result.ok.injEq]
  generalize policyRun :
    authenticate_registry_policy_and_accounts input = policyResult at run
  cases policyResult with
  | fail error => simp [policyRun] at run
  | div => simp [policyRun] at run
  | ok policyResult =>
      cases policyResult with
      | Err error =>
          simp [policyRun, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at run
      | Ok unit =>
          cases unit
          generalize registryRun :
            authenticate_registry_v2_certificate input = registryResult at run
          cases registryResult with
          | fail error => simp [policyRun, registryRun,
              core.result.Result.Insts.CoreOpsTry.branch] at run
          | div => simp [policyRun, registryRun,
              core.result.Result.Insts.CoreOpsTry.branch] at run
          | ok registryResult =>
              cases registryResult with
              | Err error =>
                  simp [policyRun, registryRun,
                    core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                    core.convert.FromSame.from] at run
              | Ok unit =>
                  cases unit
                  generalize entryRun :
                    authenticate_entry_v2_certificate input = entryResult at run
                  cases entryResult with
                  | fail error => simp [policyRun, registryRun, entryRun,
                      core.result.Result.Insts.CoreOpsTry.branch] at run
                  | div => simp [policyRun, registryRun, entryRun,
                      core.result.Result.Insts.CoreOpsTry.branch] at run
                  | ok entryResult =>
                      cases entryResult with
                      | Err error =>
                          simp [policyRun, registryRun, entryRun,
                            core.result.Result.Insts.CoreOpsTry.branch,
                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                            core.convert.FromSame.from] at run
                      | Ok unit =>
                          cases unit
                          generalize activeRun :
                            authenticate_entry_active input = activeResult at run
                          cases activeResult with
                          | fail error => simp [policyRun, registryRun, entryRun,
                              activeRun,
                              core.result.Result.Insts.CoreOpsTry.branch] at run
                          | div => simp [policyRun, registryRun, entryRun,
                              activeRun,
                              core.result.Result.Insts.CoreOpsTry.branch] at run
                          | ok activeResult =>
                              cases activeResult with
                              | Err error =>
                                  simp [policyRun, registryRun, entryRun,
                                    activeRun,
                                    core.result.Result.Insts.CoreOpsTry.branch,
                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                    core.convert.FromSame.from] at run
                              | Ok unit =>
                                  cases unit
                                  exact ⟨
                                    translated_registry_policy_success_is_exact input policyRun,
                                    translated_registry_certificate_success_is_exact input registryRun,
                                    translated_entry_certificate_success_is_exact input entryRun,
                                    translated_entry_active_success_is_exact input activeRun⟩

private theorem translated_selected_verifier_success_is_exact
    (input : CallerInput)
    (run : authenticate_selected_verifier input = ok (.Ok ())) :
    ExactSelectedVerifierAuthentication input := by
  unfold authenticate_selected_verifier at run
  all_goals repeat (split at run <;>
    simp_all [ExactSelectedVerifierAuthentication])

private theorem translated_distinct_accounts_success_is_exact
    (input : CallerInput)
    (run : authenticate_distinct_cpi_accounts input = ok (.Ok ())) :
    ExactDistinctCpiAccounts input := by
  unfold ExactDistinctCpiAccounts
  repeat' apply And.intro
  all_goals by_contra h
  all_goals simp [authenticate_distinct_cpi_accounts, h] at run

theorem translated_authentication_success_is_exact
    (input : CallerInput)
    (run : authenticate_accounts_and_release input = ok (.Ok ())) :
    ExactReleaseAuthentication input := by
  unfold authenticate_accounts_and_release at run
  simp_all only [Bind.bind, Aeneas.Std.bind, bind_tc_ok, bind_tc_fail,
    bind_tc_div, Aeneas.Std.Result.ok.injEq]
  generalize requestRun : authenticate_request input = requestResult at run
  cases requestResult with
  | fail error => simp [requestRun] at run
  | div => simp [requestRun] at run
  | ok requestResult =>
      cases requestResult with
      | Err error => simp [requestRun,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from] at run
      | Ok unit =>
          cases unit
          generalize poolRun : authenticate_pool_accounts input = poolResult at run
          cases poolResult with
          | fail error => simp [requestRun, poolRun,
              core.result.Result.Insts.CoreOpsTry.branch] at run
          | div => simp [requestRun, poolRun,
              core.result.Result.Insts.CoreOpsTry.branch] at run
          | ok poolResult =>
              cases poolResult with
              | Err error => simp [requestRun, poolRun,
                  core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                  core.convert.FromSame.from] at run
              | Ok unit =>
                  cases unit
                  generalize registryRun : authenticate_registry input = registryResult at run
                  cases registryResult with
                  | fail error => simp [requestRun, poolRun, registryRun,
                      core.result.Result.Insts.CoreOpsTry.branch] at run
                  | div => simp [requestRun, poolRun, registryRun,
                      core.result.Result.Insts.CoreOpsTry.branch] at run
                  | ok registryResult =>
                      cases registryResult with
                      | Err error => simp [requestRun, poolRun, registryRun,
                          core.result.Result.Insts.CoreOpsTry.branch,
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                          core.convert.FromSame.from] at run
                      | Ok unit =>
                          cases unit
                          generalize verifierRun : authenticate_selected_verifier input = verifierResult at run
                          cases verifierResult with
                          | fail error => simp [requestRun, poolRun, registryRun,
                              verifierRun, core.result.Result.Insts.CoreOpsTry.branch] at run
                          | div => simp [requestRun, poolRun, registryRun,
                              verifierRun, core.result.Result.Insts.CoreOpsTry.branch] at run
                          | ok verifierResult =>
                              cases verifierResult with
                              | Err error => simp [requestRun, poolRun, registryRun,
                                  verifierRun, core.result.Result.Insts.CoreOpsTry.branch,
                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                  core.convert.FromSame.from] at run
                              | Ok unit =>
                                  cases unit
                                  generalize distinctRun : authenticate_distinct_cpi_accounts input = distinctResult at run
                                  cases distinctResult with
                                  | fail error => simp [requestRun, poolRun, registryRun,
                                      verifierRun, distinctRun,
                                      core.result.Result.Insts.CoreOpsTry.branch] at run
                                  | div => simp [requestRun, poolRun, registryRun,
                                      verifierRun, distinctRun,
                                      core.result.Result.Insts.CoreOpsTry.branch] at run
                                  | ok distinctResult =>
                                      cases distinctResult with
                                      | Err error => simp [requestRun, poolRun, registryRun,
                                          verifierRun, distinctRun,
                                          core.result.Result.Insts.CoreOpsTry.branch,
                                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                          core.convert.FromSame.from] at run
                                      | Ok unit =>
                                          cases unit
                                          exact ⟨
                                            translated_request_success_is_exact input requestRun,
                                            translated_pool_accounts_success_is_exact input poolRun,
                                            translated_registry_success_is_exact input registryRun,
                                            translated_selected_verifier_success_is_exact input verifierRun,
                                            translated_distinct_accounts_success_is_exact input distinctRun⟩

theorem translated_result_success_is_exact
    (input : CallerInput) (result : ReturnedResult)
    (run : authenticate_result input = ok (.Ok result)) :
    ExactResultBinding input result := by
  cases verifierCpi : input.runtime.verifier_cpi_succeeded with
  | false => simp [authenticate_result, verifierCpi] at run
  | true =>
      have programEq : input.verifier_return.program =
          input.release.verifier_program := by
        by_contra h
        simp [authenticate_result, verifierCpi, h] at run
      have lengthEq : input.verifier_return.encoded_len = ASR8_BYTES := by
        by_contra h
        simp [authenticate_result, verifierCpi, programEq, h] at run
      cases canonicalEq : input.verifier_return.canonical with
      | false =>
          simp [authenticate_result, verifierCpi, programEq, lengthEq,
            canonicalEq] at run
      | true =>
          generalize decodedEq : input.verifier_return.decoded = decoded at run
          cases decoded with
          | none =>
              simp [authenticate_result, verifierCpi, programEq, lengthEq,
                canonicalEq, decodedEq] at run
          | some returned =>
              have kindEq : returned.transition_kind =
                  input.request.payment_kind := by
                by_contra h
                cases returnedKind : returned.transition_kind <;>
                  cases requestKind : input.request.payment_kind <;>
                  try simp [returnedKind, requestKind] at h <;>
                  simp [authenticate_result, verifierCpi, programEq, lengthEq,
                    canonicalEq, decodedEq, returnedKind, requestKind,
                    PaymentKind.read_discriminant,
                    PaymentKind.Insts.CoreCmpPartialEqPaymentKind.eq,
                    core.cmp.PartialEq.ne.trait_default,
                    core.cmp.PartialEq.ne.default] at run h
              have masterEq : returned.master_account =
                  input.master.account.key := by
                by_contra h
                simp [authenticate_result, verifierCpi, programEq, lengthEq,
                  canonicalEq, decodedEq, kindEq,
                  PaymentKind.Insts.CoreCmpPartialEqPaymentKind.eq,
                  core.cmp.PartialEq.ne.trait_default,
                  core.cmp.PartialEq.ne.default, h] at run
              have laneEq : returned.selected_lane_account =
                  input.lane.account.key := by
                by_contra h
                simp [authenticate_result, verifierCpi, programEq, lengthEq,
                  canonicalEq, decodedEq, kindEq, masterEq,
                  PaymentKind.Insts.CoreCmpPartialEqPaymentKind.eq,
                  core.cmp.PartialEq.ne.trait_default,
                  core.cmp.PartialEq.ne.default, h] at run
              have outputEq : returned.output_lane =
                  input.request.output_lane := by
                by_contra h
                simp [authenticate_result, verifierCpi, programEq, lengthEq,
                  canonicalEq, decodedEq, kindEq, masterEq, laneEq,
                  PaymentKind.Insts.CoreCmpPartialEqPaymentKind.eq,
                  core.cmp.PartialEq.ne.trait_default,
                  core.cmp.PartialEq.ne.default, h] at run
              have nullifierEq : returned.nullifier =
                  input.request.nullifier := by
                by_contra h
                simp [authenticate_result, verifierCpi, programEq, lengthEq,
                  canonicalEq, decodedEq, kindEq, masterEq, laneEq, outputEq,
                  PaymentKind.Insts.CoreCmpPartialEqPaymentKind.eq,
                  core.cmp.PartialEq.ne.trait_default,
                  core.cmp.PartialEq.ne.default, h] at run
              have nextEq :
                  U64.checked_add input.lane.next_pair_index 1#u64 =
                    some returned.next_pair_index := by
                generalize nextOptionEq :
                  U64.checked_add input.lane.next_pair_index 1#u64 = nextOption
                cases nextOption with
                | none =>
                    simp [authenticate_result, verifierCpi, programEq, lengthEq,
                      canonicalEq, decodedEq, kindEq, masterEq, laneEq,
                      outputEq, nullifierEq, nextOptionEq, lift, Bind.bind,
                      Aeneas.Std.bind,
                      PaymentKind.Insts.CoreCmpPartialEqPaymentKind.eq,
                      core.cmp.PartialEq.ne.trait_default,
                      core.cmp.PartialEq.ne.default,
                      core.option.Option.Insts.CoreCmpPartialEqOption.eq] at run
                | some next =>
                    have nextValueEq : next = returned.next_pair_index := by
                      by_contra h
                      simp [authenticate_result, verifierCpi, programEq,
                        lengthEq, canonicalEq, decodedEq, kindEq, masterEq,
                        laneEq, outputEq, nullifierEq, nextOptionEq, h, lift,
                        Bind.bind, Aeneas.Std.bind,
                        PaymentKind.Insts.CoreCmpPartialEqPaymentKind.eq,
                        core.cmp.PartialEq.ne.trait_default,
                        core.cmp.PartialEq.ne.default,
                        core.option.Option.Insts.CoreCmpPartialEqOption.eq] at run
                    simpa [nextOptionEq, nextValueEq]
              cases frontierCanonical : returned.next_frontier_canonical with
              | false =>
                  simp [authenticate_result, verifierCpi, programEq, lengthEq,
                    canonicalEq, decodedEq, kindEq, masterEq, laneEq, outputEq,
                    nullifierEq, nextEq, frontierCanonical, lift, Bind.bind,
                    Aeneas.Std.bind,
                    PaymentKind.Insts.CoreCmpPartialEqPaymentKind.eq,
                    core.cmp.PartialEq.ne.trait_default,
                    core.cmp.PartialEq.ne.default,
                    core.option.Option.Insts.CoreCmpPartialEqOption.eq] at run
              | true =>
                  have returnedEq : returned = result := by
                    simpa [authenticate_result, verifierCpi, programEq,
                      lengthEq, canonicalEq, decodedEq, kindEq, masterEq,
                      laneEq, outputEq, nullifierEq, nextEq,
                      frontierCanonical, lift, Bind.bind, Aeneas.Std.bind,
                      PaymentKind.Insts.CoreCmpPartialEqPaymentKind.eq,
                      core.cmp.PartialEq.ne.trait_default,
                      core.cmp.PartialEq.ne.default,
                      core.option.Option.Insts.CoreCmpPartialEqOption.eq]
                      using run
                  subst returned
                  exact ⟨verifierCpi, programEq, lengthEq, canonicalEq,
                    decodedEq, kindEq, masterEq, laneEq, outputEq,
                    nullifierEq, nextEq, frontierCanonical⟩

theorem translated_marker_success_is_exact
    (input : CallerInput) (marker : MarkerImage)
    (run : exact_marker input = ok (.Ok marker)) :
    ExactMarkerBinding input marker := by
  unfold exact_marker at run
  repeat' (split at run <;> simp_all [ExactMarkerBinding])

theorem translated_prepare_success_is_exact
    (input : CallerInput) (prepared : PreparedTerminal)
    (run : prepare_terminal input = ok (.Ok prepared)) :
    ExactPreparedTerminal input prepared := by
  unfold prepare_terminal at run
  generalize authRun : authenticate_accounts_and_release input = authOuter at run
  cases authOuter with
  | fail error => simp [authRun] at run
  | div => simp [authRun] at run
  | ok authInner =>
      cases authInner with
      | Err error => simp [authRun,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from] at run
      | Ok unit =>
          cases unit
          simp [core.result.Result.Insts.CoreOpsTry.branch] at run
          generalize markerRun : exact_marker input = markerOuter at run
          cases markerOuter with
          | fail error => simp [authRun, markerRun,
              core.result.Result.Insts.CoreOpsTry.branch] at run
          | div => simp [authRun, markerRun,
              core.result.Result.Insts.CoreOpsTry.branch] at run
          | ok markerInner =>
              cases markerInner with
              | Err error => simp [authRun, markerRun,
                  core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                  core.convert.FromSame.from] at run
              | Ok marker =>
                  simp [core.result.Result.Insts.CoreOpsTry.branch] at run
                  generalize resultRun : authenticate_result input = resultOuter at run
                  cases resultOuter with
                  | fail error => simp [authRun, markerRun, resultRun,
                      core.result.Result.Insts.CoreOpsTry.branch] at run
                  | div => simp [authRun, markerRun, resultRun,
                      core.result.Result.Insts.CoreOpsTry.branch] at run
                  | ok resultInner =>
                      cases resultInner with
                      | Err error => simp [authRun, markerRun, resultRun,
                          core.result.Result.Insts.CoreOpsTry.branch,
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                          core.convert.FromSame.from] at run
                      | Ok result =>
                          simp [core.result.Result.Insts.CoreOpsTry.branch] at run
                          generalize historyRun :
                            select_history_route input result.next_pair_index = historyOuter at run
                          cases historyOuter with
                          | fail error => simp [authRun, markerRun, resultRun,
                              historyRun, core.result.Result.Insts.CoreOpsTry.branch] at run
                          | div => simp [authRun, markerRun, resultRun,
                              historyRun, core.result.Result.Insts.CoreOpsTry.branch] at run
                          | ok historyInner =>
                              cases historyInner with
                              | Err error => simp [authRun, markerRun, resultRun,
                                  historyRun,
                                  core.result.Result.Insts.CoreOpsTry.branch,
                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                  core.convert.FromSame.from] at run
                              | Ok history =>
                                  simp [core.result.Result.Insts.CoreOpsTry.branch] at run
                                  have preparedEq : prepared = {
                                      marker := marker
                                      result := result
                                      history := {
                                        history with
                                        first_sequence := result.next_pair_index
                                        root := result.next_root
                                      }
                                    } := by simpa using run.symm
                                  subst prepared
                                  exact ⟨
                                    translated_authentication_success_is_exact input authRun,
                                    translated_result_success_is_exact input result resultRun,
                                    translated_marker_success_is_exact input marker markerRun,
                                    rfl,
                                    rfl⟩

theorem translated_finalize_success_is_exact
    (input : CallerInput) (base : PoolImages)
    (prepared : PreparedTerminal) (accepted : AcceptedExecution)
    (preparedExact : ExactPreparedTerminal input prepared)
    (run : finalize_prepared_terminal input base prepared = ok accepted) :
    ExactFinalizeBinding input base prepared accepted := by
  cases routeEq : prepared.history.route <;>
    simp [finalize_prepared_terminal, routeEq, lift, ExactFinalizeBinding,
      ExactFinalizedCore, ExactHistoryState, ExactCpiAccounts,
      exact_cpi_accounts,
      ExactPreparedTerminal] at run preparedExact ⊢
  all_goals subst accepted <;> simp_all

theorem translated_withdrawal_apply_success_is_exact
    (input : CallerInput) (before after : PoolImages)
    (run : apply_withdrawal input before = ok (.Ok (), after)) :
    ExactWithdrawalState input before after := by
  cases exactFive : input.tokens.exact_five_accounts with
  | false => simp [apply_withdrawal, exactFive] at run
  | true =>
      cases tokenProgram : input.tokens.token_program_exact with
      | false => simp [apply_withdrawal, exactFive, tokenProgram] at run
      | true =>
          cases mint : input.tokens.mint_exact with
          | false => simp [apply_withdrawal, exactFive, tokenProgram, mint] at run
          | true =>
              cases vaultAuthority : input.tokens.vault_authority_exact with
              | false => simp [apply_withdrawal, exactFive, tokenProgram, mint,
                  vaultAuthority] at run
              | true =>
                  cases destination : input.tokens.destination_exact with
                  | false => simp [apply_withdrawal, exactFive, tokenProgram,
                      mint, vaultAuthority, destination] at run
                  | true =>
                      by_cases destinationZero :
                          input.request.withdrawal_destination = 0#u64
                      · simp [apply_withdrawal, exactFive, tokenProgram, mint,
                          vaultAuthority, destination, destinationZero] at run
                      · cases withdrawalCpi :
                            input.runtime.withdrawal_cpi_succeeded with
                        | false =>
                            simp [apply_withdrawal, exactFive, tokenProgram,
                              mint, vaultAuthority, destination,
                              destinationZero, withdrawalCpi,
                              UScalar.eq_equiv] at run
                        | true =>
                            have vaultDelta :
                                U64.checked_sub input.tokens.vault_before
                                  input.request.withdrawal_amount =
                                    some input.tokens.vault_after := by
                              generalize vaultOptionEq :
                                U64.checked_sub input.tokens.vault_before
                                  input.request.withdrawal_amount = vaultOption
                                  at run
                              cases vaultOption with
                              | none =>
                                  simp [apply_withdrawal, exactFive,
                                    tokenProgram, mint, vaultAuthority,
                                    destination, destinationZero,
                                    withdrawalCpi, vaultOptionEq,
                                    core.cmp.PartialEq.ne.trait_default,
                                    core.cmp.PartialEq.ne.default,
                                    core.option.Option.Insts.CoreCmpPartialEqOption.eq,
                                    lift, UScalar.eq_equiv] at run
                              | some vault =>
                                  by_cases vaultEq :
                                      vault = input.tokens.vault_after
                                  · simpa [vaultOptionEq, vaultEq]
                                  · simp only [UScalar.eq_equiv] at vaultEq
                                    simp [apply_withdrawal, exactFive,
                                      tokenProgram, mint, vaultAuthority,
                                      destination, destinationZero,
                                      withdrawalCpi, vaultOptionEq, vaultEq,
                                      core.cmp.PartialEq.ne.trait_default,
                                      core.cmp.PartialEq.ne.default,
                                      core.option.Option.Insts.CoreCmpPartialEqOption.eq,
                                      lift, UScalar.eq_equiv] at run
                            have destinationDelta :
                                U64.checked_add input.tokens.destination_before
                                  input.request.withdrawal_amount =
                                    some input.tokens.destination_after := by
                              generalize destinationOptionEq :
                                U64.checked_add input.tokens.destination_before
                                  input.request.withdrawal_amount =
                                    destinationOption at run
                              cases destinationOption with
                              | none =>
                                  simp [apply_withdrawal, exactFive,
                                    tokenProgram, mint, vaultAuthority,
                                    destination, destinationZero,
                                    withdrawalCpi, vaultDelta,
                                    destinationOptionEq,
                                    core.cmp.PartialEq.ne.trait_default,
                                    core.cmp.PartialEq.ne.default,
                                    core.option.Option.Insts.CoreCmpPartialEqOption.eq,
                                    lift, UScalar.eq_equiv] at run
                              | some nextDestination =>
                                  by_cases destinationEq :
                                      nextDestination =
                                        input.tokens.destination_after
                                  · simpa [destinationOptionEq, destinationEq]
                                  · simp only [UScalar.eq_equiv] at destinationEq
                                    simp [apply_withdrawal, exactFive,
                                      tokenProgram, mint, vaultAuthority,
                                      destination, destinationZero,
                                      withdrawalCpi, vaultDelta,
                                      destinationOptionEq, destinationEq,
                                      core.cmp.PartialEq.ne.trait_default,
                                      core.cmp.PartialEq.ne.default,
                                      core.option.Option.Insts.CoreCmpPartialEqOption.eq,
                                      lift, UScalar.eq_equiv] at run
                            have afterEq : after = {
                                before with
                                vault_balance := input.tokens.vault_after
                                destination_balance :=
                                  input.tokens.destination_after
                              } := by
                              simpa [apply_withdrawal, exactFive, tokenProgram,
                                mint, vaultAuthority, destination,
                                destinationZero, withdrawalCpi, vaultDelta,
                                destinationDelta,
                                core.cmp.PartialEq.ne.trait_default,
                                core.cmp.PartialEq.ne.default,
                                core.option.Option.Insts.CoreCmpPartialEqOption.eq,
                                lift, UScalar.eq_equiv] using run.symm
                            exact ⟨exactFive, tokenProgram, mint,
                              vaultAuthority, destination, destinationZero,
                              withdrawalCpi, vaultDelta, destinationDelta,
                              afterEq⟩

theorem translated_apply_prepared_success_is_exact
    (input : CallerInput) (before : PoolImages)
    (prepared : PreparedTerminal) (accepted : AcceptedExecution)
    (preparedExact : ExactPreparedTerminal input prepared)
    (run : apply_prepared_terminal input before prepared =
      ok (.Ok accepted)) :
    ExactAcceptedWriteback input before accepted := by
  cases laneBorrow : input.runtime.lane_borrow_succeeded with
  | false => simp [apply_prepared_terminal, laneBorrow] at run
  | true =>
      cases pageBorrow : input.runtime.page_borrow_succeeded with
      | false => simp [apply_prepared_terminal, laneBorrow, pageBorrow] at run
      | true =>
          cases markerBorrow : input.runtime.marker_borrow_succeeded with
          | false => simp [apply_prepared_terminal, laneBorrow, pageBorrow,
              markerBorrow] at run
          | true =>
              cases kindEq : input.request.payment_kind with
              | PrivateTransfer =>
                  have finalizeRun :
                      finalize_prepared_terminal input before prepared =
                        ok accepted := by
                    apply lifted_ok_success
                    simpa [apply_prepared_terminal, laneBorrow, pageBorrow,
                      markerBorrow, kindEq, apply_transfer_prepared] using run
                  have finalized := translated_finalize_success_is_exact input
                    before prepared accepted preparedExact finalizeRun
                  rcases preparedExact with
                    ⟨releaseExact, resultExact, markerExact, _, _⟩
                  rcases finalized with
                    ⟨coreExact, resultEq, markerEq, vaultEq, destinationEq⟩
                  have acceptedResultExact :
                      ExactResultBinding input accepted.certificate.result := by
                    simpa [resultEq] using resultExact
                  have acceptedMarkerExact :
                      ExactMarkerBinding input accepted.certificate.marker := by
                    simpa [markerEq] using markerExact
                  refine ⟨releaseExact, acceptedResultExact,
                    acceptedMarkerExact, coreExact,
                    laneBorrow, pageBorrow, markerBorrow, ?_⟩
                  constructor
                  · intro _
                    exact ⟨vaultEq, destinationEq⟩
                  · intro impossible
                    cases kindEq.symm.trans impossible
              | Withdrawal =>
                  unfold apply_prepared_terminal at run
                  simp [laneBorrow, pageBorrow, markerBorrow, kindEq] at run
                  unfold apply_withdrawal_prepared at run
                  generalize withdrawalRun :
                    apply_withdrawal input before = withdrawalOuter at run
                  cases withdrawalOuter with
                  | fail error => simp [withdrawalRun] at run
                  | div => simp [withdrawalRun] at run
                  | ok withdrawalPair =>
                      rcases withdrawalPair with ⟨withdrawalInner, after⟩
                      cases withdrawalInner with
                      | Err error => simp [withdrawalRun,
                          core.result.Result.Insts.CoreOpsTry.branch,
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                          core.convert.FromSame.from] at run
                      | Ok unit =>
                          cases unit
                          simp [core.result.Result.Insts.CoreOpsTry.branch] at run
                          have withdrawalExact :=
                            translated_withdrawal_apply_success_is_exact input
                              before after withdrawalRun
                          have finalized :=
                            translated_finalize_success_is_exact input after
                              prepared accepted preparedExact
                                (lifted_ok_success _ _ run)
                          rcases preparedExact with
                            ⟨releaseExact, resultExact, markerExact, _, _⟩
                          rcases finalized with
                            ⟨coreAfter, resultEq, markerEq, vaultEq,
                              destinationEq⟩
                          rcases withdrawalExact with
                            ⟨_, _, _, _, _, _, withdrawalCpi, vaultDelta,
                              destinationDelta, afterEq⟩
                          subst after
                          have acceptedResultExact :
                              ExactResultBinding input
                                accepted.certificate.result := by
                            simpa [resultEq] using resultExact
                          have acceptedMarkerExact :
                              ExactMarkerBinding input
                                accepted.certificate.marker := by
                            simpa [markerEq] using markerExact
                          have coreBefore :
                              ExactFinalizedCore input before accepted := by
                            simpa [ExactFinalizedCore, ExactHistoryState]
                              using coreAfter
                          refine ⟨releaseExact, acceptedResultExact,
                            acceptedMarkerExact,
                            coreBefore, laneBorrow, pageBorrow, markerBorrow,
                            ?_⟩
                          constructor
                          · intro impossible
                            cases kindEq.symm.trans impossible
                          · intro _
                            exact ⟨withdrawalCpi, vaultDelta,
                              destinationDelta, vaultEq, destinationEq⟩

theorem translated_rejected_atomic_transaction_is_exact_prestate
    (input : CallerInput) (before : PoolImages) (out : TransactionOutcome)
    (run : execute_atomic_transaction input before = ok out)
    (rejected : out.committed = false) :
    out.state = before ∧ out.certificate = none ∧
      ∃ error, out.error = some error := by
  unfold execute_atomic_transaction at run
  generalize callerRun : execute_terminal_caller input before = callerResult at run
  cases callerResult with
  | fail error => simp [callerRun] at run
  | div => simp [callerRun] at run
  | ok caller =>
      cases caller with
      | Ok accepted => simp [callerRun] at run; subst out; simp at rejected
      | Err error =>
          simp [callerRun] at run
          subst out
          exact ⟨rfl, rfl, error, rfl⟩

theorem translated_accepted_caller_has_exact_writeback
    (input : CallerInput) (before : PoolImages) (accepted : AcceptedExecution)
    (run : execute_terminal_caller input before = ok (.Ok accepted)) :
    ExactAcceptedWriteback input before accepted := by
  unfold execute_terminal_caller at run
  generalize prepareRun : prepare_terminal input = prepareOuter at run
  cases prepareOuter with
  | fail error => simp [prepareRun] at run
  | div => simp [prepareRun] at run
  | ok prepareInner =>
      cases prepareInner with
      | Err error => simp [prepareRun,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from] at run
      | Ok prepared =>
          simp [core.result.Result.Insts.CoreOpsTry.branch] at run
          exact translated_apply_prepared_success_is_exact input before
            prepared accepted
            (translated_prepare_success_is_exact input prepared prepareRun) run

theorem translated_accepted_atomic_transaction_has_exact_writeback
    (input : CallerInput) (before : PoolImages) (out : TransactionOutcome)
    (run : execute_atomic_transaction input before = ok out)
    (accepted : out.committed = true) :
    ∃ caller,
      execute_terminal_caller input before = ok (.Ok caller) ∧
      out.state = caller.state ∧
      out.certificate = some caller.certificate ∧
      out.error = none ∧
      ExactAcceptedWriteback input before caller := by
  unfold execute_atomic_transaction at run
  generalize callerRun : execute_terminal_caller input before = callerResult at run
  cases callerResult with
  | fail error => simp [callerRun] at run
  | div => simp [callerRun] at run
  | ok callerResult =>
      cases callerResult with
      | Err error => simp [callerRun] at run; subst out; simp at accepted
      | Ok caller =>
          simp [callerRun] at run
          subst out
          exact ⟨caller, rfl, rfl, rfl, rfl,
            translated_accepted_caller_has_exact_writeback input before caller
              callerRun⟩

#print axioms translated_authentication_success_is_exact
#print axioms translated_result_success_is_exact
#print axioms translated_marker_success_is_exact
#print axioms translated_prepare_success_is_exact
#print axioms translated_finalize_success_is_exact
#print axioms translated_withdrawal_apply_success_is_exact
#print axioms translated_apply_prepared_success_is_exact
#print axioms translated_rejected_atomic_transaction_is_exact_prestate
#print axioms translated_accepted_caller_has_exact_writeback
#print axioms translated_accepted_atomic_transaction_has_exact_writeback

end V7RegistryV2OneTerminalCallerGenerated
