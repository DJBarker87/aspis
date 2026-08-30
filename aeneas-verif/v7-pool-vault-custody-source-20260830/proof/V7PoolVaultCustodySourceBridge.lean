import V7PoolVaultCustody.Funs

/-!
# Literal Pool vault custody source bridge

The predicates in this file expose the exact legacy SPL Token program,
loader, mint and token-account facts established by successful translated
control flow. Token-2022 is an explicitly rejected owner/program shape.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option linter.constructorNameAsVariable false
set_option linter.unusedSimpArgs false

namespace V7PoolVaultCustodyGenerated

open Aeneas Aeneas.Std Result ControlFlow Error

attribute [local simp] UScalar.eq_equiv

theorem u64_cast_ne_of_ne {x y : U64} (different : x ≠ y) :
    (↑x : Nat) ≠ ↑y := by
  intro castEqual
  exact different ((UScalar.eq_equiv x y).mpr castEqual)

@[simp] theorem value_limit_literal :
    VALUE_LIMIT = 1073741824#u64 := by
  unfold VALUE_LIMIT
  rfl

def ExactSupportedLoader (owner : U64) : Prop :=
  owner = BPF_LOADER_ID ∨
  owner = BPF_UPGRADEABLE_LOADER_ID ∨
  owner = LOADER_V4_ID

def ExactLegacyTokenProgram
    (identityTokenProgram : U64) (program : AccountView) : Prop :=
  identityTokenProgram = LEGACY_TOKEN_PROGRAM_ID ∧
  program.key = LEGACY_TOKEN_PROGRAM_ID ∧
  program.executable = true ∧
  program.signer = false ∧
  program.writable = false ∧
  ExactSupportedLoader program.owner

def ExactLegacyMint (expectedMint : U64) (mint : MintView) : Prop :=
  mint.account.key = expectedMint ∧
  mint.account.owner = LEGACY_TOKEN_PROGRAM_ID ∧
  mint.account.executable = false ∧
  mint.account.signer = false ∧
  mint.account.writable = false ∧
  mint.data_len = LEGACY_MINT_BYTES ∧
  mint.initialized = true ∧
  mint.option_tags_canonical = true

def ExactLegacyTokenAccount
    (account : TokenAccountView) (writable : Bool) : Prop :=
  account.account.owner = LEGACY_TOKEN_PROGRAM_ID ∧
  account.account.executable = false ∧
  account.account.signer = false ∧
  account.account.writable = writable ∧
  account.data_len = LEGACY_TOKEN_ACCOUNT_BYTES ∧
  account.initialized = true ∧
  account.option_tags_canonical = true

theorem translated_token_program_success_is_exact
    (identityTokenProgram : U64) (program : AccountView)
    (run : authenticate_token_program identityTokenProgram program =
      .ok (.Ok ())) :
    ExactLegacyTokenProgram identityTokenProgram program := by
  unfold authenticate_token_program at run
  repeat' first
    | split at run <;> simp_all [supported_loader, ExactSupportedLoader,
        ExactLegacyTokenProgram]

theorem translated_mint_success_is_exact
    (expectedMint : U64) (mint : MintView)
    (run : authenticate_mint expectedMint mint = .ok (.Ok ())) :
    ExactLegacyMint expectedMint mint := by
  unfold authenticate_mint at run
  repeat' first
    | split at run <;> simp_all [ExactLegacyMint]

theorem translated_token_account_success_is_exact
    (account : TokenAccountView) (writable : Bool)
    (run : authenticate_token_account account writable = .ok (.Ok ())) :
    ExactLegacyTokenAccount account writable := by
  unfold authenticate_token_account at run
  repeat' first
    | split at run <;> simp_all [ExactLegacyTokenAccount]

def ExactDepositPlan (input : DepositInput) (plan : DepositPlan) : Prop :=
  input.exact_account_count_and_unique = true ∧
  input.amount ≠ 0#u64 ∧
  ¬ input.amount ≥ 1073741824#u64 ∧
  ExactLegacyTokenProgram input.identity_token_program input.token_program ∧
  ExactLegacyMint input.identity_mint input.mint ∧
  ExactLegacyTokenAccount input.source true ∧
  ExactLegacyTokenAccount input.vault true ∧
  input.source_authority.signer = true ∧
  input.source_authority.writable = false ∧
  input.source_authority.executable = false ∧
  input.source.mint = input.identity_mint ∧
  input.vault.mint = input.identity_mint ∧
  input.source.authority = input.source_authority.key ∧
  input.vault.account.key = input.expected_vault ∧
  input.vault.authority = input.expected_vault_authority ∧
  input.vault.has_delegate = false ∧
  input.vault.is_native = false ∧
  input.vault.delegated_amount = 0#u64 ∧
  input.vault.has_close_authority = false ∧
  U64.checked_sub input.source.amount input.amount = some plan.source_after ∧
  U64.checked_add input.vault.amount input.amount = some plan.vault_after ∧
  plan = {
    instruction := {
      program_id := LEGACY_TOKEN_PROGRAM_ID
      source := input.source.account.key
      mint := input.mint.account.key
      destination := input.vault.account.key
      authority := input.source_authority.key
      amount := input.amount
      decimals := input.mint.decimals
      pda_signed := false
    }
    source_before := input.source.amount
    source_after := plan.source_after
    vault_before := input.vault.amount
    vault_after := plan.vault_after
  }

def ExactWithdrawalPlan
    (input : WithdrawalInput) (plan : WithdrawalPlan) : Prop :=
  input.terminal_prefix_authenticated = true ∧
  input.exact_account_count_and_unique = true ∧
  input.amount ≠ 0#u64 ∧
  ¬ input.amount ≥ 1073741824#u64 ∧
  ExactLegacyTokenProgram input.identity_token_program input.token_program ∧
  ExactLegacyMint input.identity_mint input.mint ∧
  ExactLegacyTokenAccount input.vault true ∧
  ExactLegacyTokenAccount input.destination true ∧
  input.vault_authority.key = input.expected_vault_authority ∧
  input.vault_authority.owner = SYSTEM_PROGRAM_ID ∧
  input.vault_authority.executable = false ∧
  input.vault_authority.signer = false ∧
  input.vault_authority.writable = false ∧
  input.destination.account.key = input.requested_destination ∧
  input.vault.account.key = input.expected_vault ∧
  input.vault.mint = input.identity_mint ∧
  input.destination.mint = input.identity_mint ∧
  input.vault.authority = input.expected_vault_authority ∧
  input.vault.has_delegate = false ∧
  input.vault.is_native = false ∧
  input.vault.delegated_amount = 0#u64 ∧
  input.vault.has_close_authority = false ∧
  input.destination.is_native = false ∧
  U64.checked_sub input.vault.amount input.amount = some plan.vault_after ∧
  U64.checked_add input.destination.amount input.amount =
    some plan.destination_after ∧
  plan = {
    instruction := {
      program_id := LEGACY_TOKEN_PROGRAM_ID
      source := input.vault.account.key
      mint := input.mint.account.key
      destination := input.destination.account.key
      authority := input.vault_authority.key
      amount := input.amount
      decimals := input.mint.decimals
      pda_signed := true
    }
    vault_before := input.vault.amount
    vault_after := plan.vault_after
    destination_before := input.destination.amount
    destination_after := plan.destination_after
  }

theorem translated_deposit_plan_success_is_exact
    (input : DepositInput) (plan : DepositPlan)
    (run : plan_deposit input = .ok (.Ok plan)) :
    ExactDepositPlan input plan := by
  unfold plan_deposit at run
  simp only [value_limit_literal, Bind.bind, Aeneas.Std.bind, lift] at run
  have unique : input.exact_account_count_and_unique = true := by
    by_contra different
    have falseValue := Bool.eq_false_of_not_eq_true different
    simp [falseValue] at run
  simp only [unique, if_pos] at run
  have amountZero : input.amount ≠ 0#u64 := by
    intro zero
    simp [zero] at run
  simp only [amountZero, if_false] at run
  have amountHigh : ¬ input.amount ≥ 1073741824#u64 := by
    intro high
    simp [high] at run
  simp only [amountHigh, if_false] at run
  cases tokenRun :
      authenticate_token_program input.identity_token_program
        input.token_program with
  | fail error => simp [tokenRun] at run
  | div => simp [tokenRun] at run
  | ok tokenResult =>
      cases tokenResult with
      | Err error =>
          simp [tokenRun,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
            at run
      | Ok unit =>
          cases unit
          have tokenExact := translated_token_program_success_is_exact
            input.identity_token_program input.token_program tokenRun
          simp only [tokenRun,
            core.result.Result.Insts.CoreOpsTry.branch, Bind.bind,
            Aeneas.Std.bind] at run
          cases mintRun : authenticate_mint input.identity_mint input.mint with
          | fail error => simp [mintRun] at run
          | div => simp [mintRun] at run
          | ok mintResult =>
              cases mintResult with
              | Err error =>
                  simp [mintRun,
                    core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                    at run
              | Ok unit =>
                  cases unit
                  have mintExact := translated_mint_success_is_exact
                    input.identity_mint input.mint mintRun
                  simp only [mintRun,
                    core.result.Result.Insts.CoreOpsTry.branch, Bind.bind,
                    Aeneas.Std.bind] at run
                  cases sourceRun :
                      authenticate_token_account input.source true with
                  | fail error => simp [sourceRun] at run
                  | div => simp [sourceRun] at run
                  | ok sourceResult =>
                      cases sourceResult with
                      | Err error =>
                          simp [sourceRun,
                            core.result.Result.Insts.CoreOpsTry.branch,
                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                            at run
                      | Ok unit =>
                          cases unit
                          have sourceExact :=
                            translated_token_account_success_is_exact
                              input.source true sourceRun
                          simp only [sourceRun,
                            core.result.Result.Insts.CoreOpsTry.branch,
                            Bind.bind, Aeneas.Std.bind] at run
                          cases vaultRun :
                              authenticate_token_account input.vault true with
                          | fail error => simp [vaultRun] at run
                          | div => simp [vaultRun] at run
                          | ok vaultResult =>
                              cases vaultResult with
                              | Err error =>
                                  simp [vaultRun,
                                    core.result.Result.Insts.CoreOpsTry.branch,
                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                                    at run
                              | Ok unit =>
                                  cases unit
                                  have vaultExact :=
                                    translated_token_account_success_is_exact
                                      input.vault true vaultRun
                                  simp only [vaultRun,
                                    core.result.Result.Insts.CoreOpsTry.branch,
                                    Bind.bind, Aeneas.Std.bind] at run
                                  have signer :
                                      input.source_authority.signer = true := by
                                    by_contra different
                                    have falseValue :=
                                      Bool.eq_false_of_not_eq_true different
                                    simp [falseValue] at run
                                  simp only [signer, if_pos] at run
                                  have writableNot :
                                      input.source_authority.writable ≠ true := by
                                    intro writable
                                    simp [writable] at run
                                  have writable :
                                      input.source_authority.writable = false :=
                                    Bool.eq_false_of_not_eq_true writableNot
                                  simp only [writable, Bool.false_eq_true,
                                    if_false] at run
                                  have executableNot :
                                      input.source_authority.executable ≠ true := by
                                    intro executable
                                    simp [executable] at run
                                  have executable :
                                      input.source_authority.executable = false :=
                                    Bool.eq_false_of_not_eq_true executableNot
                                  simp only [executable, Bool.false_eq_true,
                                    if_false] at run
                                  have sourceMint :
                                      input.source.mint = input.identity_mint := by
                                    by_contra different
                                    have castDifferent :=
                                      u64_cast_ne_of_ne different
                                    simp [different, castDifferent] at run
                                  simp [sourceMint] at run
                                  have vaultMint :
                                      input.vault.mint = input.identity_mint := by
                                    by_contra different
                                    have castDifferent :=
                                      u64_cast_ne_of_ne different
                                    simp [different, castDifferent] at run
                                  simp [vaultMint] at run
                                  have sourceAuthority :
                                      input.source.authority =
                                        input.source_authority.key := by
                                    by_contra different
                                    have castDifferent :=
                                      u64_cast_ne_of_ne different
                                    simp [different, castDifferent] at run
                                  simp [sourceAuthority] at run
                                  have vaultKey :
                                      input.vault.account.key =
                                        input.expected_vault := by
                                    by_contra different
                                    have castDifferent :=
                                      u64_cast_ne_of_ne different
                                    simp [different, castDifferent] at run
                                  simp [vaultKey] at run
                                  have vaultAuthority :
                                      input.vault.authority =
                                        input.expected_vault_authority := by
                                    by_contra different
                                    have castDifferent :=
                                      u64_cast_ne_of_ne different
                                    simp [different, castDifferent] at run
                                  simp [vaultAuthority] at run
                                  have delegateNot :
                                      input.vault.has_delegate ≠ true := by
                                    intro delegate
                                    simp [delegate] at run
                                  have delegate :
                                      input.vault.has_delegate = false :=
                                    Bool.eq_false_of_not_eq_true delegateNot
                                  simp only [delegate, Bool.false_eq_true,
                                    if_false] at run
                                  have nativeNot :
                                      input.vault.is_native ≠ true := by
                                    intro native
                                    simp [native] at run
                                  have native : input.vault.is_native = false :=
                                    Bool.eq_false_of_not_eq_true nativeNot
                                  simp only [native, Bool.false_eq_true,
                                    if_false] at run
                                  have delegated :
                                      input.vault.delegated_amount = 0#u64 := by
                                    by_contra different
                                    have castDifferent :=
                                      u64_cast_ne_of_ne different
                                    have castDifferentZero :
                                        (↑input.vault.delegated_amount : Nat) ≠
                                          0 := by
                                      simpa using castDifferent
                                    simp [castDifferentZero] at run
                                  simp [delegated] at run
                                  have closeAuthorityNot :
                                      input.vault.has_close_authority ≠ true := by
                                    intro closeAuthority
                                    simp [closeAuthority] at run
                                  have closeAuthority :
                                      input.vault.has_close_authority = false :=
                                    Bool.eq_false_of_not_eq_true closeAuthorityNot
                                  simp only [closeAuthority,
                                    Bool.false_eq_true, if_false] at run
                                  cases sourceDelta :
                                      U64.checked_sub input.source.amount
                                        input.amount with
                                  | none => simp [sourceDelta,
                                      core.option.Option.ok_or,
                                      core.result.Result.Insts.CoreOpsTry.branch,
                                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                                      at run
                                  | some sourceAfter =>
                                      simp only [sourceDelta,
                                        core.option.Option.ok_or,
                                        core.result.Result.Insts.CoreOpsTry.branch,
                                        Bind.bind, Aeneas.Std.bind] at run
                                      cases vaultDelta :
                                          U64.checked_add input.vault.amount
                                            input.amount with
                                      | none => simp [vaultDelta,
                                          core.option.Option.ok_or,
                                          core.result.Result.Insts.CoreOpsTry.branch,
                                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                                          at run
                                      | some vaultAfter =>
                                          simp only [vaultDelta,
                                            core.option.Option.ok_or,
                                            core.result.Result.Insts.CoreOpsTry.branch,
                                            Bind.bind, Aeneas.Std.bind] at run
                                          have planEq : plan = {
                                              instruction := {
                                                program_id :=
                                                  LEGACY_TOKEN_PROGRAM_ID
                                                source := input.source.account.key
                                                mint := input.mint.account.key
                                                destination :=
                                                  input.expected_vault
                                                authority :=
                                                  input.source_authority.key
                                                amount := input.amount
                                                decimals := input.mint.decimals
                                                pda_signed := false
                                              }
                                              source_before := input.source.amount
                                              source_after := sourceAfter
                                              vault_before := input.vault.amount
                                              vault_after := vaultAfter
                                            } := by simpa using run.symm
                                          subst plan
                                          simp [ExactDepositPlan, unique,
                                            amountZero, amountHigh, tokenExact,
                                            mintExact, sourceExact, vaultExact,
                                            signer, writable, executable,
                                            sourceMint, vaultMint,
                                            sourceAuthority, vaultKey,
                                            vaultAuthority, delegate, native,
                                            delegated, closeAuthority,
                                            sourceDelta, vaultDelta]

theorem translated_withdrawal_plan_success_is_exact
    (input : WithdrawalInput) (plan : WithdrawalPlan)
    (run : plan_withdrawal input = .ok (.Ok plan)) :
    ExactWithdrawalPlan input plan := by
  unfold plan_withdrawal at run
  simp only [value_limit_literal, Bind.bind, Aeneas.Std.bind, lift] at run
  have prefixAuth : input.terminal_prefix_authenticated = true := by
    by_contra different
    have falseValue := Bool.eq_false_of_not_eq_true different
    simp [falseValue] at run
  simp only [prefixAuth, if_pos] at run
  have unique : input.exact_account_count_and_unique = true := by
    by_contra different
    have falseValue := Bool.eq_false_of_not_eq_true different
    simp [falseValue] at run
  simp only [unique, if_pos] at run
  have amountZero : input.amount ≠ 0#u64 := by
    intro zero
    simp [zero] at run
  simp only [amountZero, if_false] at run
  have amountHigh : ¬ input.amount ≥ 1073741824#u64 := by
    intro high
    simp [high] at run
  simp only [amountHigh, if_false] at run
  cases tokenRun :
      authenticate_token_program input.identity_token_program
        input.token_program with
  | fail error => simp [tokenRun] at run
  | div => simp [tokenRun] at run
  | ok tokenResult =>
      cases tokenResult with
      | Err error =>
          simp [tokenRun,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
            at run
      | Ok unit =>
          cases unit
          have tokenExact := translated_token_program_success_is_exact
            input.identity_token_program input.token_program tokenRun
          simp only [tokenRun,
            core.result.Result.Insts.CoreOpsTry.branch, Bind.bind,
            Aeneas.Std.bind] at run
          cases mintRun : authenticate_mint input.identity_mint input.mint with
          | fail error => simp [mintRun] at run
          | div => simp [mintRun] at run
          | ok mintResult =>
              cases mintResult with
              | Err error =>
                  simp [mintRun,
                    core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                    at run
              | Ok unit =>
                  cases unit
                  have mintExact := translated_mint_success_is_exact
                    input.identity_mint input.mint mintRun
                  simp only [mintRun,
                    core.result.Result.Insts.CoreOpsTry.branch, Bind.bind,
                    Aeneas.Std.bind] at run
                  cases vaultRun :
                      authenticate_token_account input.vault true with
                  | fail error => simp [vaultRun] at run
                  | div => simp [vaultRun] at run
                  | ok vaultResult =>
                      cases vaultResult with
                      | Err error =>
                          simp [vaultRun,
                            core.result.Result.Insts.CoreOpsTry.branch,
                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                            at run
                      | Ok unit =>
                          cases unit
                          have vaultExact :=
                            translated_token_account_success_is_exact
                              input.vault true vaultRun
                          simp only [vaultRun,
                            core.result.Result.Insts.CoreOpsTry.branch,
                            Bind.bind, Aeneas.Std.bind] at run
                          cases destinationRun :
                              authenticate_token_account input.destination true with
                          | fail error => simp [destinationRun] at run
                          | div => simp [destinationRun] at run
                          | ok destinationResult =>
                              cases destinationResult with
                              | Err error =>
                                  simp [destinationRun,
                                    core.result.Result.Insts.CoreOpsTry.branch,
                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                                    at run
                              | Ok unit =>
                                  cases unit
                                  have destinationExact :=
                                    translated_token_account_success_is_exact
                                      input.destination true destinationRun
                                  simp only [destinationRun,
                                    core.result.Result.Insts.CoreOpsTry.branch,
                                    Bind.bind, Aeneas.Std.bind] at run
                                  have authorityKey :
                                      input.vault_authority.key =
                                        input.expected_vault_authority := by
                                    by_contra different
                                    have castDifferent :=
                                      u64_cast_ne_of_ne different
                                    simp [different, castDifferent] at run
                                  simp [authorityKey] at run
                                  have authorityOwner :
                                      input.vault_authority.owner =
                                        SYSTEM_PROGRAM_ID := by
                                    by_contra different
                                    have castDifferent :=
                                      u64_cast_ne_of_ne different
                                    simp [different, castDifferent] at run
                                  simp [authorityOwner] at run
                                  have authorityExecutableNot :
                                      input.vault_authority.executable ≠ true := by
                                    intro executable
                                    simp [executable] at run
                                  have authorityExecutable :
                                      input.vault_authority.executable = false :=
                                    Bool.eq_false_of_not_eq_true
                                      authorityExecutableNot
                                  simp only [authorityExecutable,
                                    Bool.false_eq_true, if_false] at run
                                  have authoritySignerNot :
                                      input.vault_authority.signer ≠ true := by
                                    intro signer
                                    simp [signer] at run
                                  have authoritySigner :
                                      input.vault_authority.signer = false :=
                                    Bool.eq_false_of_not_eq_true authoritySignerNot
                                  simp only [authoritySigner,
                                    Bool.false_eq_true, if_false] at run
                                  have authorityWritableNot :
                                      input.vault_authority.writable ≠ true := by
                                    intro writable
                                    simp [writable] at run
                                  have authorityWritable :
                                      input.vault_authority.writable = false :=
                                    Bool.eq_false_of_not_eq_true
                                      authorityWritableNot
                                  simp only [authorityWritable,
                                    Bool.false_eq_true, if_false] at run
                                  have destinationKey :
                                      input.destination.account.key =
                                        input.requested_destination := by
                                    by_contra different
                                    have castDifferent :=
                                      u64_cast_ne_of_ne different
                                    simp [different, castDifferent] at run
                                  simp [destinationKey] at run
                                  have vaultKey :
                                      input.vault.account.key =
                                        input.expected_vault := by
                                    by_contra different
                                    have castDifferent :=
                                      u64_cast_ne_of_ne different
                                    simp [different, castDifferent] at run
                                  simp [vaultKey] at run
                                  have vaultMint :
                                      input.vault.mint = input.identity_mint := by
                                    by_contra different
                                    have castDifferent :=
                                      u64_cast_ne_of_ne different
                                    simp [different, castDifferent] at run
                                  simp [vaultMint] at run
                                  have destinationMint :
                                      input.destination.mint =
                                        input.identity_mint := by
                                    by_contra different
                                    have castDifferent :=
                                      u64_cast_ne_of_ne different
                                    simp [different, castDifferent] at run
                                  simp [destinationMint] at run
                                  have vaultAuthority :
                                      input.vault.authority =
                                        input.expected_vault_authority := by
                                    by_contra different
                                    have castDifferent :=
                                      u64_cast_ne_of_ne different
                                    simp [different, castDifferent] at run
                                  simp [vaultAuthority] at run
                                  have delegateNot :
                                      input.vault.has_delegate ≠ true := by
                                    intro delegate
                                    simp [delegate] at run
                                  have delegate :
                                      input.vault.has_delegate = false :=
                                    Bool.eq_false_of_not_eq_true delegateNot
                                  simp only [delegate, Bool.false_eq_true,
                                    if_false] at run
                                  have nativeNot :
                                      input.vault.is_native ≠ true := by
                                    intro native
                                    simp [native] at run
                                  have native : input.vault.is_native = false :=
                                    Bool.eq_false_of_not_eq_true nativeNot
                                  simp only [native, Bool.false_eq_true,
                                    if_false] at run
                                  have delegated :
                                      input.vault.delegated_amount = 0#u64 := by
                                    by_contra different
                                    have castDifferent :=
                                      u64_cast_ne_of_ne different
                                    have castDifferentZero :
                                        (↑input.vault.delegated_amount : Nat) ≠
                                          0 := by
                                      simpa using castDifferent
                                    simp [castDifferentZero] at run
                                  simp [delegated] at run
                                  have closeAuthorityNot :
                                      input.vault.has_close_authority ≠ true := by
                                    intro closeAuthority
                                    simp [closeAuthority] at run
                                  have closeAuthority :
                                      input.vault.has_close_authority = false :=
                                    Bool.eq_false_of_not_eq_true closeAuthorityNot
                                  simp only [closeAuthority,
                                    Bool.false_eq_true, if_false] at run
                                  have destinationNativeNot :
                                      input.destination.is_native ≠ true := by
                                    intro destinationNative
                                    simp [destinationNative] at run
                                  have destinationNative :
                                      input.destination.is_native = false :=
                                    Bool.eq_false_of_not_eq_true
                                      destinationNativeNot
                                  simp only [destinationNative,
                                    Bool.false_eq_true, if_false] at run
                                  cases vaultDelta :
                                      U64.checked_sub input.vault.amount
                                        input.amount with
                                  | none => simp [vaultDelta,
                                      core.option.Option.ok_or,
                                      core.result.Result.Insts.CoreOpsTry.branch,
                                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                                      at run
                                  | some vaultAfter =>
                                      simp only [vaultDelta,
                                        core.option.Option.ok_or,
                                        core.result.Result.Insts.CoreOpsTry.branch,
                                        Bind.bind, Aeneas.Std.bind] at run
                                      cases destinationDelta :
                                          U64.checked_add input.destination.amount
                                            input.amount with
                                      | none => simp [destinationDelta,
                                          core.option.Option.ok_or,
                                          core.result.Result.Insts.CoreOpsTry.branch,
                                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                                          at run
                                      | some destinationAfter =>
                                          simp only [destinationDelta,
                                            core.option.Option.ok_or,
                                            core.result.Result.Insts.CoreOpsTry.branch,
                                            Bind.bind, Aeneas.Std.bind] at run
                                          have planEq : plan = {
                                              instruction := {
                                                program_id :=
                                                  LEGACY_TOKEN_PROGRAM_ID
                                                source := input.expected_vault
                                                mint := input.mint.account.key
                                                destination :=
                                                  input.requested_destination
                                                authority :=
                                                  input.expected_vault_authority
                                                amount := input.amount
                                                decimals := input.mint.decimals
                                                pda_signed := true
                                              }
                                              vault_before := input.vault.amount
                                              vault_after := vaultAfter
                                              destination_before :=
                                                input.destination.amount
                                              destination_after := destinationAfter
                                            } := by simpa using run.symm
                                          subst plan
                                          simp [ExactWithdrawalPlan, prefixAuth,
                                            unique, amountZero, amountHigh,
                                            tokenExact, mintExact, vaultExact,
                                            destinationExact, authorityKey,
                                            authorityOwner, authorityExecutable,
                                            authoritySigner, authorityWritable,
                                            destinationKey, vaultKey, vaultMint,
                                            destinationMint, vaultAuthority,
                                            delegate, native, delegated,
                                            closeAuthority, destinationNative,
                                            vaultDelta, destinationDelta]

#print axioms translated_token_program_success_is_exact
#print axioms translated_mint_success_is_exact
#print axioms translated_token_account_success_is_exact
#print axioms translated_deposit_plan_success_is_exact
#print axioms translated_withdrawal_plan_success_is_exact

end V7PoolVaultCustodyGenerated
