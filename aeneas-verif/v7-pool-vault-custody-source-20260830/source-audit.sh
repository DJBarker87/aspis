#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(CDPATH= cd -- "$script_dir/../.." && pwd)
vault_source="$repo_root/programs/aspis-pool/src/vault.rs"
pair_source="$repo_root/programs/aspis-pool/src/pair_forest.rs"
processor_source="$repo_root/programs/aspis-pool/src/processor.rs"
deposit_source="$repo_root/programs/aspis-pool/src/deposit.rs"
dispatch_source="$repo_root/programs/aspis-pool/src/pair_forest_dispatch.rs"

git -C "$repo_root" merge-base --is-ancestor \
  f96b4becb87dfc6e2cfab1cb399dc1322ae016e7 HEAD

check_hash() {
  expected=$1
  path=$2
  test "$(shasum -a 256 "$path" | awk '{print $1}')" = "$expected"
}

check_hash d7889cbdec8c3987cfa5aaad3984475e18e390c84712826847de611680d90463 \
  "$vault_source"
check_hash 0b5a2824cb6b9a31971d75dd5bb0fcc224aece6873ac12f54b6a81822275ce0b \
  "$pair_source"
check_hash 3c989ba201b622c01e67edec7cba8b17ba30663b386a4f316e757ff06dad7354 \
  "$processor_source"
check_hash 5635bd40c8bec466f3e90cde5c10abe11817faaa0164f852440110e21ea6ab3c \
  "$deposit_source"
check_hash 08b9b563118e8fd9d0d43d2d36d1824e2e984a96610ed0fcb846835866e9f02e \
  "$dispatch_source"

"$repo_root/aeneas-verif/v7-pool-one-terminal-caller-source-20260828/source-audit.sh"

# Launch is intentionally legacy SPL Token only. Exact 82/165-byte parsing,
# canonical COption tags and owner checks reject Token-2022/extensions rather
# than treating them as compatible legacy layouts.
for needle in \
  'Pubkey::from_str_const("TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA")' \
  'pub const LEGACY_SPL_TOKEN_MINT_ACCOUNT_BYTES: usize = 82;' \
  'pub const LEGACY_SPL_TOKEN_ACCOUNT_BYTES: usize = 165;' \
  'if data.len() != LEGACY_SPL_TOKEN_MINT_ACCOUNT_BYTES' \
  'if data.len() != LEGACY_SPL_TOKEN_ACCOUNT_BYTES' \
  'parse_coption_pubkey(&data[..36])?;' \
  'parse_coption_pubkey(&data[TOKEN_MINT_FREEZE_AUTHORITY_OFFSET..])?;' \
  'account.owner != &LEGACY_SPL_TOKEN_PROGRAM_ID' \
  'identity.token_program != LEGACY_SPL_TOKEN_PROGRAM_ID.to_bytes()' \
  'token_program.key != &LEGACY_SPL_TOKEN_PROGRAM_ID' \
  '!token_program.executable' \
  'require_token_owned_account(mint_account, false)?;' \
  'pool_v1_vault_token_account_address(program_id, pool).0' \
  'pool_v1_vault_authority_address(program_id, pool).0' \
  'destination_account.key != destination' \
  'vault.delegated_amount != 0' \
  'destination_state.is_native' \
  '.checked_sub(amount)' \
  '.checked_add(amount)' \
  'pub(crate) fn validate_exact_deposit_delta_v1(' \
  'pub(crate) fn validate_exact_withdrawal_delta_v1('
do
  rg -F -q "$needle" "$vault_source"
done

# Program-address and executable checks are not enough: the loader owner is
# authenticated against the three supported Solana loader programs.
for needle in \
  'pub(crate) fn require_token_program_account(account: &AccountInfo' \
  'owner == &bpf_loader::id()' \
  'owner == &bpf_loader_upgradeable::id()' \
  'owner == &loader_v4::id()'
do
  rg -F -q "$needle" "$processor_source"
done

# Pin the deposit caller ordering. Every Pool mutable borrow is acquired before
# the token CPI; the exact post-CPI delta is checked before either Pool image is
# written; no fallible operation follows the first Pool write.
deposit_body=$(sed -n \
  '/^pub(crate) fn process_pair_forest_deposit_with_runtime_v1/,/^enum PairForestSpendPageV1/p' \
  "$pair_source")
line_in_deposit() {
  printf '%s\n' "$deposit_body" | rg -n -F -m1 "$1" | cut -d: -f1
}
token_auth_line=$(line_in_deposit 'require_token_program_account(&token_accounts[4])?;')
plan_line=$(line_in_deposit 'let transfer_plan = plan_legacy_deposit_transfer_from_identity_v1(')
borrow_line=$(line_in_deposit 'let mut lane_data = lane_account.try_borrow_mut_data()?;')
cpi_line=$(line_in_deposit 'runtime.invoke(&transfer_plan.instruction, &transfer_infos)?;')
delta_line=$(line_in_deposit 'validate_exact_deposit_delta_v1(token_accounts, &transfer_plan)?;')
write_line=$(line_in_deposit 'lane_data.copy_from_slice(next_lane_image.as_ref());')
test "$token_auth_line" -lt "$plan_line"
test "$plan_line" -lt "$borrow_line"
test "$borrow_line" -lt "$cpi_line"
test "$cpi_line" -lt "$delta_line"
test "$delta_line" -lt "$write_line"
if printf '%s\n' "$deposit_body" | sed -n '/lane_data\.copy_from_slice/,$p' | rg -q '\?;'; then
  echo 'fallible operation appears after first deposit Pool write' >&2
  exit 1
fi

# Hash-pin the operational projection, extraction and transparent Option
# callback used by the generated planner arithmetic.
check_hash 95334962c7285a96aa51aa3380732b6b23963032a9cec0e3bd30ca74c10dec4b \
  "$script_dir/harness/src/lib.rs"
check_hash 1e73d429d0ffbf1f844d338a7b920e4cd9fe9cf1bd43be643f900a8eace6bb6f \
  "$script_dir/extraction/V7PoolVaultCustody.llbc"
check_hash 48eb1e1fcba609a052eb2eaa1ae407d104d490061320ccb6f8d2f757f73a8c37 \
  "$script_dir/generated/V7PoolVaultCustody/FunsExternal.lean"

echo 'V7 Pool vault-custody source/control-flow audit: PASS'
