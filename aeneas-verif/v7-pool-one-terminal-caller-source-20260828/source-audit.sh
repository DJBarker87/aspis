#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(CDPATH= cd -- "$script_dir/../.." && pwd)
pair_source="$repo_root/programs/aspis-pool/src/pair_forest.rs"
dispatch_source="$repo_root/programs/aspis-pool/src/pair_forest_dispatch.rs"
registry_source="$repo_root/programs/aspis-pool/src/registry.rs"
history_source="$repo_root/programs/aspis-pool/src/history.rs"
nullifier_source="$repo_root/programs/aspis-pool/src/nullifier.rs"
vault_source="$repo_root/programs/aspis-pool/src/vault.rs"
processor_source="$repo_root/programs/aspis-pool/src/processor.rs"
verifier_source="$repo_root/programs/aspis-verifier/src/v7_pair_forest_dispatch.rs"
accounts_source="$repo_root/crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs"
terminal_source="$repo_root/crates/aspis-statement/src/pool_v1/pair_terminal.rs"
pool_manifest="$repo_root/programs/aspis-pool/Cargo.toml"
verifier_manifest="$repo_root/programs/aspis-verifier/Cargo.toml"

if git -C "$repo_root" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  git -C "$repo_root" merge-base --is-ancestor \
    da77d5f5a22681200cceec8e90fc69ac2cc81ad8 HEAD
fi

check_hash() {
  expected=$1
  path=$2
  test "$(shasum -a 256 "$path" | awk '{print $1}')" = "$expected"
}

check_hash 0b5a2824cb6b9a31971d75dd5bb0fcc224aece6873ac12f54b6a81822275ce0b "$pair_source"
check_hash 08b9b563118e8fd9d0d43d2d36d1824e2e984a96610ed0fcb846835866e9f02e "$dispatch_source"
check_hash ef68bfef98e6885167119ff6cb947f116177c0648f3aec4941893ac774079017 "$registry_source"
check_hash 7d754900fecb4d6ba4511029a3617e90f91c697fc415fabd8aa4b2c0c519107a "$history_source"
check_hash 274398d59536f19fa25dd11269945893fe02a03e5668655244b7be2f32e26c6f "$nullifier_source"
check_hash d7889cbdec8c3987cfa5aaad3984475e18e390c84712826847de611680d90463 "$vault_source"
check_hash 3c989ba201b622c01e67edec7cba8b17ba30663b386a4f316e757ff06dad7354 "$processor_source"
check_hash 276c3eb0d157408e2f132e69001e77c32f306baa86450f1e8fab9cdcb8fbadbb "$verifier_source"
check_hash d10c75884cde37792647736ed87d326b8f889ea9a17a363f14efc98b801b7175 "$accounts_source"
check_hash 820710b2284ea967bb4b9a6d2ceb6cb171ac185b01df816db99db6ea78e629a3 "$terminal_source"
check_hash faf0bffabea687d358bd67ba510afc9038f97313a184564532c99cdea565b9c5 "$pool_manifest"
check_hash 6b3bc0b45b13a8a359f8c0515c7b5d0a71ff64199dd713df8a81c2faf3e2c774 "$verifier_manifest"

# The checkpoint snapshot decode is deliberately split into its own SBF
# frame. Pin both the non-inlining boundary and the exact one-call flow so a
# later edit cannot silently put the eight depth-20 lane decodes back beside
# the planner's output images. This is a stack-only refactor: the same strict
# decoder, fixed lane order, and boxed array feed the unchanged pure planner.
rg -U -q '#\[inline\(never\)\]\nfn decode_checkpoint_lanes_box_v1\(' "$pair_source"
checkpoint_lane_helper=$(sed -n \
  '/^fn decode_checkpoint_lanes_box_v1(/,/^}/p' "$pair_source")
test "$(printf '%s\n' "$checkpoint_lane_helper" | rg -c 'decode_lane_account\(')" = 1
test "$(printf '%s\n' "$checkpoint_lane_helper" | rg -c 'for lane in 0\.\.POOL_V1_PAIR_FOREST_LANE_COUNT')" = 1
printf '%s\n' "$checkpoint_lane_helper" | rg -q '\.into_boxed_slice\(\)'
checkpoint_plan_body=$(sed -n \
  '/^pub fn plan_pair_forest_checkpoint_accounts_v1(/,/^}/p' "$pair_source")
test "$(printf '%s\n' "$checkpoint_plan_body" | rg -c 'decode_checkpoint_lanes_box_v1\(')" = 1
if printf '%s\n' "$checkpoint_plan_body" | rg -q 'decode_lane_account\('; then
  echo 'checkpoint lane decode moved back into the oversized planner frame' >&2
  exit 1
fi
printf '%s\n' "$checkpoint_plan_body" | rg -q \
  'plan_pool_v1_pair_forest_checkpoint_v1\(&master, &lane_states, global_root\)'

# Pin the aggregate release-candidate selections which decide the active
# cfg-gated caller/result path and the selected verifier implementation.
for selected in \
  pair-forest-source-result-invariant-audit \
  pair-forest-verifier-lane-invariant-audit \
  pair-forest-direct-result-audit \
  pair-forest-history-page-invariant-audit
do
  sed -n '/^v7-pair-forest-one-tx-candidate = \[/,/^\]/p' "$pool_manifest" |
    grep -Fq "\"$selected\""
done
for selected in \
  v7-pair-forest-fixed-canonical-exact-once-audit \
  v7-pair-forest-lane-invariant-audit \
  v7-pair-forest-semantic-factor-audit \
  v7-pair-forest-active-mask-basis-audit \
  v7-gamma-four-slot-block-audit
do
  sed -n '/^v7-pair-forest-one-tx-candidate = \[/,/^\]/p' "$verifier_manifest" |
    grep -Fq "\"$selected\""
done

# Pin the literal production caller and its successful control-flow order.
for needle in \
  'let request = decode_terminal_request_box_v1(instruction_data)?;' \
  'validate_pair_forest_request_accounts_v1(' \
  'let layout = plan_pair_forest_spend_layout_v1(program_id, accounts, &lane, withdrawal)?;' \
  'let payer = &accounts[layout.payer_index];' \
  'let system_program_account = &accounts[layout.system_program_index];' \
  'require_payer_and_system_program(payer, system_program_account)?;' \
  'let planned_marker = plan_nullifier_marker_consumption_v1(program_id, marker, marker_payload)?;' \
  'require_token_program_account(&token_accounts[4])?;' \
  'Some(plan_legacy_withdrawal_transfer_from_identity_v1(' \
  'let ready_marker = create_nullifier_marker_if_needed_v1(' \
  'let authenticated = verify(' \
  'validate_pair_forest_terminal_result_direct_v1(' \
  'let next_lane_image = next_lane_image_box_v1(&lane, result)?;' \
  'let mut lane_data = lane_account.try_borrow_mut_data()?;' \
  'runtime.invoke_signed(&plan.instruction, &infos, &[seeds])?;' \
  'lane_data.copy_from_slice(next_lane_image.as_ref());' \
  'marker_data.copy_from_slice(&ready_marker.encoded_marker());' \
  'set_return_data(result_bytes.as_ref());'
do
  rg -F -q "$needle" "$pair_source"
done

# Pin the marker reservation helper which closes the fresh-account lifecycle:
# canonical seeds, System create/transfer/allocate/assign, exact post-CPI
# replan and the live Rent exemption all precede verifier execution.
for needle in \
  'pub(crate) fn create_nullifier_marker_if_needed_v1' \
  'POOL_V1_NULLIFIER_MARKER_SEED,' \
  'pool.as_ref(),' \
  'create_or_allocate_pda_with_rent(' \
  'POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES,' \
  'let ready = plan_nullifier_marker_consumption_v1(program_id, marker_account, planned.marker())?;' \
  'ready.preparation() != NullifierMarkerPreparationV1::PopulateProgramOwnedZeroed' \
  'ready.encoded_marker() != planned.encoded_marker()' \
  'rent.is_exempt('
do
  rg -F -q "$needle" "$processor_source"
done
rg -F -q 'let rent = Rent::get()?;' "$processor_source"
for needle in \
  'system_instruction::create_account(' \
  'system_instruction::transfer(payer.key, account.key, deficit)' \
  'system_instruction::allocate(account.key, exact_bytes as u64)' \
  'system_instruction::assign(account.key, owner)'
do
  rg -F -q "$needle" "$processor_source"
done

# Exact six-account verifier CPI and fail-closed return-data identity.
rg -q 'let \[registry, entry\] = registry_accounts' "$dispatch_source"
test "$(rg -c 'AccountMeta::new_readonly\(\*(proof|master|checkpoint|lane|registry|entry)\.key, false\)' "$dispatch_source")" -ge 6
rg -q 'runtime\.clear_return_data\(\);' "$dispatch_source"
rg -q 'runtime\.invoke\(&instruction, &infos\)\?;' "$dispatch_source"
rg -q 'decode_pool_v1_pair_forest_terminal_result_v1\(&returned_data\)' "$dispatch_source"
rg -q 'exact_bytes: returned_data\.into_boxed_slice\(\)' "$dispatch_source"

# The verifier independently authenticates the immutable release and the same
# six account identities. No caller-chosen Pool/registry root is sufficient.
rg -q '^fn authenticate_invariant_release_registry_v1\(' "$verifier_source"
rg -q 'let \[proof_account, master_account, checkpoint_account, lane_account, registry_account, entry_account\] =' "$verifier_source"
rg -q 'PAIR_FOREST_INVARIANT_POOL_PROGRAM_AUDIT_V1' "$verifier_source"
rg -q 'PAIR_FOREST_INVARIANT_REGISTRY_PROGRAM_AUDIT_V1' "$verifier_source"
rg -q 'PAIR_FOREST_INVARIANT_POLICY_BINDING_AUDIT_V1' "$verifier_source"

# All mutable Pool borrows occur before withdrawal CPI or the first Pool write;
# after the first write there is no fallible call in the pinned caller body.
caller_tail=$(sed -n \
  '/^pub(crate) fn process_pair_forest_terminal_with_verifier_v1/,/^pub(crate) fn process_pair_forest_terminal_v1/p' \
  "$pair_source")
line_of() {
  printf '%s\n' "$caller_tail" | rg -n -F -m1 "$1" | cut -d: -f1
}
withdrawal_plan_line=$(line_of 'let withdrawal_plan =')
reserve_line=$(line_of 'let ready_marker = create_nullifier_marker_if_needed_v1(')
verifier_line=$(line_of 'let authenticated = verify(')
lane_write_line=$(line_of 'lane_data.copy_from_slice(next_lane_image.as_ref());')
marker_write_line=$(line_of 'marker_data.copy_from_slice(&ready_marker.encoded_marker());')
test "$withdrawal_plan_line" -lt "$reserve_line"
test "$reserve_line" -lt "$verifier_line"
test "$verifier_line" -lt "$lane_write_line"
test "$lane_write_line" -lt "$marker_write_line"
test "$(printf '%s\n' "$caller_tail" | rg -c 'try_borrow_mut_data\(\)\?')" = 3
test "$(printf '%s\n' "$caller_tail" | rg -c 'lane_data\.copy_from_slice')" = 1
if printf '%s\n' "$caller_tail" | sed -n '/lane_data\.copy_from_slice/,$p' | rg -q '\?;'; then
  echo 'fallible operation appears after first Pool write' >&2
  exit 1
fi

echo 'V7 Pool one-terminal production source/control-flow audit: PASS'
