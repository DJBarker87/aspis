#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(git -C "$script_dir" rev-parse --show-toplevel)
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

git -C "$repo_root" merge-base --is-ancestor \
  b76fee418079aaa244cbca4b3ffb26d8a4808192 HEAD

check_hash() {
  expected=$1
  path=$2
  test "$(shasum -a 256 "$path" | awk '{print $1}')" = "$expected"
}

check_hash 7f58b1bb8464195bdd94d849283e5d093a4d40289be93e2dc43a9ffe5d57c0cf "$pair_source"
check_hash 08b9b563118e8fd9d0d43d2d36d1824e2e984a96610ed0fcb846835866e9f02e "$dispatch_source"
check_hash ef68bfef98e6885167119ff6cb947f116177c0648f3aec4941893ac774079017 "$registry_source"
check_hash 7d754900fecb4d6ba4511029a3617e90f91c697fc415fabd8aa4b2c0c519107a "$history_source"
check_hash 274398d59536f19fa25dd11269945893fe02a03e5668655244b7be2f32e26c6f "$nullifier_source"
check_hash d7889cbdec8c3987cfa5aaad3984475e18e390c84712826847de611680d90463 "$vault_source"
check_hash ce73a104777a6d1f7b0086853e6d504f67f1d5ba6f0fb8a89cfc52e5d1eeb4d3 "$processor_source"
check_hash af12779379545b6253ab4919ae5ed2447c49d6cbdaef9f41888cfd034fb2e529 "$verifier_source"
check_hash d10c75884cde37792647736ed87d326b8f889ea9a17a363f14efc98b801b7175 "$accounts_source"
check_hash 820710b2284ea967bb4b9a6d2ceb6cb171ac185b01df816db99db6ea78e629a3 "$terminal_source"

# Pin the literal production caller and its successful control-flow order.
for needle in \
  'let request = decode_pair_forest_terminal_request_boxed_v1(instruction_data)?;' \
  'validate_pair_forest_request_accounts_v1(' \
  'let layout = plan_pair_forest_spend_layout_v1(program_id, accounts, &lane, withdrawal)?;' \
  'let planned_marker = plan_nullifier_marker_consumption_v1(program_id, marker, marker_payload)?;' \
  'Some(plan_legacy_withdrawal_transfer_from_identity_v1(' \
  'let authenticated = verify(' \
  'validate_pair_forest_terminal_result_direct_v1(' \
  'let (_next_lane, next_lane_image) = encode_next_pair_forest_lane_boxed_v1(&lane, result)?;' \
  'let mut lane_data = lane_account.try_borrow_mut_data()?;' \
  'runtime.invoke_signed(&plan.instruction, &infos, &[seeds])?;' \
  'lane_data.copy_from_slice(next_lane_image.as_ref());' \
  'marker_data.copy_from_slice(&planned_marker.encoded_marker());' \
  'set_return_data(result_bytes.as_ref());'
do
  rg -F -q "$needle" "$pair_source"
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
caller_tail=$(sed -n '1361,1402p' "$pair_source")
test "$(printf '%s\n' "$caller_tail" | rg -c 'try_borrow_mut_data\(\)\?')" = 3
test "$(printf '%s\n' "$caller_tail" | rg -c 'lane_data\.copy_from_slice')" = 1
if printf '%s\n' "$caller_tail" | sed -n '/lane_data\.copy_from_slice/,$p' | rg -q '\?;'; then
  echo 'fallible operation appears after first Pool write' >&2
  exit 1
fi

echo 'V7 Pool one-terminal production source/control-flow audit: PASS'
