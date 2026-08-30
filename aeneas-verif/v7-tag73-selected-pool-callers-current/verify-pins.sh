#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo=$(git -C "$script_dir" rev-parse --show-toplevel)

test "$(git -C "$repo" rev-parse 68ac0c73a1f93cc42c81ea04df52cd26d80ec79c^{commit})" = \
  68ac0c73a1f93cc42c81ea04df52cd26d80ec79c

test "$(sha256sum "$repo/crates/aspis-core/src/field.rs" | awk '{print $1}')" = \
  5795495e2fa9ad85e097c2ad96ffc826aaad3c16afc0e0bd00459f9f51068cd8
test "$(sha256sum "$repo/crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs" | awk '{print $1}')" = \
  50062fff8b6afbffad3ddbb8eda09992353a9171c4955151cece26a654c6a6d5
test "$(sha256sum "$repo/crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs" | awk '{print $1}')" = \
  efbc5be87e271419d7b09e1bb6e3a83984d42795bc20067ea039814fb89ffa58
test "$(sha256sum "$repo/crates/aspis-statement/src/state_only_poseidon.rs" | awk '{print $1}')" = \
  4467d15c9d473cbd42caf33f21aa0192bed007b58ccaa4a61cb5691532cab7fe

while read -r expected relative; do
  test "$(sha256sum "$script_dir/${relative#./}" | awk '{print $1}')" = "$expected"
done < "$script_dir/CHECKSUMS.sha256"
jq -e '.has_errors == false' \
  "$script_dir/extraction/V7Tag73SelectedSemanticDirectRoots.llbc" >/dev/null

generated="$script_dir/generated/V7Tag73SelectedSemanticLoopForm/Funs.lean"
grep -Fq 'evaluate_pool_v1_pair_forest_private_transfer_selected_masked_terminal_compiled_tag73_v1' "$generated"
grep -Fq 'evaluate_pool_v1_pair_forest_withdrawal_selected_masked_terminal_compiled_tag73_v1' "$generated"

! grep -REn '(^|[[:space:]])(sorry|admit|native_decide)([[:space:]]|$)' \
  "$script_dir/proof" "$script_dir/generated" --include='*.lean'
! grep -REn '^[[:space:]]*(axiom|opaque)[[:space:]]' \
  "$script_dir/proof/V7SelectedSemanticRootBridge.lean" \
  "$script_dir/generated/V7Tag73SelectedSemanticLoopForm/TypesExternal.lean" \
  "$script_dir/generated/V7Tag73SelectedSemanticLoopForm/FunsExternal.lean"

echo 'V7 selected semantic terminal pins: PASS'
