#!/usr/bin/env bash
set -euo pipefail

root=$(git rev-parse --show-toplevel)
bundle=$root/aeneas-verif/v7-cu-lock-evaluator-source-20260828
formal=$root/AspisFormal/AspisFormal/Pool/V7SelectedEvaluatorSparsitySourceBridge.lean

test "$(git rev-parse cee5947c^{commit})" = \
  cee5947cbd5929a2be96d8f7ec29728afec2d3dd

cd "$root"
shasum -a 256 -c <<'EOF'
fa7977f2be11f4676146b802e687844086f0f33c56857c83514e8b6346f14fea  crates/aspis-core/src/v6_onefold.rs
f9bbac3f9ec734ddde0522c083d37726e5377753e7076d7d8d61a2fb806b3727  crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs
572aa12e2caa6bb48e1cdf7a550a0160c642a393c2810731c059a81389da4342  crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs
bc4d72deed0c4b17cefa5092aa05bbc5587c76123df69bd4b4e1187f46280cf6  crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal_constants.rs
cf8babeac16a1987ed1dbd05454f77cb0f217779c33d6384a986eccf9e5b5231  crates/aspis-statement/Cargo.toml
6b3bc0b45b13a8a359f8c0515c7b5d0a71ff64199dd713df8a81c2faf3e2c774  programs/aspis-verifier/Cargo.toml
25cae3f276bd5831785bdb25e204ce99213934e7fcec3f5a76a5d742a018426b  Cargo.lock
EOF

for file in "$bundle"/extraction/*.llbc; do
  jq -e '.has_errors == false' "$file" >/dev/null
done
shasum -a 256 -c "$bundle/CHECKSUMS.sha256" >/dev/null

grep -Fq 'def v6_onefold.gamma_combine_v6_c1_four_slot_block' \
  "$bundle/generated/V7CuLockGamma/Funs.lean"
grep -Fq 'def pool_v1.pair_forest_semantic_terminal.add_preweighted_shared_selector' \
  "$bundle/generated/V7CuLockRange/Funs.lean"
grep -Fq 'def pool_v1.pair_forest_copy_terminal.constants.ACTIVE_ROW_MASKS' \
  "$bundle/generated/V7CuLockActivePublicOnly/Funs.lean"
grep -Fq '6144#u16, 6144#u16, 6145#u16' \
  "$bundle/generated/V7CuLockActivePublicOnly/Funs.lean"
grep -Fq 'COPY_GROUP_LOCAL_GROUP_OFFSETS' \
  "$bundle/generated/V7CuLockCopyCore/Funs.lean"
grep -Fq '0#usize, 9#usize, 15#usize, 26#usize, 30#usize' \
  "$bundle/generated/V7CuLockCopyCore/Funs.lean"
grep -Fq 'copy_tag_coordinate_dot' \
  "$bundle/generated/V7CuLockCopyCore/Funs.lean"
grep -Fq 'finish_selector_tensor_basis' \
  "$bundle/generated/V7CuLockCopyCore/Funs.lean"

! grep -En '(^|[[:space:]])(sorry|admit|native_decide)([[:space:]]|$)' "$formal"
! grep -En '^[[:space:]]*(axiom|opaque)[[:space:]]' "$formal"

# The activation branch intentionally adds one aggregate release-candidate
# feature around the pinned leaves. Pin that exact selection explicitly; the
# source hashes above continue to pin every evaluator body and table.
for selected in \
  v7-pair-forest-fixed-canonical-exact-once-audit \
  v7-pair-forest-packed-digest-selector-tensor-audit \
  v7-pair-forest-copy-tag-dot-basis-audit \
  v7-pair-forest-copy-finish-dot-basis-audit \
  v7-pair-forest-packed-range-audit \
  v7-pair-forest-active-mask-basis-audit \
  v7-gamma-four-slot-block-audit
do
  sed -n '/^v7-pair-forest-one-tx-candidate = \[/,/^\]/p' \
    programs/aspis-verifier/Cargo.toml | grep -Fq "\"$selected\""
done
echo 'V7 CU-lock source pins verified'
