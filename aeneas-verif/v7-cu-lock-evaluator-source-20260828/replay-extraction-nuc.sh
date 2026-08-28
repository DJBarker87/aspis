#!/usr/bin/env bash
set -euo pipefail

source_root=${1:?usage: replay-extraction-nuc.sh SOURCE_ROOT /tmp/v7-cu-lock-output}
output_root=${2:?usage: replay-extraction-nuc.sh SOURCE_ROOT /tmp/v7-cu-lock-output}

case "$output_root" in
  /tmp/v7-cu-lock-*) ;;
  *) echo "output must be an explicit /tmp/v7-cu-lock-* path" >&2; exit 2 ;;
esac

charon=/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/bin/charon
aeneas=/home/dombarker/project-offloads/aeneas-d860-v6-linux/bin/aeneas

test "$(git -C "$source_root" rev-parse HEAD)" = \
  cee5947cbd5929a2be96d8f7ec29728afec2d3dd

cd "$source_root"
sha256sum -c <<'EOF'
fa7977f2be11f4676146b802e687844086f0f33c56857c83514e8b6346f14fea  crates/aspis-core/src/v6_onefold.rs
f9bbac3f9ec734ddde0522c083d37726e5377753e7076d7d8d61a2fb806b3727  crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs
572aa12e2caa6bb48e1cdf7a550a0160c642a393c2810731c059a81389da4342  crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs
bc4d72deed0c4b17cefa5092aa05bbc5587c76123df69bd4b4e1187f46280cf6  crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal_constants.rs
cf8babeac16a1987ed1dbd05454f77cb0f217779c33d6384a986eccf9e5b5231  crates/aspis-statement/Cargo.toml
8ce12e7b1e43f490fdf852f4cbdd3d2937e145148d6683e4f73a111acd44f4c0  programs/aspis-verifier/Cargo.toml
25cae3f276bd5831785bdb25e204ce99213934e7fcec3f5a76a5d742a018426b  Cargo.lock
EOF

printf '%s  %s\n' \
  b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c "$charon" \
  c8dbc1f076bcbacf3493be46f7be669051c60b206ca00a6f0abf6df07b7ce50b "$aeneas" |
  sha256sum -c

rm -rf "$output_root"
mkdir -p "$output_root/extraction" "$output_root/generated"
export CARGO_BUILD_JOBS=1
export CARGO_TARGET_DIR="$output_root/cargo-target"

statement_features=pool-v1-pair-forest-packed-digest-selector-tensor-audit,pool-v1-pair-forest-binary-copy-weights-audit,pool-v1-pair-forest-endpoint-selector-cache-audit,pool-v1-pair-forest-semantic-factor-audit,pool-v1-pair-forest-pattern-window-audit,pool-v1-pair-forest-copy-tag-dot-basis-audit,pool-v1-pair-forest-copy-finish-dot-basis-audit,pool-v1-pair-forest-packed-range-audit,pool-v1-pair-forest-active-mask-basis-audit

"$charon" cargo --preset aeneas --mir built --sysroot default \
  --start-from aspis_core::v6_onefold::gamma_combine_v6_c1_four_slot_block \
  --dest-file "$output_root/extraction/V7CuLockGamma.llbc" -- \
  --package aspis-core --lib --features v7-gamma-four-slot-block-audit

"$charon" cargo --preset aeneas --mir built --sysroot default \
  --start-from aspis_statement::pool_v1::pair_forest_semantic_terminal::add_preweighted_shared_selector \
  --dest-file "$output_root/extraction/V7CuLockRange.llbc" -- \
  --package aspis-statement --lib --features "$statement_features"

"$charon" cargo --preset aeneas --mir built --sysroot default \
  --start-from aspis_statement::pool_v1::pair_forest_copy_terminal::pool_v1_pair_forest_copy_active_at_point_compiled_v1 \
  --dest-file "$output_root/extraction/V7CuLockActivePublicOnly.llbc" -- \
  --package aspis-statement --lib --features "$statement_features"

"$charon" cargo --preset aeneas --mir built --sysroot default \
  --start-from aspis_statement::pool_v1::pair_forest_copy_terminal::Selectors::active_mask_basis \
  --start-from aspis_statement::pool_v1::pair_forest_copy_terminal::copy_tag_coordinate_dot \
  --start-from aspis_statement::pool_v1::pair_forest_copy_terminal::finish_selector_tensor_basis \
  --dest-file "$output_root/extraction/V7CuLockCopyCore.llbc" -- \
  --package aspis-statement --lib --features "$statement_features"

# These two mutating roots are retained as clean LLBC.  Current Aeneas fails
# its borrow join on them; see README.md for the exact remaining boundary.
"$charon" cargo --preset aeneas --mir built --sysroot default \
  --start-from aspis_statement::pool_v1::pair_forest_semantic_terminal::add_digest_binding_packed_selector_tensor \
  --start-from aspis_statement::pool_v1::pair_forest_copy_terminal::accumulate_endpoint_selector_tensor_basis \
  --dest-file "$output_root/extraction/V7CuLockLeaves.llbc" -- \
  --package aspis-statement --lib --features "$statement_features"

for file in "$output_root"/extraction/*.llbc; do
  jq -e '.has_errors == false' "$file" >/dev/null
done

translate() {
  local stem=$1 namespace=$2
  "$aeneas" -sequential -no-progress-bar -abort-on-error -backend lean \
    -namespace "$namespace" -dest "$output_root/generated" -subdir "$stem" \
    -split-files -emit-json "$output_root/extraction/$stem.llbc"
}

translate V7CuLockGamma V7CuLockGammaGenerated
translate V7CuLockRange V7CuLockRangeGenerated
translate V7CuLockActivePublicOnly V7CuLockActivePublicOnlyGenerated
translate V7CuLockCopyCore V7CuLockCopyCoreGenerated

sha256sum "$output_root"/extraction/*.llbc \
  "$output_root"/generated/*/*.lean > "$output_root/CHECKSUMS.sha256"
