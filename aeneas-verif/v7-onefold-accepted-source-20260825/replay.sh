#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(git -C "$script_dir" rev-parse --show-toplevel)
deployed_commit=1589706d38a5e8ca705fbf7aaed2c82cf8595510
deployed_tree=d43572d059a48a871933be4ab7067e7ded2fab28

: "${CHARON_BIN:?set CHARON_BIN to the pinned Charon 0.1.223 binary}"
: "${AENEAS_BIN:?set AENEAS_BIN to the patched pinned Aeneas binary}"
: "${AENEAS_LEAN_BACKEND:?set AENEAS_LEAN_BACKEND to Aeneas backends/lean}"

test -x "$CHARON_BIN"
test -x "$AENEAS_BIN"
test -d "$AENEAS_LEAN_BACKEND"
command -v jq >/dev/null
command -v sha256sum >/dev/null
command -v patch >/dev/null
command -v rg >/dev/null
command -v git >/dev/null
command -v tar >/dev/null
command -v lake >/dev/null

test "$(sha256sum "$CHARON_BIN" | awk '{print $1}')" = \
  776344b8bfb7f3ec4ba78d5007ae79c1ef3f4ed654de05f04266693759a37375
test "$(sha256sum "$AENEAS_BIN" | awk '{print $1}')" = \
  c824ad52b6fecc69abd41ed3206781132f6c84850de2ee6bb5bbb0ed5ad29926

cd "$repo_root"
test "$(git rev-parse "$deployed_commit^{commit}")" = "$deployed_commit"
test "$(git rev-parse "$deployed_commit^{tree}")" = "$deployed_tree"
sha256sum -c "$script_dir/MANIFEST.sha256"
sha256sum -c "$script_dir/GENERATED-PROOF.sha256"

if rg -n '\b(sorry|admit)\b' \
    "$script_dir/generated" \
    "$script_dir/production-root/generated-exact" \
    "$script_dir/production-root/proof" \
    "$script_dir/parser/generated-exact" \
    "$script_dir/proof" \
    "$script_dir/parser/proof" \
    --glob '*.lean'; then
  echo 'forbidden Lean placeholder found in checked bundle source' >&2
  exit 1
fi

replay_base=${TMPDIR:-/tmp}
replay_base=${replay_base%/}
replay_tmp=$(mktemp -d "$replay_base/aspis-v7-source-replay.XXXXXX")
lean_tmp=$(mktemp -d "$AENEAS_LEAN_BACKEND/aspis-v7-source-replay.XXXXXX")
cleanup() {
  case "$replay_tmp" in
    "$replay_base"/aspis-v7-source-replay.*) rm -rf -- "$replay_tmp" ;;
    *) echo "refusing unsafe cleanup target: $replay_tmp" >&2 ;;
  esac
  case "$lean_tmp" in
    "$AENEAS_LEAN_BACKEND"/aspis-v7-source-replay.*) rm -rf -- "$lean_tmp" ;;
    *) echo "refusing unsafe cleanup target: $lean_tmp" >&2 ;;
  esac
}
trap cleanup EXIT

source_tree="$replay_tmp/source"
mkdir -p "$source_tree"
git archive "$deployed_commit" | tar -x -C "$source_tree"

(
  cd "$source_tree"
  sha256sum -c "$script_dir/DEPLOYED-SOURCE.sha256"
)

# Keep local replay bounded. Charon invokes Cargo; Lean/Lake otherwise use the
# host's full hardware concurrency and can create an avoidable RAM spike.
export CARGO_BUILD_JOBS=1
export CARGO_TARGET_DIR="$replay_tmp/charon-target"
export LEAN_NUM_THREADS=1

normalized_llbc_sha() {
  jq -cS '
    .translated.options.dest_file = null |
    .translated.options.dest_dir = null |
    .translated.item_names |= sort_by(.key | tojson) |
    .translated.short_names |= sort_by(.key | tojson) |
    .translated.assoc_item_names |= sort_by(.key | tojson)
  ' "$1" | sha256sum | awk '{print $1}'
}

compare_translation_metadata() {
  fresh=$1
  archived=$2
  normalized=$3
  jq -e '.aeneas_version == "d860ac47-dirty"' "$fresh" >/dev/null
  jq '.aeneas_version = "d860ac47-dirty"' "$fresh" > "$normalized"
  cmp "$normalized" "$archived"
}

extract_production_or_diagnostic_root() {
  start_from=$1
  destination=$2
  (
    cd "$source_tree"
    "$CHARON_BIN" cargo \
      --preset aeneas \
      --mir built \
      --sysroot default \
      --start-from "$start_from" \
      --include aspis_core::field::M31 \
      --include aspis_core::field::CM31 \
      --include aspis_core::field::QM31 \
      --opaque aspis_core::field \
      --opaque aspis_core::v7_onefold::V7CompactOneFoldWire::parse_deferred_canonicality \
      --opaque aspis_core::v6_transcript::verify_v7_compact_transcript_and_relation_prepared \
      --opaque aspis_statement::atomic_state_only_terminal::atomic_state_only_selected_masked_terminal_value_compiled_v3 \
      --opaque aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings \
      --opaque aspis_core::v6_onefold::prepare_v6_onefold_coordinates \
      --opaque aspis_core::v6_onefold::fold_v6_onefold_queries \
      --dest-file "$destination" \
      -- --package aspis-verifier --lib --no-default-features \
        --features v7-production-tag73
  )
}

production_llbc="$replay_tmp/V7ProductionRoot.llbc"
extract_production_or_diagnostic_root \
  crate::v7_verifier::verify_v7_read_only_with_statement_digest \
  "$production_llbc"
production_sha=$(normalized_llbc_sha "$production_llbc")
echo "production normalized LLBC SHA-256: $production_sha"
test "$production_sha" = \
  46e15b05151445109ce5bb3dced20242c9aac0000f086a6282e2e01d77c88763

production_generated="$replay_tmp/production-generated"
"$AENEAS_BIN" -sequential -no-progress-bar -abort-on-error -backend lean \
  -namespace V7ProductionRootGenerated \
  -dest "$production_generated" \
  -subdir V7ProductionRoot -split-files -emit-json \
  "$production_llbc"
patch --silent -d "$production_generated" -p1 < \
  "$script_dir/production-root/aeneas-lean-printer-precedence.patch"
cmp "$production_generated/V7ProductionRoot/Types.lean" \
  "$script_dir/production-root/generated-exact/V7ProductionRoot/Types.lean"
cmp "$production_generated/V7ProductionRoot/Funs.lean" \
  "$script_dir/production-root/generated-exact/V7ProductionRoot/Funs.lean"
cmp "$production_generated/V7ProductionRoot/TypesExternal_Template.lean" \
  "$script_dir/production-root/generated-exact/V7ProductionRoot/TypesExternal.lean"
cmp "$production_generated/V7ProductionRoot/FunsExternal_Template.lean" \
  "$script_dir/production-root/generated-exact/V7ProductionRoot/FunsExternal.lean"
compare_translation_metadata \
  "$production_generated/translation.json" \
  "$script_dir/production-root/generated-exact/translation.json" \
  "$replay_tmp/production-translation-normalized.json"

cp -R "$script_dir/production-root/generated-exact/V7ProductionRoot" "$lean_tmp/"
cp "$script_dir/production-root/proof/V7ProductionRootSourceBridge.lean" "$lean_tmp/"
cp -R "$script_dir/parser/generated-exact/V7DeferredParser" "$lean_tmp/"
cp "$script_dir/parser/proof/V7DeferredParserSourceBridge.lean" "$lean_tmp/"

cd "$AENEAS_LEAN_BACKEND"
export LEAN_PATH="$AENEAS_LEAN_BACKEND:$lean_tmp"
for module in TypesExternal Types FunsExternal Funs; do
  lake env lean -j1 -o "$lean_tmp/V7ProductionRoot/$module.olean" \
    "$lean_tmp/V7ProductionRoot/$module.lean"
done
lake env lean -j1 "$lean_tmp/V7ProductionRootSourceBridge.lean"

for module in Types FunsExternal Funs; do
  lake env lean -j1 -o "$lean_tmp/V7DeferredParser/$module.olean" \
    "$lean_tmp/V7DeferredParser/$module.lean"
done
lake env lean -j1 "$lean_tmp/V7DeferredParserSourceBridge.lean"

echo 'V7 exact deployed-root accepted-source replay: PASS (no source-overlay equivalence boundary)'
