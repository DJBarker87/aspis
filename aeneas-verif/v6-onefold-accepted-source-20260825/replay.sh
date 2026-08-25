#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(git -C "$script_dir" rev-parse --show-toplevel)

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
command -v rustup >/dev/null
command -v lake >/dev/null

charon_sha=$(sha256sum "$CHARON_BIN" | awk '{print $1}')
aeneas_sha=$(sha256sum "$AENEAS_BIN" | awk '{print $1}')
test "$charon_sha" = b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c
case "$aeneas_sha" in
  83a221f4c4cd2041e5ba942c945f9b0f2732031c6938b71cb3cc17a9de1d42ce)
    expected_aeneas_version=d860ac47-dirty
    ;;
  c8dbc1f076bcbacf3493be46f7be669051c60b206ca00a6f0abf6df07b7ce50b)
    # The hermetic Linux build has no .git directory, so the upstream version
    # probe emits "unknown".  The executable itself is pinned above.
    expected_aeneas_version=unknown
    ;;
  *)
    echo "unpinned Aeneas binary SHA-256: $aeneas_sha" >&2
    exit 1
    ;;
esac

cd "$repo_root"
sha256sum -c "$script_dir/MANIFEST.sha256"

if rg -n '\b(sorry|admit)\b' \
    "$script_dir/generated" \
    "$script_dir/parser/generated-exact" \
    "$script_dir/proof" \
    "$script_dir/parser/proof" \
    --glob '*.lean'; then
  echo 'forbidden Lean placeholder found' >&2
  exit 1
fi

replay_tmp=$(mktemp -d "${TMPDIR:-/tmp}/aspis-v6-source-replay.XXXXXX")
lean_tmp=$(mktemp -d "$AENEAS_LEAN_BACKEND/aspis-v6-source-replay.XXXXXX")
cleanup() {
  case "$replay_tmp" in
    "${TMPDIR:-/tmp}"/aspis-v6-source-replay.*) rm -rf -- "$replay_tmp" ;;
    *) echo "refusing unsafe cleanup target: $replay_tmp" >&2 ;;
  esac
  case "$lean_tmp" in
    "$AENEAS_LEAN_BACKEND"/aspis-v6-source-replay.*) rm -rf -- "$lean_tmp" ;;
    *) echo "refusing unsafe cleanup target: $lean_tmp" >&2 ;;
  esac
}
trap cleanup EXIT

# Charon uses its pinned nightly.  Never mix those dependency artifacts with
# the repository's ordinary stable-toolchain target directory.  A caller may
# provide an already isolated cache while diagnosing a replay; the release
# invocation leaves this unset and therefore builds in the disposable tree.
export CARGO_TARGET_DIR="${CHARON_TARGET_DIR:-$replay_tmp/charon-target}"

"$CHARON_BIN" cargo \
  --preset aeneas \
  --mir built \
  --sysroot default \
  --start-from crate::v6_verifier::verify_v6_read_only_with_statement_digest_and_schedule \
  --include aspis_core::field::M31 \
  --include aspis_core::field::CM31 \
  --include aspis_core::field::QM31 \
  --opaque aspis_core::field \
  --opaque aspis_core::v6_onefold::parse_v6_onefold_wire_deferred \
  --opaque aspis_core::v6_transcript::verify_v6_transcript_and_relation_prepared \
  --opaque aspis_statement::atomic_state_only_terminal::atomic_state_only_selected_masked_terminal_value_compiled_v3 \
  --opaque aspis_core::v6_onefold::verify_and_gamma_combine_v6_binary_openings_prepared \
  --opaque aspis_core::v6_onefold::prepare_v6_onefold_coordinates \
  --opaque aspis_core::v6_onefold::fold_v6_onefold_queries \
  --dest-file "$replay_tmp/V6AcceptedKernel.llbc" \
  -- --package aspis-verifier --lib --no-default-features --features v6-production-tag72

"$CHARON_BIN" cargo \
  --preset aeneas \
  --sysroot default \
  --start-from crate::v6_onefold::parse_v6_onefold_wire_deferred \
  --include aspis_core::field::M31 \
  --include aspis_core::field::CM31 \
  --include aspis_core::field::QM31 \
  --opaque aspis_core::field \
  --dest-file "$replay_tmp/V6DeferredParser.llbc" \
  -- --package aspis-core --lib

normalized_llbc_sha() {
  # Charon serializes these three Rust hash maps as arrays of key/value pairs.
  # Their order is process-random, while their contents and all executable IR
  # are stable.  Canonicalize only those metadata maps plus destination paths.
  jq -cS '
    .translated.options.dest_file = null |
    .translated.options.dest_dir = null |
    .translated.item_names |= sort_by(.key | tojson) |
    .translated.short_names |= sort_by(.key | tojson) |
    .translated.assoc_item_names |= sort_by(.key | tojson)
  ' "$1" |
    sha256sum | awk '{print $1}'
}

compare_translation_metadata() {
  fresh=$1
  archived=$2
  normalized=$3
  jq -e --arg expected "$expected_aeneas_version" \
    '.aeneas_version == $expected' "$fresh" >/dev/null
  # The Darwin archive records the dirty patched commit identity.  Normalize
  # only this already-checked field for the hermetic Linux binary; every other
  # byte of the translation manifest must still match.
  jq '.aeneas_version = "d860ac47-dirty"' "$fresh" > "$normalized"
  cmp "$normalized" "$archived"
}

accepted_llbc_sha=$(normalized_llbc_sha "$replay_tmp/V6AcceptedKernel.llbc")
parser_llbc_sha=$(normalized_llbc_sha "$replay_tmp/V6DeferredParser.llbc")
echo "accepted normalized LLBC SHA-256: $accepted_llbc_sha"
echo "parser normalized LLBC SHA-256:   $parser_llbc_sha"
test "$accepted_llbc_sha" = \
  7b6bdc8a6873b6ac8a0fb4940d73df2b42e8802c008816093d7d7f856942e810
test "$parser_llbc_sha" = \
  76255490dc7629846144a323e8c0fa504978e6f4466f7ac5cc196e2c5c4e4742

accepted_generated="$replay_tmp/accepted-generated"
parser_generated="$replay_tmp/parser-generated"
"$AENEAS_BIN" -backend lean \
  -namespace V6AcceptedKernelGenerated \
  -dest "$accepted_generated" \
  -subdir V6AcceptedKernel \
  -split-files -emit-json \
  "$replay_tmp/V6AcceptedKernel.llbc"
patch --silent -d "$accepted_generated" -p1 < \
  "$script_dir/generated/aeneas-lean-printer-precedence.patch"
cmp "$accepted_generated/V6AcceptedKernel/Types.lean" \
  "$script_dir/generated/V6AcceptedKernel/Types.lean"
cmp "$accepted_generated/V6AcceptedKernel/Funs.lean" \
  "$script_dir/generated/V6AcceptedKernel/Funs.lean"
compare_translation_metadata \
  "$accepted_generated/translation.json" \
  "$script_dir/extraction/translation.json" \
  "$replay_tmp/accepted-translation-normalized.json"

"$AENEAS_BIN" -backend lean \
  -namespace V6DeferredParserGenerated \
  -dest "$parser_generated" \
  -subdir V6DeferredParser \
  -split-files -emit-json \
  "$replay_tmp/V6DeferredParser.llbc"
cmp "$parser_generated/V6DeferredParser/Types.lean" \
  "$script_dir/parser/generated-exact/V6DeferredParser/Types.lean"
cmp "$parser_generated/V6DeferredParser/Funs.lean" \
  "$script_dir/parser/generated-exact/V6DeferredParser/Funs.lean"
compare_translation_metadata \
  "$parser_generated/translation.json" \
  "$script_dir/parser/generated-exact/translation.json" \
  "$replay_tmp/parser-translation-normalized.json"

cp -R "$script_dir/generated/V6AcceptedKernel" "$lean_tmp/"
cp "$script_dir/proof/V6AcceptedKernelSourceBridge.lean" "$lean_tmp/"
cp -R "$script_dir/parser/generated-exact/V6DeferredParser" "$lean_tmp/"
cp "$script_dir/parser/proof/V6DeferredParserSourceBridge.lean" "$lean_tmp/"

cd "$AENEAS_LEAN_BACKEND"
export LEAN_PATH="$AENEAS_LEAN_BACKEND:$lean_tmp"
for module in TypesExternal Types FunsExternal Funs; do
  lake env lean -o "$lean_tmp/V6AcceptedKernel/$module.olean" \
    "$lean_tmp/V6AcceptedKernel/$module.lean"
done
lake env lean "$lean_tmp/V6AcceptedKernelSourceBridge.lean"

for module in Types FunsExternal Funs; do
  lake env lean -o "$lean_tmp/V6DeferredParser/$module.olean" \
    "$lean_tmp/V6DeferredParser/$module.lean"
done
lake env lean "$lean_tmp/V6DeferredParserSourceBridge.lean"

echo 'V6 accepted-source replay: PASS'
