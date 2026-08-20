#!/usr/bin/env bash
set -euo pipefail

readonly bundle="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly root="$(cd "$bundle/../.." && pwd -P)"
readonly source_bundle="$root/kani-verif/v5-fri-transition-decoders-20260820"
readonly checked="$bundle/generated/V5FriDecoderReference"
readonly charon_bin="${CHARON_BIN:?set CHARON_BIN to the pinned Charon binary}"
readonly aeneas_bin="${AENEAS_BIN:?set AENEAS_BIN to the pinned Aeneas binary}"

readonly expected_charon_commit="cb50ff16b9f1066b8a97dc06da704de2da2fa41c"
readonly expected_aeneas_commit="b59d5188c082f704a418c7cb4e52ad69328002d1"
readonly expected_circle_query_blob="085f0d082d9d2fe61d46ceb69f4a2b06bc6a0727"
readonly expected_reference_sha256="552007a69edd76c3b223c6bbdb010cde8919f54e0f441f2ec0500ff50dc231af"

tool_repo() {
  git -C "$(dirname "$1")" rev-parse --show-toplevel
}

[[ "$(git -C "$(tool_repo "$charon_bin")" rev-parse HEAD)" == \
  "$expected_charon_commit" ]]
[[ "$(git -C "$(tool_repo "$aeneas_bin")" rev-parse HEAD)" == \
  "$expected_aeneas_commit" ]]
[[ "$(git -C "$root" hash-object crates/aspis-core/src/circle_query.rs)" == \
  "$expected_circle_query_blob" ]]
[[ "$(shasum -a 256 "$source_bundle/src/lib.rs" | awk '{print $1}')" == \
  "$expected_reference_sha256" ]]

if [[ -n "${V5_FRI_DECODER_EXTRACTION_OUT:-}" ]]; then
  out=$V5_FRI_DECODER_EXTRACTION_OUT
  mkdir -p "$out"
  [[ -z "$(find "$out" -mindepth 1 -maxdepth 1 -print -quit)" ]]
else
  out=$(mktemp -d /private/tmp/v5-fri-decoder-extraction.XXXXXX)
fi
readonly out

cd "$source_bundle"
CARGO_TARGET_DIR="$out/cargo-target" "$charon_bin" cargo --preset aeneas \
  --start-from 'v5_fri_transition_decoders::decode_later_slot_reference' \
  --start-from 'v5_fri_transition_decoders::decode_later_leaf_reference' \
  --start-from 'v5_fri_transition_decoders::decode_selected_later_slot_reference' \
  --include 'aspis_core::field' \
  --dest-file "$out/v5_fri_decoder_reference.llbc" -- --release --locked \
  >"$out/charon.log" 2>&1

mkdir -p "$out/generated"
"$aeneas_bin" -backend lean -split-files \
  -namespace V5FriDecoderReference -subdir V5FriDecoderReference \
  -dest "$out/generated" -max-heartbeats 1000000 -max-recdepth 2048 \
  "$out/v5_fri_decoder_reference.llbc" >"$out/aeneas.log" 2>&1

mkdir -p "$out/normalized"
for name in Types Funs; do
  sed -e '/^import Aeneas$/c\
import Aeneas.Std\
import Aeneas.Tactic.RustAttributes' \
    -e 's/@\[discriminant isize, /@[/' \
    -e "s#Source: '$root/#Source: '#g" \
    "$out/generated/V5FriDecoderReference/$name.lean" \
    >"$out/normalized/$name.lean"
  cmp "$out/normalized/$name.lean" "$checked/$name.lean"
done

echo "Charon/Aeneas V5 FRI decoder reference extraction: PASS"
echo "V5_FRI_DECODER_EXTRACTION_OUT=$out"
