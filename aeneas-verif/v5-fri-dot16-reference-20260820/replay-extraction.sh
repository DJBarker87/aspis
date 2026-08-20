#!/usr/bin/env bash
set -euo pipefail

readonly bundle="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly root="$(cd "$bundle/../.." && pwd -P)"
readonly source_bundle="$root/kani-verif/v5-fri-dot16-exact-20260820"
readonly checked="$bundle/generated/V5Dot16Reference"
readonly charon_bin="${CHARON_BIN:?set CHARON_BIN to the pinned Charon binary}"
readonly aeneas_bin="${AENEAS_BIN:?set AENEAS_BIN to the pinned Aeneas binary}"

readonly expected_charon_commit="cb50ff16b9f1066b8a97dc06da704de2da2fa41c"
readonly expected_aeneas_commit="b59d5188c082f704a418c7cb4e52ad69328002d1"
readonly expected_field_blob="a28ff94de05265102ca819849805a7f73c675800"
readonly expected_reference_sha256="04b782484afb5fda8be112a7a8e563bcac7f7f60b7de780ed84bf3d60c6fc09e"

tool_repo() {
  git -C "$(dirname "$1")" rev-parse --show-toplevel
}

[[ "$(git -C "$(tool_repo "$charon_bin")" rev-parse HEAD)" == \
  "$expected_charon_commit" ]]
[[ "$(git -C "$(tool_repo "$aeneas_bin")" rev-parse HEAD)" == \
  "$expected_aeneas_commit" ]]
[[ "$(git -C "$root" hash-object crates/aspis-core/src/field.rs)" == \
  "$expected_field_blob" ]]
[[ "$(shasum -a 256 "$source_bundle/src/lib.rs" | awk '{print $1}')" == \
  "$expected_reference_sha256" ]]

if [[ -n "${V5_FRI_DOT16_EXTRACTION_OUT:-}" ]]; then
  out=$V5_FRI_DOT16_EXTRACTION_OUT
  mkdir -p "$out"
  [[ -z "$(find "$out" -mindepth 1 -maxdepth 1 -print -quit)" ]]
else
  out=$(mktemp -d /private/tmp/v5-fri-dot16-extraction.XXXXXX)
fi
readonly out

cd "$source_bundle"
CARGO_TARGET_DIR="$out/cargo-target" "$charon_bin" cargo --preset aeneas \
  --start-from 'v5_fri_dot16_exact::indexed_dot16' \
  --include 'aspis_core::field' \
  --dest-file "$out/v5_dot16_reference.llbc" -- --release --locked \
  >"$out/charon.log" 2>&1

mkdir -p "$out/generated"
"$aeneas_bin" -backend lean \
  -namespace V5FriDot16ReferenceGenerated \
  -subdir V5Dot16Reference -dest "$out/generated" -split-files \
  "$out/v5_dot16_reference.llbc" >"$out/aeneas.log" 2>&1

mkdir -p "$out/normalized"
for name in Types Funs; do
  sed -e '/^import Aeneas$/c\
import Aeneas.Std\
import Aeneas.Tactic.RustAttributes' \
    -e "s#Source: '$root/#Source: '#g" \
    "$out/generated/V5Dot16Reference/$name.lean" \
    >"$out/normalized/$name.lean"
  cmp "$out/normalized/$name.lean" "$checked/$name.lean"
done

echo "Charon/Aeneas fixed-index V5 FRI dot extraction: PASS"
echo "V5_FRI_DOT16_EXTRACTION_OUT=$out"
