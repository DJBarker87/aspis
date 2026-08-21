#!/usr/bin/env bash
set -euo pipefail

readonly bundle="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly root="$(cd "$bundle/../.." && pwd -P)"
readonly lean_bin="${LEAN432_BIN:-$HOME/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean}"
readonly aeneas_path="${AENEAS_LEAN_PATH:?set AENEAS_LEAN_PATH to the Lean 4.32 Aeneas search path}"
readonly outer="$bundle/generated/Outer/Funs.lean"
readonly normalized="$root/AspisFormal/AspisFormal/V5TranscriptPrefixNormalizedGenerated.lean"

check_sha256() {
  local expected=$1
  local path=$2
  local actual
  actual=$(shasum -a 256 "$path" | awk '{print $1}')
  [[ "$actual" == "$expected" ]] || {
    echo "SHA-256 mismatch: $path" >&2
    echo "expected $expected" >&2
    echo "actual   $actual" >&2
    exit 1
  }
}

case "$($lean_bin --version)" in
  "Lean (version 4.32.0,"*) ;;
  *) echo "expected Lean 4.32.0" >&2; exit 1 ;;
esac

[[ "$(git -C / hash-object --no-filters "$root/programs/aspis-verifier/src/v5_cu_probe.rs")" == \
  "ca28d560e44e5e82e689321f32289831c889a0bd" ]]
check_sha256 \
  18624db7ce0430a57b578501af5302b378f6dfe8805059cf32992397a89497ec \
  "$outer"

if [[ -n "${ASPIS_CHARON_REPO:-}" ]]; then
  [[ "$(git -C "$ASPIS_CHARON_REPO" rev-parse HEAD)" == \
    "cb50ff16b9f1066b8a97dc06da704de2da2fa41c" ]]
  check_sha256 \
    776344b8bfb7f3ec4ba78d5007ae79c1ef3f4ed654de05f04266693759a37375 \
    "${CHARON_BIN:-$ASPIS_CHARON_REPO/bin/charon}"
fi
if [[ -n "${ASPIS_AENEAS_REPO:-}" ]]; then
  [[ "$(git -C "$ASPIS_AENEAS_REPO" rev-parse HEAD)" == \
    "d860ac47ed548d3da6d799afc013779ce470516c" ]]
  check_sha256 \
    7eb0cf355544457ae9740c649921582b4f61c9de63ef63a1ae45e016f151ed0d \
    "${AENEAS_BIN:-$ASPIS_AENEAS_REPO/src/_build/default/main.exe}"
fi

python3 "$bundle/check-unchanged-normalized-success-path.py" \
  "$outer" "$normalized"

if rg -n --glob '*.lean' \
    '(^|[^A-Za-z_])(sorry|admit|native_decide|unsafe|ofReduceBool)([^A-Za-z_]|$)' \
    "$bundle/generated/Zero" "$bundle/generated/Semantic" "$bundle/proof"; then
  echo "forbidden proof shortcut found" >&2
  exit 1
fi

readonly out="$(mktemp -d /private/tmp/v5-prefix-complete-lean432.XXXXXX)"
trap 'rm -rf "$out"' EXIT
mkdir -p "$out/Zero" "$out/Semantic"

compile() {
  local output=$1
  local source=$2
  LEAN_PATH="$out:$bundle/generated:$aeneas_path" \
    "$lean_bin" -j 1 -o "$out/$output.olean" "$source"
}

compile Zero/TypesExternal "$bundle/generated/Zero/TypesExternal.lean"
compile Zero/Types "$bundle/generated/Zero/Types.lean"
compile Zero/FunsExternal "$bundle/generated/Zero/FunsExternal.lean"
compile Zero/Funs "$bundle/generated/Zero/Funs.lean"
compile V5ZeroUnchangedProof "$bundle/proof/V5ZeroUnchangedProof.lean"

compile Semantic/TypesExternal "$bundle/generated/Semantic/TypesExternal.lean"
compile Semantic/Types "$bundle/generated/Semantic/Types.lean"
compile Semantic/FunsExternal "$bundle/generated/Semantic/FunsExternal.lean"
compile Semantic/Funs "$bundle/generated/Semantic/Funs.lean"
compile V5SemanticUnchangedProof "$bundle/proof/V5SemanticUnchangedProof.lean"

echo "checked unchanged V5 prefix and all six helper bodies"
