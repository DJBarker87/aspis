#!/usr/bin/env bash
set -euo pipefail

readonly bundle="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly root="$(cd "$bundle/../.." && pwd -P)"
readonly generated="$bundle/generated/ParentCore"
readonly lean_bin="${LEAN432_BIN:-$(command -v lean)}"
readonly aeneas_path="${AENEAS_LEAN_PATH:?set AENEAS_LEAN_PATH to the full matching Aeneas lake LEAN_PATH}"

case "$($lean_bin --version)" in
  "Lean (version 4.32.0,"*) ;;
  *) echo "expected Lean 4.32.0" >&2; exit 1 ;;
esac

test "$(git -C "$root" hash-object crates/aspis-core/src/circle_fri.rs)" = \
  "d9382a35ec7a660b696171e7609f443995a009bf"

check_sha256() {
  local expected=$1 file=$2
  test "$(shasum -a 256 "$file" | awk '{print $1}')" = "$expected"
}

check_sha256 0ee3d7a4ce86e461ef75ba0cf52ca8a1202ea7bb6b584a18763bef700b89c0ef \
  "$generated/Types.lean"
check_sha256 6a8cc396e178c581ec977bcae1c2f5e0dd96b5c7d33c0f7969d76db3febb0a88 \
  "$generated/FunsExternal.lean"
check_sha256 4da4734c25d4ff38eb52aefbb0ae58eec077920f8a672537624c61ee2549ed3d \
  "$generated/Funs.lean"

if test -n "${V5_FRI_PARENT_HELPER_REPLAY_OUT:-}"; then
  out=$V5_FRI_PARENT_HELPER_REPLAY_OUT
  mkdir -p "$out"
  test -z "$(find "$out" -mindepth 1 -maxdepth 1 -print -quit)"
else
  out=$(mktemp -d /private/tmp/v5-fri-parent-helper.XXXXXX)
fi
readonly out
mkdir -p "$out/ParentCore"

export LEAN_PATH="$out:$aeneas_path"
"$lean_bin" -j 1 -o "$out/ParentCore/Types.olean" \
  "$generated/Types.lean"
"$lean_bin" -j 1 -o "$out/ParentCore/FunsExternal.olean" \
  "$generated/FunsExternal.lean"
"$lean_bin" -j 1 -o "$out/ParentCore/Funs.olean" \
  "$generated/Funs.lean"

if rg -n '\b(sorry|admit|native_decide|unsafe|ofReduceBool)\b|\baxiom\b' \
    "$generated/Types.lean" "$generated/FunsExternal.lean" \
    "$generated/Funs.lean"; then
  echo "forbidden generated-model hole" >&2
  exit 1
fi

echo "Lean 4.32 unchanged parent-coordinate helper model: PASS"
echo "V5_FRI_PARENT_HELPER_REPLAY_OUT=$out"
