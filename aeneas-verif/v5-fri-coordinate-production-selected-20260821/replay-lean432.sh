#!/usr/bin/env bash
set -euo pipefail

readonly bundle="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly root="$(cd "$bundle/../.." && pwd -P)"
readonly generated="$bundle/generated/V5CoordinateSelectedProduction"
readonly proof="$bundle/proof/V5CoordinateSelectedProductionProof.lean"
readonly lean_bin="${LEAN432_BIN:-$(command -v lean)}"
readonly aeneas_path="${AENEAS_LEAN_PATH:?set AENEAS_LEAN_PATH to the matching Aeneas lake LEAN_PATH}"
readonly coordinate_out="${V5_FRI_COORDINATE_REPLAY_OUT:?set V5_FRI_COORDINATE_REPLAY_OUT to the checked v5-fri-coordinate-source replay output}"
readonly arithmetic_out="${V5_FRI_ARITHMETIC_LEAN_OUT:?set V5_FRI_ARITHMETIC_LEAN_OUT to the checked FRI arithmetic output}"
readonly aspis_path="${ASPIS_FORMAL_LEAN_PATH:?set ASPIS_FORMAL_LEAN_PATH to the checked AspisFormal Lean path}"

case "$($lean_bin --version)" in
  "Lean (version 4.32.0,"*) ;;
  *) echo "expected Lean 4.32.0" >&2; exit 1 ;;
esac

test -f "$coordinate_out/V5FriCoordinateReleasedPointConnection.olean"
test -f "$arithmetic_out/QM31MulProof.olean"
test -f "$aspis_path/AspisFormal.olean"
test "$(git -C "$root" hash-object crates/aspis-core/src/circle_fri.rs)" = \
  "d9382a35ec7a660b696171e7609f443995a009bf"

check_sha256() {
  local expected=$1 file=$2
  test "$(shasum -a 256 "$file" | awk '{print $1}')" = "$expected"
}

check_sha256 4e8a3906bf0b9cdf7ecd0a2471f54e1a56eaef7d66544d158d2bed868000c239 \
  "$generated/Types.lean"
check_sha256 5c7513d441d522c16005d314db0f8516a7e1db46d205c25b5cb3e3c9af2a0129 \
  "$generated/FunsExternal.lean"
check_sha256 683cc896246492bf2a4580ec1812b0bf47c55bf2e2c27b4323c594967bc44b45 \
  "$generated/FunsCore.lean"
check_sha256 cc10cf2e3ac811c50eef19164e19ff5c3685a64e21dfc6626a288535adfc3e2f \
  "$generated/FunsHighWindow.lean"
check_sha256 08ccfa4814ea3833c3bb7aed6f298f2e0d1aeb1552d7dd74758ea119277b6ba9 \
  "$generated/FunsLowWindow.lean"
check_sha256 2b0d55d4cc0cf87b7e64a504aebd7542703f4814c2963e9b7af1f92b4a7517ac \
  "$generated/FunsSelected.lean"
check_sha256 999f343fa3bc5581c6d8a913ce1ceb38867142d5e669165dfaf4628a2633b6ef \
  "$proof"

if test -n "${V5_FRI_SELECTED_REPLAY_OUT:-}"; then
  out=$V5_FRI_SELECTED_REPLAY_OUT
  mkdir -p "$out"
  test -z "$(find "$out" -mindepth 1 -maxdepth 1 -print -quit)"
else
  out=$(mktemp -d /private/tmp/v5-fri-selected-source.XXXXXX)
fi
readonly out
mkdir -p "$out/V5CoordinateSelectedProduction"

export LEAN_PATH="$out:$coordinate_out:$arithmetic_out:$aspis_path:$aeneas_path"
for module in Types FunsExternal FunsCore FunsHighWindow FunsLowWindow FunsSelected; do
  "$lean_bin" -j 1 \
    -o "$out/V5CoordinateSelectedProduction/${module}.olean" \
    "$generated/${module}.lean"
done
"$lean_bin" -j 1 \
  -o "$out/V5CoordinateSelectedProductionProof.olean" "$proof"

if rg -n '\b(sorry|admit|native_decide|unsafe|ofReduceBool)\b|\baxiom\b' \
    "$generated" "$proof"; then
  echo "forbidden generated-model or proof hole" >&2
  exit 1
fi

echo "Lean 4.32 direct production selected-circle helper proof: PASS"
echo "V5_FRI_SELECTED_REPLAY_OUT=$out"
