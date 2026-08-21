#!/usr/bin/env bash
set -euo pipefail

readonly bundle="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly root="$(cd "$bundle/../.." && pwd -P)"
readonly generated="$bundle/generated/Coordinates"
readonly lean_bin="${LEAN432_BIN:-$(command -v lean)}"
readonly aeneas_lib="${AENEAS_LEAN_LIB:?set AENEAS_LEAN_LIB to the matching Aeneas Lean library}"
readonly arithmetic_out="${V5_FRI_ARITHMETIC_LEAN_OUT:?set V5_FRI_ARITHMETIC_LEAN_OUT to the checked V5 FRI arithmetic olean directory}"

case "$($lean_bin --version)" in
  "Lean (version 4.32.0,"*) ;;
  *) echo "expected Lean 4.32.0" >&2; exit 1 ;;
esac

test -f "$aeneas_lib/Aeneas/Std.olean"
test -f "$arithmetic_out/V5FriArithmeticSemantics.olean"
test "$(git -C "$root" hash-object crates/aspis-core/src/circle_fri.rs)" = \
  "d9382a35ec7a660b696171e7609f443995a009bf"
test "$(git -C "$root" hash-object crates/aspis-core/src/circle_openings.rs)" = \
  "2e4a07db0985b3c9db631616dedf590db5e78bd1"

check_sha256() {
  local expected=$1 file=$2
  test "$(shasum -a 256 "$file" | awk '{print $1}')" = "$expected"
}

check_sha256 49ff1616879c9bff776558941c11f240fae73a0197d36b2fedd14e48cf44a0a7 \
  "$generated/Types.lean"
check_sha256 f63a2c65575fdbe9b59b30902eb1df0ec7c5695d2c73c9ccd97ae8db703790ca \
  "$generated/FunsExternal.lean"
check_sha256 fe340d53fb9989274f25f97936b63db0aa09aeb49020996099cc56168eda2d3c \
  "$generated/FunsCombined.lean"
check_sha256 2115ff7edbdbcb22d2ee37d497345cead6d2cfcbf00c430ee663745f965baf1d \
  "$generated/FunsField.lean"
check_sha256 fc3f0f83789c5f8c9c0faa494e838b7fb2d16619a7ab3eb35fb3436187df52f9 \
  "$generated/FunsHighWindow.lean"
check_sha256 d65862710d4cc647674adba999e9c29a6a86879708f3c7c31a06379474e2cad8 \
  "$generated/FunsLowWindow.lean"
check_sha256 b7f3086decf2df5f168345a29e4a83a0e953a16c9dc8b3e8efa212608b50a6d5 \
  "$generated/FunsPoint.lean"
check_sha256 5064d5908cbdda30b78e4e3c3a2d3ae38cb951256fb8e46f0bdbaa843981e9a2 \
  "$generated/Funs.lean"

if test -n "${V5_FRI_COORDINATE_REPLAY_OUT:-}"; then
  out=$V5_FRI_COORDINATE_REPLAY_OUT
  mkdir -p "$out"
  test -z "$(find "$out" -mindepth 1 -maxdepth 1 -print -quit)"
else
  out=$(mktemp -d /private/tmp/v5-fri-coordinate-source.XXXXXX)
fi
readonly out
mkdir -p "$out/Coordinates"

aspis_path=${ASPIS_FORMAL_LEAN_PATH:-$(
  cd "$root/AspisFormal" && NO_DNA=1 lake env printenv LEAN_PATH
)}
export LEAN_PATH="$out:$arithmetic_out:$aspis_path:$aeneas_lib"

"$lean_bin" -j 1 -o "$out/Coordinates/Types.olean" "$generated/Types.lean"
"$lean_bin" -j 1 -o "$out/Coordinates/FunsExternal.olean" \
  "$generated/FunsExternal.lean"
"$lean_bin" -j 1 -o "$out/Coordinates/FunsField.olean" \
  "$generated/FunsField.lean"
"$lean_bin" -j 1 -o "$out/Coordinates/FunsHighWindow.olean" \
  "$generated/FunsHighWindow.lean"
"$lean_bin" -j 1 -o "$out/Coordinates/FunsLowWindow.olean" \
  "$generated/FunsLowWindow.lean"
"$lean_bin" -j 1 -o "$out/Coordinates/FunsPoint.olean" \
  "$generated/FunsPoint.lean"
"$lean_bin" -j 1 -o "$out/Coordinates/Funs.olean" "$generated/Funs.lean"
"$lean_bin" -j 1 -o "$out/V5FriCoordinateMathematics.olean" \
  "$bundle/proof/V5FriCoordinateMathematics.lean"
"$lean_bin" -j 1 -o "$out/V5FriBatchInverseMathematics.olean" \
  "$bundle/proof/V5FriBatchInverseMathematics.lean"
"$lean_bin" -j 1 -o "$out/V5FriCoordinateTableSemantics.olean" \
  "$bundle/proof/V5FriCoordinateTableSemantics.lean"
"$lean_bin" -j 1 -o "$out/V5FriCoordinateFieldSemantics.olean" \
  "$bundle/proof/V5FriCoordinateFieldSemantics.lean"
"$lean_bin" -j 1 -o "$out/V5FriCoordinateDenominatorLoops.olean" \
  "$bundle/proof/V5FriCoordinateDenominatorLoops.lean"
"$lean_bin" -j 1 -o "$out/V5FriCoordinateInverseLoops.olean" \
  "$bundle/proof/V5FriCoordinateInverseLoops.lean"
"$lean_bin" -j 1 -o "$out/V5FriCoordinateOutputLoops.olean" \
  "$bundle/proof/V5FriCoordinateOutputLoops.lean"
"$lean_bin" -j 1 -o "$out/V5FriCoordinatePointLoops.olean" \
  "$bundle/proof/V5FriCoordinatePointLoops.lean"
"$lean_bin" -j 1 -o "$out/V5FriCoordinateTopLevel.olean" \
  "$bundle/proof/V5FriCoordinateTopLevel.lean"
"$lean_bin" -j 1 -o "$out/V5FriCoordinateReleasedPointConnection.olean" \
  "$bundle/proof/V5FriCoordinateReleasedPointConnection.lean"

if rg -n '\b(sorry|admit|native_decide|unsafe|ofReduceBool)\b|\baxiom\b' \
    "$generated/Types.lean" "$generated/FunsExternal.lean" \
    "$generated/FunsCombined.lean" "$generated/FunsField.lean" \
    "$generated/FunsHighWindow.lean" "$generated/FunsLowWindow.lean" \
    "$generated/FunsPoint.lean" "$generated/Funs.lean" \
    "$bundle/proof/V5FriCoordinateMathematics.lean" \
    "$bundle/proof"; then
  echo "forbidden generated-model hole" >&2
  exit 1
fi

echo "Lean 4.32 V5 FRI coordinate source model: PASS"
echo "V5_FRI_COORDINATE_REPLAY_OUT=$out"
