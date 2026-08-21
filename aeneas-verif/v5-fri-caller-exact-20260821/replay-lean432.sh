#!/usr/bin/env bash
set -euo pipefail

readonly bundle="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly root="$(cd "$bundle/../.." && pwd -P)"
readonly generated="$bundle/generated"
readonly proof="$bundle/proof/V5FriCallerParametric.lean"
readonly patch="$bundle/extraction/v5-fri-fixed-callbacks.patch"
readonly lean_bin="${LEAN432_BIN:-$(cd "$root/AspisFormal" && elan which lean)}"
readonly aeneas_lib="${AENEAS_LEAN_LIB:?set AENEAS_LEAN_LIB to the matching Aeneas Lean library}"

case "$($lean_bin --version)" in
  "Lean (version 4.32.0,"*) ;;
  *) echo "expected Lean 4.32.0" >&2; exit 1 ;;
esac

[[ -f "$aeneas_lib/Aeneas/Std.olean" ]]
[[ "$(git -C "$root" hash-object programs/aspis-verifier/src/v5_cu_probe.rs)" == \
  ca28d560e44e5e82e689321f32289831c889a0bd ]]
git -C "$root" apply --check "$patch"

sha256() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  else
    shasum -a 256 "$1" | awk '{print $1}'
  fi
}

check_sha256() {
  local expected=$1 file=$2
  [[ "$(sha256 "$file")" == "$expected" ]]
}

check_sha256 235c16310e970dafa081468fa17466b6ae43026907fc1df038e05d392ec2cf02 \
  "$bundle/extraction/V5FriCallerPatchedAllTypes.llbc"
check_sha256 a72270d0bce08ec930881cc9b6ae8231b7e8b7df96e84d358b31fe52b6068655 \
  "$bundle/extraction/V5FriCallerPatchedAllTypes.pretty.llbc"
check_sha256 10f8a0d5e42f996968e31e982d9ecb2b4a46be911bafb9a0745743eb6b9139b0 \
  "$patch"
check_sha256 304fa51aaf3f34dc8eab5aabd62d49abf7c581ea2422ffb3401384f8e50519fb \
  "$generated/V5FriCaller/FunsRaw.lean.txt"
check_sha256 ac0381caf2872cbc078bdc7f7804bc5ecc759e3ef5059353c7257dd34f2d077c \
  "$generated/V5FriCaller/Types.lean"
check_sha256 a1e1678fef7051200b559240dc71dfaab84efcb049ef33fe85b91a0a57d760ea \
  "$proof"

if [[ -n "${V5_FRI_CALLER_REPLAY_OUT:-}" ]]; then
  out=$V5_FRI_CALLER_REPLAY_OUT
  mkdir -p "$out"
  [[ -z "$(find "$out" -mindepth 1 -maxdepth 1 -print -quit)" ]]
else
  out=$(mktemp -d "${TMPDIR:-/tmp}/v5-fri-caller-exact.XXXXXX")
fi
readonly out
readonly log="$out/lean432.log"
mkdir -p "$out/V5FriCaller"
: > "$log"

aspis_path=${ASPIS_FORMAL_LEAN_PATH:-$(
  cd "$root/AspisFormal" && NO_DNA=1 lake env printenv LEAN_PATH
)}
readonly aspis_path
export LEAN_PATH="$out:$generated:$aspis_path:$aeneas_lib"

"$lean_bin" -j 1 -R "$generated" \
  -o "$out/V5FriCaller/Types.olean" "$generated/V5FriCaller/Types.lean" \
  >> "$log" 2>&1
"$lean_bin" -j 1 -R "$bundle/proof" \
  -o "$out/V5FriCallerParametric.olean" "$proof" >> "$log" 2>&1

if rg -n '\b(sorry|admit|native_decide|unsafe|ofReduceBool)\b' "$proof"; then
  echo "forbidden proof shortcut" >&2
  exit 1
fi
if rg -n 'sorryAx|ofReduceBool' "$log"; then
  echo "forbidden proof dependency" >&2
  exit 1
fi
if ! rg -F "depends on axioms: [propext," "$log" >/dev/null ||
   ! rg -F "Classical.choice," "$log" >/dev/null ||
   ! rg -F "Quot.sound]" "$log" >/dev/null; then
  echo "unexpected theorem dependency report" >&2
  exit 1
fi

echo "Lean 4.32 exact V5 FRI caller data-flow replay: PASS"
echo "V5_FRI_CALLER_REPLAY_OUT=$out"
echo "log: $log"
