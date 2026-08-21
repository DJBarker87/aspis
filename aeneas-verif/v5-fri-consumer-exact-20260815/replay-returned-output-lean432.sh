#!/usr/bin/env bash
set -euo pipefail

readonly bundle="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly root="$(cd "$bundle/../.." && pwd -P)"
readonly proof="$bundle/proof/V5MerkleFriReturnedOutputBridge.lean"
readonly lean_bin="${LEAN432_BIN:-$(cd "$root/AspisFormal" && elan which lean)}"
readonly aeneas_lib="${AENEAS_LEAN_LIB:?set AENEAS_LEAN_LIB to the matching Aeneas Lean library}"
readonly merkle_out="${V5_MERKLE_UNCHANGED_LEAN_OUT:?set V5_MERKLE_UNCHANGED_LEAN_OUT to a successful unchanged-Merkle replay output}"
readonly fri_out="${V5_FRI_CONSUMER_REPLAY_OUT:?set V5_FRI_CONSUMER_REPLAY_OUT to a successful FRI-consumer replay output}"

case "$($lean_bin --version)" in
  "Lean (version 4.32.0,"*) ;;
  *) echo "expected Lean 4.32.0" >&2; exit 1 ;;
esac

[[ -f "$aeneas_lib/Aeneas/Std.olean" ]]
[[ -f "$merkle_out/V5MerkleUnchangedPublicAcceptanceBridge.olean" ]]
[[ -f "$fri_out/V5FriConsumerObservationBridge.olean" ]]

aspis_path=${ASPIS_FORMAL_LEAN_PATH:-$(
  cd "$root/AspisFormal" && NO_DNA=1 lake env printenv LEAN_PATH
)}
readonly aspis_path

if [[ -n "${V5_MERKLE_FRI_RETURNED_OUT:-}" ]]; then
  out=$V5_MERKLE_FRI_RETURNED_OUT
  mkdir -p "$out"
  [[ -z "$(find "$out" -mindepth 1 -maxdepth 1 -print -quit)" ]]
else
  out=$(mktemp -d "${TMPDIR:-/tmp}/v5-merkle-fri-returned.XXXXXX")
fi
readonly out
readonly log="$out/lean432.log"
: > "$log"

export LEAN_PATH="$out:$merkle_out:$fri_out:$aspis_path:$aeneas_lib"
"$lean_bin" -j 1 -R "$bundle/proof" \
  -o "$out/V5MerkleFriReturnedOutputBridge.olean" "$proof" \
  >> "$log" 2>&1

if rg -n '\b(sorry|admit|native_decide|unsafe|ofReduceBool)\b|^axiom ' "$proof"; then
  echo "forbidden proof shortcut or axiom" >&2
  exit 1
fi
if rg -n 'sorryAx|ofReduceBool' "$log"; then
  echo "forbidden proof dependency" >&2
  exit 1
fi

echo "Lean 4.32 exact Merkle-to-FRI returned-output bridge: PASS"
echo "V5_MERKLE_FRI_RETURNED_OUT=$out"
echo "log: $log"
