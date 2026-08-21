#!/usr/bin/env bash
set -euo pipefail

readonly bundle="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly root="$(cd "$bundle/../.." && pwd -P)"
readonly generated="$bundle/generated"
readonly caller_proof="$bundle/proof/V5FriCallerParametric.lean"
readonly bridge_proof="$bundle/proof/V5FriCallerMerkleBridge.lean"
readonly resolver_proof="$bundle/proof/V5FriCallerAcceptedResolverBridge.lean"
readonly lean_bin="${LEAN432_BIN:-$(cd "$root/AspisFormal" && elan which lean)}"
readonly aeneas_lib="${AENEAS_LEAN_LIB:?set AENEAS_LEAN_LIB to the matching Aeneas Lean library}"
readonly merkle_out="${V5_MERKLE_UNCHANGED_LEAN_OUT:?set V5_MERKLE_UNCHANGED_LEAN_OUT to a successful unchanged-Merkle replay output}"
readonly fri_out="${V5_FRI_CONSUMER_REPLAY_OUT:?set V5_FRI_CONSUMER_REPLAY_OUT to a successful FRI-consumer replay output}"
readonly returned_out="${V5_MERKLE_FRI_RETURNED_OUT:?set V5_MERKLE_FRI_RETURNED_OUT to a successful returned-output replay directory}"

case "$($lean_bin --version)" in
  "Lean (version 4.32.0,"*) ;;
  *) echo "expected Lean 4.32.0" >&2; exit 1 ;;
esac

[[ -f "$aeneas_lib/Aeneas/Std.olean" ]]
[[ -f "$merkle_out/V5MerkleUnchangedPublicAcceptanceBridge.olean" ]]
[[ -f "$fri_out/V5FriConsumerObservationBridge.olean" ]]
[[ -f "$returned_out/V5MerkleFriReturnedOutputBridge.olean" ]]

sha256() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  else
    shasum -a 256 "$1" | awk '{print $1}'
  fi
}

[[ "$(sha256 "$generated/V5FriCaller/Types.lean")" == \
  8a9c03aeaa3a4fccb06b141276a78d0848089ac35f83f6a72ea69e76c984af73 ]]
[[ "$(sha256 "$caller_proof")" == \
  a1e1678fef7051200b559240dc71dfaab84efcb049ef33fe85b91a0a57d760ea ]]
[[ "$(sha256 "$bridge_proof")" == \
  8c175163521af742721215edefdb5a36e07e15b1e791175200f0db945dc759bd ]]
[[ "$(sha256 "$resolver_proof")" == \
  a1b4cc92fdc4f88de09fbb589078415c0a9807cb098c0ca429ceb5a6904dd89c ]]

aspis_path=${ASPIS_FORMAL_LEAN_PATH:-$(
  cd "$root/AspisFormal" && NO_DNA=1 lake env printenv LEAN_PATH
)}
readonly aspis_path

if [[ -n "${V5_FRI_CALLER_MERKLE_OUT:-}" ]]; then
  out=$V5_FRI_CALLER_MERKLE_OUT
  mkdir -p "$out"
  [[ -z "$(find "$out" -mindepth 1 -maxdepth 1 -print -quit)" ]]
else
  out=$(mktemp -d "${TMPDIR:-/tmp}/v5-fri-caller-merkle.XXXXXX")
fi
readonly out
readonly log="$out/lean432.log"
mkdir -p "$out/V5FriCaller"
: > "$log"

export LEAN_PATH="$out:$generated:$returned_out:$merkle_out:$fri_out:$aspis_path:$aeneas_lib"
"$lean_bin" -j 1 -R "$generated" \
  -o "$out/V5FriCaller/Types.olean" "$generated/V5FriCaller/Types.lean" \
  >> "$log" 2>&1
"$lean_bin" -j 1 -R "$bundle/proof" \
  -o "$out/V5FriCallerParametric.olean" "$caller_proof" >> "$log" 2>&1
"$lean_bin" -j 1 -R "$bundle/proof" \
  -o "$out/V5FriCallerMerkleBridge.olean" "$bridge_proof" >> "$log" 2>&1
"$lean_bin" -j 1 -R "$bundle/proof" \
  -o "$out/V5FriCallerAcceptedResolverBridge.olean" "$resolver_proof" \
  >> "$log" 2>&1

if rg -n '\b(sorry|admit|native_decide|unsafe|ofReduceBool)\b|^axiom ' \
    "$caller_proof" "$bridge_proof" "$resolver_proof"; then
  echo "forbidden proof shortcut or axiom" >&2
  exit 1
fi
if rg -n 'sorryAx|ofReduceBool' "$log"; then
  echo "forbidden proof dependency" >&2
  exit 1
fi
if ! rg -F "accepted_exact_merkle_call_yields_authenticated_fri_view' depends on axioms:" \
    "$log" >/dev/null ||
   ! rg -F "accepted_false_source_caller_event_with_released_tables' depends on axioms:" \
    "$log" >/dev/null ||
   ! rg -F "Classical.choice" "$log" >/dev/null ||
   ! rg -F "Quot.sound" "$log" >/dev/null; then
  echo "missing or unexpected theorem dependency report" >&2
  exit 1
fi

echo "Lean 4.32 exact V5 Merkle-to-FRI caller replay: PASS"
echo "V5_FRI_CALLER_MERKLE_OUT=$out"
echo "log: $log"
