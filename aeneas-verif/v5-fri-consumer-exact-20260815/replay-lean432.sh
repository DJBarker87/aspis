#!/usr/bin/env bash
set -euo pipefail

readonly bundle="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly root="$(cd "$bundle/../.." && pwd -P)"
readonly generated="$bundle/generated/CheckV5FriQueries"
readonly proof="$bundle/proof/V5FriConsumerExactProof.lean"
readonly end_to_end_proof="$bundle/proof/V5FriConsumerEndToEndProof.lean"
readonly observation_bridge="$bundle/proof/V5FriConsumerObservationBridge.lean"
readonly value_adapter="$bundle/proof/V5FriConsumerValueAdapter.lean"
readonly lean_bin="${LEAN432_BIN:-$(command -v lean)}"
readonly aeneas_lib="${AENEAS_LEAN_LIB:?set AENEAS_LEAN_LIB to the matching Aeneas Lean library}"

readonly expected_commit="f0bf37b216e426878623ba6ddec2127e9f6f4748"
readonly expected_tree="a0f99ac9591fb568b6fce9fda5ef4dd7ac32e5f0"
readonly expected_source_blob="3b1f37f2504aa2b309cad82605c88cab11afcb85"
readonly expected_types_external="8184109b4cf2fe609835f1cab610516276f575afeef53793f12d7ecc589b7c37"
readonly expected_types="c121162321fc5f7bfc00bb58f18b342d182529dca03eb4534157fcaf085cd58e"
readonly expected_funs_external="d9781f69ad77b8d453e86c818c1978643f719ccab3425e0c50dcaf88dc053318"
readonly expected_funs="370be7ac485d08bef17844e240b3d759f639cb078c91b2880c6e2747d21b3745"

case "$($lean_bin --version)" in
  "Lean (version 4.32.0,"*) ;;
  *) echo "expected Lean 4.32.0" >&2; exit 1 ;;
esac

[[ -f "$aeneas_lib/Aeneas/Std.olean" ]]
[[ "$(git -C "$root" rev-parse "$expected_commit^{commit}")" == "$expected_commit" ]]
[[ "$(git -C "$root" rev-parse "$expected_commit^{tree}")" == "$expected_tree" ]]
[[ "$(git -C "$root" rev-parse "$expected_commit:programs/aspis-verifier/src/v5_fri_checks.rs")" == "$expected_source_blob" ]]
[[ "$(git -C "$root" hash-object programs/aspis-verifier/src/v5_fri_checks.rs)" == "$expected_source_blob" ]]

check_sha256() {
  local expected=$1 file=$2
  [[ "$(shasum -a 256 "$file" | awk '{print $1}')" == "$expected" ]]
}

check_sha256 "$expected_types_external" "$generated/TypesExternal.lean"
check_sha256 "$expected_types" "$generated/Types.lean"
check_sha256 "$expected_funs_external" "$generated/FunsExternal.lean"
check_sha256 "$expected_funs" "$generated/Funs.lean"

if [[ -n "${V5_FRI_CONSUMER_REPLAY_OUT:-}" ]]; then
  out=$V5_FRI_CONSUMER_REPLAY_OUT
  mkdir -p "$out"
  [[ -z "$(find "$out" -mindepth 1 -maxdepth 1 -print -quit)" ]]
else
  out=$(mktemp -d /private/tmp/v5-fri-consumer-exact.XXXXXX)
fi
readonly out
readonly log="$out/lean432.log"
mkdir -p "$out/CheckV5FriQueries"
: > "$log"

aspis_path=${ASPIS_FORMAL_LEAN_PATH:-$(
  cd "$root/AspisFormal" && NO_DNA=1 lake env printenv LEAN_PATH
)}
export LEAN_PATH="$out:$aspis_path:$aeneas_lib"

compile() {
  local target=$1 source=$2
  echo "COMPILE $target" >> "$log"
  "$lean_bin" -j 1 -o "$out/$target.olean" "$source" >> "$log" 2>&1
}

compile CheckV5FriQueries/TypesExternal "$generated/TypesExternal.lean"
compile CheckV5FriQueries/Types "$generated/Types.lean"
compile CheckV5FriQueries/FunsExternal "$generated/FunsExternal.lean"
compile CheckV5FriQueries/Funs "$generated/Funs.lean"
compile V5FriConsumerExactProof "$proof"
compile V5FriConsumerEndToEndProof "$end_to_end_proof"
compile V5FriConsumerObservationBridge "$observation_bridge"
compile V5FriConsumerValueAdapter "$value_adapter"

if rg -n '\b(sorry|admit|native_decide|unsafe|ofReduceBool)\b' \
    "$proof" "$end_to_end_proof" "$observation_bridge" "$value_adapter"; then
  echo "forbidden proof shortcut" >&2
  exit 1
fi
if rg -n 'sorryAx|ofReduceBool' "$log"; then
  echo "forbidden proof dependency" >&2
  exit 1
fi

echo "Lean 4.32 exact production V5 FRI consumer proof: PASS"
echo "V5_FRI_CONSUMER_REPLAY_OUT=$out"
echo "log: $log"
