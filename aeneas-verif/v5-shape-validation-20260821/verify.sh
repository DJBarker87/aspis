#!/usr/bin/env bash
set -euo pipefail

readonly bundle="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly root="$(cd "$bundle/../.." && pwd -P)"
readonly generated="$bundle/generated"
readonly proof="$bundle/proof"
readonly consumer="$root/aeneas-verif/v5-fri-consumer-exact-20260815"
readonly lean_bin="${LEAN432_BIN:-$(cd "$root/AspisFormal" && elan which lean)}"
readonly aeneas_lib="${AENEAS_LEAN_LIB:?set AENEAS_LEAN_LIB to the matching Aeneas Lean library}"
readonly fri_out="${V5_FRI_ACCEPTED_FOREST_REPLAY_OUT:?set V5_FRI_ACCEPTED_FOREST_REPLAY_OUT to a successful V5 FRI-consumer replay output}"
readonly expected_source_blob="32053749499955032098aa38915ad800c200d5ce"

case "$($lean_bin --version)" in
  "Lean (version 4.32.0,"*) ;;
  *) echo "expected Lean 4.32.0" >&2; exit 1 ;;
esac

[[ -f "$aeneas_lib/Aeneas/Std.olean" ]]
[[ -f "$fri_out/FriArithmetic/Funs.olean" ]]
[[ -f "$fri_out/V5FriHelperTransparent/Funs.olean" ]]
[[ -f "$fri_out/V5FriConsumerEndToEndProof.olean" ]]
[[ "$(git -C "$root" hash-object crates/aspis-core/src/circle_pcs_shape.rs)" == \
  "$expected_source_blob" ]]

aspis_path=${ASPIS_FORMAL_LEAN_PATH:-$(
  cd "$root/AspisFormal" && NO_DNA=1 lake env printenv LEAN_PATH
)}
readonly aspis_path

if [[ -n "${V5_SHAPE_VALIDATION_REPLAY_OUT:-}" ]]; then
  out=$V5_SHAPE_VALIDATION_REPLAY_OUT
  mkdir -p "$out"
  [[ -z "$(find "$out" -mindepth 1 -maxdepth 1 -print -quit)" ]]
else
  out=$(mktemp -d "${TMPDIR:-/tmp}/v5-shape-validation.XXXXXX")
fi
readonly out
readonly log="$out/lean432.log"
mkdir -p "$out/ShapeSource" "$out/CheckV5FriQueries"
: >"$log"

export LEAN_PATH="$out:$fri_out:$aspis_path:$aeneas_lib"

compile() {
  local target=$1 source=$2
  echo "COMPILE $target" >>"$log"
  (
    cd "$(dirname "$source")"
    "$lean_bin" -j 1 -o "$out/$target.olean" "$(basename "$source")"
  ) >>"$log" 2>&1
}

# The generated shape types are normalized to the identical type from the
# consumer extraction, so compile that type before the shape source.
compile CheckV5FriQueries/TypesExternal \
  "$consumer/generated/CheckV5FriQueries/TypesExternal.lean"
compile CheckV5FriQueries/Types \
  "$consumer/generated/CheckV5FriQueries/Types.lean"

compile ShapeSource/TypesExternal "$generated/ShapeSource/TypesExternal.lean"
compile ShapeSource/Types "$generated/ShapeSource/Types.lean"
compile ShapeSource/FunsExternal "$generated/ShapeSource/FunsExternal.lean"
compile ShapeSource/Funs "$generated/ShapeSource/Funs.lean"
compile ShapePreservesInput "$proof/ShapePreservesInput.lean"

compile CheckV5FriQueries/HelperTransport \
  "$consumer/generated/CheckV5FriQueries/HelperTransport.lean"
compile CheckV5FriQueries/FunsExternal \
  "$generated/CheckV5FriQueries/FunsExternal.lean"
compile CheckV5FriQueries/Funs \
  "$consumer/generated/CheckV5FriQueries/Funs.lean"
compile V5FriConsumerExactProof \
  "$consumer/proof/V5FriConsumerExactProof.lean"
compile V5FriConsumerEndToEndProof \
  "$consumer/proof/V5FriConsumerEndToEndProof.lean"
compile ConsumerShapeClosure "$proof/ConsumerShapeClosure.lean"

if rg -n '\b(sorry|admit|native_decide|unsafe|ofReduceBool)\b|^axiom ' \
    "$generated/ShapeSource" "$proof"; then
  echo "forbidden proof shortcut or source axiom" >&2
  exit 1
fi
if rg -n 'axiom aspis_core\.circle_pcs_shape\.CirclePcsShape\.validate' \
    "$generated/CheckV5FriQueries/FunsExternal.lean"; then
  echo "consumer validator is still opaque" >&2
  exit 1
fi
if rg -n "V5ShapeValidationProof\.validationSuccessPreservesShape.*depends on axioms:.*(sorryAx|Lean\.ofReduceBool|CirclePcsShape\.validate)" "$log"; then
  echo "final theorem retains a forbidden dependency" >&2
  exit 1
fi

echo "Lean 4.32 production shape-validation connection: PASS"
echo "V5_SHAPE_VALIDATION_REPLAY_OUT=$out"
echo "log: $log"
