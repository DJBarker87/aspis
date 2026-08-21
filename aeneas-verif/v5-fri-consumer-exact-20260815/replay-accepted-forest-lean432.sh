#!/usr/bin/env bash
set -euo pipefail

readonly bundle="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly root="$(cd "$bundle/../.." && pwd -P)"
readonly consumer_generated="$bundle/generated/CheckV5FriQueries"
readonly consumer_proof="$bundle/proof"
readonly arithmetic="$root/aeneas-verif/v5-fri-arithmetic-exact-20260820"
readonly coordinate="$root/aeneas-verif/v5-fri-coordinate-source-20260820"
readonly decoder="$root/aeneas-verif/v5-fri-transition-reference-20260820"
readonly lean_bin="${LEAN432_BIN:-$(command -v lean)}"
readonly aeneas_lib="${AENEAS_LEAN_LIB:?set AENEAS_LEAN_LIB to the matching Aeneas Lean library}"
readonly arithmetic_base_out="${V5_FRI_ARITHMETIC_BASE_LEAN_OUT:?set V5_FRI_ARITHMETIC_BASE_LEAN_OUT to the checked M31/QM31 proof olean directory}"
readonly component_b_out="${V5_FRI_COMPONENTB_LEAN_OUT:?set V5_FRI_COMPONENTB_LEAN_OUT to the checked Component-B olean directory}"

case "$($lean_bin --version)" in
  "Lean (version 4.32.0,"*) ;;
  *) echo "expected Lean 4.32.0" >&2; exit 1 ;;
esac

[[ -f "$aeneas_lib/Aeneas/Std.olean" ]]
[[ -f "$arithmetic_base_out/QM31MulProof.olean" ]]
[[ -f "$arithmetic_base_out/HalfProof.olean" ]]
[[ -f "$arithmetic_base_out/M31ReduceU64Proof.olean" ]]
[[ -f "$component_b_out/SumProductsFullCorrespondence.olean" ]]

if [[ -n "${V5_FRI_ACCEPTED_FOREST_REPLAY_OUT:-}" ]]; then
  out=$V5_FRI_ACCEPTED_FOREST_REPLAY_OUT
  mkdir -p "$out"
  [[ -z "$(find "$out" -mindepth 1 -maxdepth 1 -print -quit)" ]]
else
  out=$(mktemp -d /private/tmp/v5-fri-accepted-forest.XXXXXX)
fi
readonly out
readonly log="$out/lean432.log"
mkdir -p "$out/FriArithmetic" "$out/Coordinates" \
  "$out/V5FriDecoderReference" "$out/CheckV5FriQueries"
: >"$log"

# The two independent extractions contain the same two Rust enums.  Attribute
# registration is global within one Lean process, so the coordinate copy keeps
# its Rust type name but leaves the already-registered discriminant to the
# consumer copy.  No definition or constructor is changed.
sed \
  -e 's/@\[discriminant isize, rust_type "aspis_core::circle_fri::FoldDenominator"\]/@[rust_type "aspis_core::circle_fri::FoldDenominator"]/' \
  -e 's/@\[discriminant isize, rust_type "aspis_core::circle_fri::CircleFriError"\]/@[rust_type "aspis_core::circle_fri::CircleFriError"]/' \
  "$coordinate/generated/Coordinates/Types.lean" >"$out/Coordinates/Types.lean"

(
  cd "$root/AspisFormal"
  NO_DNA=1 lake build AspisFormal.V5AcceptedExecutionDeterministicClosure
) >>"$log" 2>&1

aspis_path=${ASPIS_FORMAL_LEAN_PATH:-$(
  cd "$root/AspisFormal" && NO_DNA=1 lake env printenv LEAN_PATH
)}
export LEAN_PATH="$out:$arithmetic_base_out:$component_b_out:$aspis_path:$aeneas_lib"

compile() {
  local target=$1 source=$2
  echo "COMPILE $target" >>"$log"
  (
    cd "$(dirname "$source")"
    "$lean_bin" -j 1 -o "$out/$target.olean" "$(basename "$source")"
  ) >>"$log" 2>&1
}

compile FriArithmetic/Types \
  "$arithmetic/generated/FriArithmetic/Types.lean"
compile FriArithmetic/FunsExternal \
  "$arithmetic/generated/FriArithmetic/FunsExternal.lean"
compile FriArithmetic/Funs \
  "$arithmetic/generated/FriArithmetic/Funs.lean"
compile V5FriArithmeticSemantics \
  "$arithmetic/proof/V5FriArithmeticSemantics.lean"
compile V5FriPreparedSumSemantics \
  "$arithmetic/proof/V5FriPreparedSumSemantics.lean"
compile V5FriFoldSemantics \
  "$arithmetic/proof/V5FriFoldSemantics.lean"
compile V5FriTransitionSemantics \
  "$arithmetic/proof/V5FriTransitionSemantics.lean"

compile Coordinates/Types "$out/Coordinates/Types.lean"
compile Coordinates/FunsExternal \
  "$coordinate/generated/Coordinates/FunsExternal.lean"
compile Coordinates/FunsField \
  "$coordinate/generated/Coordinates/FunsField.lean"
compile Coordinates/FunsHighWindow \
  "$coordinate/generated/Coordinates/FunsHighWindow.lean"
compile Coordinates/FunsLowWindow \
  "$coordinate/generated/Coordinates/FunsLowWindow.lean"
compile Coordinates/FunsPoint \
  "$coordinate/generated/Coordinates/FunsPoint.lean"
compile Coordinates/Funs "$coordinate/generated/Coordinates/Funs.lean"
compile V5FriCoordinateMathematics \
  "$coordinate/proof/V5FriCoordinateMathematics.lean"
compile V5FriBatchInverseMathematics \
  "$coordinate/proof/V5FriBatchInverseMathematics.lean"
compile V5FriCoordinateTableSemantics \
  "$coordinate/proof/V5FriCoordinateTableSemantics.lean"
compile V5FriCoordinateFieldSemantics \
  "$coordinate/proof/V5FriCoordinateFieldSemantics.lean"
compile V5FriCoordinateDenominatorLoops \
  "$coordinate/proof/V5FriCoordinateDenominatorLoops.lean"
compile V5FriCoordinateInverseLoops \
  "$coordinate/proof/V5FriCoordinateInverseLoops.lean"
compile V5FriCoordinateOutputLoops \
  "$coordinate/proof/V5FriCoordinateOutputLoops.lean"
compile V5FriCoordinatePointLoops \
  "$coordinate/proof/V5FriCoordinatePointLoops.lean"
compile V5FriCoordinateTopLevel \
  "$coordinate/proof/V5FriCoordinateTopLevel.lean"
compile V5FriCoordinateReleasedPointConnection \
  "$coordinate/proof/V5FriCoordinateReleasedPointConnection.lean"

compile V5FriDecoderReference/Types \
  "$decoder/generated/V5FriDecoderReference/Types.lean"
compile V5FriDecoderReference/FunsExternal \
  "$decoder/generated/V5FriDecoderReference/FunsExternal.lean"
compile V5FriDecoderReference/Funs \
  "$decoder/generated/V5FriDecoderReference/Funs.lean"
compile V5FriDecoderReferenceSemantics \
  "$decoder/proof/V5FriDecoderReferenceSemantics.lean"

compile CheckV5FriQueries/TypesExternal \
  "$consumer_generated/TypesExternal.lean"
compile CheckV5FriQueries/Types "$consumer_generated/Types.lean"
compile CheckV5FriQueries/FunsExternal "$consumer_generated/FunsExternal.lean"
compile CheckV5FriQueries/Funs "$consumer_generated/Funs.lean"
compile V5FriConsumerExactProof "$consumer_proof/V5FriConsumerExactProof.lean"
compile V5FriConsumerEndToEndProof \
  "$consumer_proof/V5FriConsumerEndToEndProof.lean"
compile V5FriConsumerObservationBridge \
  "$consumer_proof/V5FriConsumerObservationBridge.lean"
compile V5FriConsumerValueAdapter \
  "$consumer_proof/V5FriConsumerValueAdapter.lean"
compile V5FriConsumerValueSemantics \
  "$consumer_proof/V5FriConsumerValueSemantics.lean"
compile V5FriConsumerReadSemantics \
  "$consumer_proof/V5FriConsumerReadSemantics.lean"
compile V5FriConsumerCoordinateBridge \
  "$consumer_proof/V5FriConsumerCoordinateBridge.lean"
compile V5FriAcceptedForestChecks \
  "$consumer_proof/V5FriAcceptedForestChecks.lean"
compile V5AcceptedExecutionFinalClosure \
  "$consumer_proof/V5AcceptedExecutionFinalClosure.lean"

if rg -n '\b(sorry|admit|native_decide|unsafe|ofReduceBool|axiom)\b' \
    "$consumer_proof" "$coordinate/proof" "$arithmetic/proof" \
    "$decoder/proof"; then
  echo "forbidden proof shortcut" >&2
  exit 1
fi
# Restrict the log check to Lean's axiom reports.  Imported module comments
# are sometimes repeated by linters and may mention a forbidden mechanism
# while explaining that it was deliberately not used.
if rg -n "depends on axioms:.*(sorryAx|Lean\\.ofReduceBool)" "$log"; then
  echo "forbidden proof dependency" >&2
  exit 1
fi

echo "Lean 4.32 accepted production V5 FRI-to-forest proof: PASS"
echo "V5_FRI_ACCEPTED_FOREST_REPLAY_OUT=$out"
echo "log: $log"
