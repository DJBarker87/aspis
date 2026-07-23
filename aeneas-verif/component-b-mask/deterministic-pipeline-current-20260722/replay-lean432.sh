#!/bin/sh
set -eu

: "${AENEAS432_BACKEND:?set to the patched pinned Aeneas b59d5188 backends/lean directory}"

BUNDLE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
ROOT=$(CDPATH= cd -- "$BUNDLE/../../.." && pwd)
LEAN_BIN=${LEAN432_BIN:-/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean}
EXPECTED_AENEAS=b59d5188c082f704a418c7cb4e52ad69328002d1
UNIFIED="$ROOT/aeneas-verif/component-b-mask/unified-current-20260722"
LAYOUT="$ROOT/aeneas-verif/component-b-layout-bindings"
MLE="$ROOT/aeneas-verif/multilinear-eval/fixed-u64-current-20260722"

if test -n "${COMPONENT_B_PIPELINE_REPLAY_OUT:-}"; then
  OUT=$COMPONENT_B_PIPELINE_REPLAY_OUT
  mkdir -p "$OUT"
  test -z "$(find "$OUT" -mindepth 1 -maxdepth 1 -print -quit)"
else
  OUT=$(mktemp -d /private/tmp/component-b-pipeline-replay.XXXXXX)
fi
LOG="$OUT/lean432-capstone.log"

test -x "$LEAN_BIN"
test "$(git -C "$AENEAS432_BACKEND/../.." rev-parse HEAD)" = "$EXPECTED_AENEAS"
case "$($LEAN_BIN --version)" in
  "Lean (version 4.32.0,"*) ;;
  *) echo "expected Lean 4.32.0" >&2; exit 1 ;;
esac

(cd "$BUNDLE" && shasum -a 256 -c metadata/SHA256SUMS)

check_hash() {
  expected=$1
  file=$2
  actual=$(shasum -a 256 "$file" | awk '{print $1}')
  test "$actual" = "$expected"
}

check_hash e2f683b62a7827e6b30c66cbb5038ee069db4979fe56508997e307e64d678bf4 \
  "$UNIFIED/llbc/component_b_sampler_mixing_evaluate_unified_20260722.llbc"
check_hash 1e0e6981c60e9c1cf53bb2bb50a29927448d13f7fb71c1c57342cd49c56f10bc \
  "$UNIFIED/generated/sampler-helper-raw/Types.lean"
check_hash a01017f0060aa93aba3c1ecb9dc56c90b01d51bb02b6ddc87c098ffbd115c30c \
  "$UNIFIED/generated/sampler-helper-raw/Funs.lean"
check_hash cd367c196b0e4cb0b5fac92a4b761008a81851e8fbcc9022ecf83c93333c590d \
  "$LAYOUT/llbc/layout_full_v3.llbc"
check_hash f6c1ddf1652bc255d74cd307100faa7c3ca25413d2708c9430cd913790d21538 \
  "$LAYOUT/generated/full-v3/LayoutFullV3.lean"
check_hash 06c057b0788e2907323625828677bb394f463936d41d879bdfe68f00e7f3702e \
  "$LAYOUT/generated/lean432/ComponentBLayoutBindingsGenerated.lean"
check_hash 8e956f2aa05c5223f153175daee04818170438a1ebc05319999dc89d0a67b614 \
  "$LAYOUT/c2-slot/llbc/component_b_c2_slot.llbc"
check_hash 8655c4d548ed1099cc5d846a8409bad6ca90729142a32a6cddb899ee1e7c180e \
  "$LAYOUT/c2-slot/generated/raw/ComponentBC2Slot.lean"
check_hash ad30192052563f914530e2759ea605a0c9352b26e1ef85a87f6e14c114fdc706 \
  "$UNIFIED/proof/mixing/MultilinearEvalFormula.lean"
check_hash 3000289ebfb4ffc01af6766a61449b612670863424e13b4f932b74addc6e78dd \
  "$MLE/proof/MultilinearEvalFormula.lean"

# Reconstruct and byte-check the two compatibility normalizations.
awk 'NR < 101 || (NR > 121 && NR < 141) || (NR > 149 && NR < 158) || NR > 167' \
  "$LAYOUT/generated/lean432/ComponentBLayoutBindingsGenerated.lean" \
  > "$OUT/ComponentBLayoutBindingsGenerated.expected.lean"
cmp "$OUT/ComponentBLayoutBindingsGenerated.expected.lean" \
  "$BUNDLE/generated/ComponentBLayoutBindingsGenerated.lean"
{
  printf '%s\n' 'import MLEBFormulaPrelude' 'import MultilinearEvalProofs' \
    'import CM31MultiplicativeProof' ''
  tail -n +4 "$UNIFIED/proof/mixing/MultilinearEvalFormula.lean"
  printf '\n'
  tail -n +4 "$MLE/proof/MultilinearEvalFormula.lean"
} > "$OUT/MultilinearEvalFormula.expected.lean"
cmp "$OUT/MultilinearEvalFormula.expected.lean" \
  "$BUNDLE/generated/MultilinearEvalFormula.lean"

if rg -n '\b(sorry|admit|native_decide|axiom|unsafe|ofReduceBool)\b|set_option max(Heartbeats|RecDepth)' \
    "$BUNDLE/generated" "$BUNDLE/proof"; then
  echo "forbidden token or raised proof limit" >&2
  exit 1
fi

AENEAS_PATH=$(cd "$AENEAS432_BACKEND" && lake env printenv LEAN_PATH)
ASPIS_PATH=$(cd "$ROOT/AspisFormal" && lake env printenv LEAN_PATH)
UNIFIED_OLEAN="$UNIFIED/olean-sampler-helper"
export LEAN_PATH="$OUT:$UNIFIED_OLEAN:$BUNDLE/olean-deps:$ASPIS_PATH:$AENEAS_PATH"

compile() {
  module=$1
  source=$2
  echo "COMPILE $module" >> "$LOG"
  "$LEAN_BIN" -o "$OUT/$module.olean" "$source" >> "$LOG" 2>&1
}

compile MultilinearEvalFormula "$BUNDLE/generated/MultilinearEvalFormula.lean"
compile ComponentBLayoutBindingsGenerated \
  "$BUNDLE/generated/ComponentBLayoutBindingsGenerated.lean"
compile ComponentBLayoutBindingsProof \
  "$LAYOUT/proof/ComponentBLayoutBindingsProof.lean"
compile ComponentBEncodedMessageBindingProof \
  "$LAYOUT/proof/ComponentBEncodedMessageBindingProof.lean"
compile ComponentBC2SlotGenerated \
  "$LAYOUT/c2-slot/generated/lean432/ComponentBC2SlotGenerated.lean"
compile ComponentBC2SlotProof \
  "$LAYOUT/c2-slot/proof/ComponentBC2SlotProof.lean"
compile ComponentBRelationClaimsLayoutInstantiation \
  "$LAYOUT/c2-slot/proof/ComponentBRelationClaimsLayoutInstantiation.lean"
compile ComponentBDeterministicPipelineCapstone \
  "$BUNDLE/proof/ComponentBDeterministicPipelineCapstone.lean"

test "$(rg -c "^'ComponentBDeterministicPipelineCapstone\.[^']+' depends on axioms:" "$LOG")" = 8
if rg -n 'sorryAx|ofReduceBool' "$LOG"; then
  echo "forbidden axiom in closure" >&2
  exit 1
fi
if awk '
  / depends on axioms: \[/ { active = 1; sub(/^.*\[/, "") }
  active {
    line = $0
    gsub(/propext|Classical\.choice|Quot\.sound/, "", line)
    gsub(/[\[\],[:space:]]/, "", line)
    if (line != "") { print "unexpected axiom: " line; bad = 1 }
    if ($0 ~ /\]/) active = 0
  }
  END { exit bad }
' "$LOG"; then :; else exit 1; fi

echo "PASS Component-B deterministic pipeline Lean-4.32 capstone"
echo "REPLAY_OUT=$OUT"
