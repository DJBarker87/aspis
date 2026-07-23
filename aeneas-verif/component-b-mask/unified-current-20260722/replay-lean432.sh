#!/bin/sh
set -eu

: "${AENEAS432_BACKEND:?set to the patched pinned Aeneas b59d5188 backends/lean directory}"

BUNDLE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
ROOT=$(CDPATH= cd -- "$BUNDLE/../../.." && pwd)
LEAN_BIN=${LEAN432_BIN:-/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean}
EXPECTED_AENEAS=b59d5188c082f704a418c7cb4e52ad69328002d1
GEN="$BUNDLE/generated/final-sampler-helper"
LLBC="$BUNDLE/llbc/component_b_sampler_mixing_evaluate_unified_20260722.llbc"
MANIFEST="$BUNDLE/metadata/SHA256SUMS"

if test -n "${COMPONENT_B_REPLAY_OUT:-}"; then
  OUT=$COMPONENT_B_REPLAY_OUT
  mkdir -p "$OUT"
  if test -n "$(find "$OUT" -mindepth 1 -maxdepth 1 -print -quit)"; then
    echo "COMPONENT_B_REPLAY_OUT must be empty" >&2
    exit 1
  fi
else
  OUT=$(mktemp -d /private/tmp/component-b-unified-replay.XXXXXX)
fi
LOG="$OUT/lean432-clean-replay.log"

test -x "$LEAN_BIN"
test "$(git -C "$AENEAS432_BACKEND" rev-parse HEAD)" = "$EXPECTED_AENEAS"
case "$($LEAN_BIN --version)" in
  "Lean (version 4.32.0,"*) ;;
  *) echo "expected Lean 4.32.0" >&2; exit 1 ;;
esac

if test -f "$MANIFEST"; then
  (cd "$BUNDLE" && shasum -a 256 -c metadata/SHA256SUMS)
fi

jq -e '.has_errors == false and
  (.translated.ordered_decls | length) == 129 and
  (.translated.files | length) == 68' "$LLBC" >/dev/null

for source in \
  crates/aspis-prover/src/v5_sumcheck_mask.rs \
  crates/aspis-prover/src/v5_mask.rs
do
  target="$OUT/embedded-$(basename "$source")"
  jq -j --arg source "$source" '.translated.files[] |
    select(.name.Local == $source) | .contents' "$LLBC" > "$target"
  cmp "$ROOT/$source" "$target"
done

# Cross-crate file records carry exact spans but Charon does not embed their
# bytes in this cargo-root LLBC.  Bind them to the extraction-time hashes.
test "$(shasum -a 256 "$ROOT/crates/aspis-core/src/state_only_sumcheck.rs" |
  awk '{print $1}')" = 5458d3134a3123b8b02bef0374ccbf96a05461974d7e274966c6a3f0d2d496f9
test "$(shasum -a 256 "$ROOT/crates/aspis-core/src/field.rs" |
  awk '{print $1}')" = dadd6bac7c6c44fcb13e1a1ca26e9d2b6f767370bb6e802640948f15fc795836

(diff -u --label Types.raw.lean --label Types.lean \
    "$BUNDLE/generated/sampler-helper-raw/Types.lean" \
    "$GEN/ComponentBSamplerMixingEvaluateUnified20260722/Types.lean" || true
 diff -u --label Funs.raw.lean --label Funs.lean \
    "$BUNDLE/generated/sampler-helper-raw/Funs.lean" \
    "$GEN/ComponentBSamplerMixingEvaluateUnified20260722/Funs.lean" || true) |
  sed 's/[[:space:]]*$//' > "$OUT/lean432-normalization.diff"
cmp "$GEN/lean432-normalization.diff" "$OUT/lean432-normalization.diff"

if rg -n '\b(sorry|admit|native_decide|axiom|unsafe|ofReduceBool)\b|set_option max(Heartbeats|RecDepth)' \
    "$BUNDLE/proof" \
    "$GEN/ComponentBSamplerMixingEvaluateUnified20260722.lean" \
    "$GEN/ComponentBSamplerMixingEvaluateUnified20260722/Types.lean" \
    "$GEN/ComponentBSamplerMixingEvaluateUnified20260722/Funs.lean"
then
  echo "forbidden token or raised proof limit" >&2
  exit 1
fi

find "$BUNDLE/proof" -type f -name '*.lean' -print0 |
  xargs -0 rg --no-filename '^(@\[[^]]+\] )?theorem ' |
  sed -E 's/^(@\[[^]]+\] )?theorem ([^ (]+).*/\2/' | sort \
  > "$OUT/theorems"
find "$BUNDLE/proof" -type f -name '*.lean' -print0 |
  xargs -0 rg --no-filename '^#print axioms ' |
  sed -E 's/^#print axioms ([^ .]+\.)*([^ .]+).*/\2/' | sort \
  > "$OUT/audits"
diff -u "$OUT/theorems" "$OUT/audits"
test "$(wc -l < "$OUT/theorems" | tr -d ' ')" = 200

AENEAS_PATH=$(cd "$AENEAS432_BACKEND" && lake env printenv LEAN_PATH)
ASPIS_PATH=$(cd "$ROOT/AspisFormal" && lake env printenv LEAN_PATH)
PROOF_PATH="$BUNDLE/proof:$BUNDLE/proof/deps:$BUNDLE/proof/retarget:$BUNDLE/proof/mixing:$BUNDLE/proof/terminal:$BUNDLE/proof/sampler"
export LEAN_PATH="$OUT:$GEN:$PROOF_PATH:$ASPIS_PATH:$AENEAS_PATH"

mkdir -p "$OUT/ComponentBSamplerMixingEvaluateUnified20260722"
for module in Types Funs; do
  echo "COMPILE generated/$module" >> "$LOG"
  "$LEAN_BIN" -R "$GEN" \
    -o "$OUT/ComponentBSamplerMixingEvaluateUnified20260722/$module.olean" \
    "$GEN/ComponentBSamplerMixingEvaluateUnified20260722/$module.lean" \
    >> "$LOG" 2>&1
done
echo "COMPILE generated/root" >> "$LOG"
"$LEAN_BIN" -R "$GEN" \
  -o "$OUT/ComponentBSamplerMixingEvaluateUnified20260722.olean" \
  "$GEN/ComponentBSamplerMixingEvaluateUnified20260722.lean" \
  >> "$LOG" 2>&1

MODULES="
ComponentBMixingProof
AspisCoreFieldReduceU64
M31ReduceU64Proof
ComponentBBoundaryProof
ComponentBHalfProof
ComponentBEndpointProof
ComponentBRoundMixingProof
MLEBFormulaPrelude
AspisCoreCm31Multiplicative
AspisCoreFieldMulNamespaced
M31MulProof
CM31ExactModel
CM31MultiplicativeProof
MultilinearEvalFormula
ComponentBMixedEndpointProof
ComponentBEvaluatorFieldBridge
ComponentBEvaluatorOperationalProof
ComponentBEvaluatorProof
ComponentBEvaluatorCorrespondence
ComponentBPublicEvaluateRecurrence
ComponentBHalfCombinedProof
ComponentBRoundCombinedProof
ComponentBMaintainedTerminalBridge
ComponentBGeneratedBoundaryBridge
ComponentBDegree27CoordinateFormulaD1E7
ComponentBOptimizedPrimitiveBridge
SumProductsArithmetic
SumProductsLoop
SumProductsComponentLoop
SumProductsFullCorrespondence
ComponentBSumProducts3GeneratedCorrespondence
ComponentBCurrentFieldEvaluatorCorrespondence
ComponentBMaintainedTerminalCapstone
ComponentBUnifiedTransportFree
ComponentBUnifiedTeeth
ComponentBSumProducts3OperationalAdapterD1E7
ComponentBOperationalPrimitiveCapstoneD1E7
HalfShiftCountAdapter
AspisCoreHalf
AspisCoreFieldAddSubNeg
HalfProof
QM31AddSubNegProof
ComponentBSamplerZeroBoundary
ComponentBSamplerMaintainedPredicatesBridge
ComponentBSamplerTerminalCapstone
ComponentBSamplerUnifiedCapstone
ComponentBAllTheoremAxiomAudit
"

for module in $MODULES; do
  source=$(find "$BUNDLE/proof" -type f -name "$module.lean" -print)
  test "$(printf '%s\n' "$source" | wc -l | tr -d ' ')" = 1
  echo "COMPILE $module" >> "$LOG"
  "$LEAN_BIN" -R "$BUNDLE/proof" -o "$OUT/$module.olean" "$source" \
    >> "$LOG" 2>&1
done

test "$(find "$OUT" -type f -name '*.olean' | wc -l | tr -d ' ')" = 50
test "$(rg -c "^'[^']+' (depends on axioms|does not depend on any axioms)" "$LOG")" = 200
if rg -n 'sorryAx' "$LOG"; then
  echo "sorryAx in axiom closure" >&2
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

echo "Lean 4.32 clean replay passed: 129 LLBC declarations, 50 oleans, 200/200 theorem audits"
echo "log: $LOG"
