#!/bin/sh
set -eu

: "${AENEAS432_BACKEND:?set to the patched Aeneas b59d5188 backends/lean directory}"

ROOT=${REPO_ROOT:-/Users/dominic/ZK}
BUNDLE="$ROOT/aeneas-verif/component-b-mask"
ARITH_SOURCE=${COMPONENT_B_ARITH432_SOURCE:-$ROOT/aeneas-verif/component-b-weight-at/arithmetic-lean432}
LEAN_BIN=${LEAN432_BIN:-/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean}
EXPECTED_AENEAS=b59d5188c082f704a418c7cb4e52ad69328002d1
SPLIT="$BUNDLE/generated/v5-evaluate-current-split-20260722"
GENERATED_DEPS="$BUNDLE/generated-deps/current-20260722"
MANIFEST=${COMPONENT_B_REPLAY_MANIFEST:-metadata/SHA256SUMS}
if test -n "${COMPONENT_B_REPLAY_OUT:-}"; then
  OUT=$COMPONENT_B_REPLAY_OUT
  mkdir -p "$OUT"
  PRESERVE_OUT=1
else
  OUT=$(mktemp -d /private/tmp/component-b-mask-replay.XXXXXX)
  PRESERVE_OUT=0
fi
LOG="$OUT/lean432-replay.log"
cleanup() {
  status=$?
  trap - EXIT
  if test "$status" -ne 0 && test -f "$LOG"; then
    cat "$LOG" >&2
  fi
  if test "$PRESERVE_OUT" -eq 0; then
    rm -rf "$OUT"
  fi
  exit "$status"
}
trap cleanup EXIT
trap 'exit 1' HUP INT TERM

(test -x "$LEAN_BIN")
test "$(git -C "$AENEAS432_BACKEND" rev-parse HEAD)" = "$EXPECTED_AENEAS"
case "$($LEAN_BIN --version)" in
  "Lean (version 4.32.0,"*) ;;
  *) echo "expected Lean 4.32.0" >&2; exit 1 ;;
esac
(cd "$BUNDLE" && shasum -a 256 -c "$MANIFEST")
(cd "$ARITH_SOURCE" && shasum -a 256 -c SOURCE_MANIFEST.sha256)

# Bind the generated evaluator to the exact current candidate wrapper and the
# exact core reverse-fold implementation used by this extraction.  Charon
# embeds the wrapper bytes; the cross-crate core file is recorded by hash
# because its file record carries source spans but no embedded contents.
EVALUATOR_LLBC="$BUNDLE/llbc/component_b_v5_evaluate_current_20260722.llbc"
jq -e '.has_errors == false and (.translated.ordered_decls | length) == 101' \
  "$EVALUATOR_LLBC" >/dev/null
jq -j '.translated.files[]
  | select(.name.Local == "crates/aspis-prover/src/v5_sumcheck_mask.rs")
  | .contents' "$EVALUATOR_LLBC" > "$OUT/evaluator-embedded-wrapper.rs"
cmp "$ROOT/crates/aspis-prover/src/v5_sumcheck_mask.rs" \
  "$OUT/evaluator-embedded-wrapper.rs"
EXPECTED_CORE_SOURCE=5458d3134a3123b8b02bef0374ccbf96a05461974d7e274966c6a3f0d2d496f9
ACTUAL_CORE_SOURCE=$(shasum -a 256 \
  "$ROOT/crates/aspis-core/src/state_only_sumcheck.rs" | awk '{print $1}')
test "$ACTUAL_CORE_SOURCE" = "$EXPECTED_CORE_SOURCE"

for module in AspisCoreFieldAddSubNeg AspisCoreFieldReduceU64 \
  AspisCoreFieldMulNamespaced AspisCoreCm31Multiplicative
do
  cmp "$ARITH_SOURCE/$module.lean" "$GENERATED_DEPS/raw/$module.lean"
  sed -e '/maxHeartbeats/d' -e '/maxRecDepth/d' \
    "$GENERATED_DEPS/raw/$module.lean" > "$OUT/$module.normalized.lean"
  cmp "$GENERATED_DEPS/normalized/$module.lean" \
    "$OUT/$module.normalized.lean"
done

(diff -u --label Types.raw.lean --label Types.lean \
    "$SPLIT/Types.raw.lean" \
    "$SPLIT/ComponentBV5EvaluateCurrent20260722/Types.lean" || true
 diff -u --label Funs.raw.lean --label Funs.lean \
    "$SPLIT/Funs.raw.lean" \
    "$SPLIT/ComponentBV5EvaluateCurrent20260722/Funs.lean" || true) \
  | sed 's/[[:space:]]*$//' \
  > "$OUT/current-generated-normalization.diff"
cmp "$SPLIT/lean432-normalization.diff" \
  "$OUT/current-generated-normalization.diff"

ARITH_MODULES="
AspisCoreFieldReduceU64
M31ReduceU64Proof
AspisCoreFieldMulNamespaced
M31MulProof
CM31ExactModel
AspisCoreCm31Multiplicative
CM31MultiplicativeProof
"
RETARGET_MODULES="
SumProductsArithmetic
SumProductsLoop
SumProductsComponentLoop
SumProductsFullCorrespondence
"
PROOF_MODULES="
ComponentBEvaluatorFieldBridge
ComponentBEvaluatorProof
ComponentBEvaluatorOperationalProof
ComponentBEvaluatorCorrespondence
ComponentBPublicEvaluateRecurrence
ComponentBHalfCombinedProof
ComponentBRoundCombinedProof
ComponentBOptimizedPrimitiveBridge
ComponentBSumProducts3OperationalAdapterD1E7
ComponentBOperationalPrimitiveCapstoneD1E7
ComponentBSumProducts3GeneratedCorrespondence
ComponentBCurrentFieldEvaluatorCorrespondence
ComponentBMaintainedTerminalBridge
ComponentBDegree27CoordinateFormulaD1E7
ComponentBMaintainedTerminalCapstone
"
for module in $RETARGET_MODULES; do
  if rg -n '\b(sorry|admit|native_decide|axiom|unsafe|ofReduceBool)\b|maxHeartbeats|maxRecDepth' \
      "$BUNDLE/retarget-test/$module.lean"; then
    echo "forbidden token in retained retarget proof: $module" >&2
    exit 1
  fi
done
for module in $PROOF_MODULES; do
  if rg -n '\b(sorry|admit|native_decide|axiom|unsafe|ofReduceBool)\b|maxHeartbeats|maxRecDepth' \
      "$BUNDLE/proof/$module.lean"; then
    echo "forbidden token in retained handwritten proof: $module" >&2
    exit 1
  fi
done
for module in M31ReduceU64Proof M31MulProof CM31ExactModel \
  CM31MultiplicativeProof QM31AddSubNegProof
do
  if rg -n '\b(sorry|admit|native_decide|axiom|unsafe|ofReduceBool)\b|maxHeartbeats|maxRecDepth' \
      "$ARITH_SOURCE/$module.lean"; then
    echo "forbidden token in authenticated arithmetic proof dependency: $module" >&2
    exit 1
  fi
done
if rg -n '\b(sorry|admit|native_decide|axiom|unsafe|ofReduceBool)\b|maxHeartbeats|maxRecDepth' \
    "$GENERATED_DEPS/normalized"/*.lean
then
  echo "forbidden token or raised limit in normalized generated arithmetic dependency" >&2
  exit 1
fi
if rg -n '\b(sorry|admit|native_decide|unsafe|ofReduceBool)\b|maxHeartbeats|maxRecDepth' \
    "$SPLIT/ComponentBV5EvaluateCurrent20260722.lean" \
    "$SPLIT/ComponentBV5EvaluateCurrent20260722/Types.lean" \
    "$SPLIT/ComponentBV5EvaluateCurrent20260722/Funs.lean"
then
  echo "forbidden token or raised proof limit in normalized generated module" >&2
  exit 1
fi

: > "$OUT/theorems"
: > "$OUT/audits"
for module in $RETARGET_MODULES; do
  rg --no-filename '^(@\[[^]]+\] )?theorem ' "$BUNDLE/retarget-test/$module.lean" \
    | sed -E 's/^(@\[[^]]+\] )?theorem ([^ (]+).*/\2/' >> "$OUT/theorems"
  rg --no-filename '^#print axioms ' "$BUNDLE/retarget-test/$module.lean" \
    | sed -E 's/^#print axioms ([^ ]+).*/\1/' >> "$OUT/audits"
done
for module in $PROOF_MODULES; do
  rg --no-filename '^(@\[[^]]+\] )?theorem ' "$BUNDLE/proof/$module.lean" \
    | sed -E 's/^(@\[[^]]+\] )?theorem ([^ (]+).*/\2/' >> "$OUT/theorems"
  rg --no-filename '^#print axioms ' "$BUNDLE/proof/$module.lean" \
    | sed -E 's/^#print axioms ([^ ]+).*/\1/' >> "$OUT/audits"
done
sort -o "$OUT/theorems" "$OUT/theorems"
sort -o "$OUT/audits" "$OUT/audits"
if ! diff -u "$OUT/theorems" "$OUT/audits"; then
  echo "exported theorem/#print axioms coverage mismatch" >&2
  exit 1
fi
THEOREM_COUNT=$(wc -l < "$OUT/theorems" | tr -d ' ')
if test "$THEOREM_COUNT" -ne 49; then
  echo "expected 49 exported theorems, found $THEOREM_COUNT" >&2
  exit 1
fi

AENEAS_PATH=$(cd "$AENEAS432_BACKEND" && lake env printenv LEAN_PATH)
LEAN_PATH="$OUT:$AENEAS_PATH"

# The additive extraction and the reducer extraction each own the same Rust
# declarations.  Replay the additive one under a collision-free namespace;
# the proof body is otherwise byte-for-byte unchanged.
sed -e 's/^namespace aspis_core$/namespace AspisCoreAdditive/' \
    -e 's/^end aspis_core$/end AspisCoreAdditive/' \
  "$GENERATED_DEPS/normalized/AspisCoreFieldAddSubNeg.lean" \
  > "$OUT/AspisCoreFieldAddSubNeg.lean"
sed -e 's/^open aspis_core$/open AspisCoreAdditive/' \
  "$ARITH_SOURCE/QM31AddSubNegProof.lean" \
  > "$OUT/QM31AddSubNegProof.lean"
for module in AspisCoreFieldAddSubNeg QM31AddSubNegProof; do
  LEAN_PATH="$LEAN_PATH" "$LEAN_BIN" -R "$OUT" -o "$OUT/$module.olean" \
    "$OUT/$module.lean" >> "$LOG" 2>&1
done

for module in $ARITH_MODULES; do
  case "$module" in
    AspisCoreFieldReduceU64|AspisCoreFieldMulNamespaced|AspisCoreCm31Multiplicative)
      cp "$GENERATED_DEPS/normalized/$module.lean" "$OUT/"
      ;;
    *)
      cp "$ARITH_SOURCE/$module.lean" "$OUT/"
      ;;
  esac
  LEAN_PATH="$LEAN_PATH" "$LEAN_BIN" -R "$OUT" -o "$OUT/$module.olean" \
    "$OUT/$module.lean" >> "$LOG" 2>&1
done

mkdir -p "$OUT/ComponentBV5EvaluateCurrent20260722"
cp "$SPLIT/ComponentBV5EvaluateCurrent20260722.lean" "$OUT/"
cp "$SPLIT/ComponentBV5EvaluateCurrent20260722/Types.lean" \
  "$OUT/ComponentBV5EvaluateCurrent20260722/"
cp "$SPLIT/ComponentBV5EvaluateCurrent20260722/Funs.lean" \
  "$OUT/ComponentBV5EvaluateCurrent20260722/"
for module in Types Funs; do
  LEAN_PATH="$LEAN_PATH" "$LEAN_BIN" -R "$OUT" \
    -o "$OUT/ComponentBV5EvaluateCurrent20260722/$module.olean" \
    "$OUT/ComponentBV5EvaluateCurrent20260722/$module.lean" \
    >> "$LOG" 2>&1
done
LEAN_PATH="$LEAN_PATH" "$LEAN_BIN" -R "$OUT" \
  -o "$OUT/ComponentBV5EvaluateCurrent20260722.olean" \
  "$OUT/ComponentBV5EvaluateCurrent20260722.lean" >> "$LOG" 2>&1

for module in $RETARGET_MODULES; do
  cp "$BUNDLE/retarget-test/$module.lean" "$OUT/"
  LEAN_PATH="$LEAN_PATH" "$LEAN_BIN" -R "$OUT" -o "$OUT/$module.olean" \
    "$OUT/$module.lean" >> "$LOG" 2>&1
done

for module in $PROOF_MODULES; do
  cp "$BUNDLE/proof/$module.lean" "$OUT/"
done
for module in ComponentBEvaluatorFieldBridge ComponentBEvaluatorProof \
  ComponentBEvaluatorOperationalProof ComponentBEvaluatorCorrespondence \
  ComponentBPublicEvaluateRecurrence ComponentBHalfCombinedProof \
  ComponentBRoundCombinedProof ComponentBOptimizedPrimitiveBridge \
  ComponentBSumProducts3OperationalAdapterD1E7 \
  ComponentBOperationalPrimitiveCapstoneD1E7 \
  ComponentBSumProducts3GeneratedCorrespondence \
  ComponentBCurrentFieldEvaluatorCorrespondence
do
  LEAN_PATH="$LEAN_PATH" "$LEAN_BIN" -R "$OUT" -o "$OUT/$module.olean" \
    "$OUT/$module.lean" >> "$LOG" 2>&1
done

ASPIS_PATH=$(cd "$ROOT/AspisFormal" && lake env printenv LEAN_PATH)
LEAN_PATH="$OUT:$ASPIS_PATH:$AENEAS_PATH" "$LEAN_BIN" -R "$OUT" \
  -o "$OUT/ComponentBMaintainedTerminalBridge.olean" \
  "$OUT/ComponentBMaintainedTerminalBridge.lean" >> "$LOG" 2>&1

for module in ComponentBDegree27CoordinateFormulaD1E7 \
  ComponentBMaintainedTerminalCapstone
do
  LEAN_PATH="$OUT:$ASPIS_PATH:$AENEAS_PATH" "$LEAN_BIN" -R "$OUT" \
    -o "$OUT/$module.olean" "$OUT/$module.lean" >> "$LOG" 2>&1
done

cat "$LOG"

if rg -n 'sorryAx' "$LOG"; then
  echo "sorryAx in axiom audit" >&2
  exit 1
fi

awk '
  /depends on axioms:/ {
    inside = 1
    sub(/^.*depends on axioms: \[/, "")
  }
  inside {
    closes = index($0, "]")
    line = $0
    sub(/].*$/, "", line)
    count = split(line, names, ",")
    for (ix = 1; ix <= count; ix++) {
      name = names[ix]
      gsub(/^[[:space:]]+|[[:space:]]+$/, "", name)
      if (name != "") print name
    }
    if (closes != 0) inside = 0
  }
' "$LOG" | sort -u | \
  grep -v -E '^(propext|Classical\.choice|Quot\.sound)$' \
  > "$OUT/unexpected-axioms.log" || true
if test -s "$OUT/unexpected-axioms.log"; then
  cat "$OUT/unexpected-axioms.log" >&2
  echo "unallowed axiom dependency" >&2
  exit 1
fi

AXIOM_RECORD_COUNT=$(rg -c \
  'depends on axioms:|does not depend on any axioms' "$LOG")
if test "$AXIOM_RECORD_COUNT" -ne 74; then
  echo "expected 74 axiom records, found $AXIOM_RECORD_COUNT" >&2
  exit 1
fi

echo "PASS: Component-B current-source evaluator and maintained terminal capstone replayed on Lean 4.32"
