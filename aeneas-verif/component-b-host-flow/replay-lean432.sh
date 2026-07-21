#!/bin/sh
set -eu

ROOT=${REPO_ROOT:-/Users/dominic/ZK}
BUNDLE="$ROOT/aeneas-verif/component-b-host-flow"
MASK_BUNDLE="$ROOT/aeneas-verif/component-b-mask"
ARITH_SOURCE=${COMPONENT_B_ARITH432_SOURCE:-$ROOT/aeneas-verif/component-b-weight-at/arithmetic-lean432}
AENEAS432_BACKEND=${AENEAS432_BACKEND:-/private/tmp/aspis-aeneas-lean432-check.p116iK/aeneas/backends/lean}
LEAN_BIN=${LEAN432_BIN:-/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean}
EXPECTED_AENEAS=b59d5188c082f704a418c7cb4e52ad69328002d1
OUT=$(mktemp -d /private/tmp/component-b-host-flow-replay.XXXXXX)
BASE_LOG="$OUT/base-replay.stdout"
LOG="$OUT/host-capstone.log"
cleanup() {
  status=$?
  trap - EXIT
  if test "$status" -ne 0; then
    test ! -f "$BASE_LOG" || cat "$BASE_LOG" >&2
    test ! -f "$LOG" || cat "$LOG" >&2
  fi
  rm -rf "$OUT"
  exit "$status"
}
trap cleanup EXIT
trap 'exit 1' HUP INT TERM

test -x "$LEAN_BIN"
test "$(git -C "$AENEAS432_BACKEND" rev-parse HEAD)" = "$EXPECTED_AENEAS"
case "$($LEAN_BIN --version)" in
  "Lean (version 4.32.0,"*) ;;
  *) echo "expected Lean 4.32.0" >&2; exit 1 ;;
esac

(cd "$BUNDLE" && shasum -a 256 -c metadata/SHA256SUMS)

HOST_LLBC="$BUNDLE/llbc/bound_mask_flow.llbc"
SAMPLER_LLBC="$MASK_BUNDLE/llbc/component_b_v5_sampler_authenticated_constants_20260721.llbc"
jq -e '.has_errors == false and (.translated.ordered_decls | length) == 10' \
  "$HOST_LLBC" >/dev/null
jq -e '.has_errors == false and (.translated.ordered_decls | length) == 88' \
  "$SAMPLER_LLBC" >/dev/null
jq -j '.translated.files[]
  | select(.name.Local == "crates/aspis-prover/src/v5_real_host_proof.rs")
  | .contents' "$HOST_LLBC" > "$OUT/host-embedded-source.rs"
cmp "$ROOT/crates/aspis-prover/src/v5_real_host_proof.rs" \
  "$OUT/host-embedded-source.rs"
jq -j '.translated.files[]
  | select(.name.Local == "crates/aspis-prover/src/v5_sumcheck_mask.rs")
  | .contents' "$SAMPLER_LLBC" > "$OUT/sampler-embedded-source.rs"
cmp "$ROOT/crates/aspis-prover/src/v5_sumcheck_mask.rs" \
  "$OUT/sampler-embedded-source.rs"

# Rebuild and audit the current-source evaluator/maintained-terminal base in
# this same output root.  The base replay owns its 49-theorem source audit and
# 74 axiom-record audit; COMPONENT_B_REPLAY_OUT makes its verified oleans
# available for the sampler/host composition below.
COMPONENT_B_REPLAY_OUT="$OUT" \
COMPONENT_B_REPLAY_MANIFEST=metadata/SHA256SUMS \
REPO_ROOT="$ROOT" \
AENEAS432_BACKEND="$AENEAS432_BACKEND" \
LEAN432_BIN="$LEAN_BIN" \
COMPONENT_B_ARITH432_SOURCE="$ARITH_SOURCE" \
  "$MASK_BUNDLE/replay-lean432.sh" > "$BASE_LOG" 2>&1

AENEAS_PATH=$(cd "$AENEAS432_BACKEND" && lake env printenv LEAN_PATH)
ASPIS_PATH=$(cd "$ROOT/AspisFormal" && lake env printenv LEAN_PATH)
LEAN_PATH="$OUT:$ASPIS_PATH:$AENEAS_PATH"

# The half extraction is already source-authenticated by its owning arithmetic
# bundle.  Strip only Aeneas generation-resource declarations; all handwritten
# files compile at Lean's default limits.
cp "$ARITH_SOURCE/HalfShiftCountAdapter.lean" "$OUT/"
sed -e '/^set_option maxHeartbeats /d' \
    -e '/^set_option maxRecDepth /d' \
  "$ARITH_SOURCE/AspisCoreHalf.lean" > "$OUT/AspisCoreHalf.lean"
cp "$ARITH_SOURCE/HalfProof.lean" "$OUT/"

mkdir -p "$OUT/ComponentBV5SamplerAuthenticatedConstants20260721"
cp "$MASK_BUNDLE/generated/ComponentBV5SamplerAuthenticatedConstants20260721/Types.lean" \
  "$OUT/ComponentBV5SamplerAuthenticatedConstants20260721/"
cp "$MASK_BUNDLE/generated/ComponentBV5SamplerAuthenticatedConstants20260721/Funs.lean" \
  "$OUT/ComponentBV5SamplerAuthenticatedConstants20260721/"

SAMPLER_PROOFS="
ComponentBSamplerZeroBoundary
ComponentBSamplerMaintainedPredicatesBridge
ComponentBSamplerTerminalCapstone
"
HOST_PROOFS="
BoundMaskFlowCorrespondence
ComponentBSamplerHostFlowTerminalCapstone
"
for module in $SAMPLER_PROOFS; do
  cp "$MASK_BUNDLE/proof/$module.lean" "$OUT/"
done
for module in $HOST_PROOFS; do
  cp "$BUNDLE/proof/$module.lean" "$OUT/"
done

sed -e 's/^import Aeneas$/import Aeneas.Std\
import Aeneas.Tactic.RustAttributes/' \
    -e 's/^namespace aspis_prover$/namespace ComponentBHostFlowGenerated/' \
    -e 's/^end aspis_prover$/end ComponentBHostFlowGenerated/' \
    -e '/^set_option maxHeartbeats /d' \
    -e '/^set_option maxRecDepth /d' \
  "$BUNDLE/generated/bound-mask-flow/BoundMaskFlow.lean" \
  > "$OUT/BoundMaskFlow.lean"

if rg -n '\b(sorry|admit|native_decide|axiom|unsafe|ofReduceBool)\b|set_option[[:space:]]+(maxHeartbeats|maxRecDepth)' \
    "$OUT/HalfShiftCountAdapter.lean" "$OUT/AspisCoreHalf.lean" \
    "$OUT/HalfProof.lean" \
    "$OUT/ComponentBV5SamplerAuthenticatedConstants20260721/Types.lean" \
    "$OUT/ComponentBV5SamplerAuthenticatedConstants20260721/Funs.lean" \
    "$OUT/ComponentBSamplerZeroBoundary.lean" \
    "$OUT/ComponentBSamplerMaintainedPredicatesBridge.lean" \
    "$OUT/ComponentBSamplerTerminalCapstone.lean" \
    "$OUT/BoundMaskFlow.lean" "$OUT/BoundMaskFlowCorrespondence.lean" \
    "$OUT/ComponentBSamplerHostFlowTerminalCapstone.lean"
then
  echo "forbidden proof token or raised handwritten limit" >&2
  exit 1
fi

: > "$OUT/extra-theorems"
: > "$OUT/extra-audits"
for file in HalfShiftCountAdapter HalfProof \
  ComponentBSamplerZeroBoundary ComponentBSamplerMaintainedPredicatesBridge \
  ComponentBSamplerTerminalCapstone BoundMaskFlowCorrespondence \
  ComponentBSamplerHostFlowTerminalCapstone
do
  rg --no-filename '^(@\[[^]]+\][[:space:]]+)?theorem ' "$OUT/$file.lean" \
    | sed -E 's/^(@\[[^]]+\][[:space:]]+)?theorem ([^ (]+).*/\2/' \
    >> "$OUT/extra-theorems"
  rg --no-filename '^#print axioms ' "$OUT/$file.lean" \
    | sed -E 's/^#print axioms ([^ ]+).*/\1/' >> "$OUT/extra-audits"
done
sort -o "$OUT/extra-theorems" "$OUT/extra-theorems"
sort -o "$OUT/extra-audits" "$OUT/extra-audits"
diff -u "$OUT/extra-theorems" "$OUT/extra-audits"
test "$(wc -l < "$OUT/extra-theorems" | tr -d ' ')" -eq 50

for module in HalfShiftCountAdapter AspisCoreHalf HalfProof; do
  LEAN_PATH="$LEAN_PATH" "$LEAN_BIN" -R "$OUT" -o "$OUT/$module.olean" \
    "$OUT/$module.lean" >> "$LOG" 2>&1
done
for module in Types Funs; do
  LEAN_PATH="$LEAN_PATH" "$LEAN_BIN" -R "$OUT" \
    -o "$OUT/ComponentBV5SamplerAuthenticatedConstants20260721/$module.olean" \
    "$OUT/ComponentBV5SamplerAuthenticatedConstants20260721/$module.lean" \
    >> "$LOG" 2>&1
done
for module in $SAMPLER_PROOFS; do
  LEAN_PATH="$LEAN_PATH" "$LEAN_BIN" -R "$OUT" -o "$OUT/$module.olean" \
    "$OUT/$module.lean" >> "$LOG" 2>&1
done
LEAN_PATH="$LEAN_PATH" "$LEAN_BIN" -R "$OUT" \
  -o "$OUT/BoundMaskFlow.olean" "$OUT/BoundMaskFlow.lean" >> "$LOG" 2>&1
for module in $HOST_PROOFS; do
  LEAN_PATH="$LEAN_PATH" "$LEAN_BIN" -R "$OUT" -o "$OUT/$module.olean" \
    "$OUT/$module.lean" >> "$LOG" 2>&1
done

cat "$BASE_LOG"
cat "$LOG"

if rg -n 'sorryAx' "$LOG"; then
  echo "sorryAx in sampler/host capstone replay" >&2
  exit 1
fi
if rg -n '(^|/)(BoundMaskFlow|BoundMaskFlowCorrespondence|ComponentBSamplerHostFlowTerminalCapstone)\.lean:.*warning:' \
    "$LOG"; then
  echo "warning in host-flow or final-capstone replay" >&2
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
if test "$AXIOM_RECORD_COUNT" -ne 50; then
  echo "expected 50 additional axiom records, found $AXIOM_RECORD_COUNT" >&2
  exit 1
fi

echo "PASS: authentic Component-B sample -> immutable real-host roles -> maintained terminal replayed on Lean 4.32"
