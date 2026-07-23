#!/bin/sh
set -eu

BUNDLE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
ROOT=$(CDPATH= cd -- "$BUNDLE/../.." && pwd)
LEAN_BIN=${LEAN432_BIN:-/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean}
AENEAS_LIB="$ROOT/aeneas-verif/component-a-encoder-eval-residual/capstone/.lake/build/lib/lean"
ASPIS_PATH=$(cd "$ROOT/AspisFormal" && NO_DNA=1 lake env printenv LEAN_PATH)

GOOD_A_SOURCE="$BUNDLE/gooda-generated-split-root"
GOOD_A_LEGACY_CACHE="$ROOT/aeneas-lane2/component-a-gooda-matrix-current/generated-split-root"
INSTALLER_SOURCE="$BUNDLE/component-b-installer/ComponentBInstallerShared.lean"
INSTALLER_DEPS="$BUNDLE/component-b-installer/deps"
B_PIPELINE="$ROOT/aeneas-verif/component-b-mask/deterministic-pipeline-current-20260722"
B_LAYOUT="$ROOT/aeneas-verif/component-b-layout-bindings"
B_UNIFIED="$ROOT/aeneas-verif/component-b-mask/unified-current-20260722"
C_RUNTIME="$ROOT/aeneas-verif/component-c-runtime-downstream"
C_CANONICAL="$C_RUNTIME/relation-table-canonical-current-20260722/generated/normalized"
C_PUBLIC="$C_RUNTIME/released-trace-families-current-20260722"
TAG67="$ROOT/aeneas-verif/tag67-work-wire-correspondence"

if test -n "${FORMAL_CLOSURE_REPLAY_OUT:-}"; then
  OUT=$FORMAL_CLOSURE_REPLAY_OUT
  mkdir -p "$OUT"
  test -z "$(find "$OUT" -mindepth 1 -maxdepth 1 -print -quit)"
else
  OUT=$(mktemp -d /private/tmp/formal-closure-stream1.XXXXXX)
fi
LOG="$OUT/lean432.log"

if test -n "${COMPONENT_C_OLEAN_DIR:-}"; then
  C_PUBLIC_OLEAN=$COMPONENT_C_OLEAN_DIR
  test -f "$C_PUBLIC_OLEAN/RuntimeReleasedTraceFamiliesCurrentJoin.olean"
else
  C_PUBLIC_OLEAN="$OUT/component-c-public"
  COMPONENT_C_REPLAY_OUT="$C_PUBLIC_OLEAN" \
    "$C_PUBLIC/replay-lean432.sh"
fi

case "$($LEAN_BIN --version)" in
  "Lean (version 4.32.0,"*) ;;
  *) echo "expected Lean 4.32.0" >&2; exit 1 ;;
esac
test -f "$AENEAS_LIB/Aeneas/Std.olean"

compile() {
  module=$1
  source=$2
  echo "COMPILE $module" >> "$LOG"
  "$LEAN_BIN" -j 1 -o "$OUT/$module.olean" "$source" >> "$LOG" 2>&1
}

export LEAN_PATH="$OUT:$B_UNIFIED/olean-sampler-helper:$B_PIPELINE/olean-deps:$ASPIS_PATH:$AENEAS_LIB"

# The accepted Component-B capstone did not persist its terminal olean.  Build
# only its direct import boundary into this isolated output directory.
compile MultilinearEvalFormula "$B_PIPELINE/generated/MultilinearEvalFormula.lean"
compile ComponentBLayoutBindingsGenerated "$B_PIPELINE/generated/ComponentBLayoutBindingsGenerated.lean"
compile ComponentBLayoutBindingsProof "$B_LAYOUT/proof/ComponentBLayoutBindingsProof.lean"
compile ComponentBEncodedMessageBindingProof "$B_LAYOUT/proof/ComponentBEncodedMessageBindingProof.lean"
compile ComponentBC2SlotGenerated "$B_LAYOUT/c2-slot/generated/lean432/ComponentBC2SlotGenerated.lean"
compile ComponentBC2SlotProof "$B_LAYOUT/c2-slot/proof/ComponentBC2SlotProof.lean"
compile ComponentBRelationClaimsLayoutInstantiation "$B_LAYOUT/c2-slot/proof/ComponentBRelationClaimsLayoutInstantiation.lean"
compile ComponentBDeterministicPipelineCapstone "$B_PIPELINE/proof/ComponentBDeterministicPipelineCapstone.lean"

# GoodA's historical installer and current Component B share the exact same
# global field modulus declaration, while their additive support modules have
# different authenticated namespace labels.  Mechanically reuse the loaded
# current declaration and namespace; all executable bodies remain unchanged.
compile FieldHalf "$INSTALLER_DEPS/FieldHalf.lean"
compile FieldPow "$INSTALLER_DEPS/FieldPow.lean"
compile AspisCoreFieldMul "$INSTALLER_DEPS/AspisCoreFieldMul.lean"
awk '
  NR == 10 { print "import AspisCoreFieldReduceU64" }
  (NR >= 15 && NR <= 19) || (NR >= 34 && NR <= 37) { next }
  { gsub(/AuthenticFieldSub/, "AspisCoreAdditive"); print }
' "$INSTALLER_SOURCE" \
  > "$OUT/ComponentBInstallerShared.lean"
export LEAN_PATH="$OUT:$B_UNIFIED/olean-sampler-helper:$B_PIPELINE/olean-deps:$ASPIS_PATH:$AENEAS_LIB"
(cd "$OUT" && "$LEAN_BIN" -j 1 -o ComponentBInstallerShared.olean \
  ComponentBInstallerShared.lean >> "$LOG" 2>&1)

# The authenticated Lean-4.32 cache avoids rebuilding several very large
# generated kernels during an ordinary combined replay.  The exact curated
# source closure is retained beside this script for audit and cache rebuilds.
test -f "$GOOD_A_SOURCE/GoodMatricesCurrent/ConcreteProbeTerminalMatrixCapstone.lean"
if test -n "${GOOD_A_OLEAN_DIR:-}"; then
  GOOD_A_PATH=$GOOD_A_OLEAN_DIR
else
  GOOD_A_PATH=$GOOD_A_LEGACY_CACHE
fi
if ! test -f "$GOOD_A_PATH/GoodMatricesCurrent/ConcreteProbeTerminalMatrixCapstone.olean"; then
  echo "set GOOD_A_OLEAN_DIR to the authenticated Lean-4.32 Good-A cache" >&2
  exit 1
fi

# The current Component-C extraction and Component-B layout extraction use
# distinct namespaces but Aeneas 4.32 emits namespace-insensitive names for
# derived discriminant instances.  These instances are unused by the fold
# proof, so omit only those attributes in the isolated integration build.
mkdir -p "$OUT/RuntimeEvaluatorCanonicalCurrent20260722"
perl -ne '
  next if /^\@\[discriminant isize\]$/;
  s/discriminant isize, //g;
  print
' "$C_CANONICAL/RuntimeEvaluatorCanonicalCurrent20260722/Types.lean" \
  > "$OUT/RuntimeEvaluatorCanonicalCurrent20260722/Types.lean"
export LEAN_PATH="$OUT:$ASPIS_PATH:$AENEAS_LIB"
(cd "$OUT" && "$LEAN_BIN" -j 1 \
  -o RuntimeEvaluatorCanonicalCurrent20260722/Types.olean \
  RuntimeEvaluatorCanonicalCurrent20260722/Types.lean >> "$LOG" 2>&1)
compile RuntimeEvaluatorCanonicalCurrent20260722/FunsExternal \
  "$C_CANONICAL/RuntimeEvaluatorCanonicalCurrent20260722/FunsExternal.lean"
compile RuntimeEvaluatorCanonicalCurrent20260722/Funs \
  "$C_CANONICAL/RuntimeEvaluatorCanonicalCurrent20260722/Funs.lean"
compile RuntimeEvaluatorCanonicalCurrent20260722 \
  "$C_CANONICAL/RuntimeEvaluatorCanonicalCurrent20260722.lean"
compile RuntimeWeightAccumulatorFoldLevel3 \
  "$C_RUNTIME/proof/RuntimeWeightAccumulatorFoldLevel3.lean"

# Consume the already-green six-step and maintained-wire proof artifacts, and
# rebuild the exact direct boundary needed by the accepted Tag-67 closure.
export LEAN_PATH="$OUT:$TAG67/proof:$TAG67/generated:$ASPIS_PATH:$AENEAS_LIB"
compile Tag67DigestPredicate "$TAG67/generated/Tag67DigestPredicate.lean"
compile Tag67DigestPredicateProof "$TAG67/proof/Tag67DigestPredicateProof.lean"
compile Tag67WorkWireLE64Bridge "$TAG67/proof/Tag67WorkWireLE64Bridge.lean"
compile Tag67WorkVerifierClosure "$TAG67/proof/Tag67WorkVerifierClosure.lean"

export LEAN_PATH="$C_PUBLIC_OLEAN:$OUT:$TAG67/proof:$TAG67/generated:$B_UNIFIED/olean-sampler-helper:$B_PIPELINE/olean-deps:$ASPIS_PATH:$AENEAS_LIB:$GOOD_A_PATH"
compile CurrentSourceABCapstone "$BUNDLE/proof/CurrentSourceABCapstone.lean"

if rg -n '\b(sorry|admit|native_decide|axiom|unsafe)\b|set_option max(Heartbeats|RecDepth)' \
    "$BUNDLE/proof" "$OUT/ComponentBInstallerShared.lean" \
    "$OUT/RuntimeEvaluatorCanonicalCurrent20260722/Types.lean"; then
  echo "forbidden token or raised proof limit" >&2
  exit 1
fi
if rg -n 'sorryAx|ofReduceBool' "$LOG"; then
  echo "forbidden axiom in closure" >&2
  exit 1
fi

# Concrete wire execution/shape hypotheses are intentional.  Correspondence
# premise names from retired closure layers are not.
if sed -n '/^theorem current_source_combined_capstone/,/ := by$/p' \
    "$BUNDLE/proof/CurrentSourceABCapstone.lean" | \
    rg -n 'RustRuntimeArithmeticCorrespondence|GeneratedPackerRowsMatchDeployed|EncoderEvaluationPremise|EncoderNaturalLeakageFactorises|h(Parser|Projection|DigestPredicate|SixStep)|parserCorrespondence|projectionCorrespondence|digestPredicateCorrespondence|sixStepCorrespondence'; then
  echo "forbidden correspondence premise in combined theorem" >&2
  exit 1
fi
if ! sed -n '/^theorem current_source_combined_capstone/,/ := by$/p' \
    "$BUNDLE/proof/CurrentSourceABCapstone.lean" | \
    rg -q 'actualTranscriptGrindingDigest state nonce ='; then
  echo "missing exact Tag-67 hash-application premise" >&2
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

echo "PASS current-source A/B, operational and public-output Component-C, and Tag-67 combined capstone"
echo "REPLAY_OUT=$OUT"
