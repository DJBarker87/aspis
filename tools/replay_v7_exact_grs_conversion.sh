#!/bin/sh
set -eu

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
FORMAL_ROOT="$ROOT/AspisFormal"
BOUNDARY_SOURCE="$FORMAL_ROOT/AspisFormal/Pool/AlgorithmicCircleDecoderV7.lean"
CONCRETE_SOURCE="$FORMAL_ROOT/AspisFormal/K1/V7Tag73ExactGRSConversion.lean"

case "$(cd "$FORMAL_ROOT" && lake env lean --version)" in
  "Lean (version 4.32.0,"*) ;;
  *) echo "expected Lean 4.32.0" >&2; exit 2 ;;
esac

if rg -n '\b(sorry|admit|native_decide)\b' \
    "$BOUNDARY_SOURCE" "$CONCRETE_SOURCE"; then
  echo "forbidden proof shortcut in exact GRS conversion sources" >&2
  exit 1
fi

if rg -n '^[[:space:]]*axioms?[[:space:]]' \
    "$BOUNDARY_SOURCE" "$CONCRETE_SOURCE"; then
  echo "project axiom declaration in exact GRS conversion sources" >&2
  exit 1
fi

if test -n "${V7_EXACT_GRS_REPLAY_OUT:-}"; then
  OUT=$V7_EXACT_GRS_REPLAY_OUT
  mkdir -p "$OUT"
  test -z "$(find "$OUT" -mindepth 1 -maxdepth 1 -print -quit)"
else
  OUT=$(mktemp -d "${TMPDIR:-/tmp}/v7-exact-grs.XXXXXX")
fi
LOG="$OUT/lean432.log"

cd "$FORMAL_ROOT"
lake build \
  AspisFormal.Pool.AlgorithmicCircleDecoderV7 \
  AspisFormal.K1.V7Tag73ExactGRSConversion > "$LOG" 2>&1

# Replay the two changed sources directly so the log contains their complete
# terminal `#print axioms` reports even when Lake's object cache is warm.
lake env lean AspisFormal/Pool/AlgorithmicCircleDecoderV7.lean >> "$LOG" 2>&1
lake env lean AspisFormal/K1/V7Tag73ExactGRSConversion.lean >> "$LOG" 2>&1

for theorem_name in \
    AspisPool.AlgorithmicCircleDecoderV7.ExactGRSConversion.coordinateScalingEquiv \
    AspisPool.AlgorithmicCircleDecoderV7.ExactGRSConversion.agreementCount_eq \
    AspisPool.AlgorithmicCircleDecoderV7.ExactGRSConversion.closeAtLeast_iff \
    AspisPool.AlgorithmicCircleDecoderV7.ExactDecoderInstantiation.initialThreshold_transport \
    AspisPool.AlgorithmicCircleDecoderV7.ExactDecoderInstantiation.finalThreshold_transport \
    AspisK1.V7Tag73ExactGRSConversion.exactFinalGRSConversion \
    AspisK1.V7Tag73ExactGRSConversion.exactFinalEncoder_eq_grs \
    AspisK1.V7Tag73ExactGRSConversion.exactFinalAgreementCount_eq_grs \
    AspisK1.V7Tag73ExactGRSConversion.exactFinal9558_transport \
    AspisK1.V7Tag73ExactGRSConversion.exactInitialGRSConversion \
    AspisK1.V7Tag73ExactGRSConversion.exactInitialEncoder_eq_grs \
    AspisK1.V7Tag73ExactGRSConversion.exactInitialAgreementCount_eq_grs \
    AspisK1.V7Tag73ExactGRSConversion.exactInitial38230_transport; do
  if ! grep -Fq "'$theorem_name' depends on axioms:" "$LOG" &&
      ! grep -Fq "'$theorem_name' does not depend on any axioms" "$LOG"; then
    echo "missing axiom report for $theorem_name" >&2
    exit 1
  fi
done

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

echo "PASS exact V7 circle/line to GRS conversion"
echo "REPLAY_OUT=$OUT"
