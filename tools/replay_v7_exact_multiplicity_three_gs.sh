#!/bin/sh
set -eu

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
FORMAL_ROOT="$ROOT/AspisFormal"
BOUNDARY_SOURCE="$FORMAL_ROOT/AspisFormal/Pool/AlgorithmicCircleDecoderV7.lean"
GS_SOURCE="$FORMAL_ROOT/AspisFormal/K1/V7Tag73ExactMultiplicityThreeGS.lean"

case "$(cd "$FORMAL_ROOT" && lake env lean --version)" in
  "Lean (version 4.32.0,"*) ;;
  *) echo "expected Lean 4.32.0" >&2; exit 2 ;;
esac

if rg -n '\b(sorry|admit|native_decide)\b' \
    "$BOUNDARY_SOURCE" "$GS_SOURCE"; then
  echo "forbidden proof shortcut in exact multiplicity-three GS sources" >&2
  exit 1
fi

if rg -n '^[[:space:]]*axioms?[[:space:]]' \
    "$BOUNDARY_SOURCE" "$GS_SOURCE"; then
  echo "project axiom declaration in exact multiplicity-three GS sources" >&2
  exit 1
fi

if test -n "${V7_EXACT_M3_GS_REPLAY_OUT:-}"; then
  OUT=$V7_EXACT_M3_GS_REPLAY_OUT
  mkdir -p "$OUT"
  test -z "$(find "$OUT" -mindepth 1 -maxdepth 1 -print -quit)"
else
  OUT=$(mktemp -d "${TMPDIR:-/tmp}/v7-exact-m3-gs.XXXXXX")
fi
LOG="$OUT/lean432.log"

cd "$FORMAL_ROOT"
lake build \
  AspisFormal.Pool.AlgorithmicCircleDecoderV7 \
  AspisFormal.K1.V7Tag73ExactMultiplicityThreeGS > "$LOG" 2>&1

# Direct source replay ensures that the terminal axiom reports are present
# even when Lake reuses compiled objects.
lake env lean AspisFormal/Pool/AlgorithmicCircleDecoderV7.lean >> "$LOG" 2>&1
lake env lean AspisFormal/K1/V7Tag73ExactMultiplicityThreeGS.lean >> "$LOG" 2>&1

for theorem_name in \
    AspisK1.V7Tag73ExactMultiplicityThreeGS.exactInitialAmbientDegreeConvention \
    AspisK1.V7Tag73ExactMultiplicityThreeGS.exactFinalInterpolationBudget \
    AspisK1.V7Tag73ExactMultiplicityThreeGS.exactInitialInterpolationBudget \
    AspisK1.V7Tag73ExactMultiplicityThreeGS.exists_exactFinalInterpolation \
    AspisK1.V7Tag73ExactMultiplicityThreeGS.exists_exactInitialInterpolation \
    AspisK1.V7Tag73ExactMultiplicityThreeGS.interpolationMultiplicityThree_dvd \
    AspisK1.V7Tag73ExactMultiplicityThreeGS.interpolationSubstitute_eq_zero_of_agreement \
    AspisK1.V7Tag73ExactMultiplicityThreeGS.exactFinalPolynomialAgreement_card_eq \
    AspisK1.V7Tag73ExactMultiplicityThreeGS.exactFinalRootCandidates_complete \
    AspisK1.V7Tag73ExactMultiplicityThreeGS.exactFinalGSDecode_mem_iff \
    AspisK1.V7Tag73ExactMultiplicityThreeGS.exactFinalGSDecode_length_le_99 \
    AspisK1.V7Tag73ExactMultiplicityThreeGS.exactFinalMultiplicityThreeGS \
    AspisK1.V7Tag73ExactMultiplicityThreeGS.exactInitialPolynomialAgreement_card_eq \
    AspisK1.V7Tag73ExactMultiplicityThreeGS.exactInitialRootCandidates_complete \
    AspisK1.V7Tag73ExactMultiplicityThreeGS.exactInitialGSDecode_mem_iff \
    AspisK1.V7Tag73ExactMultiplicityThreeGS.exactInitialGSDecode_length_le_100 \
    AspisK1.V7Tag73ExactMultiplicityThreeGS.exactInitialMultiplicityThreeGS; do
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

echo "PASS exact V7 multiplicity-three GS decoders"
echo "REPLAY_OUT=$OUT"
