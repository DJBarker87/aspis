#!/bin/sh
set -eu

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
FORMAL_ROOT="$ROOT/AspisFormal"

case "$(cd "$FORMAL_ROOT" && lake env lean --version)" in
  "Lean (version 4.32.0,"*) ;;
  *) echo "expected Lean 4.32.0" >&2; exit 2 ;;
esac

case "$(cd "$FORMAL_ROOT" && lake --version)" in
  "Lake version 5.0.0-src+8c9756b (Lean version 4.32.0)") ;;
  *) echo "expected the pinned Lean 4.32.0 Lake tool" >&2; exit 2 ;;
esac

SOURCES=$(find "$FORMAL_ROOT/AspisFormal/K1" -maxdepth 1 -type f \
  -name 'V7ExactCorrelatedAgreement*.lean' -print | sort)
INTEGRATION_SOURCES="
$FORMAL_ROOT/AspisFormal/K1/V7Tag73ExactFixedK13K14FailureReduction.lean
$FORMAL_ROOT/AspisFormal/K1/V7Tag73CausalK14FailureProbability.lean
$FORMAL_ROOT/AspisFormal/K1/V7Tag73SuccessfulSamplerConditioningBridge.lean
$FORMAL_ROOT/AspisFormal/K1/V7Tag73ExactConcreteK13K14Events.lean"

if rg -n '\b(sorry|admit|native_decide)\b' $SOURCES $INTEGRATION_SOURCES; then
  echo "forbidden proof shortcut in exact correlated-agreement sources" >&2
  exit 1
fi

if rg -n '^[[:space:]]*axioms?[[:space:]]' $SOURCES $INTEGRATION_SOURCES; then
  echo "project axiom declaration in exact correlated-agreement sources" >&2
  exit 1
fi

if test -n "${V7_EXACT_CORRELATED_REPLAY_OUT:-}"; then
  OUT=$V7_EXACT_CORRELATED_REPLAY_OUT
  mkdir -p "$OUT"
  test -z "$(find "$OUT" -mindepth 1 -maxdepth 1 -print -quit)"
else
  OUT=$(mktemp -d "${TMPDIR:-/tmp}/v7-exact-correlated.XXXXXX")
fi
LOG="$OUT/lean432.log"

cd "$FORMAL_ROOT"
/usr/bin/time -v lake -Kjobs=1 build \
  AspisFormal.K1.V7ExactCorrelatedAgreementTerminal \
  AspisFormal.K1.V7ExactCorrelatedAgreementInitial \
  AspisFormal.K1.V7Tag73ExactFixedK13K14FailureReduction \
  AspisFormal.K1.V7Tag73CausalK14FailureProbability \
  AspisFormal.K1.V7Tag73SuccessfulSamplerConditioningBridge \
  AspisFormal.K1.V7Tag73ExactConcreteK13K14Events > "$LOG" 2>&1

# Direct source replay makes the terminal #print axioms reports visible even
# when Lake reuses the compiled objects.  The initial and final leaf modules
# import every exact correlated-agreement predecessor.
/usr/bin/time -v lake env lean \
  AspisFormal/K1/V7ExactCorrelatedAgreementTerminal.lean >> "$LOG" 2>&1
/usr/bin/time -v lake env lean \
  AspisFormal/K1/V7ExactCorrelatedAgreementInitial.lean >> "$LOG" 2>&1

for theorem_name in \
    AspisK1.V7ExactCorrelatedAgreementTerminal.exactV7FinalDegreeThreeCurveDecodable \
    AspisK1.V7ExactCorrelatedAgreementTerminal.exactV7FinalPublishedOneFoldCurveDecodability \
    AspisK1.V7ExactCorrelatedAgreementTerminal.exactV7InitialWidth29CurveDecodable \
    AspisK1.V7ExactCorrelatedAgreementTerminal.exactV7InitialPublishedWidth29CurveDecodability; do
  if ! grep -Fq "'$theorem_name' depends on axioms:" "$LOG" &&
      ! grep -Fq "'$theorem_name' does not depend on any axioms" "$LOG"; then
    echo "missing axiom report for $theorem_name" >&2
    exit 1
  fi
done

if grep -Eq 'sorryAx|declaration uses .sorry.|unknown declaration|error:' "$LOG"; then
  echo "failed exact correlated-agreement replay or axiom audit" >&2
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

echo "PASS exact V7 correlated agreement"
echo "REPLAY_OUT=$OUT"
