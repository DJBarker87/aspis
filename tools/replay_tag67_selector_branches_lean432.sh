#!/bin/sh
set -eu

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
LEAN_BIN=${LEAN432_BIN:-$(command -v lean)}
TAG67="$ROOT/aeneas-verif/tag67-work-wire-correspondence"
ASPIS_PATH=$(cd "$ROOT/AspisFormal" && NO_DNA=1 lake env printenv LEAN_PATH)

if test -z "${AENEAS_LEAN_LIB:-}"; then
  echo "set AENEAS_LEAN_LIB to an Aeneas library built with Lean 4.32" >&2
  exit 2
fi
AENEAS_LIB=$AENEAS_LEAN_LIB

case "$($LEAN_BIN --version)" in
  "Lean (version 4.32.0,"*) ;;
  *) echo "expected Lean 4.32.0" >&2; exit 2 ;;
esac
test -f "$AENEAS_LIB/Aeneas/Std.olean"

if test -n "${TAG67_SELECTOR_REPLAY_OUT:-}"; then
  OUT=$TAG67_SELECTOR_REPLAY_OUT
  mkdir -p "$OUT"
  test -z "$(find "$OUT" -mindepth 1 -maxdepth 1 -print -quit)"
else
  OUT=$(mktemp -d /private/tmp/tag67-selector-lean432.XXXXXX)
fi
LOG="$OUT/lean432.log"

compile() {
  module=$1
  source=$2
  echo "COMPILE $module" >> "$LOG"
  "$LEAN_BIN" -j 1 -o "$OUT/$module.olean" "$source" >> "$LOG" 2>&1
}

export LEAN_PATH="$OUT:$TAG67/proof:$TAG67/generated:$ASPIS_PATH:$AENEAS_LIB"
compile Tag67WorkWireCore "$TAG67/generated/Tag67WorkWireCore.lean"
compile Tag67WorkWireProof "$TAG67/proof/Tag67WorkWireProof.lean"
compile Tag67SelectorFailureBranches \
  "$TAG67/proof/Tag67SelectorFailureBranches.lean"

if rg -n \
    '\b(sorry|admit|native_decide|axiom|opaque|unsafe|extern)\b|set_option max(Heartbeats|RecDepth)' \
    "$TAG67/proof/Tag67SelectorFailureBranches.lean"; then
  echo "forbidden construct in selector proof" >&2
  exit 1
fi
if rg -n 'sorryAx|ofReduceBool' "$LOG"; then
  echo "forbidden axiom in selector proof" >&2
  exit 1
fi

for theorem_name in \
    AspisTag67SelectorFailureBranches.generated_selector_value_cases \
    AspisTag67SelectorFailureBranches.generated_parser_result_and_selector_cases \
    AspisTag67SelectorFailureBranches.three_parsed_selector_cases_iff_selected_failure \
    AspisTag67SelectorFailureBranches.selected_extraction_implies_three_parsed_selector_cases \
    AspisTag67SelectorFailureBranches.false_accept_event_subset_parsed_selector_cases \
    AspisTag67SelectorFailureBranches.false_accept_probability_le_parsed_selector_case_sum; do
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

echo "PASS Tag-67 extracted selector partition"
echo "REPLAY_OUT=$OUT"
