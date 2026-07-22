#!/bin/sh
set -eu

ROOT=${REPO_ROOT:-/Users/dominic/ZK}
BUNDLE="$ROOT/aeneas-verif/retry-cap"
AENEAS432_BACKEND=${AENEAS432_BACKEND:-/private/tmp/aspis-aeneas-lean432-check.p116iK/aeneas/backends/lean}
LEAN_BIN=${LEAN432_BIN:-/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean}
EXPECTED_AENEAS=b59d5188c082f704a418c7cb4e52ad69328002d1
OUT=$(mktemp -d /private/tmp/aspis-retry-cap-replay.XXXXXX)
LOG="$OUT/replay.log"
cleanup() {
  status=$?
  trap - EXIT
  if test "$status" -ne 0 && test -f "$LOG"; then
    cat "$LOG" >&2
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

LLBC="$BUNDLE/llbc/retry_cap.llbc"
jq -e '.has_errors == false and (.translated.ordered_decls | length) == 2' \
  "$LLBC" >/dev/null
jq -j '.translated.files[]
  | select(.name.Local == "crates/aspis-prover/src/v5_real_host_proof.rs")
  | .contents' "$LLBC" > "$OUT/embedded-source.rs"
cmp "$ROOT/crates/aspis-prover/src/v5_real_host_proof.rs" \
  "$OUT/embedded-source.rs"

sed -e 's/^import Aeneas$/import Aeneas.Std\
import Aeneas.Tactic.RustAttributes/' \
    -e '/maxHeartbeats/d' \
    -e '/maxRecDepth/d' \
  "$BUNDLE/generated/RetryCap.raw.lean" > "$OUT/RetryCap.lean"
cmp "$BUNDLE/generated/RetryCap.lean" "$OUT/RetryCap.lean"
cp "$BUNDLE/proof/RetryCapCorrespondence.lean" "$OUT/"

if rg -n '\b(sorry|admit|native_decide|axiom|unsafe|ofReduceBool)\b|set_option[[:space:]]+(maxHeartbeats|maxRecDepth)' \
    "$OUT/RetryCap.lean" "$OUT/RetryCapCorrespondence.lean"
then
  echo "forbidden proof token or raised limit" >&2
  exit 1
fi

THEOREMS=$(rg --no-filename '^theorem ' "$OUT/RetryCapCorrespondence.lean" \
  | sed -E 's/^theorem ([^ :({]+).*/\1/' | sort)
AUDITS=$(rg --no-filename '^#print axioms ' "$OUT/RetryCapCorrespondence.lean" \
  | sed -E 's/^#print axioms ([^ ]+).*/\1/' | sort)
test "$THEOREMS" = "$AUDITS"
test "$(printf '%s\n' "$THEOREMS" | wc -l | tr -d ' ')" -eq 2

AENEAS_PATH=$(cd "$AENEAS432_BACKEND" && lake env printenv LEAN_PATH)
ASPIS_PATH=$(cd "$ROOT/AspisFormal" && lake env printenv LEAN_PATH)
LEAN_PATH="$OUT:$ASPIS_PATH:$AENEAS_PATH"
for module in RetryCap RetryCapCorrespondence; do
  LEAN_PATH="$LEAN_PATH" "$LEAN_BIN" -R "$OUT" -o "$OUT/$module.olean" \
    "$OUT/$module.lean" >> "$LOG" 2>&1
done

cat "$LOG"
if rg -n 'sorryAx|ofReduceBool|(^|/).*\.lean:.*warning:' "$LOG"; then
  echo "disallowed axiom or warning in replay" >&2
  exit 1
fi
if rg -v "depends on axioms:|^'AspisV5RetryCapCorrespondence\.|^[[:space:]]*(propext,|Classical.choice,|Quot.sound|Quot.sound])$|^[[:space:]]*$" \
    "$LOG" > "$OUT/unexpected-axiom-output"
then
  cat "$OUT/unexpected-axiom-output" >&2
  echo "unexpected replay output or axiom" >&2
  exit 1
fi

echo "retry-cap Lean 4.32 replay: PASS (2 theorem audits)"
