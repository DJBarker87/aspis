#!/bin/sh
set -eu

ROOT=${REPO_ROOT:-/Users/dominic/ZK}
BUNDLE="$ROOT/aeneas-verif/wire-prefix-constants"
AENEAS432_BACKEND=${AENEAS432_BACKEND:-/private/tmp/aspis-aeneas-lean432-check.p116iK/aeneas/backends/lean}
LEAN_BIN=${LEAN432_BIN:-/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean}
EXPECTED_AENEAS=b59d5188c082f704a418c7cb4e52ad69328002d1
OUT=$(mktemp -d /private/tmp/aspis-wire-prefix-replay.XXXXXX)
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

LLBC="$BUNDLE/llbc/wire_prefix_constants.llbc"
jq -e '.has_errors == false and (.translated.ordered_decls | length) == 54' \
  "$LLBC" >/dev/null
for source in \
  crates/aspis-prover/src/v5_real_host_proof.rs \
  crates/aspis-prover/src/v5_mask.rs \
  crates/aspis-prover/src/lib.rs \
  crates/aspis-prover/src/v5_spend_messages.rs \
  crates/aspis-prover/src/v5_cu_envelope.rs
do
  jq -j --arg source "$source" '.translated.files[]
    | select(.name.Local == $source)
    | .contents' "$LLBC" > "$OUT/embedded-source.rs"
  cmp "$ROOT/$source" "$OUT/embedded-source.rs"
done

# Charon records cross-crate source names and spans but omits their source
# bodies. Bind the included arity-4 constant to the frozen dependency bytes
# and to its literal current declaration instead of pretending those bytes
# were embedded in the LLBC.
test "$(shasum -a 256 "$ROOT/crates/aspis-core/src/circle_fri.rs" | awk '{print $1}')" = \
  6ce32a64e6e996680592a214cea07d2a982fe26aec8416064e8b0a66d3406289
test "$(shasum -a 256 "$ROOT/crates/aspis-core/src/lib.rs" | awk '{print $1}')" = \
  707467acca89d780f713c8dc6274a3be854b95d7ad8224d9530fb9879c3f80a3
test "$(rg -F 'pub const FIXED_ARITY4_ROUNDS: u8 = 4;' \
  "$ROOT/crates/aspis-core/src/circle_fri.rs" | wc -l | tr -d ' ')" -eq 1

sed -e 's/^import Aeneas$/import Aeneas.Std\
import Aeneas.Tactic.RustAttributes/' \
    -e '/maxHeartbeats/d' \
    -e '/maxRecDepth/d' \
  "$BUNDLE/generated/WirePrefixConstants.raw.lean" > \
  "$OUT/WirePrefixConstants.lean"
cmp "$BUNDLE/generated/WirePrefixConstants.lean" \
  "$OUT/WirePrefixConstants.lean"
cp "$BUNDLE/proof/WirePrefixConstantsExact.lean" "$OUT/"
cp "$BUNDLE/proof/WirePrefixConstantsCorrespondence.lean" "$OUT/"

if rg -n '\b(sorry|admit|native_decide|axiom|unsafe|ofReduceBool)\b|set_option[[:space:]]+(maxHeartbeats|maxRecDepth)' \
    "$OUT/WirePrefixConstants.lean" \
    "$OUT/WirePrefixConstantsExact.lean" \
    "$OUT/WirePrefixConstantsCorrespondence.lean"
then
  echo "forbidden proof token or raised limit" >&2
  exit 1
fi

THEOREMS=$(rg --no-filename '^theorem ' \
  "$OUT/WirePrefixConstantsExact.lean" \
  "$OUT/WirePrefixConstantsCorrespondence.lean" \
  | sed -E 's/^theorem ([^ :({]+).*/\1/' | sort)
AUDITS=$(rg --no-filename '^#print axioms ' \
  "$OUT/WirePrefixConstantsExact.lean" \
  "$OUT/WirePrefixConstantsCorrespondence.lean" \
  | sed -E 's/^#print axioms ([^ ]+).*/\1/' | sort)
test "$THEOREMS" = "$AUDITS"
test "$(printf '%s\n' "$THEOREMS" | wc -l | tr -d ' ')" -eq 38

AENEAS_PATH=$(cd "$AENEAS432_BACKEND" && lake env printenv LEAN_PATH)
ASPIS_PATH=$(cd "$ROOT/AspisFormal" && lake env printenv LEAN_PATH)
LEAN_PATH="$OUT:$ASPIS_PATH:$AENEAS_PATH"
for module in \
  WirePrefixConstants \
  WirePrefixConstantsExact \
  WirePrefixConstantsCorrespondence
do
  LEAN_PATH="$LEAN_PATH" "$LEAN_BIN" -R "$OUT" -o "$OUT/$module.olean" \
    "$OUT/$module.lean" >> "$LOG" 2>&1
done

cat "$LOG"
if rg -n 'sorryAx|ofReduceBool|(^|/).*\.lean:.*warning:' "$LOG"; then
  echo "disallowed axiom or warning in replay" >&2
  exit 1
fi
if rg -v "depends on axioms:|^'(AspisV5WirePrefixConstantsExact|AspisV5WirePrefixConstantsCorrespondence)\.|^[[:space:]]*(propext,|Classical.choice,|Quot.sound|Quot.sound])$|^[[:space:]]*$" \
    "$LOG" > "$OUT/unexpected-axiom-output"
then
  cat "$OUT/unexpected-axiom-output" >&2
  echo "unexpected replay output or axiom" >&2
  exit 1
fi

echo "wire-prefix Lean 4.32 replay: PASS (38 theorem audits)"
