#!/usr/bin/env bash
set -euo pipefail

readonly bundle="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly root="$(cd "$bundle/../.." && pwd -P)"

readonly charon_repo="${ASPIS_CHARON_REPO:?set ASPIS_CHARON_REPO to pinned Charon cb50ff16}"
readonly aeneas_repo="${ASPIS_AENEAS_REPO:?set ASPIS_AENEAS_REPO to pinned Aeneas b59d5188}"
readonly charon_bin="${CHARON_BIN:-$charon_repo/bin/charon}"
readonly aeneas_bin="${AENEAS_BIN:-$aeneas_repo/bin/aeneas}"

readonly expected_charon_commit="cb50ff16b9f1066b8a97dc06da704de2da2fa41c"
readonly expected_aeneas_commit="b59d5188c082f704a418c7cb4e52ad69328002d1"
readonly recorded_commit="06788d44d30ea8cbd391899dddaf6f0acc6e4a3f"
readonly recorded_tree="9b6bdfddb3c213addc2bb705c8130cce4fb2c351"
readonly recorded_atomic_blob="dca4626b5b49da6aa48076fad748dc838ce9c7d6"
readonly recorded_lifecycle_blob="560466bb84c85dde599b4b918f95b3015bf6b52a"
readonly current_atomic_blob="53e44db042f6035d06dbddb08f80a76c67b25b80"

[[ -x "$charon_bin" ]]
[[ -x "$aeneas_bin" ]]
command -v jq >/dev/null
command -v rg >/dev/null
[[ "$(git -C "$charon_repo" rev-parse HEAD)" == "$expected_charon_commit" ]]
[[ "$(git -C "$aeneas_repo" rev-parse HEAD)" == "$expected_aeneas_commit" ]]
[[ "$(git -C "$root" cat-file -t "$recorded_commit")" == commit ]]
[[ "$(git -C "$root" rev-parse "$recorded_commit^{tree}")" == "$recorded_tree" ]]
[[ "$(git -C "$root" rev-parse "$recorded_commit:programs/aspis-verifier/src/atomic_payment.rs")" == "$recorded_atomic_blob" ]]
[[ "$(git -C "$root" rev-parse "$recorded_commit:programs/aspis-verifier/src/lifecycle.rs")" == "$recorded_lifecycle_blob" ]]
[[ "$(git -C "$root" hash-object programs/aspis-verifier/src/atomic_payment.rs)" == "$current_atomic_blob" ]]

if [[ -n "${V5_RECORDED_CLOSE_REPLAY_OUT:-}" ]]; then
  out=$V5_RECORDED_CLOSE_REPLAY_OUT
  mkdir -p "$out"
  [[ -z "$(find "$out" -mindepth 1 -maxdepth 1 -print -quit)" ]]
else
  out=$(mktemp -d /private/tmp/v5-recorded-close.XXXXXX)
fi
readonly out
readonly source="$out/source"
readonly llbc="$out/refund.llbc"
readonly generated="$out/generated"
readonly log="$out/replay.log"
mkdir -p "$source" "$generated"
: > "$log"

git -C "$root" archive "$recorded_commit" | tar -x -C "$source"
[[ "$(git -C "$root" hash-object "$source/programs/aspis-verifier/src/atomic_payment.rs")" == "$recorded_atomic_blob" ]]
[[ "$(git -C "$root" hash-object "$source/programs/aspis-verifier/src/lifecycle.rs")" == "$recorded_lifecycle_blob" ]]

# The recorded source has address derivation but no separate numeric-bump
# rejection. The current source blob contains that later check.
rg -F 'let (expected_nullifier, bump) = atomic_nullifier_address' \
  "$source/programs/aspis-verifier/src/atomic_payment.rs" >/dev/null
if rg -F 'required_nullifier_bump' \
    "$source/programs/aspis-verifier/src/atomic_payment.rs"; then
  echo "recorded source unexpectedly contains the later numeric-bump check" >&2
  exit 1
fi
rg -F 'required_nullifier_bump.is_some_and(|required| bump != required)' \
  "$root/programs/aspis-verifier/src/atomic_payment.rs" >/dev/null

(
  cd "$source"
  CARGO_TARGET_DIR="$out/test-target" cargo test -p aspis-verifier \
    close_finalized_proof_refunds_exact_balance_and_tombstones_overallocation \
    --locked -- --nocapture
) >> "$log" 2>&1

(
  cd "$source"
  CARGO_TARGET_DIR="$out/charon-target" "$charon_bin" cargo \
    --preset aeneas \
    --sysroot default \
    --start-from 'aspis_verifier::atomic_payment::refund_program_owned_proof_account' \
    --opaque 'solana_account_info::_::lamports' \
    --opaque 'solana_account_info::_::try_borrow_mut_data' \
    --opaque 'solana_account_info::_::try_borrow_mut_lamports' \
    --dest-file "$llbc" -- --release --locked -p aspis-verifier
) >> "$log" 2>&1

jq -e '.has_errors == false' "$llbc" >/dev/null
jq --rawfile source_file "$source/programs/aspis-verifier/src/atomic_payment.rs" -e '
  any(.translated.files[];
    .name.Local == "programs/aspis-verifier/src/atomic_payment.rs" and
    .contents == $source_file)
' "$llbc" >/dev/null
jq -e '
  any(.translated.fun_decls[];
    (.item_meta.name | tostring | contains("refund_program_owned_proof_account")) and
    .item_meta.opacity == "Transparent" and .body != null)
' "$llbc" >/dev/null
for method in lamports try_borrow_mut_data try_borrow_mut_lamports; do
  jq --arg method "$method" -e '
    any(.translated.fun_decls[];
      (.item_meta.name | tostring | contains($method)) and
      .item_meta.opacity == "Opaque")
  ' "$llbc" >/dev/null
done

# Aeneas currently cannot interpret Solana AccountInfo's nested mutable
# reference projection. Require the precise known failure and do not label it
# as a successful translation.
set +e
"$aeneas_bin" -backend lean -split-files -no-progress-bar \
  -print-error-diagnostics -dest "$generated" "$llbc" \
  > "$out/aeneas.log" 2>&1
aeneas_status=$?
set -e
cat "$out/aeneas.log" >> "$log"
if [[ $aeneas_status -eq 0 ]]; then
  echo "Aeneas unexpectedly translated the full close; review and replace the named boundary" >&2
  exit 1
fi
rg -F "Could not translate the body of function 'aspis_verifier::atomic_payment::refund_program_owned_proof_account" \
  "$out/aeneas.log" >/dev/null
rg -F "solana-account-info-2.3.0/src/lib.rs', lines 72:4-72:33" \
  "$out/aeneas.log" >/dev/null
rg -F 'InterpProjectors.ml' "$out/aeneas.log" >/dev/null

if rg -n '\b(sorry|admit|native_decide|axiom|unsafe|ofReduceBool)\b' \
    "$root/AspisFormal/AspisFormal/V5RecordedCloseBytes.lean"; then
  echo "forbidden proof token" >&2
  exit 1
fi

(
  cd "$root/AspisFormal"
  NO_DNA=1 lake env lean AspisFormal/V5RecordedCloseBytes.lean
) >> "$log" 2>&1

if rg -n 'sorryAx|ofReduceBool' "$log"; then
  echo "forbidden axiom in recorded-close proof" >&2
  exit 1
fi
if ! awk '
  / depends on axioms: \[/ { active = 1; sub(/^.*\[/, "") }
  active {
    line = $0
    gsub(/propext|Classical\.choice|Quot\.sound/, "", line)
    gsub(/[\[\],[:space:]]/, "", line)
    if (line != "") { print "unexpected axiom: " line; bad = 1 }
    if ($0 ~ /\]/) active = 0
  }
  END { exit bad }
' "$log"; then
  exit 1
fi

echo "Recorded close source/model replay: PASS"
echo "Aeneas AccountInfo translation limitation: reproduced and still explicit"
echo "V5_RECORDED_CLOSE_REPLAY_OUT=$out"
echo "log: $log"
