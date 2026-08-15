#!/usr/bin/env bash
set -euo pipefail

readonly bundle="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly root="$(cd "$bundle/../.." && pwd -P)"
readonly projection_harness="$bundle/projection-harness"
readonly checked_projection="$bundle/generated/V5RecordedCloseProjection"
readonly projection_proof="$bundle/proof/V5RecordedCloseProjectionProof.lean"

readonly charon_repo="${ASPIS_CHARON_REPO:?set ASPIS_CHARON_REPO to pinned Charon cb50ff16}"
readonly aeneas_repo="${ASPIS_AENEAS_REPO:?set ASPIS_AENEAS_REPO to pinned Aeneas b59d5188}"
readonly lean432_aeneas_root="${LEAN432_AENEAS_ROOT:?set LEAN432_AENEAS_ROOT to the Lean-4.32 Aeneas backend root}"
readonly charon_bin="${CHARON_BIN:-$charon_repo/bin/charon}"
readonly aeneas_bin="${AENEAS_BIN:-$aeneas_repo/bin/aeneas}"

readonly expected_charon_commit="cb50ff16b9f1066b8a97dc06da704de2da2fa41c"
readonly expected_aeneas_commit="b59d5188c082f704a418c7cb4e52ad69328002d1"
readonly recorded_commit="06788d44d30ea8cbd391899dddaf6f0acc6e4a3f"
readonly recorded_tree="9b6bdfddb3c213addc2bb705c8130cce4fb2c351"
readonly recorded_atomic_blob="dca4626b5b49da6aa48076fad748dc838ce9c7d6"
readonly recorded_lifecycle_blob="560466bb84c85dde599b4b918f95b3015bf6b52a"
readonly current_atomic_blob="53e44db042f6035d06dbddb08f80a76c67b25b80"
readonly projection_toml_blob="0e079bdc60f9dcd778e1402fc193f98f22734acb"
readonly projection_lock_blob="c7a462cd9db477c53bb355899627c911bd1dd5dc"
readonly projection_source_blob="d91011767477561d8af5568ddcab03bf38041c11"
readonly projection_types_sha256="6b74ccf823c425ee6b105822a090df63022db036488777e691c72b92a248ead9"
readonly projection_funs_sha256="b4b8626ae2c6eec70dedbf4ace52ea12ad1073905aa34d464c67acd8c01076e5"

[[ -x "$charon_bin" ]]
[[ -x "$aeneas_bin" ]]
command -v jq >/dev/null
command -v rg >/dev/null
if [[ -n "${LEAN432_BIN:-}" ]]; then
  lean_cmd=("$LEAN432_BIN")
elif command -v elan >/dev/null 2>&1; then
  lean_cmd=(elan run leanprover/lean4:v4.32.0 lean)
else
  lean_cmd=("$(command -v lean)")
fi
readonly -a lean_cmd
case "$("${lean_cmd[@]}" --version)" in
  "Lean (version 4.32.0,"*) ;;
  *) echo "expected Lean 4.32.0" >&2; exit 1 ;;
esac
readonly aeneas_lean_path="$(cd "$lean432_aeneas_root" && lake env printenv LEAN_PATH)"
[[ -f "$lean432_aeneas_root/.lake/build/lib/lean/Aeneas/Std.olean" ]]
[[ "$(git -C "$charon_repo" rev-parse HEAD)" == "$expected_charon_commit" ]]
[[ "$(git -C "$aeneas_repo" rev-parse HEAD)" == "$expected_aeneas_commit" ]]
[[ "$(git -C "$root" cat-file -t "$recorded_commit")" == commit ]]
[[ "$(git -C "$root" rev-parse "$recorded_commit^{tree}")" == "$recorded_tree" ]]
[[ "$(git -C "$root" rev-parse "$recorded_commit:programs/aspis-verifier/src/atomic_payment.rs")" == "$recorded_atomic_blob" ]]
[[ "$(git -C "$root" rev-parse "$recorded_commit:programs/aspis-verifier/src/lifecycle.rs")" == "$recorded_lifecycle_blob" ]]
[[ "$(git -C "$root" hash-object programs/aspis-verifier/src/atomic_payment.rs)" == "$current_atomic_blob" ]]
[[ "$(git -C "$root" hash-object "$projection_harness/Cargo.toml")" == "$projection_toml_blob" ]]
[[ "$(git -C "$root" hash-object "$projection_harness/Cargo.lock")" == "$projection_lock_blob" ]]
[[ "$(git -C "$root" hash-object "$projection_harness/src/lib.rs")" == "$projection_source_blob" ]]

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
readonly accountinfo_partial="$out/accountinfo-partial"
readonly projection_llbc="$out/V5RecordedCloseProjection.llbc"
readonly projection_raw="$out/projection-raw"
readonly projection_checked_src="$out/projection-checked-src"
readonly projection_olean="$out/projection-olean"
readonly log="$out/replay.log"
mkdir -p "$source" "$accountinfo_partial" "$projection_raw" \
  "$projection_checked_src/V5RecordedCloseProjection" \
  "$projection_olean/V5RecordedCloseProjection"
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
  -print-error-diagnostics -dest "$accountinfo_partial" "$llbc" \
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

# Translate the same successful check/mutation order over plain values. This
# isolates the arithmetic and byte update from AccountInfo's unsupported
# nested RefCell representation.
(
  cd "$projection_harness"
  CARGO_TARGET_DIR="$out/projection-target" "$charon_bin" cargo \
    --preset aeneas --sysroot default \
    --start-from 'aspis_close_projection::source_shaped_close' \
    --dest-file "$projection_llbc" -- --release --locked
) >> "$log" 2>&1
"$aeneas_bin" -backend lean \
  -namespace V5RecordedCloseProjectionGenerated \
  -split-files -no-progress-bar -dest "$projection_raw" "$projection_llbc" \
  >> "$log" 2>&1

normalize_projection() {
  perl -0777 -pe \
    's/import Aeneas(?:\.Std)?\n//g; s/import Aeneas\.Tactic\.RustAttributes\n//g; s/@\[discriminant isize\]\n//g; s/import V5RecordedCloseProjection\.Types\n//g; s{/-.*?-/}{}gs; s{--[^\n]*}{}g; s/\s+//g' \
    "$1"
}

compare_projection() {
  local raw=$1 checked=$2 expected=$3 name=$4
  normalize_projection "$raw" > "$out/raw-$name.semantic"
  normalize_projection "$checked" > "$out/checked-$name.semantic"
  cmp "$out/raw-$name.semantic" "$out/checked-$name.semantic"
  [[ "$(shasum -a 256 "$out/raw-$name.semantic" | awk '{print $1}')" == "$expected" ]]
}

compare_projection "$projection_raw/Types.lean" \
  "$checked_projection/Types.lean" "$projection_types_sha256" types
compare_projection "$projection_raw/Funs.lean" \
  "$checked_projection/Funs.lean" "$projection_funs_sha256" funs

cp "$checked_projection/Types.lean" \
  "$projection_checked_src/V5RecordedCloseProjection/Types.lean"
cp "$checked_projection/Funs.lean" \
  "$projection_checked_src/V5RecordedCloseProjection/Funs.lean"
cp "$projection_proof" \
  "$projection_checked_src/V5RecordedCloseProjection/Proof.lean"

(
  export LEAN_PATH="$projection_olean:$projection_checked_src:$aeneas_lean_path"
  cd "$projection_checked_src"
  "${lean_cmd[@]}" -j 1 \
    -o "$projection_olean/V5RecordedCloseProjection/Types.olean" \
    V5RecordedCloseProjection/Types.lean
  "${lean_cmd[@]}" -j 1 \
    -o "$projection_olean/V5RecordedCloseProjection/Funs.olean" \
    V5RecordedCloseProjection/Funs.lean
  "${lean_cmd[@]}" -j 1 \
    -o "$projection_olean/V5RecordedCloseProjection/Proof.olean" \
    V5RecordedCloseProjection/Proof.lean
) >> "$log" 2>&1

if rg -n '\b(sorry|admit|native_decide|axiom|unsafe|ofReduceBool)\b' \
    "$root/AspisFormal/AspisFormal/V5RecordedCloseBytes.lean" \
    "$checked_projection" "$projection_proof"; then
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
echo "Aeneas successful close projection and exact-effect theorem: PASS"
echo "V5_RECORDED_CLOSE_REPLAY_OUT=$out"
echo "log: $log"
