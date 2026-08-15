#!/usr/bin/env bash
set -euo pipefail

readonly bundle="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly root="$(cd "$bundle/../.." && pwd -P)"
readonly harness="$bundle/harness"
readonly patch="$bundle/extraction/v5-fri-monotone-recursion.patch"
readonly checked_generated="$bundle/generated/V5FriMonotone"
readonly proof="$bundle/proof/V5FriMonotoneProof.lean"
readonly lean_bin="${LEAN432_BIN:-$(command -v lean)}"
readonly aeneas_lib="${AENEAS_LEAN_LIB:?set AENEAS_LEAN_LIB to the patched Aeneas Lean 4.32 library}"
readonly charon_repo="${ASPIS_CHARON_REPO:?set ASPIS_CHARON_REPO to pinned Charon cb50ff16}"
readonly aeneas_repo="${ASPIS_AENEAS_REPO:?set ASPIS_AENEAS_REPO to pinned Aeneas b59d5188}"
readonly charon_bin="${CHARON_BIN:-$charon_repo/bin/charon}"
readonly aeneas_bin="${AENEAS_BIN:-$aeneas_repo/bin/aeneas}"

readonly expected_charon_commit="cb50ff16b9f1066b8a97dc06da704de2da2fa41c"
readonly expected_aeneas_commit="b59d5188c082f704a418c7cb4e52ad69328002d1"
readonly expected_fri_checks_blob="3b1f37f2504aa2b309cad82605c88cab11afcb85"
readonly expected_private_openings_blob="6970faa793b69cbf949a893d5844a162d526fb5b"
readonly expected_core_openings_blob="3a1510440a09f6bdfaa67ad280d75fc8ef9a5712"
readonly expected_core_merkle_blob="dd166e9713d305c3f7432369d54ea68ce3062be0"
readonly expected_harness_manifest_blob="2b9472e979bbcc73f7306751de7b1675a5245e2b"
readonly expected_harness_lock_blob="e002701bf47a1ae9be13939ec5e06cb88521c658"
readonly expected_harness_source_blob="075ccdfd7b840ec193f37d1d7037e96c0ce7c3f3"
readonly expected_patch_sha256="980f4d92d678a6e2c530784fa386d739ce6cb58606f399675a9907a93f0c7b31"

case "$($lean_bin --version)" in
  "Lean (version 4.32.0,"*) ;;
  *) echo "expected Lean 4.32.0" >&2; exit 1 ;;
esac

[[ -x "$charon_bin" ]]
[[ -x "$aeneas_bin" ]]
[[ -f "$aeneas_lib/Aeneas/Std.olean" ]]
[[ -f "$aeneas_lib/Aeneas/Tactic/RustAttributes.olean" ]]
[[ -f "$aeneas_lib/Aeneas/Data/Discriminant.olean" ]]
[[ "$(git -C "$charon_repo" rev-parse HEAD)" == "$expected_charon_commit" ]]
[[ "$(git -C "$aeneas_repo" rev-parse HEAD)" == "$expected_aeneas_commit" ]]
[[ "$(git -C "$root" hash-object programs/aspis-verifier/src/v5_fri_checks.rs)" == \
  "$expected_fri_checks_blob" ]]
[[ "$(git -C "$root" hash-object programs/aspis-verifier/src/v5_private_openings.rs)" == \
  "$expected_private_openings_blob" ]]
[[ "$(git -C "$root" hash-object crates/aspis-core/src/state_only_private_openings.rs)" == \
  "$expected_core_openings_blob" ]]
[[ "$(git -C "$root" hash-object crates/aspis-core/src/state_only_private_merkle.rs)" == \
  "$expected_core_merkle_blob" ]]
[[ "$(git -C "$root" hash-object aeneas-verif/v5-fri-monotone-source-20260815/harness/Cargo.toml)" == \
  "$expected_harness_manifest_blob" ]]
[[ "$(git -C "$root" hash-object aeneas-verif/v5-fri-monotone-source-20260815/harness/Cargo.lock)" == \
  "$expected_harness_lock_blob" ]]
[[ "$(git -C "$root" hash-object aeneas-verif/v5-fri-monotone-source-20260815/harness/src/lib.rs)" == \
  "$expected_harness_source_blob" ]]
[[ "$(shasum -a 256 "$patch" | awk '{print $1}')" == "$expected_patch_sha256" ]]

if [[ -n "${V5_FRI_MONOTONE_REPLAY_OUT:-}" ]]; then
  out=$V5_FRI_MONOTONE_REPLAY_OUT
  mkdir -p "$out"
  [[ -z "$(find "$out" -mindepth 1 -maxdepth 1 -print -quit)" ]]
else
  out=$(mktemp -d /private/tmp/v5-fri-monotone.XXXXXX)
fi
readonly out
readonly source="$out/source"
readonly llbc="$out/v5_fri_monotone.llbc"
readonly raw_generated="$out/raw-generated"
readonly normalized_generated="$out/normalized-generated/V5FriMonotone"
readonly olean_out="$out/olean"
readonly log="$out/replay.log"
mkdir -p "$source/programs/aspis-verifier/src" \
  "$source/aeneas-verif/v5-fri-monotone-source-20260815" \
  "$raw_generated" "$normalized_generated" "$olean_out/V5FriMonotone"
: > "$log"

# The repository source is never edited.  This temporary copy changes only
# the spelling of the monotone scan so the pinned Aeneas version can translate
# it; the checked Rust build below confirms that copy remains well typed.
cp "$root/programs/aspis-verifier/src/v5_fri_checks.rs" \
  "$source/programs/aspis-verifier/src/"
cp "$root/programs/aspis-verifier/src/v5_private_openings.rs" \
  "$source/programs/aspis-verifier/src/"
cp -R "$harness" \
  "$source/aeneas-verif/v5-fri-monotone-source-20260815/"
CORE_PATH="$root/crates/aspis-core" perl -pi -e '
  s{path = "\.\./\.\./\.\./crates/aspis-core"}{path = "$ENV{CORE_PATH}"};
' "$source/aeneas-verif/v5-fri-monotone-source-20260815/harness/Cargo.toml"
git -C "$source" init -q
git -C "$source" apply --unidiff-zero --check "$patch"
git -C "$source" apply --unidiff-zero "$patch"

echo "EXTRACT temporary recursive spelling of the production monotone helper" | \
  tee -a "$log"
(
  cd "$source/aeneas-verif/v5-fri-monotone-source-20260815/harness"
  CARGO_TARGET_DIR="$out/cargo-target" "$charon_bin" cargo \
    --preset aeneas \
    --start-from \
      'v5_relation_prepared_claims_harness::fri_checks::opening_value_for_monotone_index' \
    --include 'aspis_core::state_only_private_openings' \
    --dest-file "$llbc" -- --release --locked
) >> "$log" 2>&1

echo "TRANSLATE monotone helper" | tee -a "$log"
"$aeneas_bin" -backend lean -split-files \
  -namespace V5FriMonotoneGenerated \
  -dest "$raw_generated" \
  -max-heartbeats 800000 -max-recdepth 3000 \
  "$llbc" >> "$log" 2>&1

SOURCE_PREFIX="$source/" ROOT_PREFIX="$root/" perl -pe '
  if ($_ eq "import Aeneas\n") {
    $_ = "import Aeneas.Std\nimport Aeneas.Tactic.RustAttributes\nimport Aeneas.Data.Discriminant\n";
  }
  s/\Q$ENV{SOURCE_PREFIX}\E//g;
  s/\Q$ENV{ROOT_PREFIX}\E//g;
' "$raw_generated/Types.lean" > "$normalized_generated/Types.lean"

SOURCE_PREFIX="$source/" ROOT_PREFIX="$root/" perl -pe '
  if ($_ eq "import Aeneas\n") {
    $_ = "import Aeneas.Std\nimport Aeneas.Tactic.RustAttributes\n";
  }
  s/\Q$ENV{SOURCE_PREFIX}\E//g;
  s/\Q$ENV{ROOT_PREFIX}\E//g;
' "$raw_generated/Funs.lean" > "$normalized_generated/Funs.lean"

cmp "$normalized_generated/Types.lean" "$checked_generated/Types.lean"
cmp "$normalized_generated/Funs.lean" "$checked_generated/Funs.lean"

echo "COMPILE generated helper proof" | tee -a "$log"
aspis_path=${ASPIS_FORMAL_LEAN_PATH:-$(
  cd "$root/AspisFormal" && NO_DNA=1 lake env printenv LEAN_PATH
)}
export LEAN_PATH="$olean_out:$aspis_path:$aeneas_lib"

"$lean_bin" -j 1 -o "$olean_out/V5FriMonotone/Types.olean" \
  "$checked_generated/Types.lean" >> "$log" 2>&1
"$lean_bin" -j 1 -o "$olean_out/V5FriMonotone/FunsExternal.olean" \
  "$checked_generated/FunsExternal.lean" >> "$log" 2>&1
"$lean_bin" -j 1 -o "$olean_out/V5FriMonotone/Funs.olean" \
  "$checked_generated/Funs.lean" >> "$log" 2>&1
"$lean_bin" -j 1 -o "$olean_out/V5FriMonotoneProof.olean" \
  "$proof" >> "$log" 2>&1

if rg -n '\b(sorry|admit|native_decide|axiom|unsafe|ofReduceBool)\b' \
    "$checked_generated/Types.lean" "$checked_generated/Funs.lean" \
    "$checked_generated/FunsExternal.lean" "$proof"; then
  echo "forbidden proof token or generated axiom" >&2
  exit 1
fi
if rg -n 'sorryAx|ofReduceBool' "$log"; then
  echo "forbidden axiom in monotone helper proof" >&2
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

echo "Lean 4.32 V5 monotone opening lookup extraction proof: PASS"
echo "V5_FRI_MONOTONE_REPLAY_OUT=$out"
echo "log: $log"
